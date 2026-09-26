import Blanc.Lift.Curve3Crv.Refine
import Blanc.Lift.StaticCall
import Blanc.Lift.WalkSteps

/-!
# Safety: the writing bodies, inverted

Each segment inverts one function body inside entry 0 from its entry state `entrySt sevm b G`
(the dispatcher's hand-off): a successful halt means the body's raw effect (`Spec.lean`)
succeeded and the post state `Lands` as it says.  The kit: `ric_vyNonpayable`,
`ric_vyAddrArg` (Vyper guards), `ri_caller`, `ri_keccak`, `ri_sload`, `ri_sstore`, `ri_log3`,
`ri_xor`, `ri_staticcall`, the loop rule `SFunc.RunP.loop` / `SFunc.RunCutP.loop`, and
`false_of_noOk` for the reverting arms (`push 0; dup; revert`).  The scratch-slot sequence
`mstore(0xe0, key); mstore(0xc0, slot); keccak(0xc0, 0x40)` inverts to `mapSlot slot key`
by `vySlot_keccak`.

Memory: the prologue image `vyImg [] w` with the constants (`VyClamps`) is carried through
the scratch writes at `0xc0 … 0x100` and `0x140` (`VyClamps.writeAt`); only `0x20` is read.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

/-- **The safety form of a body**: every successful halt from the body's entry lands as a
successful raw effect says. -/
def SafeBody (sevm : Sevm) (b : Devm) (f : SFunc) (raw : Option Raw) : Prop :=
  ∀ G post, SFunc.Run prog sevm (entrySt sevm b G) f (.halted post) →
    ∃ r, raw = some r ∧ Lands sevm b post r

section

variable {sevm : Sevm} {b : Devm}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

-- SEGMENT: safeSetMinter (36 nodes)
/-- `set_minter`.  Proof sketch: `ric_vyNonpayable`, `ric_vyAddrArg` (prologue image),
`ri_push`, `ri_sload` (slot 6), `ri_caller`, `ri_eq`, `ri_push`, `ric_branch` (fall-through
`noOk`), `ric_dest`, `ri_push`, `ri_calldataload`, `ri_push`, `ri_sstore`, and the `STOP`
terminal (`Linst.world_of_ok`-style: `Linst.Run … .stop` keeps the state).  Storage:
`afterSstore`'s target map is `stor₀.set 6 a0` (`afterSstore_getStor_self`), other accounts
unchanged, logs unchanged. -/
theorem safe_setMinter (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_00b0_c0 (rawSetMinter sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x00) (l := 0xba) (fail := t_00b6_c0)
    (by decide) run
  obtain ⟨hm, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x00) (l := 0xcb) (fail := t_00c7_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨hw, G8, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_sstore hfork s1
  cases run with
  | last hl =>
    cases hl
    have hmin : (stor₀).get vyMinterSlot = sevm.caller.toB256 := by
      have h := hw
      simp only [B256.eqCheck] at h
      split_ifs at h with he
      · exact he.symm
      · exact absurd rfl h
    have hm' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := hm
    refine ⟨((stor₀).set vyMinterSlot (Sevm.argWord sevm 0), [], none),
      by simp only [rawSetMinter, hv, hm', hmin, and_self, ite_true], ?_⟩
    refine ⟨?_, fun a ha => ?_, ?_, fun o ho => by cases ho⟩
    · show Devm.getStor (afterSstore sevm _ _ _) _ = _
      rw [afterSstore_getStor_self, afterSload_getStor]
      rfl
    · show Devm.getStor (afterSstore sevm _ _ _) _ = _
      rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]
    · show (afterSstore sevm _ _ _).logs = _
      rw [afterSstore_logs, afterSload_logs, List.append_nil]

-- SEGMENT: safeTransfer (107 nodes)
/-- `transfer`.  Proof sketch: guards as `safeSetMinter`; `PUSH1 3 CALLER` and the scratch
sequence give `vyBalSlot caller`; `DUP1 SLOAD PUSH1 0x24 CALLDATALOAD DUP1 DUP3 LT ISZERO` is the
underflow guard (`ri_lt`, `ri_iszero`, then the taken arm: `¬ (x < v)`), `DUP1 DUP3 SUB SWAP1 POP
SWAP1 POP DUP2 SSTORE POP` stores `x - v` (`ri_sub`, `ri_swap`, `ri_pop`, `ri_sstore`); the
second slot `mapSlot 3 a0` and `DUP2 DUP2 DUP4 ADD LT ISZERO` the overflow guard (`y + v < y` is
`ltCheck` of the wrapped sum: false iff `y.toNat + v.toNat < 2^256`, `B256.toNat_add` and
`Nat.lo_eq_of_lt`); the second `SSTORE`; `mstore(0x140, v)`; `LOG3(0x140, 0x20, sig, caller,
a0)` (`ri_log3`, the window reads back `v.toBytes`); `mstore(0, 1); return(0, 32)`.  The
second read is over the first write's base (`afterSstore`, `getStorVal`), which is exactly
`rawTransfer`'s `st1`. -/
theorem safe_transfer (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_02ce_c0 (rawTransfer sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x02) (l := 0xd8) (fail := t_02d4_c0)
    (by decide) run
  obtain ⟨hd, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x02) (l := 0xe9) (fail := t_02e5_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_caller s1
  obtain ⟨G5, run⟩ := ric_vySlot run
  obtain ⟨hle, G6, run⟩ := ric_vySubStore (p := 0x24) (h := 0x03) (l := 0x0a) (fail := t_0306_c0)
    hfork (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_calldataload s1
  obtain ⟨G10, run⟩ := ric_vySlot run
  obtain ⟨hnof, G11, run⟩ := ric_vyAddStore (p := 0x24) (h := 0x03) (l := 0x38)
    (fail := t_0334_c0) hfork (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_log3 s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
    obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
    have h3 : Bytes.toB256 [0x03] = 3 := by decide
    have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
    have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
    have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
    have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
      show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
      congr 1
    have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
    have htopic : Bytes.toB256 [0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b, 0x69, 0xc2, 0xb0,
        0x68, 0xfc, 0x37, 0x8d, 0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16, 0x28, 0xf5, 0x5a,
        0x4d, 0xf5, 0x23, 0xb3, 0xef] = transferTopic := by decide
    simp only [h3, hv1, hd0] at hle hnof hout hstor hlogs
    simp only [getStorVal_afterStore] at hnof hstor hlogs
    simp only [h320, h32, h0] at hout hlogs
    set M2 := vySlotMem (vySlotMem (vyMem Mem.empty (Sevm.dataWord sevm 0)) 3 sevm.caller.toB256) 3
      (Sevm.argWord sevm 0)
    have hwf2 : Mem.Wf M2 := vySlotMem_wf (vySlotMem_wf hwf0 _ _) _ _
    have hwf3 : Mem.Wf (((M2.write 320 (Sevm.argWord sevm 1).toBytes).read 320 32).2) :=
      (hwf2.write _ _).extend _ _
    rw [Mem.read_write_word_of_wf hwf3] at hout
    rw [Mem.read_write_word_of_wf hwf2] at hlogs
    have hd' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := hd
    set st1 := (stor₀).set (mapSlot 3 sevm.caller.toB256)
      ((stor₀).get (mapSlot 3 sevm.caller.toB256) - Sevm.argWord sevm 1)
    refine ⟨(st1.set (mapSlot 3 (Sevm.argWord sevm 0))
        (st1.get (mapSlot 3 (Sevm.argWord sevm 0)) + Sevm.argWord sevm 1),
      [⟨sevm.currentTarget, [transferTopic, sevm.caller.toB256, Sevm.argWord sevm 0],
        (Sevm.argWord sevm 1).toBytes⟩], some (1 : B256).toBytes), ?_,
      ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_⟩⟩
    · simp only [rawTransfer, vyBalSlot]
      exact ite_eq_left ⟨hv, hd', hle, hnof⟩
    · rw [hstor, getStor_addLog, getStor_afterStore, getStor_afterStore]
      rfl
    · rw [hstor, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha]
    · rw [hlogs, logs_addLog, logs_afterStore, logs_afterStore, htopic]
    · cases ho
      exact hout

-- SEGMENT: safeTransferFrom (172 nodes incl. join entry 3)
/-- `transferFrom`.  Proof sketch: as `safeTransfer` for the two clamps and two balance writes;
then `PUSH1 6 SLOAD CALLER XOR ISZERO PUSH2 0x045b JUMPI` (`ri_xor`; `ric_branchTo` into join
entry 3 `t_045b_c3` when the minter is the caller) or the allowance block (`mapSlot (mapSlot 4
a0) caller`, underflow guard, `SSTORE`, falling into `t_045b_c0`, the inline copy of entry 3).
Both arms end in the same `LOG3(0x140, 0x20, sig, a0, a1)` and `return(0, 32)`: prove the
tail once over an arbitrary base (`ric_jump`/`ric_branchTo` hand the run of `t_045b_c3` over
unchanged). -/
theorem safe_transferFrom (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_0390_c0 (rawTransferFrom sevm stor₀) := by
  sorry

-- SEGMENT: safeApprove (97 nodes incl. join entry 4)
/-- `approve`.  Proof sketch: guards; `PUSH1 0x24 CALLDATALOAD ISZERO ISZERO JUMPI`: a zero value
pushes `1` and jumps (`.jump 4`) to the join `t_04f6_c4`; otherwise the allowance slot
`mapSlot (mapSlot 4 caller) a0` is read and `ISZERO`'d, falling into the same join; the join's
`JUMPI` requires the flag (`noOk` arm).  Then the slot recomputed, `SSTORE v`, `LOG3(0x140,
0x20, approvalSig, caller, a0)`, `return(0, 32)`. -/
theorem safe_approve (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_04ab_c0 (rawApprove sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have h4 : Bytes.toB256 [0x04] = 4 := by decide
  have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  set p := Sevm.argWord sevm 0
  set v := Sevm.argWord sevm 1
  set slot := mapSlot (mapSlot 4 sevm.caller.toB256) p
  -- the join (entry 4) and the write, from any base with `b`'s storage and logs
  have tail : ∀ (b' : Devm) (M' : Mem) (G' : Nat) (flag : B256), Mem.Wf M' →
      (∀ a, Devm.getStor b' a = Devm.getStor b a) → b'.logs = b.logs →
      SFunc.RunCut prog sevm [] (St b' [flag] M' G') t_04f6_c4 (.done (.halted post)) →
      flag ≠ 0 ∧ Lands sevm b post ((stor₀).set slot v,
        [⟨sevm.currentTarget, [approvalTopic, sevm.caller.toB256, p], v.toBytes⟩],
        some (1 : B256).toBytes) := by
    intro b' M' G' flag hwf hst hlg run
    unfold t_04f6_c4 t_04f7_c4 at run
    obtain ⟨G1, run⟩ := ric_dest run
    obtain ⟨G2, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
    rcases ric_branch run with ⟨-, G4, run⟩ | ⟨hflag, G4, run⟩
    · exact (run.false_of_noOk (by decide)).elim
    refine ⟨hflag, ?_⟩
    obtain ⟨G5, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_calldataload s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_caller s1
    obtain ⟨G10, run⟩ := ric_vySlot run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_calldataload s1
    obtain ⟨G13, run⟩ := ric_vySlot run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_sstore hfork s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_calldataload s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_mstore s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_calldataload s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_caller s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_log3 s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_mstore s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_push s1
    cases run with
    | last hl =>
      obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
      have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
      have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
      have htopic : Bytes.toB256 [0x8c, 0x5b, 0xe1, 0xe5, 0xeb, 0xec, 0x7d, 0x5b, 0xd1, 0x4f, 0x71,
          0x42, 0x7d, 0x1e, 0x84, 0xf3, 0xdd, 0x03, 0x14, 0xc0, 0xf7, 0xb2, 0x29, 0x1e, 0x5b, 0x20,
          0x0a, 0xc8, 0xc7, 0xc3, 0xb9, 0x25] = approvalTopic := by decide
      have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
      simp only [hv1, hd0] at hout hstor hlogs
      simp only [h4] at hout hstor hlogs
      simp only [h320, h32, h0] at hout hlogs
      set M2 := vySlotMem (vySlotMem M' 4 sevm.caller.toB256) (mapSlot 4 sevm.caller.toB256) p
      have hwf2 : Mem.Wf M2 := vySlotMem_wf (vySlotMem_wf hwf _ _) _ _
      have hwf3 : Mem.Wf (((M2.write 320 v.toBytes).read 320 32).2) :=
        (hwf2.write _ _).extend _ _
      rw [Mem.read_write_word_of_wf hwf3] at hout
      rw [Mem.read_write_word_of_wf hwf2] at hlogs
      refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_⟩
      · rw [hstor, getStor_addLog, afterSstore_getStor_self, hst]
      · rw [hstor, getStor_addLog, afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), hst]
      · rw [hlogs, logs_addLog, afterSstore_logs, hlg, htopic]
      · cases ho
        exact hout
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x04) (l := 0xb5) (fail := t_04b1_c0)
    (by decide) run
  obtain ⟨hp, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x04) (l := 0xc6) (fail := t_04c2_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  have hp' : p.toNat < 2 ^ 160 := hp
  rcases ric_branch run with ⟨hz, G8, run⟩ | ⟨hnz, G8, run⟩
  · -- a zero value: straight to the join
    have hv0 : v = 0 := by
      rw [hv1] at hz
      by_contra hne
      simp [B256.eqCheck, hne] at hz
      exact absurd hz (by decide)
    unfold t_04d1_c0 at run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨G11, run⟩ := ric_jump (g := t_04f6_c4) (by simp) rfl run
    obtain ⟨-, hl⟩ := tail b _ _ _ hwf0 (fun _ => rfl) rfl run
    exact ⟨_, by simp only [rawApprove]; exact ite_eq_left ⟨hv, hp', .inl hv0⟩, hl⟩
  · -- a nonzero value: the current allowance is read and must be zero
    obtain ⟨G9, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_caller s1
    obtain ⟨G12, run⟩ := ric_vySlot run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_calldataload s1
    obtain ⟨G15, run⟩ := ric_vySlot run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_sload hfork s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_iszero s1
    simp only [hd0] at run
    simp only [h4] at run
    obtain ⟨hflag, hl⟩ := tail _ _ _ _ (vySlotMem_wf (vySlotMem_wf hwf0 _ _) _ _)
      (fun a => afterSload_getStor _ _ _ _) (afterSload_logs _ _ _) run
    have hcur : (stor₀).get slot = 0 := eq_zero_of_iszero_ne_zero hflag
    exact ⟨_, by simp only [rawApprove]; exact ite_eq_left ⟨hv, hp', .inr hcur⟩, hl⟩

-- SEGMENT: safeMintBurn (121 + 117 nodes; `mint` and `burnFrom`, mechanically identical)
/-- `mint` and `burnFrom`.  Proof sketch: guards; minter check as `safeSetMinter`;
`PUSH1 0 PUSH1 4 CALLDATALOAD XOR PUSH2 JUMPI` is `a0 ≠ 0` (`ri_xor`); `PUSH1 5 DUP1 SLOAD …`
the supply update with the overflow (mint) or underflow (burn) guard; the balance slot
`mapSlot 3 a0` read over the supply write's base and its guard and write; `LOG3` with topics
`[sig, 0, a0]` (mint) or `[sig, a0, 0]` (burn); `return(0, 32)`. -/
theorem safe_mint (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_056e_c0 (rawMint sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x05) (l := 0x78) (fail := t_0574_c0)
    (by decide) run
  obtain ⟨hd, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x05) (l := 0x89) (fail := t_0585_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨hmin, G8, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_xor s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G15, run⟩ | ⟨hnz, G15, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  obtain ⟨G16, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨hnof1, G18, run⟩ := ric_vyAddStore (p := 0x24) (h := 0x05) (l := 0xbd)
    (fail := t_05b9_c0) hfork (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_calldataload s1
  obtain ⟨G22, run⟩ := ric_vySlot run
  obtain ⟨hnof2, G23, run⟩ := ric_vyAddStore (p := 0x24) (h := 0x05) (l := 0xeb)
    (fail := t_05e7_c0) hfork (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_log3 s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
    obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
    have h3 : Bytes.toB256 [0x03] = 3 := by decide
    have h5 : Bytes.toB256 [0x05] = vySupplySlot := by decide
    have h6 : Bytes.toB256 [0x06] = vyMinterSlot := by decide
    have hz : Bytes.toB256 [0x00] = 0 := by decide
    have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
    have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
    have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
      show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
      congr 1
    have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
    have htopic : Bytes.toB256 [0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b, 0x69, 0xc2, 0xb0,
        0x68, 0xfc, 0x37, 0x8d, 0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16, 0x28, 0xf5, 0x5a,
        0x4d, 0xf5, 0x23, 0xb3, 0xef] = transferTopic := by decide
    simp only [h3, h5, h6, hz, hv1, hd0] at hmin hnz hnof1 hnof2 hout hstor hlogs
    simp only [getStorVal_afterStore, getStorVal_afterSload,
      afterSload_getStor] at hnof1 hnof2 hstor hlogs
    simp only [h320, h32] at hout hlogs
    set M2 := vySlotMem (vyMem Mem.empty (Sevm.dataWord sevm 0)) 3 (Sevm.argWord sevm 0)
    have hwf2 : Mem.Wf M2 := vySlotMem_wf hwf0 _ _
    have hwf3 : Mem.Wf (((M2.write 320 (Sevm.argWord sevm 1).toBytes).read 320 32).2) :=
      (hwf2.write _ _).extend _ _
    rw [Mem.read_write_word_of_wf hwf3] at hout
    rw [Mem.read_write_word_of_wf hwf2] at hlogs
    have hd' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := hd
    have hmin' : (stor₀).get vyMinterSlot = sevm.caller.toB256 := by
      have h := hmin
      simp only [B256.eqCheck] at h
      split_ifs at h with he
      · exact he.symm
      · exact absurd rfl h
    have hnz' : Sevm.argWord sevm 0 ≠ 0 := by
      rw [B256.xor_zero] at hnz; exact hnz
    set st1 := (stor₀).set vySupplySlot ((stor₀).get vySupplySlot + Sevm.argWord sevm 1)
    refine ⟨(st1.set (mapSlot 3 (Sevm.argWord sevm 0))
        (st1.get (mapSlot 3 (Sevm.argWord sevm 0)) + Sevm.argWord sevm 1),
      [⟨sevm.currentTarget, [transferTopic, 0, Sevm.argWord sevm 0],
        (Sevm.argWord sevm 1).toBytes⟩], some (1 : B256).toBytes), ?_,
      ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_⟩⟩
    · simp only [rawMint]
      exact ite_eq_left ⟨hv, hd', hmin', hnz', hnof1, hnof2⟩
    · rw [hstor, getStor_addLog, getStor_afterStore, getStor_afterStore, afterSload_getStor]
      rfl
    · rw [hstor, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha,
        afterSload_getStor]
    · rw [hlogs, logs_addLog, logs_afterStore, logs_afterStore, afterSload_logs, htopic]
    · cases ho
      exact hout

-- SEGMENT: safeMintBurn (see `safe_mint`)
theorem safe_burnFrom (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_0644_c0 (rawBurnFrom sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x06) (l := 0x4e) (fail := t_064a_c0)
    (by decide) run
  obtain ⟨hd, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x06) (l := 0x5f) (fail := t_065b_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨hmin, G8, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_xor s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G15, run⟩ | ⟨hnz, G15, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  obtain ⟨G16, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨hnof1, G18, run⟩ := ric_vySubStore (p := 0x24) (h := 0x06) (l := 0x91)
    (fail := t_068d_c0) hfork (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_calldataload s1
  obtain ⟨G22, run⟩ := ric_vySlot run
  obtain ⟨hnof2, G23, run⟩ := ric_vySubStore (p := 0x24) (h := 0x06) (l := 0xbd)
    (fail := t_06b9_c0) hfork (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_log3 s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
    obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
    have h3 : Bytes.toB256 [0x03] = 3 := by decide
    have h5 : Bytes.toB256 [0x05] = vySupplySlot := by decide
    have h6 : Bytes.toB256 [0x06] = vyMinterSlot := by decide
    have hz : Bytes.toB256 [0x00] = 0 := by decide
    have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
    have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
    have hv1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
      show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
      congr 1
    have hd0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
    have htopic : Bytes.toB256 [0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b, 0x69, 0xc2, 0xb0,
        0x68, 0xfc, 0x37, 0x8d, 0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16, 0x28, 0xf5, 0x5a,
        0x4d, 0xf5, 0x23, 0xb3, 0xef] = transferTopic := by decide
    simp only [h3, h5, h6, hz, hv1, hd0] at hmin hnz hnof1 hnof2 hout hstor hlogs
    simp only [getStorVal_afterStore, getStorVal_afterSload,
      afterSload_getStor] at hnof1 hnof2 hstor hlogs
    simp only [h320, h32] at hout hlogs
    set M2 := vySlotMem (vyMem Mem.empty (Sevm.dataWord sevm 0)) 3 (Sevm.argWord sevm 0)
    have hwf2 : Mem.Wf M2 := vySlotMem_wf hwf0 _ _
    have hwf3 : Mem.Wf (((M2.write 320 (Sevm.argWord sevm 1).toBytes).read 320 32).2) :=
      (hwf2.write _ _).extend _ _
    rw [Mem.read_write_word_of_wf hwf3] at hout
    rw [Mem.read_write_word_of_wf hwf2] at hlogs
    have hd' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := hd
    have hmin' : (stor₀).get vyMinterSlot = sevm.caller.toB256 := by
      have h := hmin
      simp only [B256.eqCheck] at h
      split_ifs at h with he
      · exact he.symm
      · exact absurd rfl h
    have hnz' : Sevm.argWord sevm 0 ≠ 0 := by
      rw [B256.xor_zero] at hnz; exact hnz
    set st1 := (stor₀).set vySupplySlot ((stor₀).get vySupplySlot - Sevm.argWord sevm 1)
    refine ⟨(st1.set (mapSlot 3 (Sevm.argWord sevm 0))
        (st1.get (mapSlot 3 (Sevm.argWord sevm 0)) - Sevm.argWord sevm 1),
      [⟨sevm.currentTarget, [transferTopic, Sevm.argWord sevm 0, 0],
        (Sevm.argWord sevm 1).toBytes⟩], some (1 : B256).toBytes), ?_,
      ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_⟩⟩
    · simp only [rawBurnFrom]
      exact ite_eq_left ⟨hv, hd', hmin', hnz', hnof1, hnof2⟩
    · have e : b.getStorVal sevm.currentTarget vySupplySlot = (stor₀).get vySupplySlot := rfl
      rw [hstor, getStor_addLog, getStor_afterStore, getStor_afterStore, afterSload_getStor, e]
    · rw [hstor, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha,
        afterSload_getStor]
    · rw [hlogs, logs_addLog, logs_afterStore, logs_afterStore, afterSload_logs, htopic]
    · cases ho
      exact hout

-- SEGMENT: safeSetName (217 nodes incl. loop entries 8 and 11, joins 1 and 2; the largest)
/-- `set_name`: the owner's answer came from the frame's static call to the stored minter.

Proof sketch.  Guards and decoding (`t_00fb_c0`, `t_011b_c0`): two `CALLDATACOPY`s (0x60 bytes
from `a0 + 4` to `0x140`, 0x40 bytes from `a1 + 4` to `0x1c0`; `ri_calldatacopy`) and the length
guards (`GT ISZERO`: `L0 ≤ 64`, `L1 ≤ 32`).  The call (`t_013b_c0`): `mstore(0x220, 0x8da5cb5b)`,
`SLOAD 6`, `GAS`, `ri_staticcall` with window `0x23c … 0x240` (reads `ownerCalldata`) and output
`0x280 … 0x2a0`; the flag's `JUMPI` needs `flag = 1`, giving `StaticAnswered` over the call
site's base, whose `state` is `b`'s (`afterSload` and the pushes keep it); `RETURNDATASIZE > 31`
(`ri_returndatasize`, `ri_gt`) gives `32 ≤ out.length`, and `mload(0x280)` reads
`Bytes.toB256 (out.take 32)` (the output window write), compared to `CALLER` by `EQ`: that is
`OwnerAnswer … w` with `w = caller.toB256`.  Storage and logs are unchanged across the call
(`StaticCallPost.stor`/`logs`).  The two copy loops (entry 8 with join 1, entry 11 with join 2,
each first iteration inlined: `t_019a_c0`, `t_01f4_c1`) are one Vyper shape: stack
`[cap, 0x120, L + 32, base, src, src]`, counter word at `0x120`; invert one generic loop lemma
by `SFunc.RunP.loop` with the invariant "counter `i` at `0x120`, storage is `vyCopyStore … i`,
`i ≤ cap`, `32 (i - 1) ≤ L + 32`", exiting on `32 i > L + 32` (to the join by `.jump 1`/`2`) or
`i = cap` (`branchTo` fall-through); the join pops six words, and after the second loop
`STOP`s.  Neither loop touches `0x140 … 0x200`, the words it copies. -/
theorem safe_setName (hfork : CoveredFork sevm.benvStat.fork) {G : Nat} {post : Devm}
    (run : SFunc.Run prog sevm (entrySt sevm b G) t_00f1_c0 (.halted post)) :
    ∃ w, OwnerAnswer sevm b ((stor₀).get vyMinterSlot).toAdr w ∧
      ∃ r, rawSetName sevm stor₀ (some w) = some r ∧ Lands sevm b post r := by
  sorry

end

end Blanc.Lift.Curve3Crv
