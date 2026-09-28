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

Memory: the address clamp at `0x20` is read from the prologue image `vyImg [] w`
(`vyImg_clamps`, `VyClamps.clamp`) before any scratch write.
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
    refine ⟨?_, fun a ha => ?_, ?_, (fun o ho => by cases ho), ?_⟩
    · show Devm.getStor (afterSstore sevm _ _ _) _ = _
      rw [afterSstore_getStor_self, afterSload_getStor]
      rfl
    · show Devm.getStor (afterSstore sevm _ _ _) _ = _
      rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSload_getStor]
    · show (afterSstore sevm _ _ _).logs = _
      rw [afterSstore_logs, afterSload_logs, List.append_nil]
    · intro _
      change (afterSstore sevm _ _ _).output = b.output
      rw [afterSstore_output, afterSload_output]

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
      ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩⟩
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
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have h3 : Bytes.toB256 [0x03] = 3 := by decide
  have h4 : Bytes.toB256 [0x04] = 4 := by decide
  have h6 : Bytes.toB256 [0x06] = vyMinterSlot := by decide
  have hf0 : Sevm.dataWord sevm (Bytes.toB256 [0x04]) = Sevm.argWord sevm 0 := rfl
  have hd1 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hv2 : Sevm.dataWord sevm (Bytes.toB256 [0x44]) = Sevm.argWord sevm 2 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  -- the shared tail (join entry 3): the event and `return(1)`, from any base
  have tail : ∀ (b' : Devm) (M' : Mem) (G' : Nat), Mem.Wf M' →
      SFunc.RunCut prog sevm [] (St b' [] M' G') t_045b_c3 (.done (.halted post)) →
      (∀ a, Devm.getStor post a = Devm.getStor b' a) ∧
      post.logs = b'.logs ++ [⟨sevm.currentTarget,
        [transferTopic, Sevm.argWord sevm 0, Sevm.argWord sevm 1],
        (Sevm.argWord sevm 2).toBytes⟩] ∧ post.output = (1 : B256).toBytes := by
    intro b' M' G' hwf run
    unfold t_045b_c3 at run
    obtain ⟨G1, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_calldataload s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_mstore s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_calldataload s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_calldataload s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_log3 s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_mstore s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
    cases run with
    | last hl =>
      obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
      have h320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
      have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
      have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
      have htopic : Bytes.toB256 [0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b, 0x69, 0xc2, 0xb0,
          0x68, 0xfc, 0x37, 0x8d, 0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16, 0x28, 0xf5,
          0x5a, 0x4d, 0xf5, 0x23, 0xb3, 0xef] = transferTopic := by decide
      simp only [hf0, hd1, hv2] at hout hlogs
      simp only [h320, h32, h0] at hout hlogs
      have hwf3 : Mem.Wf (((M'.write 320 (Sevm.argWord sevm 2).toBytes).read 320 32).2) :=
        (hwf.write _ _).extend _ _
      rw [Mem.read_write_word_of_wf hwf3] at hout
      rw [Mem.read_write_word_of_wf hwf] at hlogs
      refine ⟨fun a => by rw [hstor, getStor_addLog], ?_, hout⟩
      rw [hlogs, logs_addLog, htopic]
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x03) (l := 0x9a) (fail := t_0396_c0)
    (by decide) run
  obtain ⟨hf, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x03) (l := 0xab) (fail := t_03a7_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨hd, G3, run⟩ := ric_vyAddrArg (p := 0x24) (h := 0x03) (l := 0xbd) (fail := t_03b9_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_calldataload s1
  obtain ⟨G7, run⟩ := ric_vySlot run
  obtain ⟨hle, G8, run⟩ := ric_vySubStore (p := 0x44) (h := 0x03) (l := 0xe0) (fail := t_03dc_c0)
    hfork (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_calldataload s1
  obtain ⟨G12, run⟩ := ric_vySlot run
  obtain ⟨hnof, G13, run⟩ := ric_vyAddStore (p := 0x44) (h := 0x04) (l := 0x0e)
    (fail := t_040a_c0) hfork (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_xor s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  have hwf1 : Mem.Wf (vySlotMem (vySlotMem (vyMem Mem.empty (Sevm.dataWord sevm 0))
      (Bytes.toB256 [0x03]) (Sevm.dataWord sevm (Bytes.toB256 [0x04]))) (Bytes.toB256 [0x03])
      (Sevm.dataWord sevm (Bytes.toB256 [0x24]))) := vySlotMem_wf (vySlotMem_wf hwf0 _ _) _ _
  rcases ric_branchTo (g := t_045b_c3) (by simp) rfl run with ⟨hx, G20, run⟩ | ⟨hx, G20, run⟩
  · -- the caller is not the minter: the allowance is spent
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_calldataload s1
    obtain ⟨G24, run⟩ := ric_vySlot run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_caller s1
    obtain ⟨G26, run⟩ := ric_vySlot run
    obtain ⟨hle2, G27, run⟩ := ric_vySubStore (p := 0x44) (h := 0x04) (l := 0x50)
      (fail := t_044c_c0) hfork (by decide) run
    obtain ⟨hst, hlg, hout⟩ := tail _ _ _ (vySlotMem_wf (vySlotMem_wf hwf1 _ _) _ _) run
    have gv : ∀ k, b.getStorVal sevm.currentTarget k = (stor₀).get k := fun _ => rfl
    have hf' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := hf
    have hd' : (Sevm.argWord sevm 1).toNat < 2 ^ 160 := by rw [← hd1]; exact hd
    simp only [hf0, hd1, hv2] at hle hnof hle2 hx hst hlg
    simp only [h3, h4, h6] at hle hnof hle2 hx hst hlg
    simp only [getStorVal_afterStore, getStorVal_afterSload, getStor_afterStore] at hnof hle2 hx
    simp only [gv] at hle hnof hle2 hx
    have hspend : ((((stor₀).set (mapSlot 3 (Sevm.argWord sevm 0))
        ((stor₀).get (mapSlot 3 (Sevm.argWord sevm 0)) - Sevm.argWord sevm 2)).set
        (mapSlot 3 (Sevm.argWord sevm 1))
        ((((stor₀).set (mapSlot 3 (Sevm.argWord sevm 0))
          ((stor₀).get (mapSlot 3 (Sevm.argWord sevm 0)) - Sevm.argWord sevm 2)).get
          (mapSlot 3 (Sevm.argWord sevm 1))) + Sevm.argWord sevm 2)).get vyMinterSlot) ≠
        sevm.caller.toB256 := by
      intro he
      rw [he] at hx
      simp [B256.eqCheck, B256.xor_eq_zero_iff] at hx
      exact absurd hx (by decide)
    refine ⟨?r, ?raw, ?lands⟩
    case raw =>
      simp only [rawTransferFrom]
      rw [ite_eq_left ⟨hv, hf', hd', hle, hnof, fun _ => hle2⟩, ite_eq_left hspend]
    refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩
    · rw [hst, getStor_afterStore, afterSload_getStor, getStor_afterStore, getStor_afterStore]
      simp only [getStorVal_afterStore, getStorVal_afterSload, getStor_afterStore, gv]
    · rw [hst, getStor_afterStore_ne ha, afterSload_getStor, getStor_afterStore_ne ha,
        getStor_afterStore_ne ha]
    · rw [hlg, logs_afterStore, afterSload_logs, logs_afterStore, logs_afterStore]
    · cases ho
      exact hout
  · -- the caller is the minter: no allowance
    obtain ⟨hst, hlg, hout⟩ := tail _ _ _ hwf1 run
    have gv : ∀ k, b.getStorVal sevm.currentTarget k = (stor₀).get k := fun _ => rfl
    have hf' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := hf
    have hd' : (Sevm.argWord sevm 1).toNat < 2 ^ 160 := by rw [← hd1]; exact hd
    simp only [hf0, hd1, hv2] at hle hnof hx hst hlg
    simp only [h3, h6] at hle hnof hx hst hlg
    simp only [getStorVal_afterStore, getStor_afterStore] at hnof hx
    simp only [gv] at hle hnof hx
    have hnspend : ¬ (((((stor₀).set (mapSlot 3 (Sevm.argWord sevm 0))
        ((stor₀).get (mapSlot 3 (Sevm.argWord sevm 0)) - Sevm.argWord sevm 2)).set
        (mapSlot 3 (Sevm.argWord sevm 1))
        ((((stor₀).set (mapSlot 3 (Sevm.argWord sevm 0))
          ((stor₀).get (mapSlot 3 (Sevm.argWord sevm 0)) - Sevm.argWord sevm 2)).get
          (mapSlot 3 (Sevm.argWord sevm 1))) + Sevm.argWord sevm 2)).get vyMinterSlot) ≠
        sevm.caller.toB256) := by
      intro hne
      apply hne
      have := eq_zero_of_iszero_ne_zero hx
      rw [B256.xor_eq_zero_iff] at this
      exact this.symm
    refine ⟨?r2, ?raw2, ?lands2⟩
    case raw2 =>
      simp only [rawTransferFrom]
      rw [ite_eq_left ⟨hv, hf', hd', hle, hnof, fun h => absurd h hnspend⟩, ite_eq_right hnspend]
    refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩
    · rw [hst, afterSload_getStor, getStor_afterStore, getStor_afterStore]
      simp only [getStorVal_afterStore, gv]
    · rw [hst, afterSload_getStor, getStor_afterStore_ne ha, getStor_afterStore_ne ha]
    · rw [hlg, afterSload_logs, logs_afterStore, logs_afterStore]
    · cases ho
      exact hout

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
      refine ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩
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
      ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩⟩
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
      ⟨?_, fun a ha => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩⟩
    · simp only [rawBurnFrom]
      exact ite_eq_left ⟨hv, hd', hmin', hnz', hnof1, hnof2⟩
    · have e : b.getStorVal sevm.currentTarget vySupplySlot = (stor₀).get vySupplySlot := rfl
      rw [hstor, getStor_addLog, getStor_afterStore, getStor_afterStore, afterSload_getStor, e]
    · rw [hstor, getStor_addLog, getStor_afterStore_ne ha, getStor_afterStore_ne ha,
        afterSload_getStor]
    · rw [hlogs, logs_addLog, logs_afterStore, logs_afterStore, afterSload_logs, htopic]
    · cases ho
      exact hout

/-! ### `set_name`'s two copy loops, inverted -/

/-- A copy loop's word `i`, read back from memory. -/
private theorem storeWord {M : Mem} {sn i : Nat} {src : Bytes}
    (h : (M.read (sn + 32 * i) 32).1 = src.sliceD (32 * i) 32 0) :
    Bytes.toB256 (M.read (sn + 32 * i) 32).1 = Bytes.toB256 (src.sliceD (32 * i) 32 0) := by
  rw [h]

/-- **One of `set_name`'s store segments, inverted**: the set-up and the loop at entry `k` (cap
`n + 1`) store `min (n + 1) ((32 + L) / 32 + 1)` words of `src` (read at `sn` in memory, `L` its
first word) at the string's base, and the run goes on at the loop's exit tree `exitT` (entry `j`)
with six more words on the stack; memory from `0x140` up is kept. -/
theorem ric_storeSeg (hfork : CoveredFork sevm.benvStat.fork) {d : Devm} {S : List B256} {M : Mem}
    {G : Nat} {o : Outcome} {s0 s1 sl cp e0 e1 x0 x1 r0 r1 : UInt8} {j k n sn : Nat}
    {exitT : SFunc} {src : Bytes}
    (hk : prog[k]? = some (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT))
    (hj : prog[j]? = some exitT) (hcase : (cp = 3 ∧ n = 2) ∨ (cp = 2 ∧ n = 1))
    (hs : M.size = 672) (hwf : Mem.Wf M) (hsn : (Bytes.toB256 [s0, s1]).toNat = sn)
    (hsn1 : 0x140 ≤ sn) (hsn2 : sn + 32 * (n + 1) ≤ 672)
    (hsrc : ∀ i, i ≤ n → (M.read (sn + 32 * i) 32).1 = src.sliceD (32 * i) 32 0)
    (hL : (Bytes.toB256 (src.sliceD 0 32 0)).toNat ≤ 32 * n)
    (run : SFunc.RunCut prog sevm [] (St d S M G)
      (vyStoreHead s0 s1 sl cp (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT)) (.done o)) :
    ∃ (x1 x2 x3 x4 x5 x6 : B256) (d' : Devm) (M' : Mem) (G' : Nat),
      SFunc.RunCut prog sevm [] (St d' (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: S) M' G') exitT
        (.done o) ∧
      Devm.getStor d' sevm.currentTarget = vyCopyStore (Devm.getStor d sevm.currentTarget)
        (Bytes.toB256 [sl]).toBytes.keccak src
        (min (n + 1) ((32 + (Bytes.toB256 (src.sliceD 0 32 0)).toNat) / 32 + 1)) ∧
      (∀ a, a ≠ sevm.currentTarget → Devm.getStor d' a = Devm.getStor d a) ∧
      d'.logs = d.logs ∧ d'.output = d.output ∧ M'.size = 672 ∧ Mem.Wf M' ∧
      (∀ a len, 0x140 ≤ a → (M'.read a len).1 = (M.read a len).1) := by
  obtain ⟨G1, run⟩ := ric_vyStoreHead hs (by decide) (by decide) hwf hsn (by omega) (by omega) run
  set base := (Bytes.toB256 [sl]).toBytes.keccak
  set L := (Bytes.toB256 (src.sliceD 0 32 0)).toNat with hLdef
  have hLw : Bytes.toB256 (M.read sn 32).1 = Bytes.toB256 (src.sliceD 0 32 0) := by
    have := hsrc 0 (Nat.zero_le _); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this]
  rw [hLw] at run
  set lp := Bytes.toB256 (src.sliceD 0 32 0) + Bytes.toB256 [0x20]
  have hlp : lp.toNat = L + 32 := by
    rw [B256.toNat_add, show (Bytes.toB256 [0x20]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by omega)]
  set M1 := M.write 0xc0 (Bytes.toB256 [sl]).toBytes
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  set M2 := M1.write 0x120 (Nat.toB256 0).toBytes
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hsz : ∀ (N : Mem) (w : B256), N.size = 672 → (N.write 0x120 w.toBytes).size = 672 := by
    intro N w h; rw [Mem.size_write_of_le (by rw [B256.length_toBytes, h]; omega), h]
  have hs1 : M1.size = 672 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hs]; omega), hs]
  have hs2 : M2.size = 672 := hsz M1 _ hs1
  have hkeep : ∀ (N : Mem) (w : B256) (n' : Nat), Mem.Wf N → n' + 32 ≤ 0x140 →
      ∀ a len, 0x140 ≤ a → ((N.write n' w.toBytes).read a len).1 = (N.read a len).1 :=
    fun N w n' hN hn a len ha =>
      Mem.read_write_disjoint hN _ _ (Or.inl (by rw [B256.length_toBytes]; omega))
  have hk2 : ∀ a len, 0x140 ≤ a → (M2.read a len).1 = (M.read a len).1 := by
    intro a len ha
    rw [hkeep M1 _ _ hwf1 (by omega) a len ha, hkeep M _ _ hwf (by omega) a len ha]
  have hc2 : (M2.read 0x120 32).1 = (Nat.toB256 0).toBytes := Mem.read_write_word_of_wf hwf1 _ _
  set cap := Bytes.toB256 [cp] + Bytes.toB256 [0x00]
  have hne1 : cap ≠ Nat.toB256 (0 + 1) := by rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hkC : k ∉ ([] : List Nat) := by simp
  have hjC : j ∉ ([] : List Nat) := by simp
  -- iteration 0
  rcases ric_vyStoreIter hfork (i := 0) hs2 (by decide) (by decide) hsn (by omega) (by decide) hc2
    hk hkC hj hjC run with ⟨hlt, -⟩ | ⟨-, G2, run⟩
  · omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false hne1)] at run
  rw [hk2 _ _ (by omega), storeWord (hsrc 0 (Nat.zero_le _))] at run
  set d1 := afterSstore sevm d (base + Nat.toB256 0) (Bytes.toB256 (src.sliceD (32 * 0) 32 0))
  set M3 := M2.write 0x120 (Nat.toB256 (0 + 1)).toBytes
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hs3 : M3.size = 672 := hsz M2 _ hs2
  have hk3 : ∀ a len, 0x140 ≤ a → (M3.read a len).1 = (M.read a len).1 := by
    intro a len ha; rw [hkeep M2 _ _ hwf2 (by omega) a len ha, hk2 a len ha]
  have hc3 : (M3.read 0x120 32).1 = (Nat.toB256 1).toBytes := Mem.read_write_word_of_wf hwf2 _ _
  -- iteration 1
  rcases ric_vyStoreIter hfork (i := 1) hs3 (by decide) (by decide) hsn (by omega) (by decide) hc3
    hk hkC hj hjC run with ⟨hlt, -⟩ | ⟨-, G3, run⟩
  · omega
  rw [hk3 _ _ (by omega), storeWord (hsrc 1 (by omega))] at run
  set d2 := afterSstore sevm d1 (base + Nat.toB256 1) (Bytes.toB256 (src.sliceD (32 * 1) 32 0))
  set M4 := M3.write 0x120 (Nat.toB256 (1 + 1)).toBytes
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hs4 : M4.size = 672 := hsz M3 _ hs3
  have hk4 : ∀ a len, 0x140 ≤ a → (M4.read a len).1 = (M.read a len).1 := by
    intro a len ha; rw [hkeep M3 _ _ hwf3 (by omega) a len ha, hk3 a len ha]
  have hst2 : Devm.getStor d2 sevm.currentTarget =
      vyCopyStore (Devm.getStor d sevm.currentTarget) base src 2 := by
    simp only [d2, d1, afterSstore_getStor_self]; rfl
  have hot2 : ∀ a, a ≠ sevm.currentTarget → Devm.getStor d2 a = Devm.getStor d a := by
    intro a ha
    simp only [d2, d1]
    rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha)]
  have hlg2 : d2.logs = d.logs := by simp only [d2, d1, afterSstore_logs]
  have hout2 : d2.output = d.output := by simp only [d2, d1, afterSstore_output]
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `name`: a third pass
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at run
    have hc4 : (M4.read 0x120 32).1 = (Nat.toB256 2).toBytes := Mem.read_write_word_of_wf hwf3 _ _
    rcases ric_vyStoreIter hfork (i := 2) hs4 (by decide) (by decide) hsn (by omega) (by decide)
      hc4 hk hkC hj hjC run with ⟨hlt, G4, run⟩ | ⟨hle, G4, run⟩
    · refine ⟨_, _, _, _, _, _, d2, M4, G4, run, ?_, hot2, hlg2, hout2, hs4, hwf4, hk4⟩
      rw [hst2]
      congr 1
      omega
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at run
      rw [hk4 _ _ (by omega), storeWord (hsrc 2 le_rfl)] at run
      refine ⟨_, _, _, _, _, _, _, M4.write 0x120 (Nat.toB256 (2 + 1)).toBytes, G4, run, ?_, ?_,
        ?_, ?_, hsz M4 _ hs4, hwf4.write _ _, ?_⟩
      · rw [afterSstore_getStor_self, hst2, show min (2 + 1) ((32 + L) / 32 + 1) = 3 by omega]
        rfl
      · intro a ha
        rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ha), hot2 a ha]
      · rw [afterSstore_logs, hlg2]
      · rw [afterSstore_output, hout2]
      · intro a len ha; rw [hkeep M4 _ _ hwf4 (by omega) a len ha, hk4 a len ha]
  · -- `symbol`: the counter reached the cap
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at run
    refine ⟨_, _, _, _, _, _, d2, M4, G3, run, ?_, hot2, hlg2, hout2, hs4, hwf4, hk4⟩
    rw [hst2, show min (1 + 1) ((32 + L) / 32 + 1) = 2 by omega]

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
  have hM0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 := vyMem_wf Mem.wf_empty (Sevm.dataWord sevm 0)
  have hr0 : Mem.Reads (vyMem Mem.empty (Sevm.dataWord sevm 0)) (vyImg [] (Sevm.dataWord sevm 0)) :=
    vyMem_reads Mem.wf_empty Mem.reads_empty _
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x00) (l := 0xfb) (fail := t_00f7_c0)
    (by decide) run
  -- `name`'s bytes to `0x140`, its length guard
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_calldatacopy s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G18, run⟩ | ⟨hg0, G18, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  obtain ⟨G19, run⟩ := ric_dest run
  -- `symbol`'s bytes to `0x1c0`, its length guard
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_calldatacopy s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G36, run⟩ | ⟨hg1, G36, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  obtain ⟨G37, run⟩ := ric_dest run
  -- the owner call
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨gw, G48, rfl⟩ := ri_gas s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨flag, out, hpost, hans⟩ := ri_staticcall hfork s1
  rw [hpost.eq_St] at run
  have n320 : (Bytes.toB256 [0x01, 0x40]).toNat = 320 := by decide
  have n96 : (Bytes.toB256 [0x60]).toNat = 96 := by decide
  have n448 : (Bytes.toB256 [0x01, 0xc0]).toNat = 448 := by decide
  have n64 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have n544 : (Bytes.toB256 [0x02, 0x20]).toNat = 544 := by decide
  have n572 : (Bytes.toB256 [0x02, 0x3c]).toNat = 572 := by decide
  have n4 : (Bytes.toB256 [0x04]).toNat = 4 := by decide
  have n640 : (Bytes.toB256 [0x02, 0x80]).toNat = 640 := by decide
  have n32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have n6 : Bytes.toB256 [0x06] = vyMinterSlot := by decide
  simp only [n320, n96, n448, n64, n544, n572, n4, n640, n32, n6] at run hans
  set s0B := Bytes.toB256 [0x04] + Sevm.dataWord sevm (Bytes.toB256 [0x04])
  set s1B := Bytes.toB256 [0x04] + Sevm.dataWord sevm (Bytes.toB256 [0x24])
  set src0 := sevm.data.sliceD s0B.toNat 96 0
  set src1 := sevm.data.sliceD s1B.toNat 64 0
  set selw := Bytes.toB256 [0x8d, 0xa5, 0xcb, 0x5b]
  set M0 := vyMem Mem.empty (Sevm.dataWord sevm 0)
  set M1 := M0.write 320 src0
  set M2 := M1.write 448 src1
  set M3 := M2.write 544 selw.toBytes
  set M3e := M3.extends [(572, 4), (640, 32)]
  set M4 := M3e.write 640 (out.take 32)
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf3e : Mem.Wf M3e := Mem.Wf.extends _ hwf3
  have hwf4 : Mem.Wf M4 := hwf3e.write _ _
  have hs1 : M1.size = 416 := by
    rw [Mem.size_write_of_length (List.length_sliceD _ _ _ _) (by decide), hM0]; rfl
  have hs2 : M2.size = 512 := by
    rw [Mem.size_write_of_length (List.length_sliceD _ _ _ _) (by decide), hs1]; rfl
  have hs3 : M3.size = 576 := by
    rw [Mem.size_write_of_length (B256.length_toBytes _) (by decide), hs2]; rfl
  have hs3e : M3e.size = 672 := by
    show memExtsSize M3.size _ = _
    rw [hs3]; rfl
  have hs4 : M4.size = 672 := by
    rw [Mem.size_write_of_le (by rw [hs3e, List.length_take]; omega), hs3e]
  have hr4 : Mem.Reads M4 (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (vyImg [] (Sevm.dataWord sevm 0)) 320 src0) 448 src1) 544 selw.toBytes) 640 (out.take 32)) :=
    (Mem.Reads.extends _ (((hr0.write hwf0 _ _).write hwf1 _ _).write hwf2 _ _)).write hwf3e _ _
  -- the flag, the answer's length, its first word
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G50, run⟩ | ⟨hfl, G50, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hflag : flag = 1 := by
    rcases hpost.flag with h | h
    · exact absurd h hfl
    · exact h
  obtain ⟨G51, run⟩ := ric_dest run
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G52, rfl⟩ := ri_push s1
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G53, rfl⟩ := ri_returndatasize s1
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G54, rfl⟩ := ri_gt s1
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G55, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G56, run⟩ | ⟨hrds, G56, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  rw [hpost.returnData] at hrds
  have hlen : 32 ≤ out.length := by
    by_contra hc
    apply hrds
    rw [B256.gtCheck, ite_eq_right_iff]
    intro h
    rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256, Nat.lo,
      show (Bytes.toB256 [0x1f]).toNat = 31 by decide] at h
    have := Nat.mod_le out.length (2 ^ 256)
    omega
  obtain ⟨G57, run⟩ := ric_dest run
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G58, rfl⟩ := ri_push s1
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G59, rfl⟩ := ri_pop s1
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G60, rfl⟩ := ri_push s1
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G61, rfl⟩ := ri_mload s1
  rw [n640, read_covered hs4 (by decide) (by decide)] at run
  have hw640 : (M4.read 640 32).1 = out.take 32 := by
    rw [hr4.read]
    have h := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (vyImg [] (Sevm.dataWord sevm 0)) 320 src0) 448 src1) 544 selw.toBytes) (out.take 32) 640
    rwa [List.length_take, Nat.min_eq_left hlen] at h
  rw [hw640] at run
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G62, rfl⟩ := ri_eq s1
  obtain ⟨d2, s1, run⟩ := ric_next run; obtain ⟨G63, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G64, run⟩ | ⟨heq, G64, run⟩
  · exact (run.false_of_noOk (by decide)).elim
  have hword : Bytes.toB256 (out.take 32) = sevm.caller.toB256 := by
    by_contra hc
    exact heq (by simp [B256.eqCheck, hc])
  obtain ⟨G65, run⟩ := ric_dest run
  -- the two copy loops
  have hL0w : Bytes.toB256 (src0.sliceD 0 32 0) = Sevm.dataWord sevm s0B := by
    rw [Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by decide), Nat.add_zero]; rfl
  have hL1w : Bytes.toB256 (src1.sliceD 0 32 0) = Sevm.dataWord sevm s1B := by
    rw [Bytes.sliceD_sliceD_of_le _ _ _ _ _ (by decide), Nat.add_zero]; rfl
  have hL0 : (Sevm.dataWord sevm s0B).toNat ≤ 64 :=
    toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hg0)
  have hL1 : (Sevm.dataWord sevm s1B).toNat ≤ 32 :=
    toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hg1)
  have hsrc0 : ∀ i, i ≤ 2 → (M4.read (320 + 32 * i) 32).1 = src0.sliceD (32 * i) 32 0 := by
    intro i hi
    rw [hr4.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_sliceD]; omega),
      Nat.add_sub_cancel_left]
  obtain ⟨y1, y2, y3, y4, y5, y6, d2, M5, G66, run, hst2, hot2, hlg2, hout2, hs5, hwf5, hkeep5⟩ :=
    ric_storeSeg (s0 := 0x01) (s1 := 0x40) (sl := 0x00) (cp := 0x03) (e0 := 0x01) (e1 := 0xad)
      (x0 := 0x01) (x1 := 0xcf) (r0 := 0x01) (r1 := 0x9a) (j := 1) (k := 8) (n := 2)
      (exitT := t_01cf_c1) (src := src0) hfork rfl rfl (Or.inl ⟨rfl, rfl⟩) hs4 hwf4 n320
      (by decide) (by decide) hsrc0 (by rw [hL0w]; omega) run
  have hsrc1 : ∀ i, i ≤ 1 → (M5.read (448 + 32 * i) 32).1 = src1.sliceD (32 * i) 32 0 := by
    intro i hi
    rw [hkeep5 _ _ (by omega), hr4.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_sliceD]; omega),
      Nat.add_sub_cancel_left]
  unfold t_01cf_c1 at run
  obtain ⟨G67, run⟩ := ric_dest run
  obtain ⟨d3, s1, run⟩ := ric_next run; obtain ⟨G68, rfl⟩ := ri_pop s1
  obtain ⟨d3, s1, run⟩ := ric_next run; obtain ⟨G69, rfl⟩ := ri_pop s1
  obtain ⟨d3, s1, run⟩ := ric_next run; obtain ⟨G70, rfl⟩ := ri_pop s1
  obtain ⟨d3, s1, run⟩ := ric_next run; obtain ⟨G71, rfl⟩ := ri_pop s1
  obtain ⟨d3, s1, run⟩ := ric_next run; obtain ⟨G72, rfl⟩ := ri_pop s1
  obtain ⟨d3, s1, run⟩ := ric_next run; obtain ⟨G73, rfl⟩ := ri_pop s1
  obtain ⟨z1, z2, z3, z4, z5, z6, d3, M6, G74, run, hst3, hot3, hlg3, hout3, -, -, -⟩ :=
    ric_storeSeg (s0 := 0x01) (s1 := 0xc0) (sl := 0x01) (cp := 0x02) (e0 := 0x02) (e1 := 0x07)
      (x0 := 0x02) (x1 := 0x29) (r0 := 0x01) (r1 := 0xf4) (j := 2) (k := 11) (n := 1)
      (exitT := t_0229_c2) (src := src1) hfork rfl rfl (Or.inr ⟨rfl, rfl⟩) hs5 hwf5 n448
      (by decide) (by decide) hsrc1 (by rw [hL1w]; omega) run
  unfold t_0229_c2 at run
  obtain ⟨G75, run⟩ := ric_dest run
  obtain ⟨d4, s1, run⟩ := ric_next run; obtain ⟨G76, rfl⟩ := ri_pop s1
  obtain ⟨d4, s1, run⟩ := ric_next run; obtain ⟨G77, rfl⟩ := ri_pop s1
  obtain ⟨d4, s1, run⟩ := ric_next run; obtain ⟨G78, rfl⟩ := ri_pop s1
  obtain ⟨d4, s1, run⟩ := ric_next run; obtain ⟨G79, rfl⟩ := ri_pop s1
  obtain ⟨d4, s1, run⟩ := ric_next run; obtain ⟨G80, rfl⟩ := ri_pop s1
  obtain ⟨d4, s1, run⟩ := ric_next run; obtain ⟨G81, rfl⟩ := ri_pop s1
  cases run with
  | last hl =>
    cases hl
    have hs0 : s0B = Sevm.argWord sevm 0 + 4 := by
      show Bytes.toB256 [0x04] + Sevm.dataWord sevm (Bytes.toB256 [0x04]) = _
      rw [B256.add_comm, show Bytes.toB256 [0x04] = 4 by decide]; rfl
    have hs1 : s1B = Sevm.argWord sevm 1 + 4 := by
      show Bytes.toB256 [0x04] + Sevm.dataWord sevm (Bytes.toB256 [0x24]) = _
      rw [B256.add_comm, show Bytes.toB256 [0x04] = 4 by decide]
      congr 1
    have hnb : (Bytes.toB256 [0x00]).toBytes.keccak = vyNameBase := by
      rw [show Bytes.toB256 [0x00] = 0 by decide]; rfl
    have hsb : (Bytes.toB256 [0x01]).toBytes.keccak = vySymbolBase := by
      rw [show Bytes.toB256 [0x01] = 1 by decide]; rfl
    have hd1 : ∀ a, Devm.getStor d1 a = Devm.getStor b a := by
      intro a; rw [hpost.stor a, afterSload_getStor]
    have hin : (M3.read 572 4).1 = ownerCalldata := by
      rw [((Mem.reads_data M2).write hwf2 544 selw.toBytes).read,
        Bytes.sliceD_writeAt_inside _ _ _ _ _ (by decide) (by rw [B256.length_toBytes])]
      decide
    have hans' := hans hflag
    rw [hin] at hans'
    refine ⟨sevm.caller.toB256, ⟨out, ?_, hlen, hword⟩,
      (vyCopyStore (vyCopyStore stor₀ vyNameBase src0
        (min 3 ((32 + (Sevm.dataWord sevm s0B).toNat) / 32 + 1))) vySymbolBase src1
        (min 2 ((32 + (Sevm.dataWord sevm s1B).toNat) / 32 + 1)), [], none), ?_, ?_⟩
    · obtain ⟨parent, child, xl, dp, na, code, gas, hst, hdel, hfill, hproc, hclean, hout⟩ := hans'
      refine ⟨parent, child, xl, dp, na, code, gas, ?_, ?_, hfill, hproc, hclean, hout⟩
      · rw [hst]; unfold afterSload; split <;> rfl
      · simp only [afterSload_getCode] at hdel; exact hdel
    · simp only [rawSetName, ← hs0, ← hs1]
      exact ite_eq_left ⟨hv, hL0, hL1, trivial⟩
    · refine ⟨?_, fun a ha => ?_, ?_, (fun o ho => by cases ho), ?_⟩
      · show Devm.getStor d3 _ = _
        rw [hst3, hst2, hd1, hnb, hsb, hL0w, hL1w]
      · show Devm.getStor d3 _ = _
        rw [hot3 a ha, hot2 a ha, hd1]
      · show d3.logs = _
        rw [hlg3, hlg2, hpost.logs, afterSload_logs, List.append_nil]
      · intro _
        change d3.output = b.output
        rw [hout3, hout2, hpost.output hflag, afterSload_output]

/-! ### The word views, inverted -/

/-- The tail every word view ends with, inverted: `SLOAD` the key, `mstore(0, word)`,
`return(0, 32)` returns exactly the stored word and keeps storage and logs. -/
private theorem safe_wordTail (hfork : CoveredFork sevm.benvStat.fork) {M : Mem} (hwf : Mem.Wf M)
    {k : B256} {G : Nat} {post : Devm}
    (run : SFunc.RunCut prog sevm [] (St b [k] M G)
      (.next (.reg .sload) (.next (.push [0x00] (by decide)) (.next (.reg .mstore)
        (.next (.push [0x20] (by decide)) (.next (.push [0x00] (by decide)) (.last .return_))))))
      (.done (.halted post))) :
    Lands sevm b post (stor₀, [], some (b.getStorVal sevm.currentTarget k).toBytes) := by
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
    obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
    have h0 : (Bytes.toB256 [0x00]).toNat = 0 := by decide
    have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
    refine ⟨?_, fun a _ => ?_, ?_, fun o ho => ?_, fun h => by cases h⟩
    · rw [hstor, afterSload_getStor]
    · rw [hstor, afterSload_getStor]
    · rw [hlogs, afterSload_logs, List.append_nil]
    · cases ho
      rw [hout, h0, h32, Mem.read_write_word_of_wf hwf]

-- SEGMENT: safeWordViews (the four word views, inverted)
/-- `totalSupply()`, inverted. -/
theorem safe_totalSupply (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_0240_c0 (rawTotalSupply sevm stor₀) := by
  intro G post run
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x02) (l := 0x4a) (fail := t_0246_c0)
    (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  exact ⟨_, by simp only [rawTotalSupply, hv, ite_true]; rfl,
    safe_wordTail hfork (vyMem_wf Mem.wf_empty _) run⟩

/-- `decimals()`, inverted. -/
theorem safe_decimals (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_087e_c0 (rawDecimals sevm stor₀) := by
  intro G post run
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x08) (l := 0x88) (fail := t_0884_c0)
    (by decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  exact ⟨_, by simp only [rawDecimals, hv, ite_true]; rfl,
    safe_wordTail hfork (vyMem_wf Mem.wf_empty _) run⟩

/-- `balanceOf(a)`, inverted. -/
theorem safe_balanceOf (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_08a5_c0 (rawBalanceOf sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x08) (l := 0xaf) (fail := t_08ab_c0)
    (by decide) run
  obtain ⟨ha, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x08) (l := 0xc0) (fail := t_08bc_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_calldataload s1
  obtain ⟨G6, run⟩ := ric_vySlot run
  have ha' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := ha
  exact ⟨_, by simp only [rawBalanceOf, hv, ha', and_self, ite_true]; rfl,
    safe_wordTail hfork (vySlotMem_wf (vyMem_wf Mem.wf_empty _) _ _) run⟩

/-- `allowance(o, p)`, inverted. -/
theorem safe_allowance (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_0267_c0 (rawAllowance sevm stor₀) := by
  intro G post run
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold entrySt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := 0x02) (l := 0x71) (fail := t_026d_c0)
    (by decide) run
  obtain ⟨ho, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x02) (l := 0x82) (fail := t_027e_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨hq, G3, run⟩ := ric_vyAddrArg (p := 0x24) (h := 0x02) (l := 0x94) (fail := t_0290_c0)
    (by decide) (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_calldataload s1
  obtain ⟨G7, run⟩ := ric_vySlot run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_calldataload s1
  obtain ⟨G10, run⟩ := ric_vySlot run
  have ho' : (Sevm.argWord sevm 0).toNat < 2 ^ 160 := ho
  have hq4 : Sevm.dataWord sevm (Bytes.toB256 [0x24]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have hq' : (Sevm.argWord sevm 1).toNat < 2 ^ 160 := by rw [← hq4]; exact hq
  rw [hq4] at run
  exact ⟨_, by simp only [rawAllowance, hv, ho', hq', and_self, ite_true]; rfl,
    safe_wordTail hfork (vySlotMem_wf (vySlotMem_wf (vyMem_wf Mem.wf_empty _) _ _) _ _) run⟩

end


/-! ### The string views, inverted -/

section StrViews

variable {sevm : Sevm} {b : Devm}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

/-- The string views' join, inverted: over a memory whose word at `0x180` is the length and
whose bytes at `0x1a0` are the string, a successful halt returns exactly `abiString` of the
string and keeps storage and logs. -/
theorem safe_strJoin (hcd : sevm.data.length < 2 ^ 256) {M : Mem} {sz : Nat} {Lw : B256}
    {str : Bytes} {a1 a2 a3 a4 a5 a6 : B256} (hwf : Mem.Wf M) (hs : M.size = sz)
    (hsz32 : sz % 32 = 0) (hsz : 0x1a0 + ceil32 Lw.toNat ≤ sz) (hL : Lw.toNat ≤ 64)
    (hLw : (M.read 0x180 32).1 = Lw.toBytes) (hstr : (M.read 0x1a0 Lw.toNat).1 = str)
    (hlen : str.length = Lw.toNat) (bb : Devm) {G : Nat} {post : Devm}
    (run : SFunc.RunCut prog sevm [] (St bb [a1, a2, a3, a4, a5, a6] M G) t_0774_c5
      (.done (.halted post))) :
    (∀ a, Devm.getStor post a = Devm.getStor bb a) ∧ post.logs = bb.logs ∧
      post.output = abiString str := by
  unfold t_0774_c5 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_dup (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_mod s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_calldatasize s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_calldatacopy s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_mod s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G48, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G50, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
  refine ⟨hstor, hlogs, ?_⟩
  rw [hout]
  set L := Lw.toNat with hLdef
  have hc := ceil32_eq L
  have h180 : (Bytes.toB256 [0x01, 0x80]).toNat = 384 := by decide
  have h160 : (Bytes.toB256 [0x01, 0x60]).toNat = 352 := by decide
  rw [h180, read_covered hs hsz32 (by omega), hLw, B256.toB256_toBytes]
  set z := ceil32 L - L with hzdef
  have hz : z = 31 - (L + 31) % 32 := by omega
  have hLt : L < 2 ^ 256 := by omega
  have h1a0 : (Bytes.toB256 [0x01, 0xa0]).toNat = 416 := by decide
  have hX : (Bytes.toB256 [0x01, 0xa0] + Lw).toNat = 416 + L := by
    rw [B256.toNat_add, h1a0, Nat.lo_eq_of_lt (by omega)]
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h1f : (Bytes.toB256 [0x1f]).toNat = 31 := by decide
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hmod : ∀ x : B256, x.toNat < 2 ^ 256 → ((x - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat
      = (x.toNat + 31) % 32 := by
    intro x _
    rw [B256.toNat_mod (by decide), B256.toNat_sub, h1, h20, Nat.lo]
    omega
  have hm : ((Lw - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat = (L + 31) % 32 :=
    hmod Lw (B256.toNat_lt Lw)
  have hL31 : (Lw + Bytes.toB256 [0x1f]).toNat = L + 31 := by
    rw [B256.toNat_add, h1f, Nat.lo_eq_of_lt (by omega)]
  have hsub1 : (Lw + Bytes.toB256 [0x1f] - (Lw - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat
      = L + 31 - (L + 31) % 32 := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hm, hL31]; omega), hm, hL31]
  have hzB : (Lw + Bytes.toB256 [0x1f] - (Lw - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20] -
      Lw).toNat = z := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hsub1]; omega), hsub1]
    omega
  rw [hX, hzB, B256.toNat_toB256_of_lt hcd, sliceD_data_end, h160]
  have hA : (Lw + Bytes.toB256 [0x40]).toNat = L + 64 := by
    rw [B256.toNat_add, h40, Nat.lo_eq_of_lt (by omega)]
  have hm' : ((Lw + Bytes.toB256 [0x40] - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat =
      (L + 63) % 32 := by
    rw [hmod _ (B256.toNat_lt _), hA]; omega
  have hA31 : (Lw + Bytes.toB256 [0x40] + Bytes.toB256 [0x1f]).toNat = L + 95 := by
    rw [B256.toNat_add, h1f, hA, Nat.lo_eq_of_lt (by omega)]
  have hret : (Lw + Bytes.toB256 [0x40] + Bytes.toB256 [0x1f] -
      (Lw + Bytes.toB256 [0x40] - Bytes.toB256 [0x01]) % Bytes.toB256 [0x20]).toNat =
      64 + ceil32 L := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hm', hA31]; omega), hm',
      hA31]
    omega
  -- the memory
  have hrd : ∀ i n, (M.read i n).1 = M.data.toList.sliceD i n 0 := (Mem.reads_data M).read
  set M1 := M.write (416 + L) (List.replicate z 0)
  have hM1s : M1.size = sz := by
    rw [Mem.size_write_of_le (by rw [List.length_replicate, hs]; omega), hs]
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hr1 : Mem.Reads M1 (Bytes.writeAt M.data.toList (416 + L) (List.replicate z 0)) :=
    (Mem.reads_data M).write hwf _ _
  set M2 := M1.write 352 (Bytes.toB256 [0x20]).toBytes
  have hM2s : M2.size = sz := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hM1s]; omega), hM1s]
  have hr2 := hr1.write hwf1 352 (Bytes.toB256 [0x20]).toBytes
  have hread180 : Bytes.toB256 (M2.read 384 32).1 = Lw := by
    rw [hr2.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hLw, B256.toB256_toBytes]
  rw [read_covered hM2s hsz32 (by omega), hread180, hret]
  rw [hr2.read, show 64 + ceil32 L = 32 + (32 + (L + z)) by omega, List.sliceD_split,
    List.sliceD_split, List.sliceD_split, sliceD_word_same,
    show (352 : Nat) + 32 = 384 from rfl, show (384 : Nat) + 32 = 416 from rfl,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hLw,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hrd, hstr,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
    Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [List.length_replicate]),
    Nat.sub_self, Bytes.sliceD_zero_length (List.length_replicate ..)]
  unfold abiString
  rw [hlen, hLdef, toB256_toNat, show Bytes.toB256 [0x20] = (32 : B256) by decide]
  simp only [List.append_assoc]
  rfl

/-- **The string views, inverted**, for either view: a successful halt passed the `CALLVALUE`
guard and returns exactly `abiString` of the stored string (`n` data words), over storage whose
length word is within the variable's bound; storage and logs are kept. -/
theorem safe_strView (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    {h0 h1 sl cp : UInt8} {fail : SFunc} (hf : fail.noOk = true) {e0 e1 x0 x1 r0 r1 : UInt8}
    {j k n : Nat} {joinT : SFunc} (hjT : joinT = t_0774_c5)
    (hk : prog[k]? = some (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k joinT))
    (hj : prog[j]? = some joinT)
    (hcase : (cp = 3 ∧ n = 2 ∧ ((stor₀).get (Bytes.toB256 [sl]).toBytes.keccak).toNat ≤ 64) ∨
      (cp = 2 ∧ n = 1 ∧ ((stor₀).get (Bytes.toB256 [sl]).toBytes.keccak).toNat ≤ 32))
    {G : Nat} {post : Devm}
    (run : SFunc.Run prog sevm (entrySt sevm b G)
      (vyStrView h0 h1 sl cp fail (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k joinT)) (.halted post)) :
    sevm.value = 0 ∧
      Lands sevm b post (stor₀, [], some (abiString (vyStrOf stor₀ (Bytes.toB256 [sl]).toBytes.keccak n))) := by
  subst hjT
  have run := run.cut
  unfold entrySt vyStrView at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (h := h0) (l := h1) (fail := fail) hf run
  refine ⟨hv, ?_⟩
  set base := (Bytes.toB256 [sl]).toBytes.keccak with hbase
  set Lw := b.getStorVal sevm.currentTarget base with hLwdef
  have hLst : (stor₀).get base = Lw := rfl
  rw [hLst] at hcase
  set L := Lw.toNat with hLdef
  have hM0 := vyMem_empty_size (Sevm.dataWord sevm 0)
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 192 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h120 : (Bytes.toB256 [0x01, 0x20]).toNat = 288 := by decide
  have hz0 : Bytes.toB256 [0x00] = Nat.toB256 0 := by decide
  set M1 := (vyMem Mem.empty (Sevm.dataWord sevm 0)).write 192 (Bytes.toB256 [sl]).toBytes
  have hM1 : M1.size = 224 := by simp only [M1, Mem.size_write_word_at, hM0]; decide
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  -- the prefix
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_mstore s1
  rw [hc0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_keccak s1
  rw [hc0, h20, Mem.read_write_word_of_wf hwf0, read_covered hM1 (by decide) (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_mstore s1
  rw [h120, hz0] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_add s1
  have hp120 : Bytes.toB256 [0x01, 0x20] = 0x120 := by decide
  have h384 : (Bytes.toB256 [0x01, 0x80]).toNat = 384 := by decide
  rw [hp120] at run
  clear s1
  set lp := b.getStorVal sevm.currentTarget (Bytes.toB256 [sl]).toBytes.keccak + Bytes.toB256 [0x20]
  have hlp : lp.toNat = L + 32 := by
    show (Lw + Bytes.toB256 [0x20]).toNat = L + 32
    rw [B256.toNat_add, show (Bytes.toB256 [0x20]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by have := hcase; omega)]
  set b1 := afterSload sevm b base
  set M2 := M1.write 288 (Nat.toB256 0).toBytes
  have hM2 : M2.size = 320 := by simp only [M2, Mem.size_write_word_at, hM1]; decide
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hc2 : (M2.read 0x120 32).1 = (Nat.toB256 0).toBytes := Mem.read_write_word_of_wf hwf1 _ _
  have hkC : k ∉ ([] : List Nat) := by simp
  have hjC : j ∉ ([] : List Nat) := by simp
  have hcap1 : Bytes.toB256 [cp] + Nat.toB256 0 ≠ Nat.toB256 (0 + 1) := by
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  -- iteration 0
  rcases ric_vyLoadIter hfork (i := 0) hM2 (by decide) (by decide) h384 (by decide) (by decide)
    (by decide) (by decide) hwf2 hc2 hk hkC hj hjC run with ⟨hlt, -⟩ | ⟨-, G21, run⟩
  · omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false hcap1)] at run
  set b2 := afterSload sevm b1 (base + Nat.toB256 0)
  set b3 := afterSload sevm b2 (base + Nat.toB256 1)
  set u0 := b1.getStorVal sevm.currentTarget (base + Nat.toB256 0)
  set u1 := b2.getStorVal sevm.currentTarget (base + Nat.toB256 1)
  have hu0 : u0 = Lw := by
    show (afterSload sevm b base).getStorVal _ _ = _
    rw [getStorVal_afterSload, show base + Nat.toB256 0 = base by
      apply B256.toNat_inj
      rw [B256.toNat_add, B256.toNat_toB256_of_lt (by decide), Nat.add_zero,
        Nat.lo_eq_of_lt (B256.toNat_lt _)]]
  have hu1 : u1 = (stor₀).get (base + Nat.toB256 (0 + 1)) := by
    show (afterSload sevm (afterSload sevm b base) _).getStorVal _ _ = _
    rw [getStorVal_afterSload, getStorVal_afterSload]; rfl
  set M3 := (M2.write (384 + 32 * 0) u0.toBytes).write 0x120 (Nat.toB256 (0 + 1)).toBytes
  have hM3 : M3.size = 416 := by
    simp only [M3, Mem.size_write_word_at, hM2]; decide
  have hwf3 : Mem.Wf M3 := (hwf2.write _ _).write _ _
  have hc3 : (M3.read 0x120 32).1 = (Nat.toB256 1).toBytes :=
    Mem.read_write_word_of_wf (hwf2.write _ _) _ _
  -- iteration 1
  rcases ric_vyLoadIter hfork (i := 1) hM3 (by decide) (by decide) h384 (by decide) (by decide)
    (by decide) (by decide) hwf3 hc3 hk hkC hj hjC run with ⟨hlt, -⟩ | ⟨-, G22, run⟩
  · omega
  set M4 := (M3.write (384 + 32 * 1) u1.toBytes).write 0x120 (Nat.toB256 (1 + 1)).toBytes
  have hM4 : M4.size = 448 := by
    simp only [M4, Mem.size_write_word_at, hM3]; decide
  have hwf4 : Mem.Wf M4 := (hwf3.write _ _).write _ _
  have hc4 : (M4.read 0x120 32).1 = (Nat.toB256 2).toBytes :=
    Mem.read_write_word_of_wf (hwf3.write _ _) _ _
  have hr2 := Mem.reads_data M2
  have hr4 := ((((hr2.write hwf2 (384 + 32 * 0) u0.toBytes).write (hwf2.write _ _) 0x120
    (Nat.toB256 (0 + 1)).toBytes).write hwf3 (384 + 32 * 1) u1.toBytes).write
    (hwf3.write _ _) 0x120 (Nat.toB256 (1 + 1)).toBytes)
  have hLw4 : (M4.read 384 32).1 = Lw.toBytes := by
    rw [hr4.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]),
      show 384 - (384 + 32 * 0) = 0 from rfl, Bytes.sliceD_zero_length (B256.length_toBytes _), hu0]
  have hread4 : (M4.read 416 L).1 = u1.toBytes.take L ∨ 32 < L := by
    by_cases hL32 : L ≤ 32
    · left
      rw [hr4.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
        Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega),
        show 416 - (384 + 32 * 1) = 0 from rfl,
        sliceD_zero_take _ (by rw [B256.length_toBytes]; exact hL32)]
    · right; omega
  have hlen4 : ((M4.read 416 L).1).length = L := by rw [hr4.read, List.length_sliceD]
  have hc := ceil32_eq L
  have hlands : ∀ post : Devm, ∀ bb : Devm, (∀ a, Devm.getStor bb a = Devm.getStor b a) →
      bb.logs = b.logs → (∀ a, Devm.getStor post a = Devm.getStor bb a) → post.logs = bb.logs →
      post.output = abiString (vyStrOf stor₀ base n) →
      Lands sevm b post (stor₀, [], some (abiString (vyStrOf stor₀ base n))) := by
    intro post bb h1 h2 h3 h4 h5
    refine ⟨by rw [h3, h1], fun a _ => by rw [h3, h1], by rw [h4, h2, List.append_nil],
      fun o ho => ?_, fun h => by cases h⟩
    cases ho; exact h5
  rcases hcase with ⟨rfl, rfl, hL⟩ | ⟨rfl, rfl, hL⟩
  · -- `name`: a third pass
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide))] at run
    set u2 := b3.getStorVal sevm.currentTarget (base + Nat.toB256 2)
    have hu2 : u2 = (stor₀).get (base + Nat.toB256 (1 + 1)) := by
      show (afterSload sevm (afterSload sevm (afterSload sevm b base) _) _).getStorVal _ _ = _
      rw [getStorVal_afterSload, getStorVal_afterSload, getStorVal_afterSload]; rfl
    have hW : vyStrWords stor₀ base 2 = u1.toBytes ++ u2.toBytes := by
      rw [hu1, hu2]; rfl
    rcases ric_vyLoadIter hfork (i := 2) hM4 (by decide) (by decide) h384 (by decide) (by decide)
      (by decide) (by decide) hwf4 hc4 hk hkC hj hjC run with ⟨hlt, G23, run⟩ | ⟨hle, G23, run⟩
    · -- the test fails at the third word
      have hstr : (M4.read 416 L).1 = vyStrOf stor₀ base 2 := by
        rcases hread4 with h | h
        · rw [h, vyStrOf, hLst, hW, List.take_append_of_le_length (by rw [B256.length_toBytes]; omega)]
        · omega
      obtain ⟨hst, hlg, hout⟩ := safe_strJoin hcd hwf4 hM4 (by decide)
        (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw4 hstr (by rw [← hstr, hlen4]) b3 run
      exact hlands post b3 (fun a => by simp only [b3, b2, b1, afterSload_getStor])
        (by simp only [b3, b2, b1, afterSload_logs]) hst hlg hout
    · -- the third word is copied, and the counter reaches the cap
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at run
      set b4 := afterSload sevm b3 (base + Nat.toB256 2)
      set M5 := (M4.write (384 + 32 * 2) u2.toBytes).write 0x120 (Nat.toB256 (2 + 1)).toBytes
      have hM5 : M5.size = 480 := by
        simp only [M5, Mem.size_write_word_at, hM4]; decide
      have hwf5 : Mem.Wf M5 := (hwf4.write _ _).write _ _
      have hr5 := (hr4.write hwf4 (384 + 32 * 2) u2.toBytes).write (hwf4.write _ _) 0x120
        (Nat.toB256 (2 + 1)).toBytes
      have hLw5 : (M5.read 384 32).1 = Lw.toBytes := by
        rw [hr5.read, Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
          Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hr4.read, hLw4]
      have hstr' : (M5.read 416 (32 + (L - 32))).1 = vyStrOf stor₀ base 2 := by
        rw [hr5.read, List.sliceD_split,
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
          Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), ← hr4.read,
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
          Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]; omega),
          show 416 + 32 - (384 + 32 * 2) = 0 from rfl,
          sliceD_zero_take _ (by rw [B256.length_toBytes]; omega), hr4.read,
          Bytes.sliceD_writeAt_after _ _ _ _ _ (by simp [B256.length_toBytes]),
          Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by simp [B256.length_toBytes]),
          show 416 - (384 + 32 * 1) = 0 from rfl,
          Bytes.sliceD_zero_length (B256.length_toBytes _), vyStrOf, hLst, hW,
          List.take_append, B256.length_toBytes,
          List.take_of_length_le (l := u1.toBytes) (by rw [B256.length_toBytes]; omega)]
      have hstr : (M5.read 416 L).1 = vyStrOf stor₀ base 2 := by
        rwa [show 32 + (L - 32) = L by omega] at hstr'
      have hlen5 : ((M5.read 416 L).1).length = L := by rw [hr5.read, List.length_sliceD]
      obtain ⟨hst, hlg, hout⟩ := safe_strJoin hcd hwf5 hM5 (by decide)
        (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw5 hstr (by rw [← hstr, hlen5]) b4 run
      exact hlands post b4 (fun a => by simp only [b4, b3, b2, b1, afterSload_getStor])
        (by simp only [b4, b3, b2, b1, afterSload_logs]) hst hlg hout
  · -- `symbol`: the counter reached the cap
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by decide))] at run
    have hstr : (M4.read 416 L).1 = vyStrOf stor₀ base 1 := by
      rcases hread4 with h | h
      · rw [h, vyStrOf, hLst, hu1]; rfl
      · omega
    obtain ⟨hst, hlg, hout⟩ := safe_strJoin hcd hwf4 hM4 (by decide)
      (by rw [← hLdef]; omega) (by rw [← hLdef]; omega) hLw4 hstr (by rw [← hstr, hlen4]) b3 run
    exact hlands post b3 (fun a => by simp only [b3, b2, b1, afterSload_getStor])
      (by simp only [b3, b2, b1, afterSload_logs]) hst hlg hout

-- SEGMENT: safeStringViews (`name` and `symbol`, one shape, inverted)
/-- `name()`, inverted, over storage whose length word is within `String[64]`. -/
theorem safe_name (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    (hL : ((stor₀).get vyNameBase).toNat ≤ 64) :
    SafeBody sevm b t_0716_c0 (rawName sevm stor₀) := by
  intro G post run
  have hb : vyNameBase = (Bytes.toB256 [0x00]).toBytes.keccak := by
    rw [show Bytes.toB256 [0x00] = 0 by decide]; rfl
  obtain ⟨hv, hl⟩ := safe_strView (h0 := 0x07) (h1 := 0x20) (fail := t_071c_c0) (e0 := 0x07)
    (e1 := 0x52) (x0 := 0x07) (x1 := 0x74) (r0 := 0x07) (r1 := 0x3f) hfork hcd (by decide) rfl rfl
    rfl (Or.inl ⟨rfl, rfl, by rw [← hb]; exact hL⟩) run
  rw [← hb] at hl
  exact ⟨_, by simp only [rawName, hv, hL, and_self, ite_true], hl⟩

/-- `symbol()`, inverted, over storage whose length word is within `String[32]`. -/
theorem safe_symbol (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    (hL : ((stor₀).get vySymbolBase).toNat ≤ 32) :
    SafeBody sevm b t_07ca_c0 (rawSymbol sevm stor₀) := by
  intro G post run
  have hb : vySymbolBase = (Bytes.toB256 [0x01]).toBytes.keccak := by
    rw [show Bytes.toB256 [0x01] = 1 by decide]; rfl
  obtain ⟨hv, hl⟩ := safe_strView (h0 := 0x07) (h1 := 0xd4) (fail := t_07d0_c0) (e0 := 0x08)
    (e1 := 0x06) (x0 := 0x08) (x1 := 0x28) (r0 := 0x07) (r1 := 0xf3) (joinT := t_0828_c6) hfork hcd
    (by decide) rfl rfl rfl (Or.inr ⟨rfl, rfl, by rw [← hb]; exact hL⟩) run
  rw [← hb] at hl
  exact ⟨_, by simp only [rawSymbol, hv, hL, and_self, ite_true], hl⟩

end StrViews

end Blanc.Lift.Curve3Crv
