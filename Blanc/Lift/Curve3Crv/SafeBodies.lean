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
  sorry

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
  sorry

-- SEGMENT: safeMintBurn (121 + 117 nodes; `mint` and `burnFrom`, mechanically identical)
/-- `mint` and `burnFrom`.  Proof sketch: guards; minter check as `safeSetMinter`;
`PUSH1 0 PUSH1 4 CALLDATALOAD XOR PUSH2 JUMPI` is `a0 ≠ 0` (`ri_xor`); `PUSH1 5 DUP1 SLOAD …`
the supply update with the overflow (mint) or underflow (burn) guard; the balance slot
`mapSlot 3 a0` read over the supply write's base and its guard and write; `LOG3` with topics
`[sig, 0, a0]` (mint) or `[sig, a0, 0]` (burn); `return(0, 32)`. -/
theorem safe_mint (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_056e_c0 (rawMint sevm stor₀) := by
  sorry

-- SEGMENT: safeMintBurn (see `safe_mint`)
theorem safe_burnFrom (hfork : CoveredFork sevm.benvStat.fork) :
    SafeBody sevm b t_0644_c0 (rawBurnFrom sevm stor₀) := by
  sorry

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
