import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 8: the storing iteration and the return

The insertion loop's pass at a height `h` whose size bit is set: from the loop head (pc
`0x0f6e`, tree `t_0f6e_c23`) through the `SSTORE` of the node, the `JUMP` to entry 21
(pc `0x10ac`) and its return to the decoder's tag.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: insertLive
/-- **Segment 8 (`0x0f6e → return`, trees `t_0f6e_c23`, `t_0f78_c23`, `t_0f84_c23`,
`t_0f91_c23`, `t_10ac_c21`).**  At height `h < 32` with `size` odd: the head test, the bit test
`size & 1 == 1` succeeds, the bounds check `h < 32`, `SSTORE branch[h] := nd`; then `POP`,
`PUSH2 0x10ac`, `SWAP6`, six `POP`s and `JUMP` to entry 21, whose seven `POP`s drop the frame's
arguments and whose `JUMP` returns through the tag `d`.  No memory access.  143 gas and the
`SSTORE`.

Proof sketch.  Straight-line `rx_*` steps; the `SSTORE` through
`Ninst.runCompiled_sstore_selected_setMach` (the gas left after it is `G + 51`, hence
`hsentry`); `rx_jump` with `prog[21] = t_10ac_c21`; `rx_ret`.  The key is
`Nat.toB256 h + 0 = solBranchSlot h`. -/
theorem body_insertLive {sevm : Sevm} {b : Devm}
    {sz nd x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ y₅ y₆ y₇ d : B256} {rest : List B256} {h G : Nat} {M : Mem}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hh : h < 32) (hsz : sz.toNat % 2 = 1) (hrest : rest.length ≤ 16)
    (hsentry : gCallStipend < G + 51 + sstoreCost sevm b (solBranchSlot h) nd) :
    SFunc.RunExact prog sevm
      (St b (Nat.toB256 h :: sz :: nd :: x₁ :: x₂ :: x₃ :: x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ :: y₆ ::
        y₇ :: d :: rest) M (G + (143 + sstoreCost sevm b (solBranchSlot h) nd))) t_0f6e_c23
      (.returned (St (afterSstore sevm b (solBranchSlot h) nd) rest M G)) := by
  have hhv : (Nat.toB256 h).toNat = h := B256.toNat_toB256_of_lt (by omega)
  have hlt : B256.ltCheck (Nat.toB256 h) (Bytes.toB256 [0x20]) = 1 := by
    rw [B256.ltCheck, ite_eq_left]
    rw [B256.lt_iff_toNat_lt_toNat, hhv]
    exact (by show h < 32; omega)
  have hbit : (Bytes.toB256 [0x01] &&& sz) = 1 := by
    apply B256.toNat_inj
    rw [B256.toNat_and, show (Bytes.toB256 [0x01]).toNat = 1 from rfl, Nat.and_comm,
      Nat.and_one_is_mod, hsz]
    rfl
  have hkey : Nat.toB256 h + Bytes.toB256 [0x00] = solBranchSlot h := by
    apply B256.toNat_inj
    rw [B256.toNat_add, hhv, show (Bytes.toB256 [0x00]).toNat = 0 from rfl, Nat.add_zero,
      Nat.lo_eq_of_lt (by omega)]
    exact (B256.toNat_toB256_of_lt (by omega)).symm
  rw [show G + (143 + sstoreCost sevm b (solBranchSlot h) nd) =
    ((G + 51) + sstoreCost sevm b (solBranchSlot h) nd) + 92 by omega]
  unfold t_0f6e_c23
  refine rx_dest ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_lt hlt (by simp; omega) ?_
  refine rx_iszero (v := 0) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_zero ?_
  unfold t_0f78_c23
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_and hbit (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_eq (v := 1) (by decide) (by simp; omega) ?_
  refine rx_iszero (v := 0) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_zero ?_
  unfold t_0f84_c23
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_lt hlt (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0f91_c23
  refine rx_dest ?_
  refine rx_add (by simp; omega) ?_
  rw [hkey]
  refine .next (Ninst.runCompiled_sstore_selected_setMach hfork (by omega) hstatic) ?_
  rw [show (afterSstore sevm b (solBranchSlot h) nd).setMach
      ⟨Nat.toB256 h :: sz :: nd :: x₁ :: x₂ :: x₃ :: x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ :: y₆ :: y₇ ::
        d :: rest, M, G + 51, b.stateGas⟩ =
      St (afterSstore sevm b (solBranchSlot h) nd) (Nat.toB256 h :: sz :: nd :: x₁ :: x₂ :: x₃ ::
        x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ :: y₆ :: y₇ :: d :: rest) M (G + 51) by
    rw [St, afterSstore_stateGas]]
  refine rx_pop ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_swap (n := 5) rfl ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_jump (j := 21) rfl ?_
  unfold t_10ac_c21
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

end Blanc.Lift.BeaconDeposit
