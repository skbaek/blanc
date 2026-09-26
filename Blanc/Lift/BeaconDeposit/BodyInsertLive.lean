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
  sorry

end Blanc.Lift.BeaconDeposit
