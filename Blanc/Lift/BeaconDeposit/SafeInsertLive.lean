import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment L2: the storing pass and the return, inverted
(converse of `body_insertLive`, as a cut run at the loop head)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeInsertLive
/-- **Inversion of the storing pass (`t_0f6e_c23` cut at entry 23).**  From the loop head at a
height `h ≤ 32` with `size` odd, every successful cut run passes the head test (so `h < 32`),
stores the node at `solBranchSlot h` and returns through entry 21.

Proof sketch.  `cases` along `body_insertLive`'s proof (about 40 nodes, no memory access); the
head test's failing arm is `POP; undefined`; the bounds check's failing arm `t_0f90_c23` is
`undefined`; the `SSTORE`'s successor is `afterSstore`; `.jump 21` is not cut; `.ret` gives the
`.done (.returned …)`. -/
theorem safe_insertLive {sevm : Sevm} {b : Devm}
    {sz nd x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ y₅ y₆ y₇ d : B256} {rest : List B256} {h G : Nat} {M : Mem}
    {r : Seg}
    (hh : h ≤ 32) (hsz : sz.toNat % 2 = 1)
    (run : SFunc.RunCut prog sevm [23]
      (St b (Nat.toB256 h :: sz :: nd :: x₁ :: x₂ :: x₃ :: x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ ::
        y₆ :: y₇ :: d :: rest) M G) t_0f6e_c23 r) :
    h < 32 ∧ ∃ b' G', Keep (afterSstore sevm b (solBranchSlot h) nd) b' ∧
      r = .done (.returned (St b' rest M G')) := by
  sorry

end Blanc.Lift.BeaconDeposit
