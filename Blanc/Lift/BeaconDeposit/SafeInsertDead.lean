import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment L1: one hashing pass of the insertion loop, inverted
(converse of `body_insertDead`, as a cut run at the loop head)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeInsertDead
/-- **Inversion of a dead pass (`t_0f6e_c23` cut at entry 23).**  From the loop head at a height
`h ≤ 32` with `size` even, every successful cut run passes the head test (so `h < 32`) and ends
at the next head, one height up, with the combined node.

Proof sketch.  `cases` along `body_insertDead`'s walk with `SFunc.RunCutP` in place of `Run`
(the same constructors; `.jump 23` is `jumpCut`, the only way to `.at`; `.jump 22` is followed).
The head test `h < 32` has `t_10a9_c23 = POP; undefined` as its failing arm (no rule).  The bit
test is decided by `hsz` (`Nat.and_one_is_mod` through `B256.toNat_and`, as in
`body_insertLive`).  The precompile block as in segment B3's sketch; the `SLOAD` of
`Nat.toB256 h + 0 = solBranchSlot h` has successor `afterSload`. -/
theorem safe_insertDead {sevm : Sevm} {b : Devm} {sz nd : B256} {R : List B256} {h G : Nat}
    {M : Mem} {r : Seg}
    (hsha : ShaReady sevm b) (hh : h ≤ 32) (hsz : sz.toNat % 2 = 0) (hR : R.length ≤ 16)
    (hM : BodyMem M (1024 + 96 * h) (Nat.toB256 (928 + 96 * h)) [])
    (run : SFunc.RunCut prog sevm [23] (St b (Nat.toB256 h :: sz :: nd :: R) M G) t_0f6e_c23 r) :
    h < 32 ∧ ∃ b' M' G', Keep (afterSload sevm b (solBranchSlot h)) b' ∧
      BodyMem M' (1120 + 96 * h) (Nat.toB256 (1024 + 96 * h)) [] ∧
      r = .at 23 (St b' (Nat.toB256 (h + 1) :: sz / 2 ::
        BeaconDeposit.hashPair Bytes.sha256
          (b.getStorVal sevm.currentTarget (solBranchSlot h)) nd :: R) M' G') := by
  sorry

end Blanc.Lift.BeaconDeposit
