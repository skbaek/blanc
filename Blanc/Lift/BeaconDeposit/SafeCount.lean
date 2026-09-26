import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment B6: the root check, the cap guard and the count increment, inverted
(converse of `body_countBump`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeCountBump
/-- **Inversion of segment 6 (`t_0ea6_c20 → t_0f6e_c20`).**  Success forces the reconstructed
node to equal `deposit_data_root` and the count below the cap.

Proof sketch.  `cases` along `body_countBump`'s walk (about 30 nodes).  The `EQ`/`JUMPI` of the
root check: its fall-through arm `t_0eb2_c20` is an `Error(string)` revert, so the `EQ` word is
nonzero, i.e. `nd = rt` (`B256.eqCheck`).  The cap check `0xffffffff > count`: its fall-through
`t_0f10_c20` reverts, so `count < 2^32 - 1`.  Both `SLOAD`s return `b`'s count (the base is `b`
or `afterSload` of it, same storage).  The `SSTORE`'s successor is `afterSstore` (compare
`Ninst.runCompiled_sstore_selected`). -/
theorem safe_countBump {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR sR nd : B256} {G : Nat}
    {M : Mem} {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork)
    (hM : BodyMem M 1024 0x3a0 [(0x3a0, nd.toBytes)])
    (run : SFunc.Run prog sevm
      (St b [0x20, 0x3a0, 0, sR, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M G)
      t_0ea6_c20 o) :
    nd = rt ∧ (b.getStorVal sevm.currentTarget solCountSlot).toNat < 2 ^ 32 - 1 ∧
      ∃ b' M' G', Keep (afterSstore sevm b solCountSlot
          (1 + b.getStorVal sevm.currentTarget solCountSlot)) b' ∧
        BodyMem M' 1024 0x3a0 [] ∧
        SFunc.Run prog sevm
          (St b' [0, 1 + b.getStorVal sevm.currentTarget solCountSlot, nd, sR, pkR, 0x80, a, rt,
            96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G') t_0f6e_c20 o := by
  sorry

end Blanc.Lift.BeaconDeposit
