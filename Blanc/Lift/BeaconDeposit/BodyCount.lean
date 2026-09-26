import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 6: the root check, the cap guard and the count increment

From `0x0ea6` (tree `t_0ea6_c20`, the node in memory) to the insertion loop's head
(pc `0x0f6e`, tree `t_0f6e_c20`: the head's first pass, inlined in entry 20).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: countBump
/-- **Segment 6 (`0x0ea6 → 0x0f6e`, trees `t_0ea6_c20`, `t_0f02_c20`, `t_0f60_c20`, ending at
`t_0f6e_c20`).**  The node is loaded from `0x3a0` and compared with `deposit_data_root` (`EQ`,
the `JUMPI` jumps over the revert); `SLOAD 0x20` (warm) and the cap guard
`0xffffffff > count`; `SLOAD 0x20` again, `1 + count` stored back (`SSTORE`, warm key), and the
loop's height `0` pushed.  Memory is untouched.  281 gas and the `SSTORE`.

Proof sketch.  Straight-line `rx_*` steps: `rx_mload` (no expansion), `rx_eq` with `hroot`,
`rx_branch_succ`, twice `rx_sload_warm`, `rx_gt` with `hcap`, and the `SSTORE` through
`Ninst.runCompiled_sstore_selected_setMach` (sentry `hsentry`: the gas left after the
`SSTORE` is `G + 3`).  The post base is exactly `afterSstore`; memory is `M`. -/
theorem body_countBump {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR sR nd : B256} {G : Nat}
    {M : Mem}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hwarm : (⟨sevm.currentTarget, solCountSlot⟩ : Adr × B256) ∈ b.accessedStorageKeys)
    (hroot : nd = rt)
    (hcap : (b.getStorVal sevm.currentTarget solCountSlot).toNat < 2 ^ 32 - 1)
    (hsentry : gCallStipend < G + 3 +
      sstoreCost sevm b solCountSlot (1 + b.getStorVal sevm.currentTarget solCountSlot))
    (hM : BodyMem M 1024 0x3a0 [(0x3a0, nd.toBytes)]) :
    ∃ b' M', Keep (afterSstore sevm b solCountSlot
        (1 + b.getStorVal sevm.currentTarget solCountSlot)) b' ∧
      BodyMem M' 1024 0x3a0 [] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0, 1 + b.getStorVal sevm.currentTarget solCountSlot, nd, sR, pkR, 0x80, a, rt,
            96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G) t_0f6e_c20 o →
        SFunc.RunExact prog sevm
          (St b [0x20, 0x3a0, 0, sR, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M
            (G + (281 + sstoreCost sevm b solCountSlot
              (1 + b.getStorVal sevm.currentTarget solCountSlot)))) t_0ea6_c20 o := by
  sorry

end Blanc.Lift.BeaconDeposit
