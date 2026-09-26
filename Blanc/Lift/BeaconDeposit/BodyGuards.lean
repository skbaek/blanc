import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 1: the six guards and the two `to_little_endian_64` calls

From the entry of `deposit` (entry 7, pc `0x0304`) to the return tag `0x0575` of the second
`to_little_endian_64` call (tree `t_0575_c7`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: guards
/-- **Segment 1 (`0x0304 → 0x0575`, trees `t_0304_c7 … t_0575_c7`).**  With the success path's
lengths `48, 32, 96` on the stack and a value passing the three value guards, the body runs its
six guards (each `JUMPI` jumps over its `Error(string)` revert block), calls
`to_little_endian_64(value / 1 gwei)` (allocating `0x80`), pushes the event topic and its
arguments, reads the count (`SLOAD 0x20`) and calls `to_little_endian_64(count)` (allocating
`0xc0`).  1882 gas and the count `SLOAD`.

Proof sketch.  The guards: `rx_*` steps with `rx_branch_succ` on each `JUMPI` (`EQ` of the
literal lengths, `LT`/`ISZERO` of `CALLVALUE` against `1 ether`, `MOD` by `1 gwei`, `GT`
against `2^64 - 1`; `MOD` needs a small `rx_mod` step alongside `rx_div`).  The calls:
`rx_callRet (j := 25)` with `to_little_endian_64_run` (`LittleEndian.lean`, over `mem0` then over
its `leImg`, 830 and 827 gas), exactly as `count_getter` does in `CountView.lean`; the `SLOAD`
with `Ninst.runCompiled_sload_selected` (it charges `sloadCost` and moves to `afterSload`).
The memory facts come from `leImg`'s `sliceD` algebra (`img1_fp`, `img1_len` in `CountView`). -/
theorem body_guards {sevm : Sevm} {b : Devm} {sel rt sP wP pP : B256} {G : Nat}
    (hcd : sevm.data.length < 2 ^ 256)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hv1 : 10 ^ 18 ≤ sevm.value.toNat)
    (hv2 : sevm.value.toNat % 10 ^ 9 = 0)
    (hv3 : sevm.value.toNat / 10 ^ 9 < 2 ^ 64) :
    ∃ b' M', Keep (afterSload sevm b solCountSlot) b' ∧
      BodyMem M' 256 0x100
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 (gweiAmount sevm).toNat),
          (0xc0, (8 : B256).toBytes),
          (0xe0, BeaconDeposit.le64 (b.getStorVal sevm.currentTarget solCountSlot).toNat)] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0xc0, 96, sP, 0x80, 32, wP, 48, pP, BeaconDeposit.depositEventTopic, 0x80,
            gweiAmount sevm, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G) t_0575_c7 o →
        SFunc.RunExact prog sevm
          (St b [rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] mem0
            (G + (1882 + sloadCost sevm b solCountSlot))) t_0304_c7 o := by
  sorry

end Blanc.Lift.BeaconDeposit
