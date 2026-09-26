import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 7: one hashing iteration of the insertion loop

One pass of the insertion loop at a height `h` whose size bit is clear: from the loop head
(pc `0x0f6e`, tree `t_0f6e_c23`, entry 23) back to it.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: insertDead
/-- **Segment 7 (`0x0f6e → 0x0f6e`, one pass: trees `t_0f6e_c23`, `t_0f78_c23`, `t_0fa0_c23`,
`t_0faf_c23`, `t_0fe8_c23`, loop entry 22, back through `.jump 23`).**  At height `h < 32` with
`size` even: the head test `h < 32`, the bit test `size & 1 == 1` fails, the bounds check
`h < 32` (over `INVALID`), `SLOAD branch[h]`, the pair `branch[h] ‖ node` packed at the free
pointer `fp = 928 + 96 h` (words at `fp + 0x20`, `fp + 0x40`, length at `fp`, free pointer to
`fp + 0x60`), copied by the count-down word loop (first pass inlined in entry 23's tree, second
pass and exit in entry 22), the empty partial word merged (its `MLOAD` extends memory by the
last word), `STATICCALL` to the SHA-256 precompile, both checks; then `size / 2`, `h + 1` and
`JUMP` to the head.  Memory grows by 96 bytes.  `deadGas h` and the `SLOAD`.

Proof sketch.  Straight-line `rx_*` steps with `Ninst.runCompiled_sload_selected` (the
`SLOAD`'s charge `sloadCost`, successor `afterSload`), the packed-copy + precompile shape of
segment 3 (both copy passes unrolled with `rx_jump`: `prog[22] = t_0fe8_c22`), and
`rx_jump` with `prog[23] = t_0f6e_c23` at the end.  The memory expansion charges telescope to
`deadGas h`'s difference (sizes `1024 + 96 h → 1088 + 96 h → 1120 + 96 h`).  The stored slot is
`Nat.toB256 h + 0 = solBranchSlot h`; the digest is `hashPair` of the loaded word and `nd`. -/
theorem body_insertDead {sevm : Sevm} {b : Devm} {sz nd : B256} {R : List B256} {h G : Nat}
    {M : Mem}
    (hsha : ShaReady sevm b) (hh : h < 32) (hsz : sz.toNat % 2 = 0) (hR : R.length ≤ 16)
    (hG : G + deadGas h + sloadCost sevm b (solBranchSlot h) < 2 ^ 256)
    (hM : BodyMem M (1024 + 96 * h) (Nat.toB256 (928 + 96 * h)) []) :
    ∃ b' M', Keep (afterSload sevm b (solBranchSlot h)) b' ∧
      BodyMem M' (1120 + 96 * h) (Nat.toB256 (1024 + 96 * h)) [] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' (Nat.toB256 (h + 1) :: sz / 2 ::
            BeaconDeposit.hashPair Bytes.sha256
              (b.getStorVal sevm.currentTarget (solBranchSlot h)) nd :: R) M' G) t_0f6e_c23 o →
        SFunc.RunExact prog sevm
          (St b (Nat.toB256 h :: sz :: nd :: R) M
            (G + (deadGas h + sloadCost sevm b (solBranchSlot h)))) t_0f6e_c23 o := by
  sorry

end Blanc.Lift.BeaconDeposit
