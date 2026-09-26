import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 2: the `DepositEvent` ABI encoding

From the return tag `0x0575` (tree `t_0575_c7`) to the join entry 4 (pc `0x071c`, tree
`t_071c_c4`), just before the `LOG1`.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: event
/-- **Segment 2 (`0x0575 → 0x071c`, trees `t_0575_c7`, loop entry 26, `t_0675_c3`, loop entry 11,
ending at `t_071c_c4`).**  Over the two little-endian buffers (`8` and the amount's bytes at
`0x80`/`0xa0`, `8` and the count's bytes at `0xc0`/`0xe0`), the code ABI-encodes the event at
the free pointer `0x100` without moving it: five head words `0xa0, 0x100, 0x140, 0x180, 0x200`
(relative), the pubkey (`CALLDATACOPY` of 48 bytes, a zero word after it, rounded up), the
withdrawal credentials (32 bytes), the amount (the solc copy loop, first pass inlined at
`0x0630`, loop entry 26; then the partial-word clean-up at `0x065c`), the signature (96 bytes,
`t_0675_c3`) and the index (copy loop at `0x06d7`, first pass inlined in entry 3, loop entry 11;
clean-up at `0x0703`).  The 576 bytes at `0x100` are then `abiDepositEvent`; memory has grown to
`0x340`.  1104 gas.

Proof sketch.  Straight-line `rx_*` steps (`rx_calldatacopy` with
`Bytes.writeAt`/`sliceD` algebra, as in `to_little_endian_64_run`); each copy loop copies one
word, so `copy_step` for the inlined pass and `copy_loop` with `N = 1` at the loop entry, joined
with `SFunc.RunExactCut.resume` exactly as `count_tail` does (`CountView.lean`), or simply
unrolled through `rx_jump`.  The clean-up keeps the top `8` bytes of the copied word (mask
`256^24 - 1`, `maskTop8_and`).  The final image equation is the longest step: split the 576 bytes
with `List.sliceD_split` and read each piece through `Bytes.sliceD_writeAt_*`. -/
theorem body_event {sevm : Sevm} {b : Devm} {sel rt sP wP pP a c : B256} {G : Nat} {M : Mem}
    (hM : BodyMem M 256 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
        (0xc0, (8 : B256).toBytes), (0xe0, BeaconDeposit.le64 c.toNat)]) :
    ∃ b' M', Keep b b' ∧
      BodyMem M' 832 0x100
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x100, BeaconDeposit.abiDepositEvent (bodyEvent sevm pP wP sP a c))] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
            48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
            sel] M' G) t_071c_c4 o →
        SFunc.RunExact prog sevm
          (St b [0xc0, 96, sP, 0x80, 32, wP, 48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt,
            96, sP, 32, wP, 48, pP, 0x01b8, sel] M (G + 1104)) t_0575_c7 o := by
  sorry

end Blanc.Lift.BeaconDeposit
