import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment B2: the event encoding, inverted (converse of `body_event`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeEvent
/-- **Inversion of segment 2 (`t_0575_c7 → t_071c_c4`).**

Proof sketch.  The same walk as `body_event`, by `cases`; no guard fails on this segment except
the copy loops' exit tests, whose words are fixed by the memory facts (`mload 0x80 = 8`,
`mload 0xc0 = 8`).  Each one-word copy loop is two passes of fixed shape (inlined pass, then
entry 26 resp. 11 exits), inverted by `cases` on `.branch`/`.jump`; a generic inversion of
`copyLoopTree` (the converse of `copy_step`/`copy_exit`, `CopyLoop.lean`) serves both.  The
image equation is the one `body_event` proves. -/
theorem safe_event {sevm : Sevm} {b : Devm} {sel rt sP wP pP a c : B256} {G : Nat} {M : Mem}
    {o : Outcome}
    (hM : BodyMem M 256 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
        (0xc0, (8 : B256).toBytes), (0xe0, BeaconDeposit.le64 c.toNat)])
    (run : SFunc.Run prog sevm
      (St b [0xc0, 96, sP, 0x80, 32, wP, 48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt,
        96, sP, 32, wP, 48, pP, 0x01b8, sel] M G) t_0575_c7 o) :
    ∃ b' M' G', Keep b b' ∧
      BodyMem M' 832 0x100
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x100, BeaconDeposit.abiDepositEvent (bodyEvent sevm pP wP sP a c))] ∧
      SFunc.Run prog sevm
        (St b' [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
          48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
          sel] M' G') t_071c_c4 o := by
  sorry

end Blanc.Lift.BeaconDeposit
