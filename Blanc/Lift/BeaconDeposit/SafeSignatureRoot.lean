import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment B4: `signature_root`, inverted (converse of `body_signatureRoot`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeSignatureRoot
/-- **Inversion of segment 4 (`t_086e_c12 → t_0b4c_c16`).**

Proof sketch.  Three instances of the inverted precompile block (segment B3's sketch), and the
slice helper (entry 13) inverted twice: its two bound checks `GT … REVERT` pass on the constants
`0 ≤ 64 ≤ 96`, `64 ≤ 96 ≤ 96`, and it returns `sP + start, end - start`.  `hsP` keeps `sP + 64`
from wrapping, so the second slice reads `sliceD (sP + 64) 32`. -/
theorem safe_signatureRoot {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR : B256} {G : Nat}
    {M : Mem} {o : Outcome}
    (hsha : ShaReady sevm b) (hsP : sP.toNat + 96 < 2 ^ 256)
    (hM : BodyMem M 832 0x160
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x160, pkR.toBytes)])
    (run : SFunc.Run prog sevm
      (St b [0x20, 0x160, 0, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M G)
      t_086e_c12 o) :
    ∃ b' M' G', Keep b b' ∧
      BodyMem M' 832 0x280
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x280, (BeaconDeposit.signatureRoot Bytes.sha256
            (sevm.data.sliceD sP.toNat 96 0)).toBytes)] ∧
      SFunc.Run prog sevm
        (St b' [0x20, 0x280, 0, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G')
        t_0b4c_c16 o := by
  sorry

end Blanc.Lift.BeaconDeposit
