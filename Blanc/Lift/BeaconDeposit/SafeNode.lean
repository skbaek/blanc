import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment B5: the `DepositData` node, inverted (converse of `body_dataNode`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeDataNode
/-- **Inversion of segment 5 (`t_0b4c_c16 → t_0ea6_c20`).**

Proof sketch.  Three instances of the inverted precompile block (segment B3's sketch); the
amount copy (`mload 0x80 = 8`: the count-down loop makes no pass, the merge keeps the top 8
bytes of `le64 a`) as in `body_dataNode`. -/
theorem safe_dataNode {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR sR : B256} {G : Nat}
    {M : Mem} {o : Outcome}
    (hsha : ShaReady sevm b)
    (hM : BodyMem M 832 0x280
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x280, sR.toBytes)])
    (run : SFunc.Run prog sevm
      (St b [0x20, 0x280, 0, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M G)
      t_0b4c_c16 o) :
    ∃ b' M' G', Keep b b' ∧
      BodyMem M' 1024 0x3a0
        [(0x3a0, (BeaconDeposit.hashPair Bytes.sha256
          (Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0))
          (Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++
            sR.toBytes))).toBytes)] ∧
      SFunc.Run prog sevm
        (St b' [0x20, 0x3a0, 0, sR, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G')
        t_0ea6_c20 o := by
  sorry

end Blanc.Lift.BeaconDeposit
