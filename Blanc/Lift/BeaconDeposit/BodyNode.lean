import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 5: the `DepositData` node

From `0x0b4c` (tree `t_0b4c_c16`, `signature_root` in memory) through the three hashes of
`node` to the return-size check's continuation at `0x0ea6` (tree `t_0ea6_c20`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: dataNode
/-- **Segment 5 (`0x0b4c → 0x0ea6`, trees `t_0b4c_c16`, loop entries 17, 19, 20, ending at
`t_0ea6_c20`).**  `sR` is loaded from `0x280`; then three precompile hashes over 64 packed bytes
each:

* `sha256(pkR ‖ withdrawal_credentials)` (`0x0b4c … 0x0c4b`): `pkR` stored, `CALLDATACOPY` of
  32 bytes from `wP`; loop `0x0b9c` (entry 17); digest at `0x2e0`;
* `sha256(amount ‖ 0^24 ‖ sR)` (`0x0c4b … 0x0dc0`): the amount's 8 bytes copied from its buffer
  (`mload 0x80 = 8`, the word loop `0x0c6c` makes no pass and stays in entry 17's copy, the
  partial word merged under the mask `256^24 - 1`), a zero word at `+8`, `sR` at `+32`;
  loop `0x0d11` (entry 19); digest at `0x340` (memory grows to `0x3a0`);
* `sha256(left ‖ right)` (`0x0dc0 … 0x0ea6`): loop `0x0df7` (entry 20); digest at `0x3a0`, the
  new free pointer (memory grows to `0x400`).

2553 gas.

Proof sketch.  Three instances of the packed-copy + precompile shape (segment 3).  The amount
copy is the only irregular piece: the count-down loop exits at once (`8 < 32`), and the merge
keeps the top 8 bytes of the source word (`le64 a`) and the low 24 of the destination, which the
following `MSTORE` of `0` at `+8` overwrites.  The digest equation is `hashPair` of the two inner
digests (`BeaconDeposit.hashPair`). -/
theorem body_dataNode {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR sR : B256} {G : Nat}
    {M : Mem}
    (hsha : ShaReady sevm b) (hG : G + 2553 < 2 ^ 256)
    (hM : BodyMem M 832 0x280
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x280, sR.toBytes)]) :
    ∃ b' M', Keep b b' ∧
      BodyMem M' 1024 0x3a0
        [(0x3a0, (BeaconDeposit.hashPair Bytes.sha256
          (Bytes.sha256 (pkR.toBytes ++ sevm.data.sliceD wP.toNat 32 0))
          (Bytes.sha256 (BeaconDeposit.le64 a.toNat ++ BeaconDeposit.zeros 24 ++
            sR.toBytes))).toBytes)] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0x20, 0x3a0, 0, sR, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G)
          t_0ea6_c20 o →
        SFunc.RunExact prog sevm
          (St b [0x20, 0x280, 0, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M
            (G + 2553)) t_0b4c_c16 o := by
  sorry

end Blanc.Lift.BeaconDeposit
