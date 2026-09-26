import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 4: `signature_root`

From `0x086e` (tree `t_086e_c12`, `pubkey_root` in memory) through the three hashes of
`signature_root` to the return-size check's continuation at `0x0b4c` (tree `t_0b4c_c16`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: signatureRoot
/-- **Segment 4 (`0x086e → 0x0b4c`, trees `t_086e_c12`, loop entries 14, 15, 16, ending at
`t_0b4c_c16`).**  `pkR` is loaded from `0x160` onto the stack; then three precompile hashes,
each over 64 packed bytes built at the free pointer, copied by the count-down word loop (two
passes: first inlined, second in the loop entry), merged and `STATICCALL`ed:

* `sha256(signature[:64])` (`0x0873 … 0x096a`): the slice helper (entry 13, pc `0x16fe`,
  `callNext 13`, bounds `0 ≤ 64 ≤ 96`) returns `sP` and `64`; `CALLDATACOPY` of 64 bytes at
  `0x180`; loop `0x08bb` (entry 14); digest at `0x1c0`, loaded;
* `sha256(signature[64:] ‖ 0^32)` (`0x096d … 0x0a66`): the slice helper returns `sP + 64` and
  `32`; `CALLDATACOPY` of 32 bytes and a zero word; loop `0x09b7` (entry 15); digest at `0x220`;
* `sha256(h₁ ‖ h₂)` (`0x0a66 … 0x0b4c`): the two words stored, loop `0x0a9d` (entry 16); the
  digest `signatureRoot` at `0x280`, the new free pointer.

2526 gas; memory stays at `0x340`.

Proof sketch.  Three instances of the packed-copy + precompile shape (see segment 3); the slice
helper's two `callNext 13` runs are short straight-line walks (`rx_callRet (j := 13)`; its
`t_16fe_c13` tree has two `GT`/`JUMPI` bound checks and returns two words).  `hsP` keeps
`sP + 64` from wrapping.  The digest equation is `BeaconDeposit.signatureRoot`'s definition with
`(sliceD sP 96).take 64 = sliceD sP 64` and `(sliceD sP 96).drop 64 = sliceD (sP + 64) 32`
(`List.sliceD_split`). -/
theorem body_signatureRoot {sevm : Sevm} {b : Devm} {sel rt sP wP pP a pkR : B256} {G : Nat}
    {M : Mem}
    (hsha : ShaReady sevm b) (hsP : sP.toNat + 96 < 2 ^ 256) (hG : G + 2526 < 2 ^ 256)
    (hM : BodyMem M 832 0x160
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x160, pkR.toBytes)]) :
    ∃ b' M', Keep b b' ∧
      BodyMem M' 832 0x280
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x280, (BeaconDeposit.signatureRoot Bytes.sha256
            (sevm.data.sliceD sP.toNat 96 0)).toBytes)] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0x20, 0x280, 0, pkR, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G)
          t_0b4c_c16 o →
        SFunc.RunExact prog sevm
          (St b [0x20, 0x160, 0, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M (G + 2526))
          t_086e_c12 o := by
  sorry

end Blanc.Lift.BeaconDeposit
