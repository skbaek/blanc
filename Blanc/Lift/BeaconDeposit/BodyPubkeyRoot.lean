import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Body segment 3: the `LOG1` and `pubkey_root`

From the join entry 4 (pc `0x071c`, tree `t_071c_c4`) through the event's `LOG1` and
`sha256(abi.encodePacked(pubkey, bytes16(0)))` to the return-size check's continuation at
`0x086e` (tree `t_086e_c12`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: pubkeyRoot
/-- **Segment 3 (`0x071c → 0x086e`, trees `t_071c_c4`, loop entry 12, ending at
`t_086e_c12`).**  Fifteen `POP`s/`SWAP14` drop the encoder's scratch, `LOG1` emits the 576 bytes
at `0x100` with the event topic (4608 + 750 gas, no expansion); then the packed input
`pubkey ‖ 0^16` is built at `0x120` (`CALLDATACOPY` of 48 bytes, an `AND`-masked zero word,
the length `0x40` at `0x100`, free pointer to `0x160`), copied by the count-down word loop
(`0x07bf`: first pass inlined in entry 4, second pass and exit in loop entry 12), the empty
partial word merged (`0x07fc`: the mask is all ones, the `MLOAD` extends nothing here), and
`STATICCALL`ed to the SHA-256 precompile with input and output at `0x160`; the success and
`RETURNDATASIZE ≥ 32` checks pass.  The digest `pubkeyRoot` sits at `0x160`, which is also the
new free pointer.  6205 gas.

Proof sketch.  `Ninst.runCompiled_log_of` for the `LOG1` (its successor is
`(St b …).addLog ⟨currentTarget, [topic], data⟩` with the machine replaced; commute `addLog`
with `setMach`).  The rest is the generic packed-copy + precompile shape
(`mcpyTree`/`mergeTree`/`shaCallTree` with `staticcall_sha_step` in the root-view worker's
`Blanc/Lift/PackedSha.lean`/`ExactWalkCutOps.lean`, once merged; otherwise the same steps by
hand, with `Ninst.runCompiled_staticcall_sha256_64_warm`, `rx_gas`, `rx_returndatasize`).  The
two loop passes are unrolled with `rx_jump` (entry 12 is `prog[12]`).  The digest equation:
the 64 input bytes are `pubkey ++ zeros 16` (`BeaconDeposit.pubkeyRoot`). -/
theorem body_pubkeyRoot {sevm : Sevm} {b : Devm} {sel rt sP wP pP a : B256} {G : Nat} {M : Mem}
    {data : Bytes}
    (hsha : ShaReady sevm b) (hstatic : sevm.isStatic = false)
    (hlen : data.length = 576) (hG : G + 6205 < 2 ^ 256)
    (hM : BodyMem M 832 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x100, data)]) :
    ∃ b' M', Keep (b.addLog ⟨sevm.currentTarget, [BeaconDeposit.depositEventTopic], data⟩) b' ∧
      BodyMem M' 832 0x160
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x160, (BeaconDeposit.pubkeyRoot Bytes.sha256
            (sevm.data.sliceD pP.toNat 48 0)).toBytes)] ∧
      ∀ o, SFunc.RunExact prog sevm
          (St b' [0x20, 0x160, 0, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G)
          t_086e_c12 o →
        SFunc.RunExact prog sevm
          (St b [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
            48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
            sel] M (G + 6205)) t_071c_c4 o := by
  sorry

end Blanc.Lift.BeaconDeposit
