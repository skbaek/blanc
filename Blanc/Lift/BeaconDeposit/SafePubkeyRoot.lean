import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment B3: the `LOG1` and `pubkey_root`, inverted (converse of `body_pubkeyRoot`)
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safePubkeyRoot
/-- **Inversion of segment 3 (`t_071c_c4 → t_086e_c12`).**

Proof sketch.  `cases` along `body_pubkeyRoot`'s walk.  `LOG1`: the `Ninst.Run` successor is
`addLog ⟨currentTarget, [topic], data⟩` (invert `Rinst.run` of `.log 1` as
`Ninst.runCompiled_log_of` computes it).  The precompile block (pack, count-down copy loop with
two passes through entry 12, merge, `GAS`, `STATICCALL`, success and `RETURNDATASIZE ≥ 32`
checks) is best inverted once generically, as the converse of the root-view worker's
`PackedSha` walk: the `STATICCALL` step by the port's `of_run_staticcall_val_with_depth_cause`
and `frame_of_processMessage_sha256_64_clean` (`BeaconDepositSha.lean`'s
`sha64_success_of_run` does the same for `Func`); its failure disjunct pushes `0`, whose
`ISZERO`/`JUMPI` arm ends in `RETURNDATACOPY … REVERT`; the short-return arm ends in `REVERT`.
Storage by `Ninst.staticcall_inv_getStor_exact`, logs by `Ninst.world_of_quiet`. -/
theorem safe_pubkeyRoot {sevm : Sevm} {b : Devm} {sel rt sP wP pP a : B256} {G : Nat} {M : Mem}
    {data : Bytes} {o : Outcome}
    (hsha : ShaReady sevm b) (hlen : data.length = 576)
    (hM : BodyMem M 832 0x100
      [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat), (0x100, data)])
    (run : SFunc.Run prog sevm
      (St b [8, 0x340, 0x180, 0x160, 0x140, 0x120, 0x100, 0x100, 0xc0, 96, sP, 0x80, 32, wP,
        48, pP, BeaconDeposit.depositEventTopic, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8,
        sel] M G) t_071c_c4 o) :
    ∃ b' M' G', Keep (b.addLog ⟨sevm.currentTarget, [BeaconDeposit.depositEventTopic], data⟩) b' ∧
      BodyMem M' 832 0x160
        [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 a.toNat),
          (0x160, (BeaconDeposit.pubkeyRoot Bytes.sha256
            (sevm.data.sliceD pP.toNat 48 0)).toBytes)] ∧
      SFunc.Run prog sevm
        (St b' [0x20, 0x160, 0, 0x80, a, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G')
        t_086e_c12 o := by
  sorry

end Blanc.Lift.BeaconDeposit
