import Blanc.Lift.WriteSiteSound
import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.Usdc.ImplWs.Check

/-! The USDC implementation passes the write-site check (unit W6).

`impl_wsCert` assembles the generated per-entry kernel decisions
(`ImplWs/Check<i>.lean`, chained in `ImplWs/Check.lean`; producer
`scripts/lift/ws_annot.py`, registered in `scripts/lift/certificates.json`), and
`implRun_ws` instantiates `lift_sound_ws` with it and the certificate's own check. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite Blanc.Lift.Usdc.ImplWs

/-- **The implementation passes the write-site check** (generated, one kernel decide per entry
group, split like `Impl.CheckPart*`). -/
theorem impl_wsCert : wsCert Impl.cert implWsAnn = true :=
  wsCert_of_wsFrom (by decide +kernel) ws_rest_0

/-- The USDC implementation's runs, with the write-site observation. -/
theorem implRun_ws {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork) :
    SProg.RunP (WsStep (wsRoot implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) Impl.cert.prog sevm pre post :=
  lift_sound_ws Impl.cert_check impl_wsCert code fork run

end Blanc.Lift.Usdc
