import Blanc.Lift.WriteSiteSound
import Blanc.Lift.Dai.Check
import Blanc.Lift.DaiWs.Check

/-! Dai passes the write-site check (Curve 3pool U0 candidate).

`dai_wsCert` assembles the generated per-entry kernel decisions (`DaiWs/Check<i>.lean`, chained
in `DaiWs/Check.lean`; producer `scripts/lift/ws_annot.py`, candidate registry
`scripts/reference/curve-u0/certificates.json` row `curve-u0-dai`), and `daiRun_ws` instantiates
`lift_sound_ws` with it and the certificate's own check.  The runtime is an unadopted observation
(see the registry row's provenance). -/

namespace Blanc.Lift.Dai

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- **Dai passes the write-site check** (generated, one kernel decide per entry). -/
theorem dai_wsCert : wsCert cert DaiWs.implWsAnn = true :=
  wsCert_of_wsFrom (by decide +kernel) DaiWs.ws_rest_0

/-- Dai's runs, with the write-site observation. -/
theorem daiRun_ws {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork) :
    SProg.RunP (WsStep (wsRoot DaiWs.implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) cert.prog sevm pre post :=
  lift_sound_ws cert_check dai_wsCert hcode fork run

end Blanc.Lift.Dai
