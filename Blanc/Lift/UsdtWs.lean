import Blanc.Lift.WriteSiteSound
import Blanc.Lift.Usdt.Check
import Blanc.Lift.UsdtWs.Check

/-! USDT TetherToken passes the write-site check (Curve 3pool U0 candidate).

`usdt_wsCert` assembles the generated per-entry kernel decisions (`UsdtWs/Check<i>.lean`, chained
in `UsdtWs/Check.lean`; producer `scripts/lift/ws_annot.py`, candidate registry
`scripts/reference/curve-u0/certificates.json` row `curve-u0-usdt`), and `usdtRun_ws` instantiates
`lift_sound_ws` with it and the certificate's own check.  The runtime is an unadopted observation
(see the registry row's provenance). -/

namespace Blanc.Lift.Usdt

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- **TetherToken passes the write-site check** (generated, one kernel decide per entry). -/
theorem usdt_wsCert : wsCert cert UsdtWs.implWsAnn = true :=
  wsCert_of_wsFrom (by decide +kernel) UsdtWs.ws_rest_0

/-- TetherToken's runs, with the write-site observation. -/
theorem usdtRun_ws {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork) :
    SProg.RunP (WsStep (wsRoot UsdtWs.implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) cert.prog sevm pre post :=
  lift_sound_ws cert_check usdt_wsCert hcode fork run

end Blanc.Lift.Usdt
