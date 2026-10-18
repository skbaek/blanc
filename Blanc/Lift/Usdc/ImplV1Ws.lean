import Blanc.Lift.WriteSiteSound
import Blanc.Lift.Usdc.ImplV1.Check
import Blanc.Lift.Usdc.ImplV1Ws.Check

/-! USDC FiatTokenV1 passes the write-site check (unit H3, as W6 for V2_2).

`implV1_wsCert` assembles the generated per-entry kernel decisions
(`ImplV1Ws/Check<i>.lean`, chained in `ImplV1Ws/Check.lean`; producer
`scripts/lift/ws_annot.py`, registered in `scripts/lift/certificates.json` row
`usdc-impl-v1`), and `implV1Run_ws` instantiates `lift_sound_ws` with it and the
certificate's own check.  Neither uses the free-pointer checker. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- **FiatTokenV1 passes the write-site check** (generated, one kernel decide per entry). -/
theorem implV1_wsCert : wsCert ImplV1.cert ImplV1Ws.implWsAnn = true :=
  wsCert_of_wsFrom (by decide +kernel) ImplV1Ws.ws_rest_0

/-- FiatTokenV1's runs, with the write-site observation. -/
theorem implV1Run_ws {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = ImplV1.code) (fork : CoveredFork sevm.benvStat.fork) :
    SProg.RunP (WsStep (wsRoot ImplV1Ws.implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) ImplV1.cert.prog sevm pre post :=
  lift_sound_ws ImplV1.cert_check implV1_wsCert code fork run

end Blanc.Lift.Usdc
