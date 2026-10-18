import Blanc.Lift.WriteSiteSound
import Blanc.Lift.Usdc.ImplV2.Check
import Blanc.Lift.Usdc.ImplV2Ws.Check

/-! USDC FiatTokenV2 passes the write-site check (unit H3, as W6 for V2_2).

`implV2_wsCert` assembles the generated per-entry kernel decisions
(`ImplV2Ws/Check<i>.lean`, chained in `ImplV2Ws/Check.lean`; producer
`scripts/lift/ws_annot.py`, registered in `scripts/lift/certificates.json` row
`usdc-impl-v2`), and `implV2Run_ws` instantiates `lift_sound_ws` with it and the
certificate's own check.  Neither uses the free-pointer checker. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.WriteSite

/-- **FiatTokenV2 passes the write-site check** (generated, one kernel decide per entry). -/
theorem implV2_wsCert : wsCert ImplV2.cert ImplV2Ws.implWsAnn = true :=
  wsCert_of_wsFrom (by decide +kernel) ImplV2Ws.ws_rest_0

/-- FiatTokenV2's runs, with the write-site observation. -/
theorem implV2Run_ws {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = ImplV2.code) (fork : CoveredFork sevm.benvStat.fork) :
    SProg.RunP (WsStep (wsRoot ImplV2Ws.implWsAnn) (WriteSite.Env.root sevm)
      (StepIn ⟨0, sevm, pre, .ok post, run⟩)) ImplV2.cert.prog sevm pre post :=
  lift_sound_ws ImplV2.cert_check implV2_wsCert code fork run

end Blanc.Lift.Usdc
