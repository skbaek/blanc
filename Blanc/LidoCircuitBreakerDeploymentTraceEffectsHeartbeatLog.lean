-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLog.lean : heartbeat log certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLogOpcode

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorHeartbeatLogLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorHeartbeatLoggedBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G + 1271⟩)
      (pushB256 heartbeatIntervalUpdatedEvent :::
        logWith 0
          (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
        rest) post := by
  apply constructorEventLog1Prefix_runCompiled
      (topic := heartbeatIntervalUpdatedEvent)
      (Gafter := G + 1262)
  · omega
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := heartbeatIntervalUpdatedEvent) (by decide +kernel)
  · exact officialConstructorHeartbeatLogOpcode_runCompiled hstatic hrest

end LidoCircuitBreaker

end Blanc
