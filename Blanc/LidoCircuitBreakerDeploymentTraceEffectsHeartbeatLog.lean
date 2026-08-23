-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLog.lean : heartbeat log certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLogOpcode

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

set_option maxRecDepth 4096 in
private theorem officialConstructorHeartbeatLogPrefix_generic
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {G : Nat} {rest : Func}
    (hlog : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[Nat.toB256 (officialConstructorEventScratch / 32) * 32,
            (2 : B256) * 32, heartbeatIntervalUpdatedEvent],
          memory, G + 1262⟩)
      (Ninst.log (Fin.succ 0) ::: rest) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 1271⟩)
      (pushB256 heartbeatIntervalUpdatedEvent :::
        logWith 0
          (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
        rest) post := by
  unfold logWith
  func_run (3)
  exact hlog

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
  apply officialConstructorHeartbeatLogPrefix_generic
  exact officialConstructorHeartbeatLogOpcode_runCompiled hstatic hrest

end LidoCircuitBreaker

end Blanc
