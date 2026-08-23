-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratch.lean : composed heartbeat scratch certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratchZero

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorHeartbeatScratchLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G + 20⟩)
      (pushB256 0 :::
        storeByteOffset officialConstructorEventScratch +++
        loadArgumentIndex 6 +++
        storeByteOffset (officialConstructorEventScratch + 32) +++
        rest) post := by
  have hvalue := officialConstructorHeartbeatScratchValue_runCompiled hrest
  exact officialConstructorHeartbeatScratchZero_runCompiled hvalue

end LidoCircuitBreaker

end Blanc

