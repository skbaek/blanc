-- LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratch.lean : composed pause scratch certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratchZero

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorPauseScratchLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G + 27⟩)
      (pushB256 0 :::
        storeByteOffset officialConstructorEventScratch +++
        loadArgumentIndex 5 +++
        storeByteOffset (officialConstructorEventScratch + 32) +++
        rest) post := by
  have hvalue := officialConstructorPauseScratchValue_runCompiled hrest
  exact officialConstructorPauseScratchZero_runCompiled hvalue

end LidoCircuitBreaker

end Blanc
