-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatStore.lean : heartbeat storage certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatSstore
import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBlocks

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorHeartbeatMemory_size_mod :
    officialConstructorHeartbeatMemory.size % 32 = 0 := by
  rw [officialConstructorHeartbeatMemory_size]

private theorem officialConstructorHeartbeatMemory_argument_window :
    192 + 32 ≤ officialConstructorHeartbeatMemory.size := by
  rw [officialConstructorHeartbeatMemory_size]
  decide

private theorem officialConstructorHeartbeatMemory_read_initialInterval :
    Bytes.toB256 ((officialConstructorHeartbeatMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
  simpa [officialConstructorArgumentWord] using
    officialConstructorHeartbeatMemory_read_argument ⟨6, by decide⟩

private theorem officialConstructorHeartbeatMemory_read_same :
    (officialConstructorHeartbeatMemory.read 192 32).2 =
      officialConstructorHeartbeatMemory := by
  simpa using officialConstructorHeartbeatMemory_read_argument_memory
    ⟨6, by decide⟩

theorem officialConstructorHeartbeatStoreLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hcurrent : (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorEffectBase sevm base).setMach
        ⟨[], officialConstructorFinalMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorHeartbeatLoggedBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G + 22109⟩)
      (loadArgumentIndex 6 +++
        pushB256 heartbeatIntervalSlot ::: sstore ::: rest) post := by
  apply constructorArgumentSstorePrefix_runCompiled
      (i := ⟨6, by decide⟩)
      (value := officialConstructorArgs.initialHeartbeatInterval)
      (Gafter := G + 22100)
  · omega
  · decide
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := heartbeatIntervalSlot) (by decide +kernel)
  · exact officialConstructorHeartbeatMemory_size_mod
  · exact officialConstructorHeartbeatMemory_argument_window
  · exact officialConstructorHeartbeatMemory_read_initialInterval
  · exact officialConstructorHeartbeatMemory_read_same
  · exact officialConstructorHeartbeatSstore_runCompiled
      hcold horiginal hcurrent hstatic hrest

end LidoCircuitBreaker

end Blanc
