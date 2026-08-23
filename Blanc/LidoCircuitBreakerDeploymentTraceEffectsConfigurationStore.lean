-- LidoCircuitBreakerDeploymentTraceEffectsConfigurationStore.lean : pause storage certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeat
import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBlocks

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorPauseMemory_size_mod_store :
    officialConstructorPauseMemory.size % 32 = 0 := by
  rw [officialConstructorPauseMemory_size]

private theorem officialConstructorPauseMemory_argument_window :
    160 + 32 ≤ officialConstructorPauseMemory.size := by
  rw [officialConstructorPauseMemory_size]
  decide

private theorem officialConstructorPauseMemory_read_initialDuration :
    Bytes.toB256 ((officialConstructorPauseMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
  simpa [officialConstructorArgumentWord] using
    officialConstructorPauseMemory_read_argument ⟨5, by decide⟩

private theorem officialConstructorPauseMemory_read_same_store :
    (officialConstructorPauseMemory.read 160 32).2 =
      officialConstructorPauseMemory := by
  simpa using officialConstructorPauseMemory_read_argument_memory
    ⟨5, by decide⟩

private theorem officialConstructorPauseSstore_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcold : (sevm.currentTarget, pauseDurationSlot) ∉
      (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hcurrent : (officialConstructorPauseLoggedBase sevm base).getStorVal
      sevm.currentTarget pauseDurationSlot = 0)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseLoggedBase sevm base).setMach
        ⟨[pauseDurationSlot, officialConstructorArgs.initialPauseDuration],
          officialConstructorPauseMemory, G + 22100⟩)
      (sstore ::: rest) post := by
  have hrest' : Func.RunCompiled fs sevm
      ((officialConstructorColdStore sevm
          (officialConstructorPauseLoggedBase sevm base)
          pauseDurationSlot
          officialConstructorArgs.initialPauseDuration).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post := by
    simpa only [officialConstructorPauseStoredBase] using hrest
  exact officialConstructorColdStore_runCompiled
    hcold horiginal hcurrent
    (by unfold officialConstructorArgs; decide)
    (by simp only [gCallStipend]; omega) hstatic hrest'

theorem officialConstructorPauseStoreLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcold : (sevm.currentTarget, pauseDurationSlot) ∉
      (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hcurrent : (officialConstructorPauseLoggedBase sevm base).getStorVal
      sevm.currentTarget pauseDurationSlot = 0)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseLoggedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G + 22109⟩)
      (loadArgumentIndex 5 +++
        pushB256 pauseDurationSlot ::: sstore ::: rest) post := by
  apply constructorArgumentSstorePrefix_runCompiled
      (i := ⟨5, by decide⟩)
      (value := officialConstructorArgs.initialPauseDuration)
      (Gafter := G + 22100)
  · omega
  · decide
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := pauseDurationSlot) (by decide +kernel)
  · exact officialConstructorPauseMemory_size_mod_store
  · exact officialConstructorPauseMemory_argument_window
  · exact officialConstructorPauseMemory_read_initialDuration
  · exact officialConstructorPauseMemory_read_same_store
  · exact officialConstructorPauseSstore_runCompiled
      hcold horiginal hcurrent hstatic hrest

end LidoCircuitBreaker

end Blanc
