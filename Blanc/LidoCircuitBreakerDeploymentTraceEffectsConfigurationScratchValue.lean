-- LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratchValue.lean : pause scratch value certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsConfigurationLog
import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBlocksMemory

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorPauseZeroMemory_size_mod :
    officialConstructorPauseZeroMemory.size % 32 = 0 := by
  rw [officialConstructorPauseZeroMemory_size]

private theorem officialConstructorPauseZeroMemory_load_window :
    160 + 32 ≤ officialConstructorPauseZeroMemory.size := by
  rw [officialConstructorPauseZeroMemory_size]
  decide

private theorem officialConstructorPauseZeroMemory_read_initialDuration :
    Bytes.toB256 ((officialConstructorPauseZeroMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
  simpa [officialConstructorArgumentWord] using
    officialConstructorPauseZeroMemory_read_argument ⟨5, by decide⟩

private theorem officialConstructorPauseZeroMemory_read_same :
    (officialConstructorPauseZeroMemory.read 160 32).2 =
      officialConstructorPauseZeroMemory := by
  simpa using officialConstructorPauseZeroMemory_read_argument_memory
    ⟨5, by decide⟩

private theorem officialConstructorPauseZeroMemory_write_initialDuration :
    officialConstructorPauseZeroMemory.write
        (officialConstructorEventScratch + 32)
        officialConstructorArgs.initialPauseDuration.toBytes =
      officialConstructorPauseMemory := by
  rfl

theorem officialConstructorPauseScratchValue_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseZeroMemory, G + 15⟩)
      (loadArgumentIndex 5 +++
        storeByteOffset (officialConstructorEventScratch + 32) +++
        rest) post := by
  apply constructorArgumentMstorePrefix_runCompiled
      (i := ⟨5, by decide⟩)
      (offset := officialConstructorEventScratch + 32)
      (indexPushCost := 3) (loadCost := 3) (storeExt := 3)
      (memory' := officialConstructorPauseMemory)
      (value := officialConstructorArgs.initialPauseDuration)
      (Gafter := G)
  · rw [officialConstructorEventScratch_eq]
    decide
  · omega
  · decide
  · intro S G'
    change gVerylow +
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨S, officialConstructorPauseZeroMemory, G'⟩).extCost
          [⟨160, 32⟩] = 3
    rw [Devm.extCost_zero_of_le
      (N := officialConstructorPauseZeroMemory)
      (i := 160) (sz := 32)
      officialConstructorPauseZeroMemory_size_mod
      officialConstructorPauseZeroMemory_load_window]
    rfl
  · exact officialConstructorPauseZeroMemory_read_initialDuration
  · exact officialConstructorPauseZeroMemory_read_same
  · intro S G'
    exact Devm.extCost_of_size officialConstructorPauseZeroMemory_size (by
      rw [officialConstructorEventScratch_eq]
      decide +kernel)
  · exact officialConstructorPauseZeroMemory_write_initialDuration
  · exact hrest

end LidoCircuitBreaker

end Blanc
