-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratchValue.lean : heartbeat scratch value certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLog
import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBlocksMemory

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorHeartbeatZeroMemory_size_mod :
    officialConstructorHeartbeatZeroMemory.size % 32 = 0 := by
  rw [officialConstructorHeartbeatZeroMemory_size]

private theorem officialConstructorHeartbeatZeroMemory_load_window :
    192 + 32 ≤ officialConstructorHeartbeatZeroMemory.size := by
  rw [officialConstructorHeartbeatZeroMemory_size]
  decide

private theorem officialConstructorHeartbeatZeroMemory_store_window :
    officialConstructorEventScratch + 32 + 32 ≤
      officialConstructorHeartbeatZeroMemory.size := by
  rw [officialConstructorHeartbeatZeroMemory_size,
    officialConstructorEventScratch_eq]

private theorem officialConstructorHeartbeatZeroMemory_read_initialInterval :
    Bytes.toB256 ((officialConstructorHeartbeatZeroMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
  simpa [officialConstructorArgumentWord] using
    officialConstructorHeartbeatZeroMemory_read_argument ⟨6, by decide⟩

private theorem officialConstructorHeartbeatZeroMemory_read_same :
    (officialConstructorHeartbeatZeroMemory.read 192 32).2 =
      officialConstructorHeartbeatZeroMemory := by
  simpa using officialConstructorHeartbeatZeroMemory_read_argument_memory
    ⟨6, by decide⟩

private theorem officialConstructorHeartbeatZeroMemory_write_initialInterval :
    officialConstructorHeartbeatZeroMemory.write
        (officialConstructorEventScratch + 32)
        officialConstructorArgs.initialHeartbeatInterval.toBytes =
      officialConstructorHeartbeatMemory := by
  rfl

theorem officialConstructorHeartbeatScratchValue_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatZeroMemory, G + 12⟩)
      (loadArgumentIndex 6 +++
        storeByteOffset (officialConstructorEventScratch + 32) +++
        rest) post := by
  apply constructorArgumentMstorePrefix_runCompiled
    (i := ⟨6, by decide⟩)
    (offset := officialConstructorEventScratch + 32)
    (indexPushCost := 3) (loadCost := 3) (storeExt := 0)
    (memory' := officialConstructorHeartbeatMemory)
    (value := officialConstructorArgs.initialHeartbeatInterval)
    (Gafter := G)
  · rw [officialConstructorEventScratch_eq]
    decide
  · omega
  · decide
  · intro S G'
    change gVerylow +
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨S, officialConstructorHeartbeatZeroMemory, G'⟩).extCost
          [⟨192, 32⟩] = 3
    rw [Devm.extCost_zero_of_le
      (N := officialConstructorHeartbeatZeroMemory)
      (i := 192) (sz := 32)
      officialConstructorHeartbeatZeroMemory_size_mod
      officialConstructorHeartbeatZeroMemory_load_window]
    rfl
  · exact officialConstructorHeartbeatZeroMemory_read_initialInterval
  · exact officialConstructorHeartbeatZeroMemory_read_same
  · intro S G'
    exact Devm.extCost_zero_of_le
      (N := officialConstructorHeartbeatZeroMemory)
      (i := officialConstructorEventScratch + 32) (sz := 32)
      officialConstructorHeartbeatZeroMemory_size_mod
      officialConstructorHeartbeatZeroMemory_store_window
  · exact officialConstructorHeartbeatZeroMemory_write_initialInterval
  · exact hrest

end LidoCircuitBreaker

end Blanc
