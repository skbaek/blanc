-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratchZero.lean : heartbeat scratch zero certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratchValue

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorPauseMemory_size_mod_heartbeat :
    officialConstructorPauseMemory.size % 32 = 0 := by
  rw [officialConstructorPauseMemory_size]

private theorem officialConstructorPauseMemory_scratch_window_heartbeat :
    officialConstructorEventScratch + 32 ≤
      officialConstructorPauseMemory.size := by
  rw [officialConstructorPauseMemory_size,
    officialConstructorEventScratch_eq]
  decide

private theorem officialConstructorPauseMemory_write_heartbeat_zero :
    officialConstructorPauseMemory.write
      officialConstructorEventScratch (0 : B256).toBytes =
      officialConstructorHeartbeatZeroMemory := by
  rfl

theorem officialConstructorHeartbeatScratchZero_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatZeroMemory, G + 12⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G + 20⟩)
      (pushB256 0 :::
        storeByteOffset officialConstructorEventScratch +++ rest) post := by
  apply constructorZeroMstorePrefix_runCompiled
    (offset := officialConstructorEventScratch) (storeExt := 0)
    (memory' := officialConstructorHeartbeatZeroMemory)
    (Gafter := G + 12)
  · rw [officialConstructorEventScratch_eq]
    decide
  · omega
  · intro S G'
    exact Devm.extCost_zero_of_le
      (N := officialConstructorPauseMemory)
      (i := officialConstructorEventScratch) (sz := 32)
      officialConstructorPauseMemory_size_mod_heartbeat
      officialConstructorPauseMemory_scratch_window_heartbeat
  · exact officialConstructorPauseMemory_write_heartbeat_zero
  · exact hrest

end LidoCircuitBreaker

end Blanc
