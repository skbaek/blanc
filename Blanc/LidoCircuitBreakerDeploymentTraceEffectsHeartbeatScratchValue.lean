-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratchValue.lean : heartbeat scratch value certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLog

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

set_option maxRecDepth 4096 in
private theorem officialConstructorHeartbeatScratchValue_generic
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory memory' : Mem} {value : B256} {G : Nat} {rest : Func}
    (h32 : memory.size % 32 = 0)
    (hload : 192 + 32 ≤ memory.size)
    (hstore : officialConstructorEventScratch + 32 + 32 ≤ memory.size)
    (hvalue : Bytes.toB256 ((memory.read 192 32).1) = value)
    (hmemory : (memory.read 192 32).2 = memory)
    (hfinal : memory.write (officialConstructorEventScratch + 32)
      value.toBytes = memory')
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory', G⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 12⟩)
      (loadArgumentIndex 6 +++
        storeByteOffset (officialConstructorEventScratch + 32) +++
        rest) post := by
  have hnextLt : officialConstructorEventScratch + 32 < 2 ^ 16 := by
    rw [officialConstructorEventScratch_eq]
    decide
  have hnextNat :
      (Bytes.toB256
        [((officialConstructorEventScratch + 32) >>> 8).toUInt8,
          (officialConstructorEventScratch + 32).toUInt8]).toNat =
        officialConstructorEventScratch + 32 := by
    rw [List.toB256_pair (officialConstructorEventScratch + 32) hnextLt]
    rw [officialConstructorEventScratch_eq]
    decide
  have hindex : (Nat.toB256 (32 * 6)).toNat = 192 := by decide
  unfold storeByteOffset loadArgumentIndex pushCompactNat pushFixedNat
  simp only [if_pos hnextLt]
  func_run (4) [3, 0]
  all_goals try rw [hnextNat]
  all_goals try rw [hindex]
  all_goals try rw [hmemory]
  all_goals try rw [hvalue]
  all_goals try rw [hfinal]
  all_goals try rw [Devm.extCost_zero_of_le
    (N := memory) (i := 192) (sz := 32) h32 hload]
  all_goals try rw [Devm.extCost_zero_of_le
    (N := memory)
    (i := officialConstructorEventScratch + 32) (sz := 32)
    h32 hstore]
  all_goals try decide
  exact hrest

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
  apply officialConstructorHeartbeatScratchValue_generic
    (memory' := officialConstructorHeartbeatMemory)
    (value := officialConstructorArgs.initialHeartbeatInterval)
  · exact officialConstructorHeartbeatZeroMemory_size_mod
  · exact officialConstructorHeartbeatZeroMemory_load_window
  · exact officialConstructorHeartbeatZeroMemory_store_window
  · exact officialConstructorHeartbeatZeroMemory_read_initialInterval
  · exact officialConstructorHeartbeatZeroMemory_read_same
  · exact officialConstructorHeartbeatZeroMemory_write_initialInterval
  · exact hrest

end LidoCircuitBreaker

end Blanc
