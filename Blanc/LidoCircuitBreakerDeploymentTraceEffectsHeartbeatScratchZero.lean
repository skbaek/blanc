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

set_option maxRecDepth 4096 in
private theorem officialConstructorHeartbeatScratchZero_generic
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory memory' : Mem} {G : Nat} {rest : Func}
    (h32 : memory.size % 32 = 0)
    (hwindow : officialConstructorEventScratch + 32 ≤ memory.size)
    (hzero : memory.write officialConstructorEventScratch
      (0 : B256).toBytes = memory')
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory', G + 12⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 20⟩)
      (pushB256 0 :::
        storeByteOffset officialConstructorEventScratch +++ rest) post := by
  have hscratchLt : officialConstructorEventScratch < 2 ^ 16 := by
    rw [officialConstructorEventScratch_eq]
    decide
  have hscratchNat :
      (Bytes.toB256
        [(officialConstructorEventScratch >>> 8).toUInt8,
          officialConstructorEventScratch.toUInt8]).toNat =
        officialConstructorEventScratch := by
    rw [List.toB256_pair officialConstructorEventScratch hscratchLt]
    rw [officialConstructorEventScratch_eq]
    decide
  unfold storeByteOffset pushFixedNat
  simp only [if_pos hscratchLt]
  func_run (3) [0]
  all_goals try rw [hscratchNat]
  all_goals try rw [hzero]
  all_goals try rw [Devm.extCost_zero_of_le
    (N := memory)
    (i := officialConstructorEventScratch) (sz := 32)
    h32 hwindow]
  exact hrest

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
  apply officialConstructorHeartbeatScratchZero_generic
    (memory' := officialConstructorHeartbeatZeroMemory)
  · exact officialConstructorPauseMemory_size_mod_heartbeat
  · exact officialConstructorPauseMemory_scratch_window_heartbeat
  · exact officialConstructorPauseMemory_write_heartbeat_zero
  · exact hrest

end LidoCircuitBreaker

end Blanc
