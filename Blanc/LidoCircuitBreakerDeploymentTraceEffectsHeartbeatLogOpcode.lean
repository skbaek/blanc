-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLogOpcode.lean : heartbeat LOG certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatStore

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorHeartbeatMemory_read_data :
    (officialConstructorHeartbeatMemory.read
        officialConstructorEventScratch 64).1 =
      (0 : B256).toBytes ++
        officialConstructorArgs.initialHeartbeatInterval.toBytes := by
  rw [Mem.Reads.read officialConstructorHeartbeatMemory_reads]
  unfold officialConstructorHeartbeatImage officialConstructorHeartbeatZeroImage
  simpa only [B256.length_toBytes] using
    Bytes.sliceD_writeAt_pair officialConstructorPauseImage
      (0 : B256).toBytes
      officialConstructorArgs.initialHeartbeatInterval.toBytes
      officialConstructorEventScratch

private theorem officialConstructorHeartbeatMemory_read_memory :
    (officialConstructorHeartbeatMemory.read
        officialConstructorEventScratch 64).2 =
      officialConstructorHeartbeatMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorHeartbeatMemory_size]
  · rw [officialConstructorHeartbeatMemory_size,
      officialConstructorEventScratch_eq]

private theorem officialConstructorHeartbeatMemory_size_mod_log :
    officialConstructorHeartbeatMemory.size % 32 = 0 := by
  rw [officialConstructorHeartbeatMemory_size]

private theorem officialConstructorHeartbeatMemory_log_window :
    officialConstructorEventScratch + 64 ≤
      officialConstructorHeartbeatMemory.size := by
  rw [officialConstructorHeartbeatMemory_size,
    officialConstructorEventScratch_eq]

private theorem officialConstructorHeartbeatLoggedBase_eq_addLog
    (sevm : Sevm) (base : Devm) :
    officialConstructorHeartbeatLoggedBase sevm base =
      (officialConstructorPauseStoredBase sevm base).addLog
        ⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          (0 : B256).toBytes ++
            officialConstructorArgs.initialHeartbeatInterval.toBytes⟩ := by
  rfl

theorem officialConstructorHeartbeatLogOpcode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorHeartbeatLoggedBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[Nat.toB256 (officialConstructorEventScratch / 32) * 32,
            (2 : B256) * 32, heartbeatIntervalUpdatedEvent],
          officialConstructorHeartbeatMemory, G + 1262⟩)
      (Ninst.log (Fin.succ 0) ::: rest) post := by
  apply constructorEventLog1Opcode_runCompiled
      (topic := heartbeatIntervalUpdatedEvent)
      (data := (0 : B256).toBytes ++
        officialConstructorArgs.initialHeartbeatInterval.toBytes)
      (Gafter := G)
  · omega
  · exact officialConstructorHeartbeatMemory_size_mod_log
  · exact officialConstructorHeartbeatMemory_log_window
  · exact officialConstructorHeartbeatMemory_read_data
  · exact officialConstructorHeartbeatMemory_read_memory
  · exact hstatic
  · rw [← officialConstructorHeartbeatLoggedBase_eq_addLog]
    exact hrest

end LidoCircuitBreaker

end Blanc
