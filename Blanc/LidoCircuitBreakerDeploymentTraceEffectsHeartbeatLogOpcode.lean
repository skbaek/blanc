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

private theorem officialConstructorHeartbeatLogOpcode_generic
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {data : Bytes} {G : Nat} {rest : Func}
    (h32 : memory.size % 32 = 0)
    (hwindow : officialConstructorEventScratch + 64 ≤ memory.size)
    (hdata : (memory.read officialConstructorEventScratch 64).1 = data)
    (hmemory : (memory.read officialConstructorEventScratch 64).2 = memory)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((base.addLog ⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
          data⟩).setMach ⟨[], memory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[Nat.toB256 (officialConstructorEventScratch / 32) * 32,
            (2 : B256) * 32, heartbeatIntervalUpdatedEvent],
          memory, G + 1262⟩)
      (Ninst.log (Fin.succ 0) ::: rest) post := by
  have hi :
      (Nat.toB256 (officialConstructorEventScratch / 32) * 32).toNat =
        officialConstructorEventScratch := by
    rw [officialConstructorEventScratch_eq]
    decide
  have hsz : ((2 : B256) * 32).toNat = 64 := by decide
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_log_of
        (n := Fin.succ 0)
        (i := Nat.toB256 (officialConstructorEventScratch / 32) * 32)
        (sz := (2 : B256) * 32)
        (topics := [heartbeatIntervalUpdatedEvent]) (s := [])
        (c := 1262) (G := G) (M := memory) (data := data)
    · rfl
    · rfl
    · exact hstatic
    · rw [hi, hsz]
      rw [Devm.extCost_zero_of_le (N := memory) h32 hwindow]
      decide
    · simpa only [Devm.memory_setMach, hi, hsz] using hdata
    · simpa only [Devm.memory_setMach, hi, hsz] using hmemory
    · simp only [Devm.gasLeft_setMach]
  · change Func.RunCompiled fs sevm
      ((base.addLog ⟨sevm.currentTarget, [heartbeatIntervalUpdatedEvent],
        data⟩).setMach ⟨[], memory, G⟩)
      rest post
    exact hrest

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
  apply officialConstructorHeartbeatLogOpcode_generic
    (data := (0 : B256).toBytes ++
      officialConstructorArgs.initialHeartbeatInterval.toBytes)
  · exact officialConstructorHeartbeatMemory_size_mod_log
  · exact officialConstructorHeartbeatMemory_log_window
  · exact officialConstructorHeartbeatMemory_read_data
  · exact officialConstructorHeartbeatMemory_read_memory
  · exact hstatic
  · rw [← officialConstructorHeartbeatLoggedBase_eq_addLog]
    exact hrest

end LidoCircuitBreaker

end Blanc
