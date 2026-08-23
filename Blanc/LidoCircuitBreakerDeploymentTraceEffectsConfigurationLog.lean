-- LidoCircuitBreakerDeploymentTraceEffectsConfigurationLog.lean : pause event certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsConfigurationStore

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorPauseMemory_read_data :
    (officialConstructorPauseMemory.read
        officialConstructorEventScratch 64).1 =
      (0 : B256).toBytes ++
        officialConstructorArgs.initialPauseDuration.toBytes := by
  rw [Mem.Reads.read officialConstructorPauseMemory_reads]
  unfold officialConstructorPauseImage officialConstructorPauseZeroImage
  simpa only [B256.length_toBytes] using
    Bytes.sliceD_writeAt_pair officialConstructorPatchedImage
      (0 : B256).toBytes
      officialConstructorArgs.initialPauseDuration.toBytes
      officialConstructorEventScratch

private theorem officialConstructorPauseMemory_read_memory :
    (officialConstructorPauseMemory.read
        officialConstructorEventScratch 64).2 =
      officialConstructorPauseMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorPauseMemory_size]
  · rw [officialConstructorPauseMemory_size,
      officialConstructorEventScratch_eq]

private theorem officialConstructorPauseMemory_size_mod_log :
    officialConstructorPauseMemory.size % 32 = 0 := by
  rw [officialConstructorPauseMemory_size]

private theorem officialConstructorPauseMemory_log_window :
    officialConstructorEventScratch + 64 ≤
      officialConstructorPauseMemory.size := by
  rw [officialConstructorPauseMemory_size,
    officialConstructorEventScratch_eq]

private theorem officialConstructorPauseLoggedBase_eq_addLog
    (sevm : Sevm) (base : Devm) :
    officialConstructorPauseLoggedBase sevm base =
      (officialConstructorInitializedBase sevm base).addLog
        ⟨sevm.currentTarget, [pauseDurationUpdatedEvent],
          (0 : B256).toBytes ++
            officialConstructorArgs.initialPauseDuration.toBytes⟩ := by
  rfl

private theorem officialConstructorPauseLogOpcode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseLoggedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[Nat.toB256 (officialConstructorEventScratch / 32) * 32,
            (2 : B256) * 32, pauseDurationUpdatedEvent],
          officialConstructorPauseMemory, G + 1262⟩)
      (Ninst.log (Fin.succ 0) ::: rest) post := by
  apply constructorEventLog1Opcode_runCompiled
      (topic := pauseDurationUpdatedEvent)
      (data := (0 : B256).toBytes ++
        officialConstructorArgs.initialPauseDuration.toBytes)
      (Gafter := G)
  · omega
  · exact officialConstructorPauseMemory_size_mod_log
  · exact officialConstructorPauseMemory_log_window
  · exact officialConstructorPauseMemory_read_data
  · exact officialConstructorPauseMemory_read_memory
  · exact hstatic
  · rw [← officialConstructorPauseLoggedBase_eq_addLog]
    exact hrest

theorem officialConstructorPauseLogLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseLoggedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G + 1271⟩)
      (pushB256 pauseDurationUpdatedEvent :::
        logWith 0
          (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
        rest) post := by
  apply constructorEventLog1Prefix_runCompiled
      (topic := pauseDurationUpdatedEvent)
      (Gafter := G + 1262)
  · omega
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := pauseDurationUpdatedEvent) (by decide +kernel)
  · exact officialConstructorPauseLogOpcode_runCompiled hstatic hrest

end LidoCircuitBreaker

end Blanc
