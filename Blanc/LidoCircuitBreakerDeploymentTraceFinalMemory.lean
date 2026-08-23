-- LidoCircuitBreakerDeploymentTraceFinalMemory.lean : event-scratch states.
--
-- Each emitted event updates two words.  Keeping the pause and heartbeat
-- checkpoints named prevents later proofs from normalizing all four writes.

import Blanc.LidoCircuitBreakerDeploymentTraceMemory

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

def officialConstructorPauseZeroMemory : Mem :=
  officialConstructorPatchedMemory.write officialConstructorEventScratch
    (0 : B256).toBytes

def officialConstructorPauseZeroImage : Bytes :=
  Bytes.writeAt officialConstructorPatchedImage
    officialConstructorEventScratch (0 : B256).toBytes

theorem officialConstructorPauseZeroMemory_wf :
    Mem.Wf officialConstructorPauseZeroMemory := by
  unfold officialConstructorPauseZeroMemory
  exact Mem.Wf.write officialConstructorPatchedMemory_wf _ _

theorem officialConstructorPauseZeroMemory_reads :
    Mem.Reads officialConstructorPauseZeroMemory
      officialConstructorPauseZeroImage := by
  unfold officialConstructorPauseZeroMemory officialConstructorPauseZeroImage
  exact Mem.Reads.write officialConstructorPatchedMemory_wf
    officialConstructorPatchedMemory_reads _ _

theorem officialConstructorPauseZeroMemory_size :
    officialConstructorPauseZeroMemory.size = 4544 := by
  unfold officialConstructorPauseZeroMemory
  rw [Mem.size_write_word_at, officialConstructorPatchedMemory_size,
    officialConstructorEventScratch_eq]
  decide

theorem officialConstructorPauseZeroMemory_read_argument
    (i : Fin 7) :
    Bytes.toB256
        ((officialConstructorPauseZeroMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  rw [Mem.Reads.read officialConstructorPauseZeroMemory_reads]
  unfold officialConstructorPauseZeroImage
  rw [Bytes.sliceD_writeAt_before _ _ (32 * i.val) 32
      officialConstructorEventScratch (by
        rw [officialConstructorEventScratch_eq]
        have hi := i.isLt
        omega),
    ← Mem.Reads.read officialConstructorPatchedMemory_reads]
  exact officialConstructorPatchedMemory_read_argument i

theorem officialConstructorPauseZeroMemory_read_argument_memory
    (i : Fin 7) :
    (officialConstructorPauseZeroMemory.read (32 * i.val) 32).2 =
      officialConstructorPauseZeroMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorPauseZeroMemory_size]
  · rw [officialConstructorPauseZeroMemory_size]
    have hi := i.isLt
    omega

def officialConstructorPauseMemory : Mem :=
  officialConstructorPauseZeroMemory.write
    (officialConstructorEventScratch + 32)
      officialConstructorArgs.initialPauseDuration.toBytes

def officialConstructorPauseImage : Bytes :=
  Bytes.writeAt officialConstructorPauseZeroImage
    (officialConstructorEventScratch + 32)
    officialConstructorArgs.initialPauseDuration.toBytes

theorem officialConstructorPauseMemory_wf :
    Mem.Wf officialConstructorPauseMemory := by
  unfold officialConstructorPauseMemory
  exact Mem.Wf.write officialConstructorPauseZeroMemory_wf _ _

theorem officialConstructorPauseMemory_reads :
    Mem.Reads officialConstructorPauseMemory
      officialConstructorPauseImage := by
  unfold officialConstructorPauseMemory officialConstructorPauseImage
  exact Mem.Reads.write officialConstructorPauseZeroMemory_wf
    officialConstructorPauseZeroMemory_reads _ _

theorem officialConstructorPauseMemory_size :
    officialConstructorPauseMemory.size = 4576 := by
  unfold officialConstructorPauseMemory
  rw [Mem.size_write_word_at, officialConstructorPauseZeroMemory_size,
    officialConstructorEventScratch_eq]
  decide

theorem officialConstructorPauseMemory_read_argument
    (i : Fin 7) :
    Bytes.toB256
        ((officialConstructorPauseMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  rw [Mem.Reads.read officialConstructorPauseMemory_reads]
  unfold officialConstructorPauseImage
  rw [Bytes.sliceD_writeAt_before _ _ (32 * i.val) 32
      (officialConstructorEventScratch + 32) (by
        rw [officialConstructorEventScratch_eq]
        have hi := i.isLt
        omega),
    ← Mem.Reads.read officialConstructorPauseZeroMemory_reads]
  exact officialConstructorPauseZeroMemory_read_argument i

theorem officialConstructorPauseMemory_read_argument_memory
    (i : Fin 7) :
    (officialConstructorPauseMemory.read (32 * i.val) 32).2 =
      officialConstructorPauseMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorPauseMemory_size]
  · rw [officialConstructorPauseMemory_size]
    have hi := i.isLt
    omega

def officialConstructorHeartbeatZeroMemory : Mem :=
  officialConstructorPauseMemory.write officialConstructorEventScratch
    (0 : B256).toBytes

def officialConstructorHeartbeatZeroImage : Bytes :=
  Bytes.writeAt officialConstructorPauseImage
    officialConstructorEventScratch (0 : B256).toBytes

theorem officialConstructorHeartbeatZeroMemory_wf :
    Mem.Wf officialConstructorHeartbeatZeroMemory := by
  unfold officialConstructorHeartbeatZeroMemory
  exact Mem.Wf.write officialConstructorPauseMemory_wf _ _

theorem officialConstructorHeartbeatZeroMemory_reads :
    Mem.Reads officialConstructorHeartbeatZeroMemory
      officialConstructorHeartbeatZeroImage := by
  unfold officialConstructorHeartbeatZeroMemory
    officialConstructorHeartbeatZeroImage
  exact Mem.Reads.write officialConstructorPauseMemory_wf
    officialConstructorPauseMemory_reads _ _

theorem officialConstructorHeartbeatZeroMemory_size :
    officialConstructorHeartbeatZeroMemory.size = 4576 := by
  unfold officialConstructorHeartbeatZeroMemory
  rw [Mem.size_write_word_at, officialConstructorPauseMemory_size,
    officialConstructorEventScratch_eq]
  decide

theorem officialConstructorHeartbeatZeroMemory_read_argument
    (i : Fin 7) :
    Bytes.toB256
        ((officialConstructorHeartbeatZeroMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  rw [Mem.Reads.read officialConstructorHeartbeatZeroMemory_reads]
  unfold officialConstructorHeartbeatZeroImage
  rw [Bytes.sliceD_writeAt_before _ _ (32 * i.val) 32
      officialConstructorEventScratch (by
        rw [officialConstructorEventScratch_eq]
        have hi := i.isLt
        omega),
    ← Mem.Reads.read officialConstructorPauseMemory_reads]
  exact officialConstructorPauseMemory_read_argument i

theorem officialConstructorHeartbeatZeroMemory_read_argument_memory
    (i : Fin 7) :
    (officialConstructorHeartbeatZeroMemory.read (32 * i.val) 32).2 =
      officialConstructorHeartbeatZeroMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorHeartbeatZeroMemory_size]
  · rw [officialConstructorHeartbeatZeroMemory_size]
    have hi := i.isLt
    omega

def officialConstructorHeartbeatMemory : Mem :=
  officialConstructorHeartbeatZeroMemory.write
    (officialConstructorEventScratch + 32)
      officialConstructorArgs.initialHeartbeatInterval.toBytes

def officialConstructorHeartbeatImage : Bytes :=
  Bytes.writeAt officialConstructorHeartbeatZeroImage
    (officialConstructorEventScratch + 32)
    officialConstructorArgs.initialHeartbeatInterval.toBytes

theorem officialConstructorHeartbeatMemory_wf :
    Mem.Wf officialConstructorHeartbeatMemory := by
  unfold officialConstructorHeartbeatMemory
  exact Mem.Wf.write officialConstructorHeartbeatZeroMemory_wf _ _

theorem officialConstructorHeartbeatMemory_reads :
    Mem.Reads officialConstructorHeartbeatMemory
      officialConstructorHeartbeatImage := by
  unfold officialConstructorHeartbeatMemory officialConstructorHeartbeatImage
  exact Mem.Reads.write officialConstructorHeartbeatZeroMemory_wf
    officialConstructorHeartbeatZeroMemory_reads _ _

theorem officialConstructorHeartbeatMemory_size :
    officialConstructorHeartbeatMemory.size = 4576 := by
  unfold officialConstructorHeartbeatMemory
  rw [Mem.size_write_word_at, officialConstructorHeartbeatZeroMemory_size,
    officialConstructorEventScratch_eq]
  decide

theorem officialConstructorHeartbeatMemory_read_argument
    (i : Fin 7) :
    Bytes.toB256
        ((officialConstructorHeartbeatMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  rw [Mem.Reads.read officialConstructorHeartbeatMemory_reads]
  unfold officialConstructorHeartbeatImage
  rw [Bytes.sliceD_writeAt_before _ _ (32 * i.val) 32
      (officialConstructorEventScratch + 32) (by
        rw [officialConstructorEventScratch_eq]
        have hi := i.isLt
        omega),
    ← Mem.Reads.read officialConstructorHeartbeatZeroMemory_reads]
  exact officialConstructorHeartbeatZeroMemory_read_argument i

theorem officialConstructorHeartbeatMemory_read_argument_memory
    (i : Fin 7) :
    (officialConstructorHeartbeatMemory.read (32 * i.val) 32).2 =
      officialConstructorHeartbeatMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorHeartbeatMemory_size]
  · rw [officialConstructorHeartbeatMemory_size]
    have hi := i.isLt
    omega

/-- Final constructor memory after the event scratch has been rewritten for
the heartbeat event. -/
def officialConstructorFinalMemory : Mem :=
  officialConstructorHeartbeatMemory

def officialConstructorFinalImage : Bytes :=
  officialConstructorHeartbeatImage

theorem officialConstructorHeartbeatMemory_eq_final :
    officialConstructorHeartbeatMemory = officialConstructorFinalMemory := by
  rfl

theorem officialConstructorFinalMemory_size :
    officialConstructorFinalMemory.size = 4576 := by
  exact officialConstructorHeartbeatMemory_size

theorem officialConstructorFinalMemory_reads :
    Mem.Reads officialConstructorFinalMemory officialConstructorFinalImage := by
  exact officialConstructorHeartbeatMemory_reads

end LidoCircuitBreaker

end Blanc
