-- LidoCircuitBreakerDeploymentTraceImages.lean : named constructor images.
--
-- This unit builds the decoded/copied/patched images and their reusable
-- invariant independently of both program-shape and patch-execution proofs.

import Blanc.LidoCircuitBreakerDeploymentTraceShape

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-! ## Named official memory images -/

def officialConstructorDecodedMemory : Mem :=
  Mem.empty.write 0 (abiEncodeConstructorArgs officialConstructorArgs)

def officialConstructorCopiedMemory : Mem :=
  officialConstructorDecodedMemory.write constructorRuntimeBase
    runtimeTemplateCode

def applyConstructorMemoryPatch
    (memory : Mem) (patch : ImmutablePatch) : Mem :=
  memory.write (constructorRuntimeBase + patch.offset) patch.value.toBytes

def applyConstructorImagePatch
    (image : Bytes) (patch : ImmutablePatch) : Bytes :=
  Bytes.writeAt image (constructorRuntimeBase + patch.offset)
    patch.value.toBytes

def officialConstructorDecodedImage : Bytes :=
  Bytes.writeAt [] 0 (abiEncodeConstructorArgs officialConstructorArgs)

def officialConstructorCopiedImage : Bytes :=
  Bytes.writeAt officialConstructorDecodedImage constructorRuntimeBase
    runtimeTemplateCode

private theorem officialConstructorDecodedMemory_reads :
    Mem.Reads officialConstructorDecodedMemory
      officialConstructorDecodedImage := by
  exact Mem.Reads.write Mem.wf_empty Mem.reads_empty _ _

def officialConstructorArgumentWord : Fin 7 → B256
  | ⟨0, _⟩ => officialParams.admin
  | ⟨1, _⟩ => officialParams.minPauseDuration
  | ⟨2, _⟩ => officialParams.maxPauseDuration
  | ⟨3, _⟩ => officialParams.minHeartbeatInterval
  | ⟨4, _⟩ => officialParams.maxHeartbeatInterval
  | ⟨5, _⟩ => officialConstructorArgs.initialPauseDuration
  | ⟨6, _⟩ => officialConstructorArgs.initialHeartbeatInterval

theorem officialConstructorDecodedMemory_read_argument (i : Fin 7) :
    Bytes.toB256
        ((officialConstructorDecodedMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  rw [Mem.Reads.read officialConstructorDecodedMemory_reads]
  unfold officialConstructorDecodedImage
  rw [show Bytes.writeAt [] 0
      (abiEncodeConstructorArgs officialConstructorArgs) =
      abiEncodeConstructorArgs officialConstructorArgs by
    simp [Bytes.writeAt]]
  unfold abiEncodeConstructorArgs
  rcases i with ⟨i, hi⟩
  have hcases :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [List.sliceD_eq_map] <;>
    simp only [officialConstructorArgumentWord] <;> decide +kernel

/-! ## Exact memory expansion checkpoints -/

theorem officialConstructorDecodedMemory_size :
    officialConstructorDecodedMemory.size = 224 := by
  unfold officialConstructorDecodedMemory
  rcases hbytes : abiEncodeConstructorArgs officialConstructorArgs with _ | ⟨b, bs⟩
  · have hlen := abiEncodeConstructorArgs_length officialConstructorArgs
    rw [hbytes] at hlen
    simp [constructorArgumentBytes] at hlen
  · rw [Mem.size_write_cons]
    have hlen : (b :: bs).length = 224 := by
      rw [← hbytes, abiEncodeConstructorArgs_length]
      decide
    rw [hlen]
    decide

theorem officialConstructorDecodedMemory_read_memory (i : Fin 7) :
    (officialConstructorDecodedMemory.read (32 * i.val) 32).2 =
      officialConstructorDecodedMemory := by
  rw [Mem.read_snd_eq_self]
  apply memExtSize_of_le
  · rw [officialConstructorDecodedMemory_size]
  · rw [officialConstructorDecodedMemory_size]
    have hi := i.isLt
    omega

theorem officialConstructorCopiedMemory_size :
    officialConstructorCopiedMemory.size = 4512 := by
  unfold officialConstructorCopiedMemory
  rcases hbytes : runtimeTemplateCode with _ | ⟨b, bs⟩
  · have hlen := runtimeTemplateCode_length_exact
    rw [hbytes] at hlen
    simp at hlen
  · rw [Mem.size_write_cons]
    have hlen : (b :: bs).length = 4282 := by
      rw [← hbytes, runtimeTemplateCode_length_exact]
    rw [hlen, officialConstructorDecodedMemory_size]
    decide

private theorem officialConstructorDecodedMemory_wf :
    Mem.Wf officialConstructorDecodedMemory := by
  exact Mem.Wf.write Mem.wf_empty _ _

private theorem officialConstructorCopiedMemory_wf :
    Mem.Wf officialConstructorCopiedMemory := by
  exact Mem.Wf.write officialConstructorDecodedMemory_wf _ _

private theorem officialConstructorCopiedMemory_reads :
    Mem.Reads officialConstructorCopiedMemory officialConstructorCopiedImage := by
  exact Mem.Reads.write officialConstructorDecodedMemory_wf
    officialConstructorDecodedMemory_reads _ _

/-- The copied runtime and every in-bounds immutable patch preserve the decoded
seven-word constructor head. -/
structure ConstructorPatchInvariant (memory : Mem) : Type where
  image : Bytes
  memory_wf : Mem.Wf memory
  memory_reads : Mem.Reads memory image
  memory_size : memory.size = 4512
  argument_reads : ∀ i : Fin 7,
    Bytes.toB256 (image.sliceD (32 * i.val) 32 0) =
      officialConstructorArgumentWord i

def officialConstructorCopiedMemory_invariant :
    ConstructorPatchInvariant officialConstructorCopiedMemory := by
  refine ⟨officialConstructorCopiedImage,
    officialConstructorCopiedMemory_wf,
    officialConstructorCopiedMemory_reads,
    officialConstructorCopiedMemory_size, ?_⟩
  intro i
  unfold officialConstructorCopiedImage
  rw [Bytes.sliceD_writeAt_before officialConstructorDecodedImage
    runtimeTemplateCode (32 * i.val) 32 constructorRuntimeBase (by
      unfold constructorRuntimeBase constructorArgumentBytes
      have hi := i.isLt
      omega)]
  have h := officialConstructorDecodedMemory_read_argument i
  rw [Mem.Reads.read officialConstructorDecodedMemory_reads] at h
  exact h

def ConstructorPatchInvariant.write
    {memory : Mem} (h : ConstructorPatchInvariant memory)
    (offset : Nat) (value : B256)
    (hbefore : constructorArgumentBytes ≤ offset)
    (hfit : offset + 32 ≤ 4512) :
    ConstructorPatchInvariant (memory.write offset value.toBytes) := by
  refine ⟨Bytes.writeAt h.image offset value.toBytes,
    Mem.Wf.write h.memory_wf _ _,
    Mem.Reads.write h.memory_wf h.memory_reads _ _, ?_, ?_⟩
  · rw [Mem.size_write_of_le]
    · exact h.memory_size
    · rw [B256.length_toBytes, h.memory_size]
      exact hfit
  · intro i
    rw [Bytes.sliceD_writeAt_before h.image value.toBytes
      (32 * i.val) 32 offset (by
        have hi := i.isLt
        unfold constructorArgumentBytes at hbefore
        omega)]
    exact h.argument_reads i

theorem ConstructorPatchInvariant.read_argument
    {memory : Mem} (h : ConstructorPatchInvariant memory) (i : Fin 7) :
    Bytes.toB256 ((memory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  rw [Mem.Reads.read h.memory_reads]
  exact h.argument_reads i

theorem ConstructorPatchInvariant.read_memory
    {memory : Mem} (h : ConstructorPatchInvariant memory) (i : Fin 7) :
    (memory.read (32 * i.val) 32).2 = memory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [h.memory_size]
  · rw [h.memory_size]
    have hi := i.isLt
    omega

end LidoCircuitBreaker

end Blanc
