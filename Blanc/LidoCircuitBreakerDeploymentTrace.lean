-- LidoCircuitBreakerDeploymentTrace.lean : exact official constructor walk.
--
-- This owner starts from the compiler-derived layout certificate and names the
-- actual memory/log images traversed by the official successful constructor.
-- Later sections turn those images into a gas-exact `Prog.RunCompiled` walk
-- and then into Jaune execution against the appended runtime and ABI suffix.

import Blanc.LidoCircuitBreakerDeploymentLayout
import Blanc.ForwardCall

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-! ## Exact public constructor observations -/

/-- Exact address, topics, data, and source order of the three official
constructor logs. -/
def officialConstructorLogs (ca : Adr) : List Log :=
  [ ⟨ca, [circuitBreakerInitializedEvent, officialParams.admin],
      officialParams.minPauseDuration.toBytes ++
        officialParams.maxPauseDuration.toBytes ++
        officialParams.minHeartbeatInterval.toBytes ++
        officialParams.maxHeartbeatInterval.toBytes⟩,
    ⟨ca, [pauseDurationUpdatedEvent],
      (0 : B256).toBytes ++
        officialConstructorArgs.initialPauseDuration.toBytes⟩,
    ⟨ca, [heartbeatIntervalUpdatedEvent],
      (0 : B256).toBytes ++
        officialConstructorArgs.initialHeartbeatInterval.toBytes⟩ ]

/-! ## Constructor code-copy windows -/

/-- The constructor's first `CODECOPY` reads exactly the official seven-word
ABI head appended after the creation template. -/
theorem officialFullCreateInput_slice_constructorArgs {sevm : Sevm}
    (hcode : sevm.code.toList = officialFullCreateInput) :
    sevm.code.sliceD 4898 224 (Linst.toUInt8 .stop) =
      abiEncodeConstructorArgs officialConstructorArgs := by
  rw [ByteArray.sliceD_eq, hcode]
  unfold officialFullCreateInput lidoCircuitBreakerFullCreateInput
  unfold List.sliceD
  rw [show 4898 = lidoCircuitBreakerCreationTemplate.length from
    lidoCircuitBreakerCreationTemplate_length_exact.symm]
  rw [List.drop_left]
  rw [List.takeD_eq_take _ (by
    rw [abiEncodeConstructorArgs_length]
    decide)]
  rw [show 224 = (abiEncodeConstructorArgs officialConstructorArgs).length by
    rw [abiEncodeConstructorArgs_length]
    decide]
  exact List.take_length

/-- The constructor's second `CODECOPY` reads exactly the parameter-neutral
runtime window that follows its 616-byte compiled prefix. -/
theorem officialFullCreateInput_slice_runtimeTemplate {sevm : Sevm}
    (hcode : sevm.code.toList = officialFullCreateInput) :
    sevm.code.sliceD 616 4282 (Linst.toUInt8 .stop) =
      runtimeTemplateCode := by
  rw [ByteArray.sliceD_eq, hcode, officialFullCreateInput_eq_layout]
  unfold List.sliceD
  rw [show 616 = lidoCircuitBreakerInitPrefix.length from
    lidoCircuitBreakerInitPrefix_length_exact.symm]
  rw [List.append_assoc]
  rw [List.drop_left]
  rw [List.takeD_eq_take _ (by
    simp [runtimeTemplateCode_length_exact])]
  rw [show 4282 = runtimeTemplateCode.length from
    runtimeTemplateCode_length_exact.symm]
  exact List.take_append_length

/-! ## Body-pinned successful effect arm -/

/-- The exact residual constructor body after all ten successful validation
branches have placed the runtime-copy operands on the stack. -/
def officialConstructorEffectBody : Func :=
  codecopy :::
    patchRuntimeLine constructorRuntimeBase +++
    loadArgumentIndex 0 +++
    pushB256 circuitBreakerInitializedEvent :::
    logWith 1 1 4 +++
    pushB256 0 :::
    storeByteOffset (constructorEventScratch 4282) +++
    loadArgumentIndex 5 +++
    storeByteOffset (constructorEventScratch 4282 + 32) +++
    pushB256 pauseDurationUpdatedEvent :::
    logWith 0
      (Nat.toB256 (constructorEventScratch 4282 / 32)) 2 +++
    loadArgumentIndex 5 +++
    pushB256 pauseDurationSlot ::: sstore :::
    pushB256 0 :::
    storeByteOffset (constructorEventScratch 4282) +++
    loadArgumentIndex 6 +++
    storeByteOffset (constructorEventScratch 4282 + 32) +++
    pushB256 heartbeatIntervalUpdatedEvent :::
    logWith 0
      (Nat.toB256 (constructorEventScratch 4282 / 32)) 2 +++
    loadArgumentIndex 6 +++
    pushB256 heartbeatIntervalSlot ::: sstore :::
    pushFixedNat 4282 :::
    pushCompactNat constructorRuntimeBase :::
    Func.ret

/-- The exact official length, decode, canonical-address, and nine validation
tree, ending at `officialConstructorEffectBody`. Its branches retain every
skipped error-arm call at the source position compiled by the constructor. -/
def officialConstructorValidationBody : Func :=
  pushFixedNat 5122 ::: codesize ::: lt :::
  ((.call 1) <?>
    (pushCompactNat 224 ::: pushFixedNat 4898 ::: pushCompactNat 0 :::
      codecopy :::
      loadArgumentIndex 0 +++ checkNonAddress +++
      ((.call 1) <?>
        (loadArgumentIndex 0 +++ iszero :::
          ((.call 2) <?>
            (loadArgumentIndex 1 +++ iszero :::
              ((.call 3) <?>
                (loadArgumentIndex 2 +++
                  loadArgumentIndex 1 +++ gt :::
                  ((.call 4) <?>
                    (loadArgumentIndex 3 +++ iszero :::
                      ((.call 5) <?>
                        (loadArgumentIndex 4 +++
                          loadArgumentIndex 3 +++ gt :::
                          ((.call 6) <?>
                            (loadArgumentIndex 1 +++
                              loadArgumentIndex 5 +++ lt :::
                              ((.call 7) <?>
                                (loadArgumentIndex 2 +++
                                  loadArgumentIndex 5 +++ gt :::
                                  ((.call 8) <?>
                                    (loadArgumentIndex 3 +++
                                      loadArgumentIndex 6 +++ lt :::
                                      ((.call 9) <?>
                                        (loadArgumentIndex 4 +++
                                          loadArgumentIndex 6 +++ gt :::
                                          ((.call 10) <?>
                                            (pushFixedNat 4282 :::
                                              pushFixedNat 616 :::
                                              pushCompactNat
                                                constructorRuntimeBase :::
                                              officialConstructorEffectBody
                                            ))))))))))))))))))))))

/-- The body-pinned official validation/effect presentation is definitionally
the constructor source specialized to its certified 616/4,898/4,282 layout. -/
theorem constructorBody_official_eq :
    constructorBody 616 4898 4282 = officialConstructorValidationBody := by
  rfl

/-- The exact main function joins the nonpayable guard to the body-pinned
official validation tree; its untaken arm is the first `.call 1` site. -/
theorem lidoCircuitBreakerConstructorProgram_main_official :
    lidoCircuitBreakerConstructorProgram.main =
      callvalue ::: iszero :::
        (officialConstructorValidationBody <?> (.call 1)) := by
  unfold lidoCircuitBreakerConstructorProgram constructorProgram
  rw [provisionalConstructorPrefix_length_exact,
    runtimeTemplateCode_length_exact]
  change callvalue ::: iszero :::
    (constructorBody 616 4898 4282 <?> (.call 1)) = _
  rw [constructorBody_official_eq]

/-! ## Named official memory images -/

def officialConstructorDecodedMemory : Mem :=
  Mem.empty.write 0 (abiEncodeConstructorArgs officialConstructorArgs)

def officialConstructorCopiedMemory : Mem :=
  officialConstructorDecodedMemory.write constructorRuntimeBase
    runtimeTemplateCode

private def applyConstructorMemoryPatch
    (memory : Mem) (patch : ImmutablePatch) : Mem :=
  memory.write (constructorRuntimeBase + patch.offset) patch.value.toBytes

private def applyConstructorImagePatch
    (image : Bytes) (patch : ImmutablePatch) : Bytes :=
  Bytes.writeAt image (constructorRuntimeBase + patch.offset)
    patch.value.toBytes

/-- Memory after the constructor's twelve source-ordered immutable writes. -/
def officialConstructorPatchedMemory : Mem :=
  (runtimeImmutablePatches officialParams).foldl
    applyConstructorMemoryPatch officialConstructorCopiedMemory

private def officialConstructorDecodedImage : Bytes :=
  Bytes.writeAt [] 0 (abiEncodeConstructorArgs officialConstructorArgs)

private def officialConstructorCopiedImage : Bytes :=
  Bytes.writeAt officialConstructorDecodedImage constructorRuntimeBase
    runtimeTemplateCode

private def officialConstructorPatchedImage : Bytes :=
  (runtimeImmutablePatches officialParams).foldl
    applyConstructorImagePatch officialConstructorCopiedImage

/-- Final constructor memory after the two event-scratch words have been
rewritten for the last event. -/
def officialConstructorFinalMemory : Mem :=
  let eventScratch := constructorEventScratch 4282
  let pauseMemory :=
    (officialConstructorPatchedMemory.write eventScratch (0 : B256).toBytes).write
      (eventScratch + 32)
      officialConstructorArgs.initialPauseDuration.toBytes
  (pauseMemory.write eventScratch (0 : B256).toBytes).write
    (eventScratch + 32)
    officialConstructorArgs.initialHeartbeatInterval.toBytes

private def officialConstructorFinalImage : Bytes :=
  let eventScratch := constructorEventScratch 4282
  let pauseImage :=
    (Bytes.writeAt officialConstructorPatchedImage eventScratch
      (0 : B256).toBytes)
      |> fun image => Bytes.writeAt image (eventScratch + 32)
        officialConstructorArgs.initialPauseDuration.toBytes
  (Bytes.writeAt pauseImage eventScratch (0 : B256).toBytes)
    |> fun image => Bytes.writeAt image (eventScratch + 32)
      officialConstructorArgs.initialHeartbeatInterval.toBytes

private theorem officialConstructorDecodedMemory_reads :
    Mem.Reads officialConstructorDecodedMemory
      officialConstructorDecodedImage := by
  exact Mem.Reads.write Mem.wf_empty Mem.reads_empty _ _

private def officialConstructorArgumentWord : Fin 7 → B256
  | ⟨0, _⟩ => officialParams.admin
  | ⟨1, _⟩ => officialParams.minPauseDuration
  | ⟨2, _⟩ => officialParams.maxPauseDuration
  | ⟨3, _⟩ => officialParams.minHeartbeatInterval
  | ⟨4, _⟩ => officialParams.maxHeartbeatInterval
  | ⟨5, _⟩ => officialConstructorArgs.initialPauseDuration
  | ⟨6, _⟩ => officialConstructorArgs.initialHeartbeatInterval

private theorem officialConstructorDecodedMemory_read_argument (i : Fin 7) :
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

private theorem officialConstructorDecodedMemory_size :
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

private theorem officialConstructorDecodedMemory_read_memory (i : Fin 7) :
    (officialConstructorDecodedMemory.read (32 * i.val) 32).2 =
      officialConstructorDecodedMemory := by
  rw [Mem.read_snd_eq_self]
  apply memExtSize_of_le
  · rw [officialConstructorDecodedMemory_size]
  · rw [officialConstructorDecodedMemory_size]
    have hi := i.isLt
    omega

private theorem officialConstructorCopiedMemory_size :
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
private structure ConstructorPatchInvariant (memory : Mem) : Type where
  image : Bytes
  memory_wf : Mem.Wf memory
  memory_reads : Mem.Reads memory image
  memory_size : memory.size = 4512
  argument_reads : ∀ i : Fin 7,
    Bytes.toB256 (image.sliceD (32 * i.val) 32 0) =
      officialConstructorArgumentWord i

private def officialConstructorCopiedMemory_invariant :
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

private def ConstructorPatchInvariant.write
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

private theorem ConstructorPatchInvariant.read_argument
    {memory : Mem} (h : ConstructorPatchInvariant memory) (i : Fin 7) :
    Bytes.toB256 ((memory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  rw [Mem.Reads.read h.memory_reads]
  exact h.argument_reads i

private theorem ConstructorPatchInvariant.read_memory
    {memory : Mem} (h : ConstructorPatchInvariant memory) (i : Fin 7) :
    (memory.read (32 * i.val) 32).2 = memory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [h.memory_size]
  · rw [h.memory_size]
    have hi := i.isLt
    omega

private theorem constructorPatchPair_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {M M' : Mem} {i : Fin 7} {offset pushGas G : Nat}
    {value : B256} {rest : Func}
    (hoffset : offset < 2 ^ 16)
    (hpush : pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = pushGas)
    (hsize : M.size = 4512)
    (hfit : offset + 32 ≤ 4512)
    (hargument : Bytes.toB256 ((M.read (32 * i.val) 32).1) = value)
    (hargumentMemory : (M.read (32 * i.val) 32).2 = M)
    (hwrite : M.write offset value.toBytes = M')
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M', G⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + (pushGas + 9)⟩)
      (loadArgumentIndex i.val +++ storeByteOffset offset +++ rest) post := by
  have hindexBound : 32 * i.val < 2 ^ 256 := by
    apply Nat.lt_trans (show 32 * i.val < 224 by
      have hi := i.isLt
      omega)
    decide
  have hindex : (Nat.toB256 (32 * i.val)).toNat = 32 * i.val :=
    B256.toNat_toB256_of_lt hindexBound
  have hoffsetBound : offset < 2 ^ 256 := by
    apply Nat.lt_trans hoffset
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  have hoffsetNat : (Nat.toB256 offset).toNat = offset :=
    B256.toNat_toB256_of_lt hoffsetBound
  unfold loadArgumentIndex storeByteOffset pushCompactNat pushFixedNat
  simp only [if_pos hoffset]
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := pushGas) (G := G + 9) hpush
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · func_run (3) [3, 0]
    all_goals try rw [List.toB256_pair offset hoffset, hoffsetNat]
    case h_cost =>
      simp only [Devm.memory_setMach, Devm.stack_setMach, hindex]
      rw [Devm.extCost_zero_of_le (N := M) (i := 32 * i.val) (sz := 32)
        (by rw [hsize]) (by
          rw [hsize]
          have hi := i.isLt
          omega)]
      rfl
    case h_ext =>
      simp only [Devm.memory_setMach, Devm.stack_setMach, hindex,
        hargumentMemory]
      exact Devm.extCost_zero_of_le (N := M) (i := offset) (sz := 32)
        (by rw [hsize]) (by rw [hsize]; exact hfit)
    case a =>
      simp only [Devm.memory_setMach, Devm.stack_setMach, hindex,
        hargumentMemory, hargument, Devm.setMach_setMach]
      rw [hwrite]
      have hg : G + 9 - 9 = G := by omega
      rw [hg]
      exact hrest

private theorem ConstructorPatchInvariant.runCompiled_write
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {i : Fin 7} {offset pushGas G : Nat}
    {value : B256} {rest : Func}
    (h : ConstructorPatchInvariant memory)
    (hoffset : offset < 2 ^ 16)
    (hpush : pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = pushGas)
    (hvalue : officialConstructorArgumentWord i = value)
    (hfit : offset + 32 ≤ 4512)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory.write offset value.toBytes, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + (pushGas + 9)⟩)
      (loadArgumentIndex i.val +++ storeByteOffset offset +++ rest) post := by
  apply constructorPatchPair_runCompiled hoffset hpush h.memory_size hfit
  · rw [h.read_argument i, hvalue]
  · exact h.read_memory i
  · rfl
  · exact hrest

private def officialConstructorPatchMemory1 : Mem :=
  officialConstructorCopiedMemory.write 398 officialParams.admin.toBytes

private def officialConstructorPatchMemory2 : Mem :=
  officialConstructorPatchMemory1.write 1318 officialParams.admin.toBytes

private def officialConstructorPatchMemory3 : Mem :=
  officialConstructorPatchMemory2.write 2057 officialParams.admin.toBytes

private def officialConstructorPatchMemory4 : Mem :=
  officialConstructorPatchMemory3.write 2144 officialParams.admin.toBytes

private def officialConstructorPatchMemory5 : Mem :=
  officialConstructorPatchMemory4.write 441
    officialParams.minPauseDuration.toBytes

private def officialConstructorPatchMemory6 : Mem :=
  officialConstructorPatchMemory5.write 937
    officialParams.minPauseDuration.toBytes

private def officialConstructorPatchMemory7 : Mem :=
  officialConstructorPatchMemory6.write 482
    officialParams.maxPauseDuration.toBytes

private def officialConstructorPatchMemory8 : Mem :=
  officialConstructorPatchMemory7.write 2185
    officialParams.maxPauseDuration.toBytes

private def officialConstructorPatchMemory9 : Mem :=
  officialConstructorPatchMemory8.write 732
    officialParams.minHeartbeatInterval.toBytes

private def officialConstructorPatchMemory10 : Mem :=
  officialConstructorPatchMemory9.write 1361
    officialParams.minHeartbeatInterval.toBytes

private def officialConstructorPatchMemory11 : Mem :=
  officialConstructorPatchMemory10.write 896
    officialParams.maxHeartbeatInterval.toBytes

private def officialConstructorPatchMemory12 : Mem :=
  officialConstructorPatchMemory11.write 1402
    officialParams.maxHeartbeatInterval.toBytes

private def officialConstructorPatchInvariant1 :
    ConstructorPatchInvariant officialConstructorPatchMemory1 :=
  officialConstructorCopiedMemory_invariant.write 398 officialParams.admin
    (by decide) (by decide)

private def officialConstructorPatchInvariant2 :
    ConstructorPatchInvariant officialConstructorPatchMemory2 :=
  officialConstructorPatchInvariant1.write 1318 officialParams.admin
    (by decide) (by decide)

private def officialConstructorPatchInvariant3 :
    ConstructorPatchInvariant officialConstructorPatchMemory3 :=
  officialConstructorPatchInvariant2.write 2057 officialParams.admin
    (by decide) (by decide)

private def officialConstructorPatchInvariant4 :
    ConstructorPatchInvariant officialConstructorPatchMemory4 :=
  officialConstructorPatchInvariant3.write 2144 officialParams.admin
    (by decide) (by decide)

private def officialConstructorPatchInvariant5 :
    ConstructorPatchInvariant officialConstructorPatchMemory5 :=
  officialConstructorPatchInvariant4.write 441
    officialParams.minPauseDuration (by decide) (by decide)

private def officialConstructorPatchInvariant6 :
    ConstructorPatchInvariant officialConstructorPatchMemory6 :=
  officialConstructorPatchInvariant5.write 937
    officialParams.minPauseDuration (by decide) (by decide)

private def officialConstructorPatchInvariant7 :
    ConstructorPatchInvariant officialConstructorPatchMemory7 :=
  officialConstructorPatchInvariant6.write 482
    officialParams.maxPauseDuration (by decide) (by decide)

private def officialConstructorPatchInvariant8 :
    ConstructorPatchInvariant officialConstructorPatchMemory8 :=
  officialConstructorPatchInvariant7.write 2185
    officialParams.maxPauseDuration (by decide) (by decide)

private def officialConstructorPatchInvariant9 :
    ConstructorPatchInvariant officialConstructorPatchMemory9 :=
  officialConstructorPatchInvariant8.write 732
    officialParams.minHeartbeatInterval (by decide) (by decide)

private def officialConstructorPatchInvariant10 :
    ConstructorPatchInvariant officialConstructorPatchMemory10 :=
  officialConstructorPatchInvariant9.write 1361
    officialParams.minHeartbeatInterval (by decide) (by decide)

private def officialConstructorPatchInvariant11 :
    ConstructorPatchInvariant officialConstructorPatchMemory11 :=
  officialConstructorPatchInvariant10.write 896
    officialParams.maxHeartbeatInterval (by decide) (by decide)

private def officialConstructorPatchInvariant12 :
    ConstructorPatchInvariant officialConstructorPatchMemory12 :=
  officialConstructorPatchInvariant11.write 1402
    officialParams.maxHeartbeatInterval (by decide) (by decide)

private theorem officialConstructorPatchMemory12_eq_patched :
    officialConstructorPatchMemory12 = officialConstructorPatchedMemory := by
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [officialConstructorPatchMemory12,
    officialConstructorPatchMemory11, officialConstructorPatchMemory10,
    officialConstructorPatchMemory9, officialConstructorPatchMemory8,
    officialConstructorPatchMemory7, officialConstructorPatchMemory6,
    officialConstructorPatchMemory5, officialConstructorPatchMemory4,
    officialConstructorPatchMemory3, officialConstructorPatchMemory2,
    officialConstructorPatchMemory1, officialConstructorPatchedMemory,
    runtimeImmutablePatches, immutableParameters, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, hadmin, hminPause,
    hmaxPause, hminHeartbeat, hmaxHeartbeat, applyConstructorMemoryPatch,
    ImmutableParameter.value]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
    applyConstructorMemoryPatch, constructorArgumentBytes,
    constructorRuntimeBase]

private def officialConstructorPatchLine : Line :=
  loadArgumentIndex 0 ++ storeByteOffset 398 ++
  loadArgumentIndex 0 ++ storeByteOffset 1318 ++
  loadArgumentIndex 0 ++ storeByteOffset 2057 ++
  loadArgumentIndex 0 ++ storeByteOffset 2144 ++
  loadArgumentIndex 1 ++ storeByteOffset 441 ++
  loadArgumentIndex 1 ++ storeByteOffset 937 ++
  loadArgumentIndex 2 ++ storeByteOffset 482 ++
  loadArgumentIndex 2 ++ storeByteOffset 2185 ++
  loadArgumentIndex 3 ++ storeByteOffset 732 ++
  loadArgumentIndex 3 ++ storeByteOffset 1361 ++
  loadArgumentIndex 4 ++ storeByteOffset 896 ++
  loadArgumentIndex 4 ++ storeByteOffset 1402

private theorem patchRuntimeLine_official_eq :
    patchRuntimeLine constructorRuntimeBase =
      officialConstructorPatchLine := by
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [patchRuntimeLine, patchFieldLine, immutableParameters,
    List.flatMap_cons, List.flatMap_nil, hadmin, hminPause, hmaxPause,
    hminHeartbeat, hmaxHeartbeat, patchArgumentIndex,
    officialConstructorPatchLine, constructorRuntimeBase,
    constructorArgumentBytes, List.nil_append, List.append_nil,
    List.append_assoc]

private theorem officialConstructorPatchLine9_12_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory12, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory8, G + 48⟩)
      (loadArgumentIndex 3 +++ storeByteOffset 732 +++
        loadArgumentIndex 3 +++ storeByteOffset 1361 +++
        loadArgumentIndex 4 +++ storeByteOffset 896 +++
        loadArgumentIndex 4 +++ storeByteOffset 1402 +++ rest) post := by
  have h12 := officialConstructorPatchInvariant11.runCompiled_write
    (i := ⟨4, by decide⟩) (offset := 1402) (pushGas := 3)
    (G := G) (value := officialParams.maxHeartbeatInterval)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory12] using hrest)
  have h11 := officialConstructorPatchInvariant10.runCompiled_write
    (i := ⟨4, by decide⟩) (offset := 896) (pushGas := 3)
    (G := G + 12) (value := officialParams.maxHeartbeatInterval)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory11] using h12)
  have h10 := officialConstructorPatchInvariant9.runCompiled_write
    (i := ⟨3, by decide⟩) (offset := 1361) (pushGas := 3)
    (G := G + 24) (value := officialParams.minHeartbeatInterval)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory10] using h11)
  have h9 := officialConstructorPatchInvariant8.runCompiled_write
    (i := ⟨3, by decide⟩) (offset := 732) (pushGas := 3)
    (G := G + 36) (value := officialParams.minHeartbeatInterval)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory9] using h10)
  exact h9

private theorem officialConstructorPatchLine5_8_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory8, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory4, G + 48⟩)
      (loadArgumentIndex 1 +++ storeByteOffset 441 +++
        loadArgumentIndex 1 +++ storeByteOffset 937 +++
        loadArgumentIndex 2 +++ storeByteOffset 482 +++
        loadArgumentIndex 2 +++ storeByteOffset 2185 +++ rest) post := by
  have h8 := officialConstructorPatchInvariant7.runCompiled_write
    (i := ⟨2, by decide⟩) (offset := 2185) (pushGas := 3)
    (G := G) (value := officialParams.maxPauseDuration)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory8] using hrest)
  have h7 := officialConstructorPatchInvariant6.runCompiled_write
    (i := ⟨2, by decide⟩) (offset := 482) (pushGas := 3)
    (G := G + 12) (value := officialParams.maxPauseDuration)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory7] using h8)
  have h6 := officialConstructorPatchInvariant5.runCompiled_write
    (i := ⟨1, by decide⟩) (offset := 937) (pushGas := 3)
    (G := G + 24) (value := officialParams.minPauseDuration)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory6] using h7)
  have h5 := officialConstructorPatchInvariant4.runCompiled_write
    (i := ⟨1, by decide⟩) (offset := 441) (pushGas := 3)
    (G := G + 36) (value := officialParams.minPauseDuration)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory5] using h6)
  exact h5

private theorem officialConstructorPatchLine1_4_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory4, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorCopiedMemory, G + 44⟩)
      (loadArgumentIndex 0 +++ storeByteOffset 398 +++
        loadArgumentIndex 0 +++ storeByteOffset 1318 +++
        loadArgumentIndex 0 +++ storeByteOffset 2057 +++
        loadArgumentIndex 0 +++ storeByteOffset 2144 +++ rest) post := by
  have h4 := officialConstructorPatchInvariant3.runCompiled_write
    (i := ⟨0, by decide⟩) (offset := 2144) (pushGas := 2)
    (G := G) (value := officialParams.admin)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory4] using hrest)
  have h3 := officialConstructorPatchInvariant2.runCompiled_write
    (i := ⟨0, by decide⟩) (offset := 2057) (pushGas := 2)
    (G := G + 11) (value := officialParams.admin)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory3] using h4)
  have h2 := officialConstructorPatchInvariant1.runCompiled_write
    (i := ⟨0, by decide⟩) (offset := 1318) (pushGas := 2)
    (G := G + 22) (value := officialParams.admin)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory2] using h3)
  have h1 := officialConstructorCopiedMemory_invariant.runCompiled_write
    (i := ⟨0, by decide⟩) (offset := 398) (pushGas := 2)
    (G := G + 33) (value := officialParams.admin)
    (by decide) (by decide +kernel) rfl (by decide) (by
      simpa only [officialConstructorPatchMemory1] using h2)
  exact h1

private theorem officialConstructorPatchLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorCopiedMemory, G + 140⟩)
      (officialConstructorPatchLine +++ rest) post := by
  have hrest12 : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory12, G⟩)
      rest post := by
    rw [officialConstructorPatchMemory12_eq_patched]
    exact hrest
  have h9 := officialConstructorPatchLine9_12_runCompiled hrest12
  have h5 := officialConstructorPatchLine5_8_runCompiled (G := G + 48) h9
  have h1 := officialConstructorPatchLine1_4_runCompiled (G := G + 96) h5
  simpa only [officialConstructorPatchLine, prepend_append] using h1

private theorem officialConstructorCopyPatch_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, G + 985⟩)
      (codecopy ::: patchRuntimeLine constructorRuntimeBase +++ rest) post := by
  have hpatch := officialConstructorPatchLine_runCompiled hrest
  refine Func.RunCompiled.next
    (devm' := base.setMach
      ⟨[], officialConstructorCopiedMemory, G + 140⟩) ?_ ?_
  · have hstep := Ninst.runCompiled_codecopy_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, G + 985⟩)
      (di := (224 : B256)) (si := (616 : B256)) (sz := (4282 : B256))
      (s := []) (c := 845) (G := G + 140)
      (M := officialConstructorCopiedMemory)
      (by simp only [Devm.stack_setMach])
      (by
        simp only [show (224 : B256).toNat = 224 by decide,
          show (4282 : B256).toNat = 4282 by decide]
        exact Devm.extCost_add_of_size
          (a := gVerylow + gasCopy * ceilDiv 4282 32)
          officialConstructorDecodedMemory_size (by decide))
      (by
        simp only [Devm.memory_setMach,
          show (224 : B256).toNat = 224 by decide,
          show (616 : B256).toNat = 616 by decide,
          show (4282 : B256).toNat = 4282 by decide]
        rw [officialFullCreateInput_slice_runtimeTemplate hcode]
        rfl)
      (by simp only [Devm.gasLeft_setMach])
    simpa only [Devm.setMach_setMach] using hstep
  · rw [patchRuntimeLine_official_eq]
    exact hpatch

private theorem officialConstructorPatches_fit :
    ∀ patch ∈ runtimeImmutablePatches officialParams,
      constructorRuntimeBase + patch.offset + 32 ≤ 4512 := by
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [runtimeImmutablePatches, immutableParameters,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat,
    constructorRuntimeBase, constructorArgumentBytes]
  simp_all

private theorem constructorPatchFold_size_of_le
    (patches : List ImmutablePatch) (memory : Mem)
    (hsize : memory.size = 4512)
    (hfit : ∀ patch ∈ patches,
      constructorRuntimeBase + patch.offset + 32 ≤ 4512) :
    (patches.foldl applyConstructorMemoryPatch memory).size = 4512 := by
  induction patches generalizing memory with
  | nil => exact hsize
  | cons patch patches ih =>
      simp only [List.foldl_cons]
      apply ih
      · unfold applyConstructorMemoryPatch
        rw [Mem.size_write_of_le]
        · exact hsize
        · rw [B256.length_toBytes, hsize]
          exact hfit patch (by simp)
      · intro next hnext
        exact hfit next (by simp [hnext])

private theorem officialConstructorPatchedMemory_size :
    officialConstructorPatchedMemory.size = 4512 := by
  unfold officialConstructorPatchedMemory
  exact constructorPatchFold_size_of_le _ _
    officialConstructorCopiedMemory_size officialConstructorPatches_fit

/-- The constructor's final two-word event scratch expands memory from 4,512
to exactly 4,576 bytes. -/
theorem officialConstructorFinalMemory_size :
    officialConstructorFinalMemory.size = 4576 := by
  unfold officialConstructorFinalMemory
  rw [Mem.size_write_word_at, Mem.size_write_word_at,
    Mem.size_write_word_at, Mem.size_write_word_at,
    officialConstructorPatchedMemory_size]
  decide

/-! ## Memory/image correspondence -/

private theorem constructorPatchFold_wf
    (patches : List ImmutablePatch) (memory : Mem)
    (hwf : Mem.Wf memory) :
    Mem.Wf (patches.foldl applyConstructorMemoryPatch memory) := by
  induction patches generalizing memory with
  | nil => exact hwf
  | cons patch patches ih =>
      simp only [List.foldl_cons]
      apply ih
      unfold applyConstructorMemoryPatch
      exact Mem.Wf.write hwf _ _

private theorem constructorPatchFold_reads
    (patches : List ImmutablePatch) (memory : Mem) (image : Bytes)
    (hwf : Mem.Wf memory) (hreads : Mem.Reads memory image) :
    Mem.Reads (patches.foldl applyConstructorMemoryPatch memory)
      (patches.foldl applyConstructorImagePatch image) := by
  induction patches generalizing memory image with
  | nil => exact hreads
  | cons patch patches ih =>
      simp only [List.foldl_cons]
      apply ih
      · unfold applyConstructorMemoryPatch
        exact Mem.Wf.write hwf _ _
      · unfold applyConstructorMemoryPatch applyConstructorImagePatch
        exact Mem.Reads.write hwf hreads _ _

private theorem officialConstructorPatchedMemory_wf :
    Mem.Wf officialConstructorPatchedMemory := by
  have hwfDecoded : Mem.Wf officialConstructorDecodedMemory := by
    exact Mem.Wf.write Mem.wf_empty _ _
  have hwfCopied : Mem.Wf officialConstructorCopiedMemory := by
    exact Mem.Wf.write hwfDecoded _ _
  exact constructorPatchFold_wf _ _ hwfCopied

private theorem officialConstructorPatchedMemory_reads :
    Mem.Reads officialConstructorPatchedMemory
      officialConstructorPatchedImage := by
  have hwfDecoded : Mem.Wf officialConstructorDecodedMemory := by
    exact Mem.Wf.write Mem.wf_empty _ _
  have hreadsDecoded : Mem.Reads officialConstructorDecodedMemory
      officialConstructorDecodedImage := by
    exact Mem.Reads.write Mem.wf_empty Mem.reads_empty _ _
  have hreadsCopied : Mem.Reads officialConstructorCopiedMemory
      officialConstructorCopiedImage := by
    exact Mem.Reads.write hwfDecoded hreadsDecoded _ _
  exact constructorPatchFold_reads _ _ _
    (Mem.Wf.write hwfDecoded _ _) hreadsCopied

private theorem officialConstructorFinalMemory_reads :
    Mem.Reads officialConstructorFinalMemory officialConstructorFinalImage := by
  let eventScratch := constructorEventScratch 4282
  let M0 := officialConstructorPatchedMemory
  let I0 := officialConstructorPatchedImage
  let M1 := M0.write eventScratch (0 : B256).toBytes
  let I1 := Bytes.writeAt I0 eventScratch (0 : B256).toBytes
  let M2 := M1.write (eventScratch + 32)
    officialConstructorArgs.initialPauseDuration.toBytes
  let I2 := Bytes.writeAt I1 (eventScratch + 32)
    officialConstructorArgs.initialPauseDuration.toBytes
  let M3 := M2.write eventScratch (0 : B256).toBytes
  let I3 := Bytes.writeAt I2 eventScratch (0 : B256).toBytes
  have hwf0 : Mem.Wf M0 := officialConstructorPatchedMemory_wf
  have hreads0 : Mem.Reads M0 I0 := officialConstructorPatchedMemory_reads
  have hwf1 : Mem.Wf M1 := Mem.Wf.write hwf0 _ _
  have hreads1 : Mem.Reads M1 I1 := Mem.Reads.write hwf0 hreads0 _ _
  have hwf2 : Mem.Wf M2 := Mem.Wf.write hwf1 _ _
  have hreads2 : Mem.Reads M2 I2 := Mem.Reads.write hwf1 hreads1 _ _
  have hwf3 : Mem.Wf M3 := Mem.Wf.write hwf2 _ _
  have hreads3 : Mem.Reads M3 I3 := Mem.Reads.write hwf2 hreads2 _ _
  have hreads4 := Mem.Reads.write hwf3 hreads3 (eventScratch + 32)
    officialConstructorArgs.initialHeartbeatInterval.toBytes
  simpa [officialConstructorFinalMemory, officialConstructorFinalImage,
    eventScratch, M0, I0, M1, I1, M2, I2, M3, I3] using hreads4

set_option maxHeartbeats 3000000 in
private theorem officialConstructorFinalImage_runtime :
    officialConstructorFinalImage.sliceD constructorRuntimeBase 4282 0 =
      lidoCircuitBreakerCode officialParams := by
  rw [← patchRuntimeTemplate_official]
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [officialConstructorFinalImage, officialConstructorPatchedImage,
    officialConstructorCopiedImage, officialConstructorDecodedImage,
    patchRuntimeTemplate, runtimeImmutablePatches, immutableParameters,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat,
    ImmutableParameter.value, constructorEventScratch, constructorRuntimeBase]
  decide +kernel

/-- The final `RETURN` window reads the exact official runtime artifact. -/
theorem officialConstructorFinalMemory_read_runtime :
    (officialConstructorFinalMemory.read constructorRuntimeBase 4282).1 =
      lidoCircuitBreakerCode officialParams := by
  rw [Mem.Reads.read officialConstructorFinalMemory_reads]
  exact officialConstructorFinalImage_runtime

/-! ## Gas-exact validation prefix -/

set_option maxRecDepth 16384 in
private theorem officialConstructorValidationPrefix_runCompiled
    {sevm : Sevm} {base post : Devm} {g : Nat}
    (hvalue : sevm.value = 0)
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hgas : 367 ≤ g)
    (hrest : Func.RunCompiled
      (lidoCircuitBreakerConstructorProgram.main ::
        lidoCircuitBreakerConstructorProgram.aux)
      sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, g - 367⟩)
      officialConstructorEffectBody post) :
    Func.RunCompiled
      (lidoCircuitBreakerConstructorProgram.main ::
        lidoCircuitBreakerConstructorProgram.aux)
      sevm (base.setMach ⟨[], Mem.empty, g⟩)
      lidoCircuitBreakerConstructorProgram.main post := by
  have hcodeSize : sevm.code.size = 5122 := by
    rw [ByteArray.size_eq_length_toList, hcode,
      officialFullCreateInput_length_exact]
  have hv0 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 0 32).1) =
      officialParams.admin := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨0, by decide⟩
  have hv1 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 32 32).1) =
      officialParams.minPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨1, by decide⟩
  have hv2 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 64 32).1) =
      officialParams.maxPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨2, by decide⟩
  have hv3 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 96 32).1) =
      officialParams.minHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨3, by decide⟩
  have hv4 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 128 32).1) =
      officialParams.maxHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨4, by decide⟩
  have hv5 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨5, by decide⟩
  have hv6 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨6, by decide⟩
  have hm0 : (officialConstructorDecodedMemory.read 0 32).2 =
      officialConstructorDecodedMemory := by
    simpa using
      officialConstructorDecodedMemory_read_memory ⟨0, by decide⟩
  have hm1 : (officialConstructorDecodedMemory.read 32 32).2 =
      officialConstructorDecodedMemory := by
    simpa using
      officialConstructorDecodedMemory_read_memory ⟨1, by decide⟩
  have hm2 : (officialConstructorDecodedMemory.read 64 32).2 =
      officialConstructorDecodedMemory := by
    simpa using
      officialConstructorDecodedMemory_read_memory ⟨2, by decide⟩
  have hm3 : (officialConstructorDecodedMemory.read 96 32).2 =
      officialConstructorDecodedMemory := by
    simpa using
      officialConstructorDecodedMemory_read_memory ⟨3, by decide⟩
  have hm4 : (officialConstructorDecodedMemory.read 128 32).2 =
      officialConstructorDecodedMemory := by
    simpa using
      officialConstructorDecodedMemory_read_memory ⟨4, by decide⟩
  have hm5 : (officialConstructorDecodedMemory.read 160 32).2 =
      officialConstructorDecodedMemory := by
    simpa using
      officialConstructorDecodedMemory_read_memory ⟨5, by decide⟩
  have hm6 : (officialConstructorDecodedMemory.read 192 32).2 =
      officialConstructorDecodedMemory := by
    simpa using
      officialConstructorDecodedMemory_read_memory ⟨6, by decide⟩
  rw [lidoCircuitBreakerConstructorProgram_main_official]
  unfold officialConstructorValidationBody
  simp only [pushFixedNat,
    if_pos (show 5122 < 2 ^ 16 by decide),
    if_pos (show 4898 < 2 ^ 16 by decide),
    if_pos (show 4282 < 2 ^ 16 by decide),
    if_pos (show 616 < 2 ^ 16 by decide)]
  unfold loadArgumentIndex pushCompactNat checkNonAddress pushAddressMask
  func_run (11) [1, 0, 45]
  all_goals try rfl
  all_goals try simp [B256.eqCheck, hvalue]
  all_goals try simp_rw [hcodeSize]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 224 32) rfl (by decide)
  all_goals try decide +kernel
  all_goals try omega
  simp only [show (Nat.toB256 0).toNat = 0 by decide,
    show (Bytes.toB256 [19, 34]).toNat = 4898 by decide,
    show (Nat.toB256 224).toNat = 224 by decide]
  have hslice : sevm.code.sliceD 4898 224 (0 : UInt8) =
      abiEncodeConstructorArgs officialConstructorArgs := by
    rw [show (0 : UInt8) = Linst.toUInt8 .stop by decide]
    exact officialFullCreateInput_slice_constructorArgs hcode
  rw [hslice]
  have hdecoded :
      Mem.empty.write 0 (abiEncodeConstructorArgs officialConstructorArgs) =
        officialConstructorDecodedMemory := by
    rfl
  rw [hdecoded]
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 0).toNat = 0 by decide]
  all_goals try simp_rw [hm0, hv0]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm0, hv0]
  func_run (6) [~~~(0 : B256), addressMask, 0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 0).toNat = 0 by decide]
  all_goals try simp_rw [hm0, hv0]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm0, hv0]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm1, hv1]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 64).toNat = 64 by decide]
  all_goals try simp_rw [hm2, hv2]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm2, hv2]
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm1, hv1]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm3, hv3]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 128).toNat = 128 by decide]
  all_goals try simp_rw [hm4, hv4]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm4, hv4]
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm3, hv3]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm1, hv1]
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 160).toNat = 160 by decide]
  all_goals try simp_rw [hm5, hv5]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm5, hv5]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 64).toNat = 64 by decide]
  all_goals try simp_rw [hm2, hv2]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm2, hv2]
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 160).toNat = 160 by decide]
  all_goals try simp_rw [hm5, hv5]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm5, hv5]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm3, hv3]
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 192).toNat = 192 by decide]
  all_goals try simp_rw [hm6, hv6]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm6, hv6]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 128).toNat = 128 by decide]
  all_goals try simp_rw [hm4, hv4]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm4, hv4]
  func_run (2) [3]
  all_goals try rfl
  all_goals try
    simp only [show (Nat.toB256 192).toNat = 192 by decide]
  all_goals try simp_rw [hm6, hv6]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  all_goals try decide +kernel
  all_goals try omega
  try rw [hm6, hv6]
  func_run (2) [0]
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  func_run (3) []
  all_goals try rfl
  all_goals try decide +kernel
  all_goals try omega
  have hrest' := hrest
  rw [lidoCircuitBreakerConstructorProgram_main_official] at hrest'
  unfold officialConstructorValidationBody at hrest'
  simp only [pushFixedNat,
    if_pos (show 5122 < 2 ^ 16 by decide),
    if_pos (show 4898 < 2 ^ 16 by decide),
    if_pos (show 4282 < 2 ^ 16 by decide),
    if_pos (show 616 < 2 ^ 16 by decide)] at hrest'
  unfold loadArgumentIndex pushCompactNat checkNonAddress
    pushAddressMask at hrest'
  have hstack :
      [Nat.toB256 constructorRuntimeBase, Bytes.toB256 [2, 104],
        Bytes.toB256 [16, 186]] =
        [(224 : B256), (616 : B256), (4282 : B256)] := by
    unfold constructorRuntimeBase constructorArgumentBytes
    decide +kernel
  rw [hstack]
  exact hrest'

/-! ## Named constructor effects and final frame -/

private theorem constructorSlice_split {ξ : Type} (xs : List ξ) (d : ξ) :
    ∀ (a m b : Nat),
      xs.sliceD m (a + b) d =
        xs.sliceD m a d ++ xs.sliceD (m + a) b d := by
  intro a
  induction a with
  | zero =>
      intro m b
      simp [List.sliceD, List.takeD]
  | succ a ih =>
      intro m b
      rw [show a + 1 + b = (a + b) + 1 by omega,
        List.sliceD_succ, ih (m + 1) b,
        List.sliceD_succ xs m a d,
        show m + (a + 1) = m + 1 + a by omega]
      rfl

private theorem Bytes.sliceD_writeAt_pair
    (bs xs ys : Bytes) (n : Nat) :
    (Bytes.writeAt (Bytes.writeAt bs n xs) (n + xs.length) ys).sliceD
        n (xs.length + ys.length) 0 =
      xs ++ ys := by
  rw [constructorSlice_split _ 0 xs.length n ys.length,
    Bytes.sliceD_writeAt_before _ _ n xs.length (n + xs.length) (by omega),
    Bytes.sliceD_writeAt, Bytes.sliceD_writeAt]

private theorem ConstructorPatchInvariant.read_argument_bytes
    {memory : Mem} (h : ConstructorPatchInvariant memory) (i : Fin 7) :
    h.image.sliceD (32 * i.val) 32 0 =
      (officialConstructorArgumentWord i).toBytes := by
  have hlen : (h.image.sliceD (32 * i.val) 32 0).length = 32 := by
    unfold List.sliceD
    rw [List.takeD_length]
  rw [← h.argument_reads i, Bytes.toBytes_toB256_of_length hlen]

/-- Exact gas consumed by the successful source-level constructor function,
excluding the compiler table's leading `JUMPDEST`. -/
def officialConstructorFuncGas : Nat := 50328

/-- Exact gas consumed by the compiled successful constructor from pc zero,
including the compiler table's leading `JUMPDEST`. -/
def officialConstructorRequiredGas : Nat := 50329

private def officialConstructorInitializedLog (ca : Adr) : Log :=
  ⟨ca, [circuitBreakerInitializedEvent, officialParams.admin],
    officialParams.minPauseDuration.toBytes ++
      officialParams.maxPauseDuration.toBytes ++
      officialParams.minHeartbeatInterval.toBytes ++
      officialParams.maxHeartbeatInterval.toBytes⟩

private theorem officialConstructorPatchedMemory_read_initializedData :
    (officialConstructorPatchedMemory.read 32 128).1 =
      officialParams.minPauseDuration.toBytes ++
        officialParams.maxPauseDuration.toBytes ++
        officialParams.minHeartbeatInterval.toBytes ++
        officialParams.maxHeartbeatInterval.toBytes := by
  rw [← officialConstructorPatchMemory12_eq_patched,
    Mem.Reads.read officialConstructorPatchInvariant12.memory_reads]
  have hminPause :
      officialConstructorPatchInvariant12.image.sliceD 32 32 0 =
        officialParams.minPauseDuration.toBytes := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorPatchInvariant12.read_argument_bytes
        ⟨1, by decide⟩
  have hmaxPause :
      officialConstructorPatchInvariant12.image.sliceD 64 32 0 =
        officialParams.maxPauseDuration.toBytes := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorPatchInvariant12.read_argument_bytes
        ⟨2, by decide⟩
  have hminHeartbeat :
      officialConstructorPatchInvariant12.image.sliceD 96 32 0 =
        officialParams.minHeartbeatInterval.toBytes := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorPatchInvariant12.read_argument_bytes
        ⟨3, by decide⟩
  have hmaxHeartbeat :
      officialConstructorPatchInvariant12.image.sliceD 128 32 0 =
        officialParams.maxHeartbeatInterval.toBytes := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorPatchInvariant12.read_argument_bytes
        ⟨4, by decide⟩
  rw [constructorSlice_split
      officialConstructorPatchInvariant12.image 0 32 32 96,
    constructorSlice_split
      officialConstructorPatchInvariant12.image 0 32 64 64,
    constructorSlice_split
      officialConstructorPatchInvariant12.image 0 32 96 32,
    hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat]
  simp only [List.append_assoc]

private def officialConstructorPauseLog (ca : Adr) : Log :=
  ⟨ca, [pauseDurationUpdatedEvent],
    (0 : B256).toBytes ++
      officialConstructorArgs.initialPauseDuration.toBytes⟩

private def officialConstructorHeartbeatLog (ca : Adr) : Log :=
  ⟨ca, [heartbeatIntervalUpdatedEvent],
    (0 : B256).toBytes ++
      officialConstructorArgs.initialHeartbeatInterval.toBytes⟩

private def officialConstructorEventScratch : Nat :=
  constructorEventScratch 4282

private theorem officialConstructorEventScratch_eq :
    officialConstructorEventScratch = 4512 := by
  decide

private def officialConstructorPauseMemory : Mem :=
  (officialConstructorPatchedMemory.write officialConstructorEventScratch
    (0 : B256).toBytes).write (officialConstructorEventScratch + 32)
      officialConstructorArgs.initialPauseDuration.toBytes

private def officialConstructorPauseImage : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt officialConstructorPatchedImage
      officialConstructorEventScratch (0 : B256).toBytes)
    (officialConstructorEventScratch + 32)
    officialConstructorArgs.initialPauseDuration.toBytes

private def officialConstructorHeartbeatMemory : Mem :=
  (officialConstructorPauseMemory.write officialConstructorEventScratch
    (0 : B256).toBytes).write (officialConstructorEventScratch + 32)
      officialConstructorArgs.initialHeartbeatInterval.toBytes

private def officialConstructorHeartbeatImage : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt officialConstructorPauseImage
      officialConstructorEventScratch (0 : B256).toBytes)
    (officialConstructorEventScratch + 32)
    officialConstructorArgs.initialHeartbeatInterval.toBytes

private theorem officialConstructorHeartbeatMemory_eq_final :
    officialConstructorHeartbeatMemory = officialConstructorFinalMemory := by
  rfl

private theorem officialConstructorPauseMemory_wf :
    Mem.Wf officialConstructorPauseMemory := by
  unfold officialConstructorPauseMemory
  exact Mem.Wf.write
    (Mem.Wf.write officialConstructorPatchedMemory_wf _ _) _ _

private theorem officialConstructorPauseMemory_reads :
    Mem.Reads officialConstructorPauseMemory
      officialConstructorPauseImage := by
  unfold officialConstructorPauseMemory officialConstructorPauseImage
  exact Mem.Reads.write
    (Mem.Wf.write officialConstructorPatchedMemory_wf _ _)
    (Mem.Reads.write officialConstructorPatchedMemory_wf
      officialConstructorPatchedMemory_reads _ _) _ _

private theorem officialConstructorPauseMemory_size :
    officialConstructorPauseMemory.size = 4576 := by
  unfold officialConstructorPauseMemory
  rw [Mem.size_write_word_at, Mem.size_write_word_at,
    officialConstructorPatchedMemory_size,
    officialConstructorEventScratch_eq]
  decide

private theorem officialConstructorHeartbeatMemory_wf :
    Mem.Wf officialConstructorHeartbeatMemory := by
  unfold officialConstructorHeartbeatMemory
  exact Mem.Wf.write
    (Mem.Wf.write officialConstructorPauseMemory_wf _ _) _ _

private theorem officialConstructorHeartbeatMemory_reads :
    Mem.Reads officialConstructorHeartbeatMemory
      officialConstructorHeartbeatImage := by
  unfold officialConstructorHeartbeatMemory officialConstructorHeartbeatImage
  exact Mem.Reads.write
    (Mem.Wf.write officialConstructorPauseMemory_wf _ _)
    (Mem.Reads.write officialConstructorPauseMemory_wf
      officialConstructorPauseMemory_reads _ _) _ _

private theorem officialConstructorHeartbeatMemory_size :
    officialConstructorHeartbeatMemory.size = 4576 := by
  rw [officialConstructorHeartbeatMemory_eq_final,
    officialConstructorFinalMemory_size]

private theorem officialConstructorPauseMemory_read_data :
    (officialConstructorPauseMemory.read
        officialConstructorEventScratch 64).1 =
      (0 : B256).toBytes ++
        officialConstructorArgs.initialPauseDuration.toBytes := by
  rw [Mem.Reads.read officialConstructorPauseMemory_reads]
  unfold officialConstructorPauseImage
  simpa only [B256.length_toBytes] using
    Bytes.sliceD_writeAt_pair officialConstructorPatchedImage
      (0 : B256).toBytes
      officialConstructorArgs.initialPauseDuration.toBytes
      officialConstructorEventScratch

private theorem officialConstructorHeartbeatMemory_read_data :
    (officialConstructorHeartbeatMemory.read
        officialConstructorEventScratch 64).1 =
      (0 : B256).toBytes ++
        officialConstructorArgs.initialHeartbeatInterval.toBytes := by
  rw [Mem.Reads.read officialConstructorHeartbeatMemory_reads]
  unfold officialConstructorHeartbeatImage
  simpa only [B256.length_toBytes] using
    Bytes.sliceD_writeAt_pair officialConstructorPauseImage
      (0 : B256).toBytes
      officialConstructorArgs.initialHeartbeatInterval.toBytes
      officialConstructorEventScratch

private theorem officialConstructorPatchedMemory_read_initializedMemory :
    (officialConstructorPatchedMemory.read 32 128).2 =
      officialConstructorPatchedMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorPatchedMemory_size]
  · rw [officialConstructorPatchedMemory_size]
    decide

private theorem officialConstructorPauseMemory_read_memory :
    (officialConstructorPauseMemory.read
        officialConstructorEventScratch 64).2 =
      officialConstructorPauseMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorPauseMemory_size]
  · rw [officialConstructorPauseMemory_size,
      officialConstructorEventScratch_eq]

private theorem officialConstructorHeartbeatMemory_read_memory :
    (officialConstructorHeartbeatMemory.read
        officialConstructorEventScratch 64).2 =
      officialConstructorHeartbeatMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorHeartbeatMemory_size]
  · rw [officialConstructorHeartbeatMemory_size,
      officialConstructorEventScratch_eq]

private def officialConstructorColdStore
    (sevm : Sevm) (base : Devm) (key value : B256) : Devm :=
  (((addAccessedStorageKey base sevm.currentTarget key).withRefundCounter
    base.refundCounter).setStorVal sevm.currentTarget key value)

/-- The non-machine constructor effects after the three logs and the two cold
zero-to-nonzero configuration writes, in exact source order. -/
def officialConstructorEffectBase (sevm : Sevm) (base : Devm) : Devm :=
  let initialized :=
    base.addLog (officialConstructorInitializedLog sevm.currentTarget)
  let pauseLogged :=
    initialized.addLog (officialConstructorPauseLog sevm.currentTarget)
  let pauseStored := officialConstructorColdStore sevm pauseLogged
    pauseDurationSlot officialConstructorArgs.initialPauseDuration
  let heartbeatLogged :=
    pauseStored.addLog (officialConstructorHeartbeatLog sevm.currentTarget)
  officialConstructorColdStore sevm heartbeatLogged heartbeatIntervalSlot
    officialConstructorArgs.initialHeartbeatInterval

private def officialConstructorReturnPre
    (sevm : Sevm) (base : Devm) (G : Nat) : Devm :=
  (officialConstructorEffectBase sevm base).setMach
    ⟨[Nat.toB256 constructorRuntimeBase, (4282 : B256)],
      officialConstructorFinalMemory, G⟩

private def officialConstructorReturnRead
    (sevm : Sevm) (base : Devm) (G : Nat) : Bytes × Devm :=
  let pre := officialConstructorReturnPre sevm base G
  (pre.setMach ⟨[], pre.memory, G⟩).memRead constructorRuntimeBase 4282

/-- Exact successful constructor post-frame at its final remaining gas. -/
def officialConstructorPost
    (sevm : Sevm) (base : Devm) (G : Nat) : Devm :=
  let returned := officialConstructorReturnRead sevm base G
  returned.2.withOutput returned.1

private theorem officialConstructorReturnLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (officialConstructorReturnPre sevm base G) rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorEffectBase sevm base).setMach
        ⟨[], officialConstructorFinalMemory, G + 6⟩)
      (pushFixedNat 4282 :::
        pushCompactNat constructorRuntimeBase ::: rest) post := by
  unfold pushFixedNat pushCompactNat
  simp only [if_pos (show 4282 < 2 ^ 16 by decide)]
  func_run (2)
  exact hrest

private theorem officialConstructorReturn_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat} :
    Func.RunCompiled fs sevm
      (officialConstructorReturnPre sevm base G) Func.ret
      (officialConstructorPost sevm base G) := by
  have hindex : (Nat.toB256 constructorRuntimeBase).toNat =
      constructorRuntimeBase := by
    apply B256.toNat_toB256_of_lt
    unfold constructorRuntimeBase constructorArgumentBytes
    decide
  have hstack : (officialConstructorReturnPre sevm base G).stack =
      [Nat.toB256 constructorRuntimeBase, (4282 : B256)] := by
    simp only [officialConstructorReturnPre, Devm.stack_setMach]
  have hext : (officialConstructorReturnPre sevm base G).extCost
      [⟨constructorRuntimeBase, 4282⟩] = 0 := by
    unfold officialConstructorReturnPre
    exact Devm.extCost_zero_of_le
      (N := officialConstructorFinalMemory)
      (i := constructorRuntimeBase) (sz := 4282)
      (by rw [officialConstructorFinalMemory_size])
      (by
        rw [officialConstructorFinalMemory_size]
        unfold constructorRuntimeBase constructorArgumentBytes
        decide)
  have hgas : (officialConstructorReturnPre sevm base G).gasLeft =
      G + (officialConstructorReturnPre sevm base G).extCost
        [⟨(Nat.toB256 constructorRuntimeBase).toNat,
          (4282 : B256).toNat⟩] := by
    rw [hindex, show (4282 : B256).toNat = 4282 by decide, hext]
    simp only [officialConstructorReturnPre, Devm.gasLeft_setMach, Nat.add_zero]
  have hread :
      ((officialConstructorReturnPre sevm base G).setMach
        ⟨[], (officialConstructorReturnPre sevm base G).memory, G⟩).memRead
          (Nat.toB256 constructorRuntimeBase).toNat (4282 : B256).toNat =
        officialConstructorReturnRead sevm base G := by
    unfold officialConstructorReturnRead
    rw [hindex, show (4282 : B256).toNat = 4282 by decide]
  have hrun := Func.runCompiled_ret
    (fs := fs) (sevm := sevm)
    (devm := officialConstructorReturnPre sevm base G)
    (i := Nat.toB256 constructorRuntimeBase) (sz := (4282 : B256))
    (s := []) (out := (officialConstructorReturnRead sevm base G).1)
    (d' := (officialConstructorReturnRead sevm base G).2) (G := G)
    hstack hgas (by simpa only [Prod.eta] using hread)
  simpa only [officialConstructorPost, Func.ret] using hrun

/-! ## Composed constructor effect suffix -/

private theorem officialConstructorColdStore_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {key value : B256} {memory : Mem} {G : Nat} {rest : Func}
    (hcold : (sevm.currentTarget, key) ∉ base.accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget key = 0)
    (hcurrent : base.getStorVal sevm.currentTarget key = 0)
    (hvalue : value ≠ 0)
    (hsentry : gCallStipend < G + 22100)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorColdStore sevm base key value).setMach
        ⟨[], memory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[key, value], memory, G + 22100⟩)
      (sstore ::: rest) post := by
  have hzeroValue : (0 : B256) ≠ value := Ne.symm hvalue
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_sstore_cold
        (c := 22100) (G := G) (rc := base.refundCounter)
    · rfl
    · simpa only [Devm.setMach, Devm.accessedStorageKeys] using hcold
    · simpa only [Devm.gasLeft_setMach] using hsentry
    · exact hstatic
    · simp only [Devm.getStorVal_setMach, hcurrent, horiginal]
      simp [sstoreValueCost, hzeroValue, gasColdSload, gasStorageSet]
    · simp only [Devm.getStorVal_setMach, Devm.setMach,
        Devm.refundCounter, hcurrent, horiginal]
      simp [sstoreNewRefundCounter, hzeroValue]
    · simp only [Devm.gasLeft_setMach]
  · change Func.RunCompiled fs sevm
      ((officialConstructorColdStore sevm base key value).setMach
        ⟨[], memory, G⟩)
      rest post
    exact hrest

private def officialConstructorInitializedBase
    (sevm : Sevm) (base : Devm) : Devm :=
  base.addLog (officialConstructorInitializedLog sevm.currentTarget)

private def officialConstructorPauseLoggedBase
    (sevm : Sevm) (base : Devm) : Devm :=
  (officialConstructorInitializedBase sevm base).addLog
    (officialConstructorPauseLog sevm.currentTarget)

private def officialConstructorPauseStoredBase
    (sevm : Sevm) (base : Devm) : Devm :=
  officialConstructorColdStore sevm
    (officialConstructorPauseLoggedBase sevm base)
    pauseDurationSlot officialConstructorArgs.initialPauseDuration

private def officialConstructorHeartbeatLoggedBase
    (sevm : Sevm) (base : Devm) : Devm :=
  (officialConstructorPauseStoredBase sevm base).addLog
    (officialConstructorHeartbeatLog sevm.currentTarget)

private theorem officialConstructorHeartbeatLoggedBase_getStor
    (sevm : Sevm) (base : Devm) :
    Devm.getStor (officialConstructorHeartbeatLoggedBase sevm base)
        sevm.currentTarget =
      (Devm.getStor base sevm.currentTarget).set pauseDurationSlot
        officialConstructorArgs.initialPauseDuration := by
  unfold officialConstructorHeartbeatLoggedBase
    officialConstructorPauseStoredBase officialConstructorColdStore
  change Devm.getStor
      (((addAccessedStorageKey
          (officialConstructorPauseLoggedBase sevm base)
          sevm.currentTarget pauseDurationSlot).withRefundCounter _).setStorVal
        sevm.currentTarget pauseDurationSlot
          officialConstructorArgs.initialPauseDuration)
        sevm.currentTarget = _
  rw [setStorVal_getStor_self]
  apply congrArg (fun s : Stor =>
    s.set pauseDurationSlot officialConstructorArgs.initialPauseDuration)
  change Devm.getStor
      (addAccessedStorageKey (officialConstructorPauseLoggedBase sevm base)
        sevm.currentTarget pauseDurationSlot)
        sevm.currentTarget = Devm.getStor base sevm.currentTarget
  rw [addAccessedStorageKey_getStor]
  rfl

private theorem officialConstructorPauseLoggedBase_accessedStorageKeys
    (sevm : Sevm) (base : Devm) :
    (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys =
      base.accessedStorageKeys := by
  rfl

private theorem officialConstructorPauseLoggedBase_getStorVal
    (sevm : Sevm) (base : Devm) (a : Adr) (key : B256) :
    (officialConstructorPauseLoggedBase sevm base).getStorVal a key =
      base.getStorVal a key := by
  rfl

private theorem officialConstructorHeartbeatLoggedBase_accessedStorageKeys
    (sevm : Sevm) (base : Devm) :
    (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys =
      base.accessedStorageKeys.insert
        (sevm.currentTarget, pauseDurationSlot) := by
  rfl

private theorem not_mem_hashSet_insert {α : Type _} [BEq α] [Hashable α]
    [LawfulBEq α] {s : Std.HashSet α} {x p : α}
    (h : p ∉ s) (hne : x ≠ p) : p ∉ s.insert x := by
  intro hmem
  rcases Std.HashSet.mem_insert.mp hmem with he | hp
  · exact hne (eq_of_beq he)
  · exact h hp

private theorem officialConstructorHeartbeatStore_eq_effectBase
    (sevm : Sevm) (base : Devm) :
    officialConstructorColdStore sevm
        (officialConstructorHeartbeatLoggedBase sevm base)
        heartbeatIntervalSlot
        officialConstructorArgs.initialHeartbeatInterval =
      officialConstructorEffectBase sevm base := by
  rfl

private theorem officialConstructorHeartbeatSstore_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hcurrent : (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorEffectBase sevm base).setMach
        ⟨[], officialConstructorFinalMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorHeartbeatLoggedBase sevm base).setMach
        ⟨[heartbeatIntervalSlot,
            officialConstructorArgs.initialHeartbeatInterval],
          officialConstructorHeartbeatMemory, G + 22100⟩)
      (sstore ::: rest) post := by
  have hrest' : Func.RunCompiled fs sevm
      ((officialConstructorColdStore sevm
          (officialConstructorHeartbeatLoggedBase sevm base)
          heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post := by
    rw [officialConstructorHeartbeatStore_eq_effectBase,
      officialConstructorHeartbeatMemory_eq_final]
    exact hrest
  exact officialConstructorColdStore_runCompiled hcold horiginal hcurrent
    (by unfold officialConstructorArgs; decide)
    (by simp only [gCallStipend]; omega) hstatic hrest'

private theorem officialConstructorHeartbeatLogOpcode_runCompiled
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
        (c := 1262) (G := G)
        (M := officialConstructorHeartbeatMemory)
        (data := (0 : B256).toBytes ++
          officialConstructorArgs.initialHeartbeatInterval.toBytes)
    · rfl
    · rfl
    · exact hstatic
    · rw [hi, hsz]
      rw [Devm.extCost_zero_of_le
        (N := officialConstructorHeartbeatMemory)
        (by rw [officialConstructorHeartbeatMemory_size])
        (by rw [officialConstructorHeartbeatMemory_size,
          officialConstructorEventScratch_eq])]
      decide
    · simp only [Devm.memory_setMach, hi, hsz]
      exact officialConstructorHeartbeatMemory_read_data
    · simp only [Devm.memory_setMach, hi, hsz]
      exact officialConstructorHeartbeatMemory_read_memory
    · simp only [Devm.gasLeft_setMach]
  · change Func.RunCompiled fs sevm
      ((officialConstructorHeartbeatLoggedBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post
    exact hrest

set_option maxRecDepth 4096 in
private theorem officialConstructorHeartbeatLogLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorHeartbeatLoggedBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G + 1271⟩)
      (pushB256 heartbeatIntervalUpdatedEvent :::
        logWith 0
          (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
        rest) post := by
  have hlog := officialConstructorHeartbeatLogOpcode_runCompiled
    hstatic hrest
  unfold logWith
  func_run (3)
  all_goals try decide +kernel
  exact hlog

private theorem officialConstructorPatchedMemory_read_argument
    (i : Fin 7) :
    Bytes.toB256
        ((officialConstructorPatchedMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  rw [← officialConstructorPatchMemory12_eq_patched]
  exact officialConstructorPatchInvariant12.read_argument i

private theorem officialConstructorPauseMemory_read_argument
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
    Bytes.sliceD_writeAt_before _ _ (32 * i.val) 32
      officialConstructorEventScratch (by
        rw [officialConstructorEventScratch_eq]
        have hi := i.isLt
        omega),
    ← Mem.Reads.read officialConstructorPatchedMemory_reads]
  exact officialConstructorPatchedMemory_read_argument i

private theorem officialConstructorHeartbeatMemory_read_argument
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
    Bytes.sliceD_writeAt_before _ _ (32 * i.val) 32
      officialConstructorEventScratch (by
        rw [officialConstructorEventScratch_eq]
        have hi := i.isLt
        omega),
    ← Mem.Reads.read officialConstructorPauseMemory_reads]
  exact officialConstructorPauseMemory_read_argument i

private theorem officialConstructorHeartbeatMemory_read_argument_memory
    (i : Fin 7) :
    (officialConstructorHeartbeatMemory.read (32 * i.val) 32).2 =
      officialConstructorHeartbeatMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorHeartbeatMemory_size]
  · rw [officialConstructorHeartbeatMemory_size]
    have hi := i.isLt
    omega

set_option maxRecDepth 4096 in
private theorem officialConstructorHeartbeatStoreLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hcurrent : (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorEffectBase sevm base).setMach
        ⟨[], officialConstructorFinalMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorHeartbeatLoggedBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G + 22109⟩)
      (loadArgumentIndex 6 +++
        pushB256 heartbeatIntervalSlot ::: sstore ::: rest) post := by
  have hvalue : Bytes.toB256
      ((officialConstructorHeartbeatMemory.read 192 32).1) =
        officialConstructorArgs.initialHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorHeartbeatMemory_read_argument
        ⟨6, by decide⟩
  have hmemory :
      (officialConstructorHeartbeatMemory.read 192 32).2 =
        officialConstructorHeartbeatMemory := by
    simpa using officialConstructorHeartbeatMemory_read_argument_memory
      ⟨6, by decide⟩
  have hstore := officialConstructorHeartbeatSstore_runCompiled
    hcold horiginal hcurrent hstatic hrest
  have hindex : (Nat.toB256 (32 * 6)).toNat = 192 := by decide
  unfold loadArgumentIndex pushCompactNat
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := G + 22106)
    · decide
    · simp only [Devm.gasLeft_setMach]
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * 6))
          (v := officialConstructorArgs.initialHeartbeatInterval)
          (s := []) (M := officialConstructorHeartbeatMemory)
          (c := 3) (G := G + 22103)
      · simp only [Devm.stack_setMach]
      · simp only [Devm.memory_setMach, hindex]
        rw [Devm.extCost_zero_of_le
          (N := officialConstructorHeartbeatMemory)
          (by rw [officialConstructorHeartbeatMemory_size])
          (by rw [officialConstructorHeartbeatMemory_size]; decide)]
        decide
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
      · simp only [Devm.stack_setMach, List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushB256 (c := 3) (G := G + 22100)
        · simpa only [gVerylow] using pushCost_of_ne_zero
            (w := heartbeatIntervalSlot) (by decide +kernel)
        · simp only [Devm.gasLeft_setMach]
          omega
        · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega
      · simpa only [Devm.setMach_setMach] using hstore

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem officialConstructorHeartbeatScratchLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G + 20⟩)
      (pushB256 0 :::
        storeByteOffset officialConstructorEventScratch +++
        loadArgumentIndex 6 +++
        storeByteOffset (officialConstructorEventScratch + 32) +++
        rest) post := by
  let zeroMemory := officialConstructorPauseMemory.write
    officialConstructorEventScratch (0 : B256).toBytes
  have hzeroEq : officialConstructorPauseMemory.write
      officialConstructorEventScratch (0 : B256).toBytes = zeroMemory := by
    rfl
  have hzeroSize : zeroMemory.size = 4576 := by
    unfold zeroMemory
    rw [Mem.size_write_of_le]
    · exact officialConstructorPauseMemory_size
    · rw [B256.length_toBytes, officialConstructorPauseMemory_size,
        officialConstructorEventScratch_eq]
      decide
  have hzeroWf : Mem.Wf zeroMemory := by
    exact Mem.Wf.write officialConstructorPauseMemory_wf _ _
  have hzeroReads : Mem.Reads zeroMemory
      (Bytes.writeAt officialConstructorPauseImage
        officialConstructorEventScratch (0 : B256).toBytes) := by
    exact Mem.Reads.write officialConstructorPauseMemory_wf
      officialConstructorPauseMemory_reads _ _
  have hvalue : Bytes.toB256 ((zeroMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
    rw [Mem.Reads.read hzeroReads]
    rw [Bytes.sliceD_writeAt_before _ _ 192 32
      officialConstructorEventScratch (by
        rw [officialConstructorEventScratch_eq]
        decide)]
    rw [← Mem.Reads.read officialConstructorPauseMemory_reads]
    simpa [officialConstructorArgumentWord] using
      officialConstructorPauseMemory_read_argument ⟨6, by decide⟩
  have hmemory : (zeroMemory.read 192 32).2 = zeroMemory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hzeroSize]
    · rw [hzeroSize]
      decide
  have hfinal : zeroMemory.write (officialConstructorEventScratch + 32)
      officialConstructorArgs.initialHeartbeatInterval.toBytes =
        officialConstructorHeartbeatMemory := by
    rfl
  have hscratchLt : officialConstructorEventScratch < 2 ^ 16 := by
    rw [officialConstructorEventScratch_eq]
    decide
  have hnextLt : officialConstructorEventScratch + 32 < 2 ^ 16 := by
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
  have hnextNat :
      (Bytes.toB256
        [((officialConstructorEventScratch + 32) >>> 8).toUInt8,
          (officialConstructorEventScratch + 32).toUInt8]).toNat =
        officialConstructorEventScratch + 32 := by
    rw [List.toB256_pair (officialConstructorEventScratch + 32) hnextLt]
    rw [officialConstructorEventScratch_eq]
    decide
  have hindex : (Nat.toB256 (32 * 6)).toNat = 192 := by decide
  have hlastExt :
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[Bytes.toB256
            [((officialConstructorEventScratch + 32) >>> 8).toUInt8,
              (officialConstructorEventScratch + 32).toUInt8],
            officialConstructorArgs.initialHeartbeatInterval],
          zeroMemory, G + 20 - 17⟩).extCost
        [⟨officialConstructorEventScratch + 32, 32⟩] = 0 := by
    exact Devm.extCost_zero_of_le
      (N := zeroMemory) (i := officialConstructorEventScratch + 32) (sz := 32)
      (by rw [hzeroSize])
      (by rw [hzeroSize, officialConstructorEventScratch_eq])
  unfold storeByteOffset loadArgumentIndex pushCompactNat pushFixedNat
  simp only [if_pos hscratchLt, if_pos hnextLt]
  func_run (7) [0, 3, 0]
  all_goals try rw [hscratchNat]
  all_goals try rw [hnextNat]
  all_goals try rw [hindex]
  all_goals try rw [hzeroEq]
  all_goals try rw [hmemory]
  all_goals try rw [hvalue]
  all_goals try rw [hfinal]
  all_goals try rw [Devm.extCost_zero_of_le
    (N := officialConstructorPauseMemory)
    (by rw [officialConstructorPauseMemory_size])
    (by rw [officialConstructorPauseMemory_size,
      officialConstructorEventScratch_eq]; decide)]
  all_goals try rw [Devm.extCost_zero_of_le
    (N := zeroMemory) (i := 192) (sz := 32)
    (by rw [hzeroSize])
    (by rw [hzeroSize]; decide)]
  all_goals try rw [Devm.extCost_zero_of_le
    (N := zeroMemory) (i := officialConstructorEventScratch + 32) (sz := 32)
    (by rw [hzeroSize])
    (by rw [hzeroSize, officialConstructorEventScratch_eq]; decide)]
  all_goals try
    exact Devm.extCost_zero_of_le
      (N := zeroMemory) (i := officialConstructorEventScratch + 32) (sz := 32)
      (by rw [hzeroSize])
      (by rw [hzeroSize, officialConstructorEventScratch_eq]; decide)
  all_goals try exact hlastExt
  all_goals try decide
  all_goals try omega
  exact hrest

private def officialConstructorHeartbeatSuffix : Func :=
  pushB256 0 :::
  storeByteOffset officialConstructorEventScratch +++
  loadArgumentIndex 6 +++
  storeByteOffset (officialConstructorEventScratch + 32) +++
  pushB256 heartbeatIntervalUpdatedEvent :::
  logWith 0
    (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
  loadArgumentIndex 6 +++
  pushB256 heartbeatIntervalSlot ::: sstore :::
  pushFixedNat 4282 :::
  pushCompactNat constructorRuntimeBase :::
  Func.ret

private theorem officialConstructorHeartbeatSuffix_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hcold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hcurrent : (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G + 23406⟩)
      officialConstructorHeartbeatSuffix
      (officialConstructorPost sevm base G) := by
  have hret := officialConstructorReturn_runCompiled
    (fs := fs) (sevm := sevm) (base := base) (G := G)
  have hreturn := officialConstructorReturnLine_runCompiled hret
  have hstore := officialConstructorHeartbeatStoreLine_runCompiled
    hcold horiginal hcurrent hstatic hreturn
  have hlog := officialConstructorHeartbeatLogLine_runCompiled hstatic hstore
  have hscratch :=
    officialConstructorHeartbeatScratchLine_runCompiled hlog
  unfold officialConstructorHeartbeatSuffix
  convert hscratch using 1 <;> omega

private theorem officialConstructorPauseMemory_read_argument_memory
    (i : Fin 7) :
    (officialConstructorPauseMemory.read (32 * i.val) 32).2 =
      officialConstructorPauseMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorPauseMemory_size]
  · rw [officialConstructorPauseMemory_size]
    have hi := i.isLt
    omega

set_option maxRecDepth 4096 in
private theorem officialConstructorPauseStoreLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcold : (sevm.currentTarget, pauseDurationSlot) ∉
      (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hcurrent : (officialConstructorPauseLoggedBase sevm base).getStorVal
      sevm.currentTarget pauseDurationSlot = 0)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseLoggedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G + 22109⟩)
      (loadArgumentIndex 5 +++
        pushB256 pauseDurationSlot ::: sstore ::: rest) post := by
  have hvalue : Bytes.toB256
      ((officialConstructorPauseMemory.read 160 32).1) =
        officialConstructorArgs.initialPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorPauseMemory_read_argument ⟨5, by decide⟩
  have hmemory :
      (officialConstructorPauseMemory.read 160 32).2 =
        officialConstructorPauseMemory := by
    simpa using officialConstructorPauseMemory_read_argument_memory
      ⟨5, by decide⟩
  have hrest' : Func.RunCompiled fs sevm
      ((officialConstructorColdStore sevm
          (officialConstructorPauseLoggedBase sevm base)
          pauseDurationSlot
          officialConstructorArgs.initialPauseDuration).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post := by
    simpa only [officialConstructorPauseStoredBase] using hrest
  have hstore := officialConstructorColdStore_runCompiled
    hcold horiginal hcurrent
    (by unfold officialConstructorArgs; decide)
    (by simp only [gCallStipend]; omega) hstatic hrest'
  have hindex : (Nat.toB256 (32 * 5)).toNat = 160 := by decide
  unfold loadArgumentIndex pushCompactNat
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := G + 22106)
    · decide
    · simp only [Devm.gasLeft_setMach]
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * 5))
          (v := officialConstructorArgs.initialPauseDuration)
          (s := []) (M := officialConstructorPauseMemory)
          (c := 3) (G := G + 22103)
      · simp only [Devm.stack_setMach]
      · simp only [Devm.memory_setMach, hindex]
        rw [Devm.extCost_zero_of_le
          (N := officialConstructorPauseMemory)
          (by rw [officialConstructorPauseMemory_size])
          (by rw [officialConstructorPauseMemory_size]; decide)]
        decide
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
      · simp only [Devm.stack_setMach, List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushB256 (c := 3) (G := G + 22100)
        · simpa only [gVerylow] using pushCost_of_ne_zero
            (w := pauseDurationSlot) (by decide +kernel)
        · simp only [Devm.gasLeft_setMach]
          omega
        · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega
      · simpa only [Devm.setMach_setMach] using hstore

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
        (topics := [pauseDurationUpdatedEvent]) (s := [])
        (c := 1262) (G := G)
        (M := officialConstructorPauseMemory)
        (data := (0 : B256).toBytes ++
          officialConstructorArgs.initialPauseDuration.toBytes)
    · rfl
    · rfl
    · exact hstatic
    · rw [hi, hsz]
      rw [Devm.extCost_zero_of_le
        (N := officialConstructorPauseMemory)
        (by rw [officialConstructorPauseMemory_size])
        (by rw [officialConstructorPauseMemory_size,
          officialConstructorEventScratch_eq])]
      decide
    · simp only [Devm.memory_setMach, hi, hsz]
      exact officialConstructorPauseMemory_read_data
    · simp only [Devm.memory_setMach, hi, hsz]
      exact officialConstructorPauseMemory_read_memory
    · simp only [Devm.gasLeft_setMach]
  · change Func.RunCompiled fs sevm
      ((officialConstructorPauseLoggedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post
    exact hrest

set_option maxRecDepth 4096 in
private theorem officialConstructorPauseLogLine_runCompiled
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
  have hlog := officialConstructorPauseLogOpcode_runCompiled hstatic hrest
  unfold logWith
  func_run (3)
  all_goals try decide +kernel
  exact hlog

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem officialConstructorPauseScratchLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G + 27⟩)
      (pushB256 0 :::
        storeByteOffset officialConstructorEventScratch +++
        loadArgumentIndex 5 +++
        storeByteOffset (officialConstructorEventScratch + 32) +++
        rest) post := by
  let zeroMemory := officialConstructorPatchedMemory.write
    officialConstructorEventScratch (0 : B256).toBytes
  have hzeroEq : officialConstructorPatchedMemory.write
      officialConstructorEventScratch (0 : B256).toBytes = zeroMemory := by
    rfl
  have hzeroSize : zeroMemory.size = 4544 := by
    unfold zeroMemory
    rw [Mem.size_write_word_at, officialConstructorPatchedMemory_size,
      officialConstructorEventScratch_eq]
    decide
  have hzeroWf : Mem.Wf zeroMemory := by
    exact Mem.Wf.write officialConstructorPatchedMemory_wf _ _
  have hzeroReads : Mem.Reads zeroMemory
      (Bytes.writeAt officialConstructorPatchedImage
        officialConstructorEventScratch (0 : B256).toBytes) := by
    exact Mem.Reads.write officialConstructorPatchedMemory_wf
      officialConstructorPatchedMemory_reads _ _
  have hvalue : Bytes.toB256 ((zeroMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
    rw [Mem.Reads.read hzeroReads]
    rw [Bytes.sliceD_writeAt_before _ _ 160 32
      officialConstructorEventScratch (by
        rw [officialConstructorEventScratch_eq]
        decide)]
    rw [← Mem.Reads.read officialConstructorPatchedMemory_reads]
    simpa [officialConstructorArgumentWord] using
      officialConstructorPatchedMemory_read_argument ⟨5, by decide⟩
  have hmemory : (zeroMemory.read 160 32).2 = zeroMemory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hzeroSize]
    · rw [hzeroSize]
      decide
  have hfinal : zeroMemory.write (officialConstructorEventScratch + 32)
      officialConstructorArgs.initialPauseDuration.toBytes =
        officialConstructorPauseMemory := by
    rfl
  have hscratchLt : officialConstructorEventScratch < 2 ^ 16 := by
    rw [officialConstructorEventScratch_eq]
    decide
  have hnextLt : officialConstructorEventScratch + 32 < 2 ^ 16 := by
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
  have hnextNat :
      (Bytes.toB256
        [((officialConstructorEventScratch + 32) >>> 8).toUInt8,
          (officialConstructorEventScratch + 32).toUInt8]).toNat =
        officialConstructorEventScratch + 32 := by
    rw [List.toB256_pair (officialConstructorEventScratch + 32) hnextLt]
    rw [officialConstructorEventScratch_eq]
    decide
  have hindex : (Nat.toB256 (32 * 5)).toNat = 160 := by decide
  have hfirstExt (S : List B256) (G' : Nat) :
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨S, officialConstructorPatchedMemory, G'⟩).extCost
          [⟨officialConstructorEventScratch, 32⟩] = 4 := by
    exact Devm.extCost_of_size officialConstructorPatchedMemory_size (by
      rw [officialConstructorEventScratch_eq]
      decide +kernel)
  have hloadExt (S : List B256) (G' : Nat) :
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨S, zeroMemory, G'⟩).extCost [⟨160, 32⟩] = 0 := by
    exact Devm.extCost_zero_of_le
      (N := zeroMemory) (i := 160) (sz := 32)
      (by rw [hzeroSize]) (by rw [hzeroSize]; decide)
  have hlastExt (S : List B256) (G' : Nat) :
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨S, zeroMemory, G'⟩).extCost
          [⟨officialConstructorEventScratch + 32, 32⟩] = 3 := by
    exact Devm.extCost_of_size hzeroSize (by
      rw [officialConstructorEventScratch_eq]
      decide +kernel)
  unfold storeByteOffset loadArgumentIndex pushCompactNat pushFixedNat
  simp only [if_pos hscratchLt, if_pos hnextLt]
  func_run (7) [4, 3, 3]
  all_goals try rw [hscratchNat]
  all_goals try rw [hnextNat]
  all_goals try rw [hindex]
  all_goals try rw [hzeroEq]
  all_goals try rw [hmemory]
  all_goals try rw [hvalue]
  all_goals try rw [hfinal]
  all_goals try exact hfirstExt _ _
  all_goals try exact hloadExt _ _
  all_goals try exact hlastExt _ _
  all_goals try decide
  all_goals try omega
  exact hrest

private def officialConstructorConfigurationSuffix : Func :=
  pushB256 0 :::
  storeByteOffset officialConstructorEventScratch +++
  loadArgumentIndex 5 +++
  storeByteOffset (officialConstructorEventScratch + 32) +++
  pushB256 pauseDurationUpdatedEvent :::
  logWith 0
    (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
  loadArgumentIndex 5 +++
  pushB256 pauseDurationSlot ::: sstore :::
  officialConstructorHeartbeatSuffix

private theorem officialConstructorConfigurationSuffix_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hpauseCold : (sevm.currentTarget, pauseDurationSlot) ∉
      (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys)
    (hpauseOriginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hpauseCurrent : (officialConstructorPauseLoggedBase sevm base).getStorVal
      sevm.currentTarget pauseDurationSlot = 0)
    (hheartbeatCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (hheartbeatOriginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hheartbeatCurrent :
      (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
        sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G + 46813⟩)
      officialConstructorConfigurationSuffix
      (officialConstructorPost sevm base G) := by
  have hheartbeat := officialConstructorHeartbeatSuffix_runCompiled
    (fs := fs) (G := G) hheartbeatCold hheartbeatOriginal
    hheartbeatCurrent hstatic
  have hpauseStore := officialConstructorPauseStoreLine_runCompiled
    hpauseCold hpauseOriginal hpauseCurrent hstatic hheartbeat
  have hpauseLog := officialConstructorPauseLogLine_runCompiled
    hstatic hpauseStore
  have hpauseScratch :=
    officialConstructorPauseScratchLine_runCompiled hpauseLog
  unfold officialConstructorConfigurationSuffix
  convert hpauseScratch using 1 <;> omega

private theorem officialConstructorInitializedLogOpcode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(1 : B256) * 32, (4 : B256) * 32,
            circuitBreakerInitializedEvent, officialParams.admin],
          officialConstructorPatchedMemory, G + 2149⟩)
      (Ninst.log (Fin.succ 1) ::: rest) post := by
  have hi : ((1 : B256) * 32).toNat = 32 := by decide
  have hsz : ((4 : B256) * 32).toNat = 128 := by decide
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_log_of
        (n := Fin.succ 1)
        (i := (1 : B256) * 32) (sz := (4 : B256) * 32)
        (topics := [circuitBreakerInitializedEvent, officialParams.admin])
        (s := []) (c := 2149) (G := G)
        (M := officialConstructorPatchedMemory)
        (data := officialParams.minPauseDuration.toBytes ++
          officialParams.maxPauseDuration.toBytes ++
          officialParams.minHeartbeatInterval.toBytes ++
          officialParams.maxHeartbeatInterval.toBytes)
    · rfl
    · rfl
    · exact hstatic
    · rw [hi, hsz]
      rw [Devm.extCost_zero_of_le
        (N := officialConstructorPatchedMemory)
        (by rw [officialConstructorPatchedMemory_size])
        (by rw [officialConstructorPatchedMemory_size]; decide)]
      decide
    · simp only [Devm.memory_setMach, hi, hsz]
      exact officialConstructorPatchedMemory_read_initializedData
    · simp only [Devm.memory_setMach, hi, hsz]
      exact officialConstructorPatchedMemory_read_initializedMemory
    · simp only [Devm.gasLeft_setMach]
  · change Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post
    exact hrest

set_option maxRecDepth 4096 in
private theorem officialConstructorInitializedLogLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchedMemory, G + 2163⟩)
      (loadArgumentIndex 0 +++
        pushB256 circuitBreakerInitializedEvent :::
        logWith 1 1 4 +++ rest) post := by
  have hvalue : Bytes.toB256
      ((officialConstructorPatchedMemory.read 0 32).1) =
        officialParams.admin := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorPatchedMemory_read_argument ⟨0, by decide⟩
  have hmemory : (officialConstructorPatchedMemory.read 0 32).2 =
      officialConstructorPatchedMemory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [officialConstructorPatchedMemory_size]
    · rw [officialConstructorPatchedMemory_size]
      decide
  have hlog := officialConstructorInitializedLogOpcode_runCompiled
    hstatic hrest
  unfold loadArgumentIndex pushCompactNat logWith
  func_run (5) [3]
  all_goals try
    simp only [show (Nat.toB256 0).toNat = 0 by decide]
  all_goals try rw [hmemory]
  all_goals try rw [hvalue]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorPatchedMemory_size
      (by decide +kernel)
  all_goals try decide +kernel
  all_goals try omega
  convert hlog using 1 <;> omega

private theorem officialConstructorEffectBody_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hpauseCold : (sevm.currentTarget, pauseDurationSlot) ∉
      (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys)
    (hpauseOriginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hpauseCurrent : (officialConstructorPauseLoggedBase sevm base).getStorVal
      sevm.currentTarget pauseDurationSlot = 0)
    (hheartbeatCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (hheartbeatOriginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hheartbeatCurrent :
      (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
        sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, G + 49961⟩)
      officialConstructorEffectBody
      (officialConstructorPost sevm base G) := by
  have hconfiguration := officialConstructorConfigurationSuffix_runCompiled
    (fs := fs) (G := G) hpauseCold hpauseOriginal hpauseCurrent
    hheartbeatCold hheartbeatOriginal hheartbeatCurrent hstatic
  have hinitialized := officialConstructorInitializedLogLine_runCompiled
    hstatic hconfiguration
  have hcopy := officialConstructorCopyPatch_runCompiled hcode hinitialized
  unfold officialConstructorConfigurationSuffix
    officialConstructorHeartbeatSuffix officialConstructorEventScratch at hcopy
  unfold officialConstructorEffectBody
  have hstart :
      base.setMach
          ⟨[(224 : B256), (616 : B256), (4282 : B256)],
            officialConstructorDecodedMemory,
            G + 46813 + 2163 + 985⟩ =
        base.setMach
          ⟨[(224 : B256), (616 : B256), (4282 : B256)],
            officialConstructorDecodedMemory, G + 49961⟩ := by
    congr
  rw [← hstart]
  exact hcopy

private theorem officialConstructorProgram_runCompiled
    {sevm : Sevm} {base : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hpauseCold : (sevm.currentTarget, pauseDurationSlot) ∉
      (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys)
    (hpauseOriginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hpauseCurrent : (officialConstructorPauseLoggedBase sevm base).getStorVal
      sevm.currentTarget pauseDurationSlot = 0)
    (hheartbeatCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (hheartbeatOriginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hheartbeatCurrent :
      (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
        sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    Prog.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩)
      lidoCircuitBreakerConstructorProgram
      (officialConstructorPost sevm base G) := by
  have heffect := officialConstructorEffectBody_runCompiled
    (fs := lidoCircuitBreakerConstructorProgram.main ::
      lidoCircuitBreakerConstructorProgram.aux)
    (G := G) hcode hpauseCold hpauseOriginal hpauseCurrent
    hheartbeatCold hheartbeatOriginal hheartbeatCurrent hstatic
  have heffect' : Func.RunCompiled
      (lidoCircuitBreakerConstructorProgram.main ::
        lidoCircuitBreakerConstructorProgram.aux)
      sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, (G + 50328) - 367⟩)
      officialConstructorEffectBody
      (officialConstructorPost sevm base G) := by
    have hgas : (G + 50328) - 367 = G + 49961 := by omega
    rw [hgas]
    exact heffect
  have hmain := officialConstructorValidationPrefix_runCompiled
    (base := base) (g := G + 50328) hvalue hcode (by omega) heffect'
  apply Prog.runCompiled_intro
    (G := G + 50328)
    (mid := base.setMach ⟨[], Mem.empty, G + 50328⟩)
  · simp only [Devm.gasLeft_setMach, officialConstructorRequiredGas,
      gJumpdest]
  · simp only [Devm.stack_setMach, Devm.memory_setMach,
      Devm.setMach_setMach]
  · exact hmain

/-- The exact official constructor run from a fresh target frame. The cold and
zero-valued premises are stated on the incoming frame; the proof derives the
corresponding intermediate premises after the first logs and configuration
write. -/
theorem officialConstructorProgram_runCompiled_fresh
    {sevm : Sevm} {base : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hpauseCold : (sevm.currentTarget, pauseDurationSlot) ∉
      base.accessedStorageKeys)
    (hpauseOriginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hpauseCurrent : base.getStorVal sevm.currentTarget
      pauseDurationSlot = 0)
    (hheartbeatCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hheartbeatOriginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hheartbeatCurrent : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    Prog.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩)
      lidoCircuitBreakerConstructorProgram
      (officialConstructorPost sevm base G) := by
  apply officialConstructorProgram_runCompiled hvalue hcode
  · rw [officialConstructorPauseLoggedBase_accessedStorageKeys]
    exact hpauseCold
  · exact hpauseOriginal
  · rw [officialConstructorPauseLoggedBase_getStorVal]
    exact hpauseCurrent
  · rw [officialConstructorHeartbeatLoggedBase_accessedStorageKeys]
    apply not_mem_hashSet_insert hheartbeatCold
    intro hpair
    have hslots : pauseDurationSlot = heartbeatIntervalSlot :=
      congrArg Prod.snd hpair
    exact (show pauseDurationSlot ≠ heartbeatIntervalSlot by decide) hslots
  · exact hheartbeatOriginal
  · change (Devm.getStor
      (officialConstructorHeartbeatLoggedBase sevm base)
        sevm.currentTarget).get heartbeatIntervalSlot = 0
    rw [officialConstructorHeartbeatLoggedBase_getStor,
      Stor.get_set_ne _
        (show pauseDurationSlot ≠ heartbeatIntervalSlot by decide)]
    exact hheartbeatCurrent
  · exact hstatic

end LidoCircuitBreaker

end Blanc
