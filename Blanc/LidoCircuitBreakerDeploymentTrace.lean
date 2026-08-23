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

end LidoCircuitBreaker

end Blanc
