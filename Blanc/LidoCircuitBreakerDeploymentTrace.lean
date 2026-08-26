-- LidoCircuitBreakerDeploymentTrace.lean : exact official constructor walk.
--
-- The proof is intentionally consolidated in this owner after its abstract
-- opcode and memory certificates made the full artifact bounded again. This
-- keeps the deployment family inside its fixed elaboration-owner budget.
import Blanc.LidoCircuitBreakerDeploymentLayout
import Blanc.ForwardCall

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

open DeploymentProof

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceShape.lean`. -/

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

/-- First word-aligned scratch address following the copied official runtime. -/
def officialConstructorEventScratch : Nat :=
  constructorEventScratchForProof 4282

theorem officialConstructorEventScratch_eq :
    officialConstructorEventScratch = 4512 := by
  decide

/-- Heartbeat initialization through the constructor return, named at the
shape layer so every later execution proof shares one sealed tail. -/
def officialConstructorHeartbeatSuffix : Func :=
  pushB256 0 :::
  storeByteOffsetForProof officialConstructorEventScratch +++
  loadArgumentIndexForProof 6 +++
  storeByteOffsetForProof (officialConstructorEventScratch + 32) +++
  pushB256 heartbeatIntervalUpdatedEvent :::
  logWith 0
    (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
  loadArgumentIndexForProof 6 +++
  pushB256 heartbeatIntervalSlot ::: sstore :::
  pushFixedNatForProof 4282 :::
  pushCompactNatForProof constructorRuntimeBaseForProof :::
  Func.ret

/-- Pause-duration initialization before the shared heartbeat tail. -/
def officialConstructorConfigurationPrefix : Line :=
  [pushB256 0] ++
  storeByteOffsetForProof officialConstructorEventScratch ++
  loadArgumentIndexForProof 5 ++
  storeByteOffsetForProof (officialConstructorEventScratch + 32) ++
  [pushB256 pauseDurationUpdatedEvent] ++
  logWith 0 (Nat.toB256 (officialConstructorEventScratch / 32)) 2 ++
  loadArgumentIndexForProof 5 ++
  [pushB256 pauseDurationSlot, sstore]

/-- Both projected configuration writes and events, through return. -/
def officialConstructorConfigurationSuffix : Func :=
  officialConstructorConfigurationPrefix +++
    officialConstructorHeartbeatSuffix

/-- Initialized event prefix between the runtime patch line and configuration
initialization. -/
def officialConstructorInitializedPrefix : Line :=
  loadArgumentIndexForProof 0 ++
  [pushB256 circuitBreakerInitializedEvent] ++
  logWith 1 1 4

/-- The exact residual constructor body after all ten successful validation
branches have placed the runtime-copy operands on the stack. -/
def officialConstructorEffectBody : Func :=
  codecopy :::
    patchRuntimeLineForProof constructorRuntimeBaseForProof +++
    officialConstructorInitializedPrefix +++
    officialConstructorConfigurationSuffix

/-- The exact official length, decode, canonical-address, and nine validation
tree, ending at `officialConstructorEffectBody`. Its branches retain every
skipped error-arm call at the source position compiled by the constructor. -/
def officialConstructorValidationBody : Func :=
  pushFixedNatForProof 5122 ::: codesize ::: lt :::
  ((.call 1) <?>
    (pushCompactNatForProof 224 ::: pushFixedNatForProof 4898 ::: pushCompactNatForProof 0 :::
      codecopy :::
      loadArgumentIndexForProof 0 +++ checkNonAddress +++
      ((.call 1) <?>
        (loadArgumentIndexForProof 0 +++ iszero :::
          ((.call 2) <?>
            (loadArgumentIndexForProof 1 +++ iszero :::
              ((.call 3) <?>
                (loadArgumentIndexForProof 2 +++
                  loadArgumentIndexForProof 1 +++ gt :::
                  ((.call 4) <?>
                    (loadArgumentIndexForProof 3 +++ iszero :::
                      ((.call 5) <?>
                        (loadArgumentIndexForProof 4 +++
                          loadArgumentIndexForProof 3 +++ gt :::
                          ((.call 6) <?>
                            (loadArgumentIndexForProof 1 +++
                              loadArgumentIndexForProof 5 +++ lt :::
                              ((.call 7) <?>
                                (loadArgumentIndexForProof 2 +++
                                  loadArgumentIndexForProof 5 +++ gt :::
                                  ((.call 8) <?>
                                    (loadArgumentIndexForProof 3 +++
                                      loadArgumentIndexForProof 6 +++ lt :::
                                      ((.call 9) <?>
                                        (loadArgumentIndexForProof 4 +++
                                          loadArgumentIndexForProof 6 +++ gt :::
                                          ((.call 10) <?>
                                            (pushFixedNatForProof 4282 :::
                                              pushFixedNatForProof 616 :::
                                              pushCompactNatForProof
                                                constructorRuntimeBaseForProof :::
                                              officialConstructorEffectBody
                                            ))))))))))))))))))))))

/-- The body-pinned official validation/effect presentation is definitionally
the constructor source specialized to its certified 616/4,898/4,282 layout. -/
theorem constructorBody_official_eq :
    constructorBodyForProof 616 4898 4282 = officialConstructorValidationBody := by
  rfl

/-- The exact main function joins the nonpayable guard to the body-pinned
official validation tree; its untaken arm is the first `.call 1` site. -/
theorem lidoCircuitBreakerConstructorProgram_main_official :
    lidoCircuitBreakerConstructorProgram.main =
      callvalue ::: iszero :::
        (officialConstructorValidationBody <?> (.call 1)) := by
  rw [DeploymentProof.lidoCircuitBreakerConstructorProgram_eq,
    provisionalConstructorPrefix_length_exact,
    runtimeTemplateCode_length_exact]
  norm_num
  rw [constructorProgramForProof_eq, constructorBody_official_eq]

/-! ## Body-pinned validation and table-call layout -/

/-- Structural traversal of internal compiler-table call sites. These are
Blanc function-table calls, not external EVM `CALL` instructions. -/
def constructorTableCallIndices : Func → List Nat
  | .branch left right =>
      constructorTableCallIndices left ++ constructorTableCallIndices right
  | .last _ => []
  | .next _ rest => constructorTableCallIndices rest
  | .call index => [index]

/-- The outer nonpayability branch stores its direct error-table call in the
first branch arm because the successful selector is nonzero. -/
def constructorOuterErrorArmIndices : Func → List Nat
  | .next _ (.next _ (.branch (.call index) _)) => [index]
  | _ => []

/-- The length, canonical-address, and nine source validation branches store
their direct error-table call in the second arm because every successful
selector is zero. -/
def constructorValidationErrorArmIndices : Func → List Nat
  | .branch success (.call index) =>
      index :: constructorValidationErrorArmIndices success
  | .next _ rest => constructorValidationErrorArmIndices rest
  | _ => []

/-- Every internal call site in the exact constructor program, including its
call-free auxiliary error bodies. -/
def officialConstructorTableCallIndices : List Nat :=
  constructorOuterErrorArmIndices lidoCircuitBreakerConstructorProgram.main ++
    constructorValidationErrorArmIndices officialConstructorValidationBody ++
    (lidoCircuitBreakerConstructorProgram.aux.map
      constructorTableCallIndices).flatten

private theorem constructorValidationErrorArmIndices_prepend
    (line : Line) (rest : Func) :
    constructorValidationErrorArmIndices (line +++ rest) =
      constructorValidationErrorArmIndices rest := by
  induction line with
  | nil => rfl
  | cons _ line ih =>
      simp only [prepend, constructorValidationErrorArmIndices]
      exact ih

private theorem officialConstructorEffectBody_validationErrorArmIndices :
    constructorValidationErrorArmIndices officialConstructorEffectBody = [] := by
  unfold officialConstructorEffectBody officialConstructorConfigurationSuffix
    officialConstructorHeartbeatSuffix
  simp only [constructorValidationErrorArmIndices,
    constructorValidationErrorArmIndices_prepend, Func.ret]

private theorem officialConstructorValidationBody_errorArmIndices :
    constructorValidationErrorArmIndices officialConstructorValidationBody =
      [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  unfold officialConstructorValidationBody
  simp only [constructorValidationErrorArmIndices,
    constructorValidationErrorArmIndices_prepend,
    officialConstructorEffectBody_validationErrorArmIndices]

/-- The exact constructor's ten auxiliary error-table entries, in source
validation order after the bare revert entry. -/
theorem lidoCircuitBreakerConstructorProgram_aux_official :
    lidoCircuitBreakerConstructorProgram.aux =
      [Func.rev,
        constructorErrorForProof "AdminZero",
        constructorErrorForProof "MinPauseDurationZero",
        constructorErrorForProof "MinPauseDurationExceedsMax",
        constructorErrorForProof "MinHeartbeatIntervalZero",
        constructorErrorForProof "MinHeartbeatIntervalExceedsMax",
        constructorErrorForProof "PauseDurationBelowMin",
        constructorErrorForProof "PauseDurationAboveMax",
        constructorErrorForProof "HeartbeatIntervalBelowMin",
        constructorErrorForProof "HeartbeatIntervalAboveMax"] := by
  rfl

private theorem constructorTableCallIndices_constructorError (name : String) :
    constructorTableCallIndices (constructorErrorForProof name) = [] := by
  rw [constructorErrorForProof_eq]
  unfold Func.revSelector
  rfl

private theorem officialConstructorAuxTableCallIndices_empty :
    (lidoCircuitBreakerConstructorProgram.aux.map
      constructorTableCallIndices).flatten = [] := by
  rw [lidoCircuitBreakerConstructorProgram_aux_official]
  simp only [List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, constructorTableCallIndices, Func.rev,
    constructorTableCallIndices_constructorError, List.nil_append]

/-- The three source-position calls to table entry one and the single calls to
entries two through ten are all retained in exact program order. -/
theorem officialConstructorTableCallIndices_exact :
    officialConstructorTableCallIndices =
      [1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  unfold officialConstructorTableCallIndices
  rw [lidoCircuitBreakerConstructorProgram_main_official]
  simp only [constructorOuterErrorArmIndices,
    officialConstructorValidationBody_errorArmIndices,
    officialConstructorAuxTableCallIndices_empty, List.append_nil]
  rfl

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceImages.lean`. -/

/-! ## Named official memory images -/

def officialConstructorDecodedMemory : Mem :=
  Mem.empty.write 0 (abiEncodeConstructorArgs officialConstructorArgs)

def officialConstructorCopiedMemory : Mem :=
  officialConstructorDecodedMemory.write constructorRuntimeBaseForProof
    runtimeTemplateCode

def applyConstructorMemoryPatch
    (memory : Mem) (patch : ImmutablePatch) : Mem :=
  memory.write (constructorRuntimeBaseForProof + patch.offset) patch.value.toBytes

def applyConstructorImagePatch
    (image : Bytes) (patch : ImmutablePatch) : Bytes :=
  Bytes.writeAt image (constructorRuntimeBaseForProof + patch.offset)
    patch.value.toBytes

def officialConstructorDecodedImage : Bytes :=
  Bytes.writeAt [] 0 (abiEncodeConstructorArgs officialConstructorArgs)

def officialConstructorCopiedImage : Bytes :=
  Bytes.writeAt officialConstructorDecodedImage constructorRuntimeBaseForProof
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
    runtimeTemplateCode (32 * i.val) 32 constructorRuntimeBaseForProof (by
      rw [constructorRuntimeBaseForProof_eq]
      unfold constructorArgumentBytes
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

/-! Consolidated from `LidoCircuitBreakerDeploymentTracePatchCore.lean`. -/

theorem constructorPatchPair_runCompiled
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
      (loadArgumentIndexForProof i.val +++ storeByteOffsetForProof offset +++ rest) post := by
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
  simp only [loadArgumentIndexForProof_eq, storeByteOffsetForProof_eq,
    pushCompactNatForProof_eq, pushFixedNatForProof_eq, if_pos hoffset]
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

theorem ConstructorPatchInvariant.runCompiled_write
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
      (loadArgumentIndexForProof i.val +++ storeByteOffsetForProof offset +++ rest) post := by
  apply constructorPatchPair_runCompiled hoffset hpush h.memory_size hfit
  · rw [h.read_argument i, hvalue]
  · exact h.read_memory i
  · rfl
  · exact hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTracePatchRun1_4.lean`. -/

def officialConstructorPatchMemory1 : Mem :=
  officialConstructorCopiedMemory.write 398 officialParams.admin.toBytes

def officialConstructorPatchMemory2 : Mem :=
  officialConstructorPatchMemory1.write 1318 officialParams.admin.toBytes

def officialConstructorPatchMemory3 : Mem :=
  officialConstructorPatchMemory2.write 2057 officialParams.admin.toBytes

def officialConstructorPatchMemory4 : Mem :=
  officialConstructorPatchMemory3.write 2144 officialParams.admin.toBytes
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

def officialConstructorPatchInvariant4 :
    ConstructorPatchInvariant officialConstructorPatchMemory4 :=
  officialConstructorPatchInvariant3.write 2144 officialParams.admin
    (by decide) (by decide)

theorem officialConstructorPatchLine1_4_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory4, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorCopiedMemory, G + 44⟩)
      (loadArgumentIndexForProof 0 +++ storeByteOffsetForProof 398 +++
        loadArgumentIndexForProof 0 +++ storeByteOffsetForProof 1318 +++
        loadArgumentIndexForProof 0 +++ storeByteOffsetForProof 2057 +++
        loadArgumentIndexForProof 0 +++ storeByteOffsetForProof 2144 +++ rest) post := by
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

/-! Consolidated from `LidoCircuitBreakerDeploymentTracePatchRun5_8.lean`. -/

def officialConstructorPatchMemory5 : Mem :=
  officialConstructorPatchMemory4.write 441
    officialParams.minPauseDuration.toBytes

def officialConstructorPatchMemory6 : Mem :=
  officialConstructorPatchMemory5.write 937
    officialParams.minPauseDuration.toBytes

def officialConstructorPatchMemory7 : Mem :=
  officialConstructorPatchMemory6.write 482
    officialParams.maxPauseDuration.toBytes

def officialConstructorPatchMemory8 : Mem :=
  officialConstructorPatchMemory7.write 2185
    officialParams.maxPauseDuration.toBytes
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

def officialConstructorPatchInvariant8 :
    ConstructorPatchInvariant officialConstructorPatchMemory8 :=
  officialConstructorPatchInvariant7.write 2185
    officialParams.maxPauseDuration (by decide) (by decide)

theorem officialConstructorPatchLine5_8_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory8, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory4, G + 48⟩)
      (loadArgumentIndexForProof 1 +++ storeByteOffsetForProof 441 +++
        loadArgumentIndexForProof 1 +++ storeByteOffsetForProof 937 +++
        loadArgumentIndexForProof 2 +++ storeByteOffsetForProof 482 +++
        loadArgumentIndexForProof 2 +++ storeByteOffsetForProof 2185 +++ rest) post := by
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

/-! Consolidated from `LidoCircuitBreakerDeploymentTracePatchRun9_12.lean`. -/

def officialConstructorPatchMemory9 : Mem :=
  officialConstructorPatchMemory8.write 732
    officialParams.minHeartbeatInterval.toBytes

def officialConstructorPatchMemory10 : Mem :=
  officialConstructorPatchMemory9.write 1361
    officialParams.minHeartbeatInterval.toBytes

def officialConstructorPatchMemory11 : Mem :=
  officialConstructorPatchMemory10.write 896
    officialParams.maxHeartbeatInterval.toBytes

def officialConstructorPatchMemory12 : Mem :=
  officialConstructorPatchMemory11.write 1402
    officialParams.maxHeartbeatInterval.toBytes
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

def officialConstructorPatchInvariant12 :
    ConstructorPatchInvariant officialConstructorPatchMemory12 :=
  officialConstructorPatchInvariant11.write 1402
    officialParams.maxHeartbeatInterval (by decide) (by decide)

/-- Memory after the constructor's twelve source-ordered immutable writes. -/
def officialConstructorPatchedMemory : Mem :=
  officialConstructorPatchMemory12

def officialConstructorPatchedImage : Bytes :=
  officialConstructorPatchInvariant12.image

theorem officialConstructorPatchLine9_12_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory12, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchMemory8, G + 48⟩)
      (loadArgumentIndexForProof 3 +++ storeByteOffsetForProof 732 +++
        loadArgumentIndexForProof 3 +++ storeByteOffsetForProof 1361 +++
        loadArgumentIndexForProof 4 +++ storeByteOffsetForProof 896 +++
        loadArgumentIndexForProof 4 +++ storeByteOffsetForProof 1402 +++ rest) post := by
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

/-! Consolidated from `LidoCircuitBreakerDeploymentTracePatchEquivalence.lean`. -/

theorem officialConstructorPatchMemory12_eq_patched :
    officialConstructorPatchMemory12 = officialConstructorPatchedMemory := by
  rfl

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceMemory.lean`. -/

theorem officialConstructorPatchedMemory_size :
    officialConstructorPatchedMemory.size = 4512 := by
  exact officialConstructorPatchInvariant12.memory_size

/-! ## Memory/image correspondence -/

theorem officialConstructorPatchedMemory_wf :
    Mem.Wf officialConstructorPatchedMemory := by
  exact officialConstructorPatchInvariant12.memory_wf

theorem officialConstructorPatchedMemory_reads :
    Mem.Reads officialConstructorPatchedMemory
      officialConstructorPatchedImage := by
  exact officialConstructorPatchInvariant12.memory_reads

theorem officialConstructorPatchedMemory_read_argument
    (i : Fin 7) :
    Bytes.toB256
        ((officialConstructorPatchedMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  simpa only [officialConstructorPatchedMemory] using
    officialConstructorPatchInvariant12.read_argument i

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceFinalMemory.lean`. -/

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

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceRuntime.lean`. -/

private theorem officialConstructorFinalImage_runtime :
    officialConstructorFinalImage.sliceD constructorRuntimeBaseForProof 4282 0 =
      lidoCircuitBreakerCode officialParams := by
  rw [← patchRuntimeTemplate_official]
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [officialConstructorFinalImage, patchRuntimeTemplate,
    runtimeImmutablePatches, immutableParameters,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat,
    ImmutableParameter.value, constructorRuntimeBaseForProof]
  decide +kernel

/-- The final `RETURN` window reads the exact official runtime artifact. -/
theorem officialConstructorFinalMemory_read_runtime :
    (officialConstructorFinalMemory.read constructorRuntimeBaseForProof 4282).1 =
      lidoCircuitBreakerCode officialParams := by
  rw [Mem.Reads.read officialConstructorFinalMemory_reads]
  exact officialConstructorFinalImage_runtime

private theorem officialConstructorFinalMemory_read_memory :
    (officialConstructorFinalMemory.read constructorRuntimeBaseForProof 4282).2 =
      officialConstructorFinalMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorFinalMemory_size]
  · rw [officialConstructorFinalMemory_size]
    rw [constructorRuntimeBaseForProof_eq]
    unfold constructorArgumentBytes
    decide

/-- The terminal return window reads the exact runtime without extending the
named final memory. -/
theorem officialConstructorFinalMemory_read :
    officialConstructorFinalMemory.read constructorRuntimeBaseForProof 4282 =
      (lidoCircuitBreakerCode officialParams,
        officialConstructorFinalMemory) := by
  cases hread : officialConstructorFinalMemory.read
      constructorRuntimeBaseForProof 4282 with
  | mk out memory =>
      have hout : out = lidoCircuitBreakerCode officialParams := by
        simpa only [hread] using officialConstructorFinalMemory_read_runtime
      have hmemory : memory = officialConstructorFinalMemory := by
        simpa only [hread] using officialConstructorFinalMemory_read_memory
      simp only [hout, hmemory]

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsBase.lean`. -/

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

theorem Bytes.sliceD_writeAt_pair
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

theorem officialConstructorPatchedMemory_read_initializedData :
    (officialConstructorPatchedMemory.read 32 128).1 =
      officialParams.minPauseDuration.toBytes ++
        officialParams.maxPauseDuration.toBytes ++
        officialParams.minHeartbeatInterval.toBytes ++
        officialParams.maxHeartbeatInterval.toBytes := by
  rw [Mem.Reads.read officialConstructorPatchedMemory_reads]
  unfold officialConstructorPatchedImage
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

theorem officialConstructorPatchedMemory_read_initializedMemory :
    (officialConstructorPatchedMemory.read 32 128).2 =
      officialConstructorPatchedMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorPatchedMemory_size]
  · rw [officialConstructorPatchedMemory_size]
    decide

def officialConstructorColdStore
    (sevm : Sevm) (base : Devm) (key value : B256) : Devm :=
  (((addAccessedStorageKey base sevm.currentTarget key).withRefundCounter
    base.refundCounter).setStorVal sevm.currentTarget key value)

theorem officialConstructorColdStore_getStor
    (sevm : Sevm) (base : Devm) (key value : B256) :
    Devm.getStor (officialConstructorColdStore sevm base key value)
        sevm.currentTarget =
      (Devm.getStor base sevm.currentTarget).set key value := by
  unfold officialConstructorColdStore
  rw [setStorVal_getStor_self, Blanc.Devm.withRefundCounter_getStor,
    addAccessedStorageKey_getStor]

theorem officialConstructorColdStore_runCompiled
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
    · simp only [Devm.setMach, Devm.refundCounter, horiginal]
      simp [sstoreNewRefundCounter, hzeroValue]
    · simp only [Devm.gasLeft_setMach]
  · change Func.RunCompiled fs sevm
      ((officialConstructorColdStore sevm base key value).setMach
        ⟨[], memory, G⟩)
      rest post
    exact hrest

def officialConstructorInitializedBase
    (sevm : Sevm) (base : Devm) : Devm :=
  base.addLog (officialConstructorInitializedLog sevm.currentTarget)

def officialConstructorPauseLoggedBase
    (sevm : Sevm) (base : Devm) : Devm :=
  (officialConstructorInitializedBase sevm base).addLog
    (officialConstructorPauseLog sevm.currentTarget)

def officialConstructorPauseStoredBase
    (sevm : Sevm) (base : Devm) : Devm :=
  officialConstructorColdStore sevm
    (officialConstructorPauseLoggedBase sevm base)
    pauseDurationSlot officialConstructorArgs.initialPauseDuration

def officialConstructorHeartbeatLoggedBase
    (sevm : Sevm) (base : Devm) : Devm :=
  (officialConstructorPauseStoredBase sevm base).addLog
    (officialConstructorHeartbeatLog sevm.currentTarget)

/-- The non-machine constructor effects after the three logs and the two cold
zero-to-nonzero configuration writes, in exact source order. -/
def officialConstructorEffectBase (sevm : Sevm) (base : Devm) : Devm :=
  officialConstructorColdStore sevm
    (officialConstructorHeartbeatLoggedBase sevm base)
    heartbeatIntervalSlot officialConstructorArgs.initialHeartbeatInterval

theorem officialConstructorHeartbeatLoggedBase_getStor
    (sevm : Sevm) (base : Devm) :
    Devm.getStor (officialConstructorHeartbeatLoggedBase sevm base)
        sevm.currentTarget =
      (Devm.getStor base sevm.currentTarget).set pauseDurationSlot
        officialConstructorArgs.initialPauseDuration := by
  unfold officialConstructorHeartbeatLoggedBase
    officialConstructorPauseStoredBase
  rw [Blanc.Devm.addLog_getStor, officialConstructorColdStore_getStor]
  unfold officialConstructorPauseLoggedBase officialConstructorInitializedBase
  rw [Blanc.Devm.addLog_getStor, Blanc.Devm.addLog_getStor]

theorem officialConstructorPauseLoggedBase_accessedStorageKeys
    (sevm : Sevm) (base : Devm) :
    (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys =
      base.accessedStorageKeys := by
  rfl

theorem officialConstructorPauseLoggedBase_getStorVal
    (sevm : Sevm) (base : Devm) (a : Adr) (key : B256) :
    (officialConstructorPauseLoggedBase sevm base).getStorVal a key =
      base.getStorVal a key := by
  rfl

theorem officialConstructorHeartbeatLoggedBase_accessedStorageKeys
    (sevm : Sevm) (base : Devm) :
    (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys =
      base.accessedStorageKeys.insert
        (sevm.currentTarget, pauseDurationSlot) := by
  rfl

theorem not_mem_hashSet_insert {α : Type _} [BEq α] [Hashable α]
    [LawfulBEq α] {s : Std.HashSet α} {x p : α}
    (h : p ∉ s) (hne : x ≠ p) : p ∉ s.insert x := by
  intro hmem
  rcases Std.HashSet.mem_insert.mp hmem with he | hp
  · exact hne (eq_of_beq he)
  · exact h hp

/-- The constructor effect changes the target's persistent storage by exactly
the two source-ordered configuration writes. -/
theorem officialConstructorEffectBase_getStor
    (sevm : Sevm) (base : Devm) :
    Devm.getStor (officialConstructorEffectBase sevm base)
        sevm.currentTarget =
      ((Devm.getStor base sevm.currentTarget).set pauseDurationSlot
        officialConstructorArgs.initialPauseDuration).set
          heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval := by
  unfold officialConstructorEffectBase
  rw [officialConstructorColdStore_getStor,
    officialConstructorHeartbeatLoggedBase_getStor]

/-- The terminal return preserves the exact two-write storage effect. -/

private theorem constructorAddLog_logs (base : Devm) (log : Log) :
    (base.addLog log).logs = base.logs ++ [log] := by
  rfl

private theorem officialConstructorColdStore_logs
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (officialConstructorColdStore sevm base key value).logs = base.logs := by
  rfl

private theorem officialConstructorLogs_eq_named (ca : Adr) :
    officialConstructorLogs ca =
      [officialConstructorInitializedLog ca,
        officialConstructorPauseLog ca,
        officialConstructorHeartbeatLog ca] := by
  rfl

/-- The effect frame appends exactly the three constructor logs in source
order, preserving any incoming log prefix. -/
theorem officialConstructorEffectBase_logs
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).logs =
      base.logs ++ officialConstructorLogs sevm.currentTarget := by
  unfold officialConstructorEffectBase officialConstructorHeartbeatLoggedBase
    officialConstructorPauseStoredBase officialConstructorPauseLoggedBase
    officialConstructorInitializedBase
  simp only [constructorAddLog_logs, officialConstructorColdStore_logs,
    officialConstructorLogs_eq_named, List.append_assoc]
  rfl

/-- The terminal return preserves the exact ordered constructor logs. -/

theorem officialConstructorEffectBase_state
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).state =
      (base.state.setStorVal sevm.currentTarget pauseDurationSlot
        officialConstructorArgs.initialPauseDuration).setStorVal
          sevm.currentTarget heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval := by
  rfl

theorem officialConstructorEffectBase_refundCounter
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).refundCounter =
      base.refundCounter := by
  rfl

theorem officialConstructorEffectBase_returnData
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).returnData =
      base.returnData := by
  rfl

theorem officialConstructorEffectBase_error
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).error = base.error := by
  rfl

theorem officialConstructorEffectBase_accountsToDelete
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).accountsToDelete =
      base.accountsToDelete := by
  rfl

theorem officialConstructorEffectBase_createdAccounts
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).createdAccounts =
      base.createdAccounts := by
  rfl

theorem officialConstructorEffectBase_accessedAddresses
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).accessedAddresses =
      base.accessedAddresses := by
  rfl

theorem officialConstructorEffectBase_transientStorage
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).transientStorage =
      base.transientStorage := by
  rfl

theorem officialConstructorEffectBase_accessedStorageKeys
    (sevm : Sevm) (base : Devm) :
    (officialConstructorEffectBase sevm base).accessedStorageKeys =
      (base.accessedStorageKeys.insert
        (sevm.currentTarget, pauseDurationSlot)).insert
          (sevm.currentTarget, heartbeatIntervalSlot) := by
  rfl

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsBlocks.lean`. -/

/-- Prepend an in-bounds constructor argument load and a three-gas key push to
an already-certified `SSTORE` continuation. Concrete deployment memory stays
outside this declaration; callers provide only its named read certificate. -/
theorem constructorArgumentSstorePrefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {i : Fin 7} {key value : B256} {memory : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter + 9)
    (hloadPush : pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = 3)
    (hkeyPush : pushCost key.toBytes.sig = 3)
    (h32 : memory.size % 32 = 0)
    (hwindow : 32 * i.val + 32 ≤ memory.size)
    (hvalue : Bytes.toB256 ((memory.read (32 * i.val) 32).1) = value)
    (hmemory : (memory.read (32 * i.val) 32).2 = memory)
    (hstore : Func.RunCompiled fs sevm
      (base.setMach ⟨[key, value], memory, Gafter⟩)
      (sstore ::: rest) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (loadArgumentIndexForProof i.val +++
        pushB256 key ::: sstore ::: rest) post := by
  rw [hgas]
  have hindexBound : 32 * i.val < 2 ^ 256 := by
    apply Nat.lt_trans (show 32 * i.val < 224 by
      have hi := i.isLt
      omega)
    decide
  have hindex : (Nat.toB256 (32 * i.val)).toNat = 32 * i.val :=
    B256.toNat_toB256_of_lt hindexBound
  rw [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter + 6)
      hloadPush
    · simp only [Devm.gasLeft_setMach]
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * i.val))
          (v := value) (s := []) (M := memory)
          (c := 3) (G := Gafter + 3)
      · simp only [Devm.stack_setMach]
      · simp only [Devm.memory_setMach, hindex]
        rw [Devm.extCost_zero_of_le (N := memory) h32 hwindow]
        decide
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
      · simp only [List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter)
          hkeyPush
        · simp only [Devm.gasLeft_setMach]
        · simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
      · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hstore

/-- Execute the deployment's 64-byte, one-topic event opcode from named
memory-read and continuation certificates. The concrete memory image and event
payload remain abstract at applications of this theorem. -/
theorem constructorEventLog1Opcode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {topic : B256} {data : Bytes} {memory : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter + 1262)
    (h32 : memory.size % 32 = 0)
    (hwindow : officialConstructorEventScratch + 64 ≤ memory.size)
    (hdata : (memory.read officialConstructorEventScratch 64).1 = data)
    (hmemory : (memory.read officialConstructorEventScratch 64).2 = memory)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((base.addLog ⟨sevm.currentTarget, [topic], data⟩).setMach
        ⟨[], memory, Gafter⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[Nat.toB256 (officialConstructorEventScratch / 32) * 32,
            (2 : B256) * 32, topic], memory, Gbefore⟩)
      (Ninst.log (Fin.succ 0) ::: rest) post := by
  rw [hgas]
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
        (topics := [topic]) (s := [])
        (c := 1262) (G := Gafter) (M := memory) (data := data)
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
      ((base.addLog ⟨sevm.currentTarget, [topic], data⟩).setMach
        ⟨[], memory, Gafter⟩)
      rest post
    exact hrest

/-- Prepend the event topic and the two `logWith` operands to an already
certified one-topic event opcode. -/
theorem constructorEventLog1Prefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {topic : B256} {memory : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter + 9)
    (htopicPush : pushCost topic.toBytes.sig = 3)
    (hlog : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[Nat.toB256 (officialConstructorEventScratch / 32) * 32,
            (2 : B256) * 32, topic], memory, Gafter⟩)
      (Ninst.log (Fin.succ 0) ::: rest) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (pushB256 topic :::
        logWith 0
          (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
        rest) post := by
  rw [hgas]
  unfold logWith
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter + 6)
      htopicPush
    · simp only [Devm.gasLeft_setMach]
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter + 3)
      · decide
      · simp only [Devm.gasLeft_setMach]
      · simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter)
        · rw [officialConstructorEventScratch_eq]
          decide
        · simp only [Devm.gasLeft_setMach]
        · simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
      · simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hlog

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsBlocksMemory.lean`. -/

/-- Load one constructor argument and store it at a fixed two-byte memory
coordinate. Read, write, and expansion behavior are supplied as abstract
certificates, so the theorem never normalizes a concrete deployment image. -/
theorem constructorArgumentMstorePrefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {i : Fin 7} {offset indexPushCost loadCost storeExt : Nat}
    {value : B256} {memory memory' : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hoffsetLt : offset < 2 ^ 16)
    (hgas : Gbefore =
      Gafter + (indexPushCost + loadCost + 6 + storeExt))
    (hindexPush :
      pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = indexPushCost)
    (hloadCost : ∀ (S : List B256) (G : Nat),
      gVerylow +
        (base.setMach ⟨S, memory, G⟩).extCost
          [⟨32 * i.val, 32⟩] = loadCost)
    (hvalue : Bytes.toB256 ((memory.read (32 * i.val) 32).1) = value)
    (hmemory : (memory.read (32 * i.val) 32).2 = memory)
    (hstoreExt : ∀ (S : List B256) (G : Nat),
      (base.setMach ⟨S, memory, G⟩).extCost [⟨offset, 32⟩] = storeExt)
    (hwrite : memory.write offset value.toBytes = memory')
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory', Gafter⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (loadArgumentIndexForProof i.val +++
        storeByteOffsetForProof offset +++ rest) post := by
  rw [hgas]
  have hindexBound : 32 * i.val < 2 ^ 256 := by
    apply Nat.lt_trans (show 32 * i.val < 224 by
      have hi := i.isLt
      omega)
    decide
  have hindex : (Nat.toB256 (32 * i.val)).toNat = 32 * i.val :=
    B256.toNat_toB256_of_lt hindexBound
  have hoffsetBound : offset < 2 ^ 256 :=
    Nat.lt_trans hoffsetLt (by decide)
  have hoffsetNat :
      (Bytes.toB256
        [(offset >>> 8).toUInt8, offset.toUInt8]).toNat = offset := by
    rw [List.toB256_pair offset hoffsetLt]
    exact B256.toNat_toB256_of_lt hoffsetBound
  simp only [loadArgumentIndexForProof_eq, storeByteOffsetForProof_eq,
    pushCompactNatForProof_eq, pushFixedNatForProof_eq, if_pos hoffsetLt]
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256
        (c := indexPushCost)
        (G := Gafter + (loadCost + 6 + storeExt))
        hindexPush
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * i.val))
          (v := value) (s := []) (M := memory)
          (c := loadCost) (G := Gafter + (6 + storeExt))
      · simp only [Devm.stack_setMach]
      · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach, hindex] using
          hloadCost [Nat.toB256 (32 * i.val)]
            (Gafter + (loadCost + 6 + storeExt))
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushBytes
            (c := 3) (G := Gafter + (3 + storeExt))
        · rfl
        · simp only [Devm.gasLeft_setMach]
          omega
        · simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
      · apply Func.RunCompiled.next
        · apply Ninst.runCompiled_mstore_of
              (i := Bytes.toB256
                [(offset >>> 8).toUInt8, offset.toUInt8])
              (v := value) (s := []) (G := Gafter)
              (e := storeExt) (M := memory')
          · simp only [Devm.stack_setMach]
          · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
              Devm.memory_setMach, Devm.gasLeft_setMach,
              hoffsetNat] using
              hstoreExt
                [Bytes.toB256
                  [(offset >>> 8).toUInt8, offset.toUInt8], value]
                (Gafter + (3 + storeExt))
          · simp only [Devm.gasLeft_setMach, gVerylow]
          · simpa only [Devm.memory_setMach, hoffsetNat] using hwrite
        · simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach] using hrest

/-- Store a zero word at a fixed two-byte memory coordinate. The expansion
charge is named by the caller, covering both in-bounds and extending writes. -/
theorem constructorZeroMstorePrefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {offset storeExt : Nat} {memory memory' : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hoffsetLt : offset < 2 ^ 16)
    (hgas : Gbefore = Gafter + (8 + storeExt))
    (hstoreExt : ∀ (S : List B256) (G : Nat),
      (base.setMach ⟨S, memory, G⟩).extCost [⟨offset, 32⟩] = storeExt)
    (hwrite : memory.write offset (0 : B256).toBytes = memory')
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory', Gafter⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (pushB256 0 ::: storeByteOffsetForProof offset +++ rest) post := by
  rw [hgas]
  have hoffsetBound : offset < 2 ^ 256 :=
    Nat.lt_trans hoffsetLt (by decide)
  have hoffsetNat :
      (Bytes.toB256
        [(offset >>> 8).toUInt8, offset.toUInt8]).toNat = offset := by
    rw [List.toB256_pair offset hoffsetLt]
    exact B256.toNat_toB256_of_lt hoffsetBound
  simp only [storeByteOffsetForProof_eq, pushFixedNatForProof_eq,
    if_pos hoffsetLt]
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 2)
        (G := Gafter + (6 + storeExt))
    · simpa only [gBase] using pushCost_zero
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_pushBytes
          (c := 3) (G := Gafter + (3 + storeExt))
      · rfl
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_mstore_of
            (i := Bytes.toB256
              [(offset >>> 8).toUInt8, offset.toUInt8])
            (v := 0) (s := []) (G := Gafter)
            (e := storeExt) (M := memory')
        · simp only [Devm.stack_setMach]
        · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach, Devm.gasLeft_setMach,
            hoffsetNat] using
            hstoreExt
              [Bytes.toB256
                [(offset >>> 8).toUInt8, offset.toUInt8], 0]
              (Gafter + (3 + storeExt))
        · simp only [Devm.gasLeft_setMach, gVerylow]
        · simpa only [Devm.memory_setMach, hoffsetNat] using hwrite
      · simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsBlocksLog2.lean`. -/

/-- Execute the deployment's 128-byte, two-topic initialized event from named
memory-read and continuation certificates. The concrete memory image and event
payload remain abstract at applications of this theorem. -/
theorem constructorEventLog2Opcode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {topic0 topic1 : B256} {data : Bytes} {memory : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter + 2149)
    (h32 : memory.size % 32 = 0)
    (hwindow : 32 + 128 ≤ memory.size)
    (hdata : (memory.read 32 128).1 = data)
    (hmemory : (memory.read 32 128).2 = memory)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((base.addLog ⟨sevm.currentTarget, [topic0, topic1], data⟩).setMach
        ⟨[], memory, Gafter⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(1 : B256) * 32, (4 : B256) * 32, topic0, topic1],
          memory, Gbefore⟩)
      (Ninst.log (Fin.succ 1) ::: rest) post := by
  rw [hgas]
  have hi : ((1 : B256) * 32).toNat = 32 := by decide
  have hsz : ((4 : B256) * 32).toNat = 128 := by decide
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_log_of
        (n := Fin.succ 1)
        (i := (1 : B256) * 32) (sz := (4 : B256) * 32)
        (topics := [topic0, topic1]) (s := [])
        (c := 2149) (G := Gafter) (M := memory) (data := data)
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
      ((base.addLog ⟨sevm.currentTarget, [topic0, topic1], data⟩).setMach
        ⟨[], memory, Gafter⟩)
      rest post
    exact hrest

/-- Load one constructor argument as the indexed topic, push an event topic,
and prepare the fixed 128-byte initialized-event `LOG2`. Concrete memory is
represented only by read and charge certificates. -/
theorem constructorArgumentLog2Prefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {i : Fin 7} {eventTopic indexedTopic : B256} {memory : Mem}
    {indexPushCost loadCost eventPushCost : Nat}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter +
      (indexPushCost + loadCost + eventPushCost + 6))
    (hindexPush :
      pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = indexPushCost)
    (hloadCost : ∀ (S : List B256) (G : Nat),
      gVerylow +
        (base.setMach ⟨S, memory, G⟩).extCost
          [⟨32 * i.val, 32⟩] = loadCost)
    (hvalue :
      Bytes.toB256 ((memory.read (32 * i.val) 32).1) = indexedTopic)
    (hmemory : (memory.read (32 * i.val) 32).2 = memory)
    (heventPush : pushCost eventTopic.toBytes.sig = eventPushCost)
    (hlog : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(1 : B256) * 32, (4 : B256) * 32,
            eventTopic, indexedTopic], memory, Gafter⟩)
      (Ninst.log (Fin.succ 1) ::: rest) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (loadArgumentIndexForProof i.val +++
        pushB256 eventTopic ::: logWith 1 1 4 +++ rest) post := by
  rw [hgas]
  have hindexBound : 32 * i.val < 2 ^ 256 := by
    apply Nat.lt_trans (show 32 * i.val < 224 by
      have hi := i.isLt
      omega)
    decide
  have hindex : (Nat.toB256 (32 * i.val)).toNat = 32 * i.val :=
    B256.toNat_toB256_of_lt hindexBound
  unfold logWith
  rw [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256
        (c := indexPushCost)
        (G := Gafter + (loadCost + eventPushCost + 6))
        hindexPush
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * i.val))
          (v := indexedTopic) (s := []) (M := memory)
          (c := loadCost) (G := Gafter + (eventPushCost + 6))
      · simp only [Devm.stack_setMach]
      · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach, hindex] using
          hloadCost [Nat.toB256 (32 * i.val)]
            (Gafter + (loadCost + eventPushCost + 6))
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushB256
            (c := eventPushCost) (G := Gafter + 6) heventPush
        · simp only [Devm.gasLeft_setMach]
          omega
        · simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
      · apply Func.RunCompiled.next
        · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter + 3)
          · decide
          · simp only [Devm.gasLeft_setMach]
          · simp only [Devm.stack_setMach, List.length_cons,
              List.length_nil]
            omega
        · apply Func.RunCompiled.next
          · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter)
            · decide
            · simp only [Devm.gasLeft_setMach]
            · simp only [Devm.stack_setMach, List.length_cons,
                List.length_nil]
              omega
          · simpa only [prepend, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using hlog

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsReturn.lean`. -/

private def officialConstructorReturnPre
    (sevm : Sevm) (base : Devm) (G : Nat) : Devm :=
  (officialConstructorEffectBase sevm base).setMach
    ⟨[Nat.toB256 constructorRuntimeBaseForProof, (4282 : B256)],
      officialConstructorFinalMemory, G⟩

private def officialConstructorReturnRead
    (sevm : Sevm) (base : Devm) (G : Nat) : Bytes × Devm :=
  let pre := officialConstructorReturnPre sevm base G
  (pre.setMach ⟨[], pre.memory, G⟩).memRead constructorRuntimeBaseForProof 4282

/-- Exact successful constructor post-frame at its final remaining gas. -/
def officialConstructorPost
    (sevm : Sevm) (base : Devm) (G : Nat) : Devm :=
  let returned := officialConstructorReturnRead sevm base G
  returned.2.withOutput returned.1

private theorem withMemory_setMach_same
    (base : Devm) (stack : List B256) (memory : Mem) (gas : Nat) :
    (base.setMach ⟨stack, memory, gas⟩).withMemory memory =
      base.setMach ⟨stack, memory, gas⟩ := by
  rfl

private theorem memRead_setMach_of_read
    (base : Devm) (stack : List B256) (memory : Mem)
    (gas i sz : Nat) (output : Bytes)
    (hread : memory.read i sz = (output, memory)) :
    let pre := base.setMach ⟨stack, memory, gas⟩
    (pre.setMach ⟨[], pre.memory, gas⟩).memRead i sz =
      (output, base.setMach ⟨[], memory, gas⟩) := by
  dsimp only
  unfold Devm.memRead
  simp only [Devm.memory_setMach]
  rw [hread]
  simp only [withMemory_setMach_same, Devm.setMach_setMach]

private theorem officialConstructorReturnRead_eq
    (sevm : Sevm) (base : Devm) (G : Nat) :
    officialConstructorReturnRead sevm base G =
      (lidoCircuitBreakerCode officialParams,
        (officialConstructorEffectBase sevm base).setMach
          ⟨[], officialConstructorFinalMemory, G⟩) := by
  unfold officialConstructorReturnRead officialConstructorReturnPre
  exact memRead_setMach_of_read
    (base := officialConstructorEffectBase sevm base)
    (stack := [Nat.toB256 constructorRuntimeBaseForProof, (4282 : B256)])
    (memory := officialConstructorFinalMemory) (gas := G)
    (i := constructorRuntimeBaseForProof) (sz := 4282)
    (output := lidoCircuitBreakerCode officialParams)
    officialConstructorFinalMemory_read

/-- The exact constructor post-frame is the named two-write/three-log effect
frame with empty stack, final memory, residual gas, and official runtime
output. -/
theorem officialConstructorPost_eq
    (sevm : Sevm) (base : Devm) (G : Nat) :
    officialConstructorPost sevm base G =
      ((officialConstructorEffectBase sevm base).setMach
        ⟨[], officialConstructorFinalMemory, G⟩).withOutput
          (lidoCircuitBreakerCode officialParams) := by
  unfold officialConstructorPost
  rw [officialConstructorReturnRead_eq]

theorem officialConstructorReturnLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[Nat.toB256 constructorRuntimeBaseForProof, (4282 : B256)], memory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 6⟩)
      (pushFixedNatForProof 4282 :::
        pushCompactNatForProof constructorRuntimeBaseForProof ::: rest) post := by
  simp only [pushFixedNatForProof_eq, pushCompactNatForProof_eq,
    if_pos (show 4282 < 2 ^ 16 by decide)]
  func_run (2)
  exact hrest

theorem officialConstructorReturn_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat} :
    Func.RunCompiled fs sevm
      (officialConstructorReturnPre sevm base G) Func.ret
      (officialConstructorPost sevm base G) := by
  have hindex : (Nat.toB256 constructorRuntimeBaseForProof).toNat =
      constructorRuntimeBaseForProof := by
    apply B256.toNat_toB256_of_lt
    rw [constructorRuntimeBaseForProof_eq]
    unfold constructorArgumentBytes
    decide
  have hstack : (officialConstructorReturnPre sevm base G).stack =
      [Nat.toB256 constructorRuntimeBaseForProof, (4282 : B256)] := by
    simp only [officialConstructorReturnPre, Devm.stack_setMach]
  have hext : (officialConstructorReturnPre sevm base G).extCost
      [⟨constructorRuntimeBaseForProof, 4282⟩] = 0 := by
    unfold officialConstructorReturnPre
    exact Devm.extCost_zero_of_le
      (N := officialConstructorFinalMemory)
      (i := constructorRuntimeBaseForProof) (sz := 4282)
      (by rw [officialConstructorFinalMemory_size])
      (by
        rw [officialConstructorFinalMemory_size]
        rw [constructorRuntimeBaseForProof_eq]
        unfold constructorArgumentBytes
        decide)
  have hgas : (officialConstructorReturnPre sevm base G).gasLeft =
      G + (officialConstructorReturnPre sevm base G).extCost
        [⟨(Nat.toB256 constructorRuntimeBaseForProof).toNat,
          (4282 : B256).toNat⟩] := by
    rw [hindex, show (4282 : B256).toNat = 4282 by decide, hext]
    simp only [officialConstructorReturnPre, Devm.gasLeft_setMach, Nat.add_zero]
  have hread :
      ((officialConstructorReturnPre sevm base G).setMach
        ⟨[], (officialConstructorReturnPre sevm base G).memory, G⟩).memRead
          (Nat.toB256 constructorRuntimeBaseForProof).toNat (4282 : B256).toNat =
        officialConstructorReturnRead sevm base G := by
    unfold officialConstructorReturnRead
    rw [hindex, show (4282 : B256).toNat = 4282 by decide]
  have hrun := Func.runCompiled_ret
    (fs := fs) (sevm := sevm)
    (devm := officialConstructorReturnPre sevm base G)
    (i := Nat.toB256 constructorRuntimeBaseForProof) (sz := (4282 : B256))
    (s := []) (out := (officialConstructorReturnRead sevm base G).1)
    (d' := (officialConstructorReturnRead sevm base G).2) (G := G)
    hstack hgas (by simpa only [Prod.eta] using hread)
  simpa only [officialConstructorPost, Func.ret] using hrun

/-! ## Composed constructor effect suffix -/

theorem officialConstructorPost_getStor
    (sevm : Sevm) (base : Devm) (G : Nat) :
    Devm.getStor (officialConstructorPost sevm base G)
        sevm.currentTarget =
      ((Devm.getStor base sevm.currentTarget).set pauseDurationSlot
        officialConstructorArgs.initialPauseDuration).set
          heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval := by
  rw [officialConstructorPost_eq]
  change Devm.getStor (officialConstructorEffectBase sevm base)
    sevm.currentTarget = _
  exact officialConstructorEffectBase_getStor sevm base

/-- The official pause duration is readable in the raw constructor post-frame. -/
theorem officialConstructorPost_pauseDuration
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).getStorVal
        sevm.currentTarget pauseDurationSlot =
      officialConstructorArgs.initialPauseDuration := by
  change (Devm.getStor (officialConstructorPost sevm base G)
    sevm.currentTarget).get pauseDurationSlot = _
  rw [officialConstructorPost_getStor,
    Stor.get_set_ne _
      (show heartbeatIntervalSlot ≠ pauseDurationSlot by decide),
    Stor.get_set_self]

/-- The official heartbeat interval is readable in the raw constructor
post-frame. -/
theorem officialConstructorPost_heartbeatInterval
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).getStorVal
        sevm.currentTarget heartbeatIntervalSlot =
      officialConstructorArgs.initialHeartbeatInterval := by
  change (Devm.getStor (officialConstructorPost sevm base G)
    sevm.currentTarget).get heartbeatIntervalSlot = _
  rw [officialConstructorPost_getStor, Stor.get_set_self]

theorem officialConstructorPost_logs
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).logs =
      base.logs ++ officialConstructorLogs sevm.currentTarget := by
  rw [officialConstructorPost_eq]
  rw [Devm.withOutput_logs, Devm.setMach_logs]
  exact officialConstructorEffectBase_logs sevm base

/-- The successful constructor returns with an empty stack. -/
theorem officialConstructorPost_stack
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).stack = [] := by
  rw [officialConstructorPost_eq]
  rfl

/-- The successful constructor retains the exact named final memory. -/
theorem officialConstructorPost_memory
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).memory =
      officialConstructorFinalMemory := by
  rw [officialConstructorPost_eq, Devm.withOutput_memory, Devm.setMach_memory]

/-- `G` is the exact residual gas after the 50,329-gas compiled run. -/
theorem officialConstructorPost_gasLeft
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).gasLeft = G := by
  rw [officialConstructorPost_eq]
  rfl

/-- The constructor's terminal output is the exact official runtime artifact. -/
theorem officialConstructorPost_output
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).output =
      lidoCircuitBreakerCode officialParams := by
  rw [officialConstructorPost_eq, Devm.withOutput_output]

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsHeartbeatSstore.lean`. -/

private theorem officialConstructorHeartbeatStore_eq_effectBase
    (sevm : Sevm) (base : Devm) :
    officialConstructorColdStore sevm
        (officialConstructorHeartbeatLoggedBase sevm base)
        heartbeatIntervalSlot
        officialConstructorArgs.initialHeartbeatInterval =
      officialConstructorEffectBase sevm base := by
  rfl

theorem officialConstructorHeartbeatSstore_runCompiled
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

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsHeartbeatStore.lean`. -/

private theorem officialConstructorHeartbeatMemory_size_mod :
    officialConstructorHeartbeatMemory.size % 32 = 0 := by
  rw [officialConstructorHeartbeatMemory_size]

private theorem officialConstructorHeartbeatMemory_argument_window :
    192 + 32 ≤ officialConstructorHeartbeatMemory.size := by
  rw [officialConstructorHeartbeatMemory_size]
  decide

private theorem officialConstructorHeartbeatMemory_read_initialInterval :
    Bytes.toB256 ((officialConstructorHeartbeatMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
  simpa [officialConstructorArgumentWord] using
    officialConstructorHeartbeatMemory_read_argument ⟨6, by decide⟩

private theorem officialConstructorHeartbeatMemory_read_same :
    (officialConstructorHeartbeatMemory.read 192 32).2 =
      officialConstructorHeartbeatMemory := by
  simpa using officialConstructorHeartbeatMemory_read_argument_memory
    ⟨6, by decide⟩

theorem officialConstructorHeartbeatStoreLine_runCompiled
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
      (loadArgumentIndexForProof 6 +++
        pushB256 heartbeatIntervalSlot ::: sstore ::: rest) post := by
  apply constructorArgumentSstorePrefix_runCompiled
      (i := ⟨6, by decide⟩)
      (value := officialConstructorArgs.initialHeartbeatInterval)
      (Gafter := G + 22100)
  · omega
  · decide
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := heartbeatIntervalSlot) (by decide +kernel)
  · exact officialConstructorHeartbeatMemory_size_mod
  · exact officialConstructorHeartbeatMemory_argument_window
  · exact officialConstructorHeartbeatMemory_read_initialInterval
  · exact officialConstructorHeartbeatMemory_read_same
  · exact officialConstructorHeartbeatSstore_runCompiled
      hcold horiginal hcurrent hstatic hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLogOpcode.lean`. -/

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

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsHeartbeatLog.lean`. -/

theorem officialConstructorHeartbeatLogLine_runCompiled
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
  apply constructorEventLog1Prefix_runCompiled
      (topic := heartbeatIntervalUpdatedEvent)
      (Gafter := G + 1262)
  · omega
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := heartbeatIntervalUpdatedEvent) (by decide +kernel)
  · exact officialConstructorHeartbeatLogOpcode_runCompiled hstatic hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratchValue.lean`. -/

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
      (loadArgumentIndexForProof 6 +++
        storeByteOffsetForProof (officialConstructorEventScratch + 32) +++
        rest) post := by
  apply constructorArgumentMstorePrefix_runCompiled
    (i := ⟨6, by decide⟩)
    (offset := officialConstructorEventScratch + 32)
    (indexPushCost := 3) (loadCost := 3) (storeExt := 0)
    (memory' := officialConstructorHeartbeatMemory)
    (value := officialConstructorArgs.initialHeartbeatInterval)
    (Gafter := G)
  · rw [officialConstructorEventScratch_eq]
    decide
  · omega
  · decide
  · intro S G'
    change gVerylow +
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨S, officialConstructorHeartbeatZeroMemory, G'⟩).extCost
          [⟨192, 32⟩] = 3
    rw [Devm.extCost_zero_of_le
      (N := officialConstructorHeartbeatZeroMemory)
      (i := 192) (sz := 32)
      officialConstructorHeartbeatZeroMemory_size_mod
      officialConstructorHeartbeatZeroMemory_load_window]
    rfl
  · exact officialConstructorHeartbeatZeroMemory_read_initialInterval
  · exact officialConstructorHeartbeatZeroMemory_read_same
  · intro S G'
    exact Devm.extCost_zero_of_le
      (N := officialConstructorHeartbeatZeroMemory)
      (i := officialConstructorEventScratch + 32) (sz := 32)
      officialConstructorHeartbeatZeroMemory_size_mod
      officialConstructorHeartbeatZeroMemory_store_window
  · exact officialConstructorHeartbeatZeroMemory_write_initialInterval
  · exact hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratchZero.lean`. -/

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
        storeByteOffsetForProof officialConstructorEventScratch +++ rest) post := by
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

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratch.lean`. -/

theorem officialConstructorHeartbeatScratchLine_runCompiled
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
        storeByteOffsetForProof officialConstructorEventScratch +++
        loadArgumentIndexForProof 6 +++
        storeByteOffsetForProof (officialConstructorEventScratch + 32) +++
        rest) post := by
  have hvalue := officialConstructorHeartbeatScratchValue_runCompiled hrest
  exact officialConstructorHeartbeatScratchZero_runCompiled hvalue

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsHeartbeatSuffix.lean`. -/

theorem officialConstructorHeartbeatSuffix_runCompiled
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
  convert hscratch using 1

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsConfigurationStore.lean`. -/

private theorem officialConstructorPauseMemory_size_mod_store :
    officialConstructorPauseMemory.size % 32 = 0 := by
  rw [officialConstructorPauseMemory_size]

private theorem officialConstructorPauseMemory_argument_window :
    160 + 32 ≤ officialConstructorPauseMemory.size := by
  rw [officialConstructorPauseMemory_size]
  decide

private theorem officialConstructorPauseMemory_read_initialDuration :
    Bytes.toB256 ((officialConstructorPauseMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
  simpa [officialConstructorArgumentWord] using
    officialConstructorPauseMemory_read_argument ⟨5, by decide⟩

private theorem officialConstructorPauseMemory_read_same_store :
    (officialConstructorPauseMemory.read 160 32).2 =
      officialConstructorPauseMemory := by
  simpa using officialConstructorPauseMemory_read_argument_memory
    ⟨5, by decide⟩

private theorem officialConstructorPauseSstore_runCompiled
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
        ⟨[pauseDurationSlot, officialConstructorArgs.initialPauseDuration],
          officialConstructorPauseMemory, G + 22100⟩)
      (sstore ::: rest) post := by
  have hrest' : Func.RunCompiled fs sevm
      ((officialConstructorColdStore sevm
          (officialConstructorPauseLoggedBase sevm base)
          pauseDurationSlot
          officialConstructorArgs.initialPauseDuration).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post := by
    simpa only [officialConstructorPauseStoredBase] using hrest
  exact officialConstructorColdStore_runCompiled
    hcold horiginal hcurrent
    (by unfold officialConstructorArgs; decide)
    (by simp only [gCallStipend]; omega) hstatic hrest'

theorem officialConstructorPauseStoreLine_runCompiled
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
      (loadArgumentIndexForProof 5 +++
        pushB256 pauseDurationSlot ::: sstore ::: rest) post := by
  apply constructorArgumentSstorePrefix_runCompiled
      (i := ⟨5, by decide⟩)
      (value := officialConstructorArgs.initialPauseDuration)
      (Gafter := G + 22100)
  · omega
  · decide
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := pauseDurationSlot) (by decide +kernel)
  · exact officialConstructorPauseMemory_size_mod_store
  · exact officialConstructorPauseMemory_argument_window
  · exact officialConstructorPauseMemory_read_initialDuration
  · exact officialConstructorPauseMemory_read_same_store
  · exact officialConstructorPauseSstore_runCompiled
      hcold horiginal hcurrent hstatic hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsConfigurationLog.lean`. -/

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

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratchValue.lean`. -/

private theorem officialConstructorPauseZeroMemory_size_mod :
    officialConstructorPauseZeroMemory.size % 32 = 0 := by
  rw [officialConstructorPauseZeroMemory_size]

private theorem officialConstructorPauseZeroMemory_load_window :
    160 + 32 ≤ officialConstructorPauseZeroMemory.size := by
  rw [officialConstructorPauseZeroMemory_size]
  decide

private theorem officialConstructorPauseZeroMemory_read_initialDuration :
    Bytes.toB256 ((officialConstructorPauseZeroMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
  simpa [officialConstructorArgumentWord] using
    officialConstructorPauseZeroMemory_read_argument ⟨5, by decide⟩

private theorem officialConstructorPauseZeroMemory_read_same :
    (officialConstructorPauseZeroMemory.read 160 32).2 =
      officialConstructorPauseZeroMemory := by
  simpa using officialConstructorPauseZeroMemory_read_argument_memory
    ⟨5, by decide⟩

private theorem officialConstructorPauseZeroMemory_write_initialDuration :
    officialConstructorPauseZeroMemory.write
        (officialConstructorEventScratch + 32)
        officialConstructorArgs.initialPauseDuration.toBytes =
      officialConstructorPauseMemory := by
  rfl

theorem officialConstructorPauseScratchValue_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseZeroMemory, G + 15⟩)
      (loadArgumentIndexForProof 5 +++
        storeByteOffsetForProof (officialConstructorEventScratch + 32) +++
        rest) post := by
  apply constructorArgumentMstorePrefix_runCompiled
      (i := ⟨5, by decide⟩)
      (offset := officialConstructorEventScratch + 32)
      (indexPushCost := 3) (loadCost := 3) (storeExt := 3)
      (memory' := officialConstructorPauseMemory)
      (value := officialConstructorArgs.initialPauseDuration)
      (Gafter := G)
  · rw [officialConstructorEventScratch_eq]
    decide
  · omega
  · decide
  · intro S G'
    change gVerylow +
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨S, officialConstructorPauseZeroMemory, G'⟩).extCost
          [⟨160, 32⟩] = 3
    rw [Devm.extCost_zero_of_le
      (N := officialConstructorPauseZeroMemory)
      (i := 160) (sz := 32)
      officialConstructorPauseZeroMemory_size_mod
      officialConstructorPauseZeroMemory_load_window]
    rfl
  · exact officialConstructorPauseZeroMemory_read_initialDuration
  · exact officialConstructorPauseZeroMemory_read_same
  · intro S G'
    exact Devm.extCost_of_size officialConstructorPauseZeroMemory_size (by
      rw [officialConstructorEventScratch_eq]
      decide +kernel)
  · exact officialConstructorPauseZeroMemory_write_initialDuration
  · exact hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratchZero.lean`. -/

private theorem officialConstructorPatchedMemory_write_pause_zero :
    officialConstructorPatchedMemory.write
        officialConstructorEventScratch (0 : B256).toBytes =
      officialConstructorPauseZeroMemory := by
  rfl

theorem officialConstructorPauseScratchZero_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPauseZeroMemory, G + 15⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G + 27⟩)
      (pushB256 0 :::
        storeByteOffsetForProof officialConstructorEventScratch +++ rest) post := by
  apply constructorZeroMstorePrefix_runCompiled
      (offset := officialConstructorEventScratch) (storeExt := 4)
      (memory' := officialConstructorPauseZeroMemory)
      (Gafter := G + 15)
  · rw [officialConstructorEventScratch_eq]
    decide
  · omega
  · intro S G'
    exact Devm.extCost_of_size officialConstructorPatchedMemory_size (by
      rw [officialConstructorEventScratch_eq]
      decide +kernel)
  · exact officialConstructorPatchedMemory_write_pause_zero
  · exact hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratch.lean`. -/

theorem officialConstructorPauseScratchLine_runCompiled
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
        storeByteOffsetForProof officialConstructorEventScratch +++
        loadArgumentIndexForProof 5 +++
        storeByteOffsetForProof (officialConstructorEventScratch + 32) +++
        rest) post := by
  have hvalue := officialConstructorPauseScratchValue_runCompiled hrest
  exact officialConstructorPauseScratchZero_runCompiled hvalue

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsConfigurationSuffix.lean`. -/

theorem officialConstructorConfigurationSuffix_eq_prefix :
    officialConstructorConfigurationSuffix =
      officialConstructorConfigurationPrefix +++
        officialConstructorHeartbeatSuffix := by
  rfl

theorem officialConstructorConfigurationSuffix_runCompiled
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
    officialConstructorConfigurationPrefix
  convert hpauseScratch using 1
  simp only [List.append_assoc, prepend_append, prepend]

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsInitializedLogOpcode.lean`. -/

private theorem officialConstructorInitializedBase_eq_addLog
    (sevm : Sevm) (base : Devm) :
    officialConstructorInitializedBase sevm base =
      base.addLog
        ⟨sevm.currentTarget,
          [circuitBreakerInitializedEvent, officialParams.admin],
          officialParams.minPauseDuration.toBytes ++
            officialParams.maxPauseDuration.toBytes ++
            officialParams.minHeartbeatInterval.toBytes ++
            officialParams.maxHeartbeatInterval.toBytes⟩ := by
  rfl

theorem officialConstructorInitializedLogOpcode_runCompiled
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
  apply constructorEventLog2Opcode_runCompiled
      (topic0 := circuitBreakerInitializedEvent)
      (topic1 := officialParams.admin)
      (data := officialParams.minPauseDuration.toBytes ++
        officialParams.maxPauseDuration.toBytes ++
        officialParams.minHeartbeatInterval.toBytes ++
        officialParams.maxHeartbeatInterval.toBytes)
      (Gafter := G)
  · omega
  · rw [officialConstructorPatchedMemory_size]
  · rw [officialConstructorPatchedMemory_size]
    decide
  · exact officialConstructorPatchedMemory_read_initializedData
  · exact officialConstructorPatchedMemory_read_initializedMemory
  · exact hstatic
  · rw [← officialConstructorInitializedBase_eq_addLog]
    exact hrest

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsInitializedLog.lean`. -/

theorem officialConstructorInitializedLogLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorPatchedMemory, G + 2163⟩)
      (officialConstructorInitializedPrefix +++ rest) post := by
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
  unfold officialConstructorInitializedPrefix
  apply constructorArgumentLog2Prefix_runCompiled
      (i := ⟨0, by decide⟩)
      (eventTopic := circuitBreakerInitializedEvent)
      (indexedTopic := officialParams.admin)
      (indexPushCost := 2) (loadCost := 3) (eventPushCost := 3)
      (Gafter := G + 2149)
  · omega
  · decide
  · intro S G'
    change gVerylow +
      (base.setMach ⟨S, officialConstructorPatchedMemory, G'⟩).extCost
        [⟨0, 32⟩] = 3
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorPatchedMemory_size
      (by decide +kernel)
  · exact hvalue
  · exact hmemory
  · simpa only [gVerylow] using pushCost_of_ne_zero
      (w := circuitBreakerInitializedEvent) (by decide +kernel)
  · exact hlog

/-! Consolidated from `LidoCircuitBreakerDeploymentTracePatchAssembly.lean`. -/

private def officialConstructorPatchLine : Line :=
  loadArgumentIndexForProof 0 ++ storeByteOffsetForProof 398 ++
  loadArgumentIndexForProof 0 ++ storeByteOffsetForProof 1318 ++
  loadArgumentIndexForProof 0 ++ storeByteOffsetForProof 2057 ++
  loadArgumentIndexForProof 0 ++ storeByteOffsetForProof 2144 ++
  loadArgumentIndexForProof 1 ++ storeByteOffsetForProof 441 ++
  loadArgumentIndexForProof 1 ++ storeByteOffsetForProof 937 ++
  loadArgumentIndexForProof 2 ++ storeByteOffsetForProof 482 ++
  loadArgumentIndexForProof 2 ++ storeByteOffsetForProof 2185 ++
  loadArgumentIndexForProof 3 ++ storeByteOffsetForProof 732 ++
  loadArgumentIndexForProof 3 ++ storeByteOffsetForProof 1361 ++
  loadArgumentIndexForProof 4 ++ storeByteOffsetForProof 896 ++
  loadArgumentIndexForProof 4 ++ storeByteOffsetForProof 1402

private theorem patchRuntimeLine_official_eq :
    patchRuntimeLineForProof constructorRuntimeBaseForProof =
      officialConstructorPatchLine := by
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [patchRuntimeLineForProof_eq, patchFieldLineForProof_eq,
    immutableParameters,
    List.flatMap_cons, List.flatMap_nil, hadmin, hminPause, hmaxPause,
    hminHeartbeat, hmaxHeartbeat, patchArgumentIndexForProof_eq,
    officialConstructorPatchLine, constructorRuntimeBaseForProof_eq,
    constructorArgumentBytes, List.append_nil,
    List.append_assoc]
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

theorem officialConstructorCopyPatch_runCompiled
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
      (codecopy ::: patchRuntimeLineForProof constructorRuntimeBaseForProof +++ rest) post := by
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

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceEffectsBody.lean`. -/

theorem officialConstructorEffectBody_runCompiled
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

/-! Consolidated from `LidoCircuitBreakerDeploymentTraceValidation.lean`. -/

/-! ## Gas-exact validation prefix -/

section validation

/-! The source body is intentionally kept literal above for bytecode-shape
certificates.  These suffix names give proof elaboration bounded continuation
checkpoints without changing that source presentation. -/

private def officialConstructorValidationFinish : Func :=
  pushFixedNatForProof 4282 :::
  pushFixedNatForProof 616 :::
  pushCompactNatForProof constructorRuntimeBaseForProof :::
  officialConstructorEffectBody

private def officialConstructorInitialHeartbeatMaxStage : Func :=
  loadArgumentIndexForProof 4 +++
  loadArgumentIndexForProof 6 +++ gt :::
  ((.call 10) <?> officialConstructorValidationFinish)

private def officialConstructorInitialHeartbeatMinStage : Func :=
  loadArgumentIndexForProof 3 +++
  loadArgumentIndexForProof 6 +++ lt :::
  ((.call 9) <?> officialConstructorInitialHeartbeatMaxStage)

private def officialConstructorInitialPauseMaxStage : Func :=
  loadArgumentIndexForProof 2 +++
  loadArgumentIndexForProof 5 +++ gt :::
  ((.call 8) <?> officialConstructorInitialHeartbeatMinStage)

private def officialConstructorInitialPauseMinStage : Func :=
  loadArgumentIndexForProof 1 +++
  loadArgumentIndexForProof 5 +++ lt :::
  ((.call 7) <?> officialConstructorInitialPauseMaxStage)

private def officialConstructorHeartbeatBoundsStage : Func :=
  loadArgumentIndexForProof 4 +++
  loadArgumentIndexForProof 3 +++ gt :::
  ((.call 6) <?> officialConstructorInitialPauseMinStage)

private def officialConstructorMinHeartbeatNonzeroStage : Func :=
  loadArgumentIndexForProof 3 +++ iszero :::
  ((.call 5) <?> officialConstructorHeartbeatBoundsStage)

private def officialConstructorPauseBoundsStage : Func :=
  loadArgumentIndexForProof 2 +++
  loadArgumentIndexForProof 1 +++ gt :::
  ((.call 4) <?> officialConstructorMinHeartbeatNonzeroStage)

private def officialConstructorMinPauseNonzeroStage : Func :=
  loadArgumentIndexForProof 1 +++ iszero :::
  ((.call 3) <?> officialConstructorPauseBoundsStage)

private def officialConstructorAdminNonzeroStage : Func :=
  loadArgumentIndexForProof 0 +++ iszero :::
  ((.call 2) <?> officialConstructorMinPauseNonzeroStage)

private def officialConstructorCanonicalAdminStage : Func :=
  loadArgumentIndexForProof 0 +++ checkNonAddress +++
  ((.call 1) <?> officialConstructorAdminNonzeroStage)

private theorem officialConstructorValidationBody_eq_staged :
    officialConstructorValidationBody =
      pushFixedNatForProof 5122 ::: codesize ::: lt :::
      ((.call 1) <?>
        (pushCompactNatForProof 224 :::
          pushFixedNatForProof 4898 :::
          pushCompactNatForProof 0 :::
          codecopy :::
          officialConstructorCanonicalAdminStage)) := by
  unfold officialConstructorValidationBody
    officialConstructorCanonicalAdminStage
    officialConstructorAdminNonzeroStage
    officialConstructorMinPauseNonzeroStage
    officialConstructorPauseBoundsStage
    officialConstructorMinHeartbeatNonzeroStage
    officialConstructorHeartbeatBoundsStage
    officialConstructorInitialPauseMinStage
    officialConstructorInitialPauseMaxStage
    officialConstructorInitialHeartbeatMinStage
    officialConstructorInitialHeartbeatMaxStage
    officialConstructorValidationFinish
  rfl

set_option maxRecDepth 929 in
private theorem officialConstructorValidationFinish_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, G⟩)
      officialConstructorEffectBody post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 9⟩)
      officialConstructorValidationFinish post := by
  unfold officialConstructorValidationFinish
  simp only [pushCompactNatForProof_eq, pushFixedNatForProof_eq,
    if_pos (show 4282 < 2 ^ 16 by decide),
    if_pos (show 616 < 2 ^ 16 by decide)]
  func_run (3)
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorInitialHeartbeatMaxStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorValidationFinish post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorInitialHeartbeatMaxStage post := by
  have hv4 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 128 32).1) =
      officialParams.maxHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨4, by decide⟩
  have hv6 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨6, by decide⟩
  have hm4 : (officialConstructorDecodedMemory.read 128 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨4, by decide⟩
  have hm6 : (officialConstructorDecodedMemory.read 192 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨6, by decide⟩
  unfold officialConstructorInitialHeartbeatMaxStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 128).toNat = 128 by decide]
  all_goals try simp_rw [hm4, hv4]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm4, hv4]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 192).toNat = 192 by decide]
  all_goals try simp_rw [hm6, hv6]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm6, hv6]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorInitialHeartbeatMinStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorInitialHeartbeatMaxStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorInitialHeartbeatMinStage post := by
  have hv3 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 96 32).1) =
      officialParams.minHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨3, by decide⟩
  have hv6 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨6, by decide⟩
  have hm3 : (officialConstructorDecodedMemory.read 96 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨3, by decide⟩
  have hm6 : (officialConstructorDecodedMemory.read 192 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨6, by decide⟩
  unfold officialConstructorInitialHeartbeatMinStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm3, hv3]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 192).toNat = 192 by decide]
  all_goals try simp_rw [hm6, hv6]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm6, hv6]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorInitialPauseMaxStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorInitialHeartbeatMinStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorInitialPauseMaxStage post := by
  have hv2 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 64 32).1) =
      officialParams.maxPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨2, by decide⟩
  have hv5 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨5, by decide⟩
  have hm2 : (officialConstructorDecodedMemory.read 64 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨2, by decide⟩
  have hm5 : (officialConstructorDecodedMemory.read 160 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨5, by decide⟩
  unfold officialConstructorInitialPauseMaxStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 64).toNat = 64 by decide]
  all_goals try simp_rw [hm2, hv2]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm2, hv2]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 160).toNat = 160 by decide]
  all_goals try simp_rw [hm5, hv5]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm5, hv5]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorInitialPauseMinStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorInitialPauseMaxStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorInitialPauseMinStage post := by
  have hv1 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 32 32).1) =
      officialParams.minPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨1, by decide⟩
  have hv5 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 160 32).1) =
      officialConstructorArgs.initialPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨5, by decide⟩
  have hm1 : (officialConstructorDecodedMemory.read 32 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨1, by decide⟩
  have hm5 : (officialConstructorDecodedMemory.read 160 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨5, by decide⟩
  unfold officialConstructorInitialPauseMinStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm1, hv1]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 160).toNat = 160 by decide]
  all_goals try simp_rw [hm5, hv5]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm5, hv5]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorHeartbeatBoundsStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorInitialPauseMinStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorHeartbeatBoundsStage post := by
  have hv4 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 128 32).1) =
      officialParams.maxHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨4, by decide⟩
  have hv3 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 96 32).1) =
      officialParams.minHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨3, by decide⟩
  have hm4 : (officialConstructorDecodedMemory.read 128 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨4, by decide⟩
  have hm3 : (officialConstructorDecodedMemory.read 96 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨3, by decide⟩
  unfold officialConstructorHeartbeatBoundsStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 128).toNat = 128 by decide]
  all_goals try simp_rw [hm4, hv4]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm4, hv4]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm3, hv3]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorMinHeartbeatNonzeroStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorHeartbeatBoundsStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 22⟩)
      officialConstructorMinHeartbeatNonzeroStage post := by
  have hv3 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 96 32).1) =
      officialParams.minHeartbeatInterval := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨3, by decide⟩
  have hm3 : (officialConstructorDecodedMemory.read 96 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨3, by decide⟩
  unfold officialConstructorMinHeartbeatNonzeroStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 96).toNat = 96 by decide]
  all_goals try simp_rw [hm3, hv3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm3, hv3]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorPauseBoundsStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorMinHeartbeatNonzeroStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 28⟩)
      officialConstructorPauseBoundsStage post := by
  have hv2 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 64 32).1) =
      officialParams.maxPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨2, by decide⟩
  have hv1 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 32 32).1) =
      officialParams.minPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨1, by decide⟩
  have hm2 : (officialConstructorDecodedMemory.read 64 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨2, by decide⟩
  have hm1 : (officialConstructorDecodedMemory.read 32 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨1, by decide⟩
  unfold officialConstructorPauseBoundsStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 64).toNat = 64 by decide]
  all_goals try simp_rw [hm2, hv2]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm2, hv2]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm1, hv1]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorMinPauseNonzeroStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorPauseBoundsStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 22⟩)
      officialConstructorMinPauseNonzeroStage post := by
  have hv1 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 32 32).1) =
      officialParams.minPauseDuration := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨1, by decide⟩
  have hm1 : (officialConstructorDecodedMemory.read 32 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨1, by decide⟩
  unfold officialConstructorMinPauseNonzeroStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 32).toNat = 32 by decide]
  all_goals try simp_rw [hm1, hv1]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm1, hv1]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorAdminNonzeroStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorMinPauseNonzeroStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 21⟩)
      officialConstructorAdminNonzeroStage post := by
  have hv0 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 0 32).1) =
      officialParams.admin := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨0, by decide⟩
  have hm0 : (officialConstructorDecodedMemory.read 0 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨0, by decide⟩
  unfold officialConstructorAdminNonzeroStage
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 0).toNat = 0 by decide]
  all_goals try simp_rw [hm0, hv0]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm0, hv0]
  func_run (2) [0]
  exact hrest

set_option maxRecDepth 930 in
private theorem officialConstructorCanonicalAdminStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorAdminNonzeroStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G + 32⟩)
      officialConstructorCanonicalAdminStage post := by
  have hv0 : Bytes.toB256
      ((officialConstructorDecodedMemory.read 0 32).1) =
      officialParams.admin := by
    simpa [officialConstructorArgumentWord] using
      officialConstructorDecodedMemory_read_argument ⟨0, by decide⟩
  have hm0 : (officialConstructorDecodedMemory.read 0 32).2 =
      officialConstructorDecodedMemory := by
    simpa using officialConstructorDecodedMemory_read_memory ⟨0, by decide⟩
  unfold officialConstructorCanonicalAdminStage checkNonAddress pushAddressMask
  simp only [loadArgumentIndexForProof_eq, pushCompactNatForProof_eq]
  func_run (2) [3]
  all_goals try simp only [show (Nat.toB256 0).toNat = 0 by decide]
  all_goals try simp_rw [hm0, hv0]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) officialConstructorDecodedMemory_size (by decide)
  try rw [hm0, hv0]
  func_run (6) [~~~(0 : B256), addressMask, 0]
  exact hrest

private theorem officialConstructorValidationDecode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], officialConstructorDecodedMemory, G⟩)
      officialConstructorCanonicalAdminStage post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + 93⟩)
      lidoCircuitBreakerConstructorProgram.main post := by
  have hcodeSize : sevm.code.size = 5122 := by
    rw [ByteArray.size_eq_length_toList, hcode,
      officialFullCreateInput_length_exact]
  rw [lidoCircuitBreakerConstructorProgram_main_official,
    officialConstructorValidationBody_eq_staged]
  simp only [pushFixedNatForProof_eq, pushCompactNatForProof_eq,
    if_pos (show 5122 < 2 ^ 16 by decide),
    if_pos (show 4898 < 2 ^ 16 by decide)]
  func_run (11) [1, 0, 45]
  all_goals try simp [B256.eqCheck, hvalue]
  all_goals try simp_rw [hcodeSize]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 224 32) rfl (by decide)
  all_goals try decide +kernel
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
  exact hrest

theorem officialConstructorValidationPrefix_runCompiled
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
  have hfinish :=
    officialConstructorValidationFinish_runCompiled hrest
  have hheartbeatMax :=
    officialConstructorInitialHeartbeatMaxStage_runCompiled hfinish
  have hheartbeatMin :=
    officialConstructorInitialHeartbeatMinStage_runCompiled hheartbeatMax
  have hpauseMax :=
    officialConstructorInitialPauseMaxStage_runCompiled hheartbeatMin
  have hpauseMin :=
    officialConstructorInitialPauseMinStage_runCompiled hpauseMax
  have hheartbeatBounds :=
    officialConstructorHeartbeatBoundsStage_runCompiled hpauseMin
  have hheartbeatNonzero :=
    officialConstructorMinHeartbeatNonzeroStage_runCompiled hheartbeatBounds
  have hpauseBounds :=
    officialConstructorPauseBoundsStage_runCompiled hheartbeatNonzero
  have hpauseNonzero :=
    officialConstructorMinPauseNonzeroStage_runCompiled hpauseBounds
  have hadmin :=
    officialConstructorAdminNonzeroStage_runCompiled hpauseNonzero
  have hcanonical :=
    officialConstructorCanonicalAdminStage_runCompiled hadmin
  have hdecode :=
    officialConstructorValidationDecode_runCompiled hvalue hcode hcanonical
  have hgasExact :
      g - 367 + 9 + 28 + 28 + 28 + 28 + 28 + 22 + 28 + 22 + 21 + 32 +
        93 = g := by
    omega
  simpa only [hgasExact] using hdecode

end validation

/-! Consolidated from `LidoCircuitBreakerDeploymentTrace.lean`. -/

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

/-- The gas-exact fresh-frame run executes against the complete official code
image: the compiled constructor prefix followed by the runtime template and
the seven-word ABI suffix observed by `CODESIZE` and `CODECOPY`. -/
theorem officialConstructor_exec_fresh
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
    exec ⟨0, sevm,
        base.setMach ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩⟩ =
      .ok (officialConstructorPost sevm base G) := by
  apply Prog.exec_of_runCompiled_appended
    (pfxCode := lidoCircuitBreakerInitPrefix)
    (sfxData := runtimeTemplateCode ++
      abiEncodeConstructorArgs officialConstructorArgs)
    (officialConstructorProgram_runCompiled_fresh hvalue hcode
      hpauseCold hpauseOriginal hpauseCurrent hheartbeatCold
      hheartbeatOriginal hheartbeatCurrent hstatic)
  · exact lidoCircuitBreakerConstructorProgram_compile.symm
  · rw [hcode, officialFullCreateInput_eq_layout, List.append_assoc]

end LidoCircuitBreaker

end Blanc
