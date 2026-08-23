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

/-- First word-aligned scratch address following the copied official runtime. -/
def officialConstructorEventScratch : Nat :=
  constructorEventScratch 4282

theorem officialConstructorEventScratch_eq :
    officialConstructorEventScratch = 4512 := by
  decide

/-- Heartbeat initialization through the constructor return, named at the
shape layer so every later execution proof shares one opaque tail. -/
def officialConstructorHeartbeatSuffix : Func :=
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

/-- Pause-duration initialization before the shared heartbeat tail. -/
def officialConstructorConfigurationPrefix : Line :=
  [pushB256 0] ++
  storeByteOffset officialConstructorEventScratch ++
  loadArgumentIndex 5 ++
  storeByteOffset (officialConstructorEventScratch + 32) ++
  [pushB256 pauseDurationUpdatedEvent] ++
  logWith 0 (Nat.toB256 (officialConstructorEventScratch / 32)) 2 ++
  loadArgumentIndex 5 ++
  [pushB256 pauseDurationSlot, sstore]

/-- Both projected configuration writes and events, through return. -/
def officialConstructorConfigurationSuffix : Func :=
  officialConstructorConfigurationPrefix +++
    officialConstructorHeartbeatSuffix

/-- Initialized event prefix between the runtime patch line and configuration
initialization. -/
def officialConstructorInitializedPrefix : Line :=
  loadArgumentIndex 0 ++
  [pushB256 circuitBreakerInitializedEvent] ++
  logWith 1 1 4

/-- The exact residual constructor body after all ten successful validation
branches have placed the runtime-copy operands on the stack. -/
def officialConstructorEffectBody : Func :=
  codecopy :::
    patchRuntimeLine constructorRuntimeBase +++
    officialConstructorInitializedPrefix +++
    officialConstructorConfigurationSuffix

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
        constructorError "AdminZero",
        constructorError "MinPauseDurationZero",
        constructorError "MinPauseDurationExceedsMax",
        constructorError "MinHeartbeatIntervalZero",
        constructorError "MinHeartbeatIntervalExceedsMax",
        constructorError "PauseDurationBelowMin",
        constructorError "PauseDurationAboveMax",
        constructorError "HeartbeatIntervalBelowMin",
        constructorError "HeartbeatIntervalAboveMax"] := by
  rfl

private theorem constructorTableCallIndices_constructorError (name : String) :
    constructorTableCallIndices (constructorError name) = [] := by
  unfold constructorError Func.revSelector
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

end LidoCircuitBreaker

end Blanc
