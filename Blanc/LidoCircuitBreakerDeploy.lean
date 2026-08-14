import Blanc.LidoCircuitBreakerCode

/-!
Creation artifact for the production Lido CircuitBreaker port.

The constructor is deliberately contract-private.  It decodes seven words
appended to the creation template, validates them in Solidity source order,
patches the parameter-neutral compiled runtime, initializes the two projected
configuration words, emits the three constructor events, and returns the
patched runtime.  These are identities of the Blanc family, not identities of
the Solidity initcode or runtime.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

def constructorArgumentBytes : Nat := 7 * 32
def eip3860InitcodeLimit : Nat := 49152

private def constructorRuntimeBase : Nat := constructorArgumentBytes

private def constructorEventScratch (runtimeLength : Nat) : Nat :=
  ((constructorRuntimeBase + runtimeLength + 31) / 32) * 32

private def pushFixedNat (value : Nat) : Ninst :=
  if value < 2 ^ 16 then
    Ninst.push [(value >>> 8).toUInt8, value.toUInt8] (by simp)
  else
    -- Never truncate a future layout that outgrows PUSH2.  Current generated
    -- coordinates take the fixed-width branch, so provisional and final
    -- constructor passes retain the same compiler shape.
    pushDeployWord (Nat.toB256 value)

private def pushCompactNat (value : Nat) : Ninst :=
  pushB256 (Nat.toB256 value)

private def loadArgumentIndex (index : Nat) : Line :=
  [pushCompactNat (32 * index), mload]

private def storeByteOffset (offset : Nat) : Line :=
  [pushFixedNat offset, mstore]

private def constructorError (name : String) : Func :=
  Func.revSelector (customErrorData name) (by
    simp [customErrorData, B256.length_toBytes])

private def patchArgumentIndex : ImmutableParameter → Nat
  | .admin => 0
  | .minPauseDuration => 1
  | .maxPauseDuration => 2
  | .minHeartbeatInterval => 3
  | .maxHeartbeatInterval => 4

private def patchFieldLine
    (runtimeBase : Nat) (field : ImmutableParameter) : Line :=
  (immutableWordOffsets field).flatMap fun offset =>
    loadArgumentIndex (patchArgumentIndex field) ++
      storeByteOffset (runtimeBase + offset)

private def patchRuntimeLine (runtimeBase : Nat) : Line :=
  immutableParameters.flatMap (patchFieldLine runtimeBase)

private def constructorBody
    (runtimeOffset argsOffset runtimeLength : Nat) : Func :=
  let eventScratch := constructorEventScratch runtimeLength
  -- The full input must contain the complete static seven-word head.  Extra
  -- trailing creation data is accepted, as by Solidity's static decoder.
  pushFixedNat (argsOffset + constructorArgumentBytes) ::: codesize ::: lt :::
  ((.call 1) <?>
    -- Decode at low memory first.  The runtime is copied only after every
    -- source-order validation succeeds, then returned from the adjacent base.
    (pushCompactNat constructorArgumentBytes ::: pushFixedNat argsOffset :::
      pushCompactNat 0 ::: codecopy :::
      -- The only address word must be canonical before source-level checks.
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
                                            (pushFixedNat runtimeLength :::
                                              pushFixedNat runtimeOffset :::
                                              pushCompactNat constructorRuntimeBase :::
                                              codecopy :::
                                              patchRuntimeLine constructorRuntimeBase +++
                                              -- CircuitBreakerInitialized.
                                              loadArgumentIndex 0 +++
                                              pushB256 circuitBreakerInitializedEvent :::
                                              logWith 1
                                                1 4 +++
                                              -- PauseDurationUpdated(0, initial).
                                              pushB256 0 :::
                                              storeByteOffset eventScratch +++
                                              loadArgumentIndex 5 +++
                                              storeByteOffset (eventScratch + 32) +++
                                              pushB256 pauseDurationUpdatedEvent :::
                                              logWith 0
                                                (Nat.toB256 (eventScratch / 32)) 2 +++
                                              loadArgumentIndex 5 +++
                                              pushB256 pauseDurationSlot ::: sstore :::
                                              -- HeartbeatIntervalUpdated(0, initial).
                                              pushB256 0 :::
                                              storeByteOffset eventScratch +++
                                              loadArgumentIndex 6 +++
                                              storeByteOffset (eventScratch + 32) +++
                                              pushB256 heartbeatIntervalUpdatedEvent :::
                                              logWith 0
                                                (Nat.toB256 (eventScratch / 32)) 2 +++
                                              loadArgumentIndex 6 +++
                                              pushB256 heartbeatIntervalSlot ::: sstore :::
                                              pushFixedNat runtimeLength :::
                                              pushCompactNat constructorRuntimeBase :::
                                              Func.ret))))))))))))))))))))))

private def constructorProgram
    (runtimeOffset argsOffset runtimeLength : Nat) : Prog :=
  { main := callvalue ::: iszero :::
      (constructorBody runtimeOffset argsOffset runtimeLength <?> (.call 1))
    aux := [Func.rev,
      constructorError "AdminZero",
      constructorError "MinPauseDurationZero",
      constructorError "MinPauseDurationExceedsMax",
      constructorError "MinHeartbeatIntervalZero",
      constructorError "MinHeartbeatIntervalExceedsMax",
      constructorError "PauseDurationBelowMin",
      constructorError "PauseDurationAboveMax",
      constructorError "HeartbeatIntervalBelowMin",
      constructorError "HeartbeatIntervalAboveMax"] }

private def provisionalConstructorPrefix : Bytes :=
  (Prog.compile
    (constructorProgram 0 0 runtimeTemplateCode.length)).getD []

/-- The exact constructor program compiled into the creation prefix. Keeping
this source owner public lets inventory gates count its actual syntax rather
than trusting a parallel hand-authored list. -/
def lidoCircuitBreakerConstructorProgram : Prog :=
  let prefixLength := provisionalConstructorPrefix.length
  constructorProgram prefixLength
    (prefixLength + runtimeTemplateCode.length)
    runtimeTemplateCode.length

/-- Constructor instructions.  Layout-dependent coordinates use PUSH2 while
they fit; the exact full-width fallback prevents silent truncation if a future
artifact crosses that bound. -/
def lidoCircuitBreakerInitPrefix : Bytes :=
  (Prog.compile lidoCircuitBreakerConstructorProgram).getD []

/-- Parameter-neutral Blanc creation-code template. -/
def lidoCircuitBreakerCreationTemplate : Bytes :=
  lidoCircuitBreakerInitPrefix ++ runtimeTemplateCode

def abiEncodeConstructorArgs (args : ConstructorArgs) : Bytes :=
  args.admin.toBytes ++ args.minPauseDuration.toBytes ++
    args.maxPauseDuration.toBytes ++ args.minHeartbeatInterval.toBytes ++
    args.maxHeartbeatInterval.toBytes ++ args.initialPauseDuration.toBytes ++
    args.initialHeartbeatInterval.toBytes

def lidoCircuitBreakerFullCreateInput (args : ConstructorArgs) : Bytes :=
  lidoCircuitBreakerCreationTemplate ++ abiEncodeConstructorArgs args

def officialFullCreateInput : Bytes :=
  lidoCircuitBreakerFullCreateInput officialConstructorArgs

def independentFullCreateInput : Bytes :=
  lidoCircuitBreakerFullCreateInput independentConstructorArgs

/-! ## Kernel-checked artifact and source-inventory facts -/

theorem abiEncodeConstructorArgs_length (args : ConstructorArgs) :
    (abiEncodeConstructorArgs args).length = constructorArgumentBytes := by
  simp [abiEncodeConstructorArgs, constructorArgumentBytes,
    B256.length_toBytes]

/-- The constructor's own source inventory is separate from the runtime's
20/3/2 inventory.  Internal table calls are not external EVM calls. -/
def constructorPersistentWriteInventory : List (SourceSite × PersistentWriteClass) :=
  [ (⟨"constructor.pauseDuration", 0⟩, .configuration),
    (⟨"constructor.heartbeatInterval", 1⟩, .configuration) ]

def constructorTransientWriteInventory : List (SourceSite × TransientWriteClass) := []
def constructorExternalCallInventory : List (SourceSite × ExternalCallClass) := []

/-- Actual syntax counts over the exact constructor `Prog`.  The differential
gate compares these computed values with the separately classified inventory,
so adding any persistent, transient, or external execution instruction cannot
be hidden by leaving the hand-labelled rows unchanged. -/
def constructorProgramSiteCounts : Nat × Nat × Nat :=
  (programSiteCount sourceSstoreSiteCount lidoCircuitBreakerConstructorProgram,
   programSiteCount sourceTstoreSiteCount lidoCircuitBreakerConstructorProgram,
   programSiteCount sourceExternalCallSiteCount lidoCircuitBreakerConstructorProgram)

theorem constructor_inventory_cardinalities :
    constructorPersistentWriteInventory.length = 2 ∧
      constructorTransientWriteInventory.length = 0 ∧
      constructorExternalCallInventory.length = 0 := by
  decide

theorem creation_template_runtime_suffix :
    lidoCircuitBreakerCreationTemplate.drop lidoCircuitBreakerInitPrefix.length =
      runtimeTemplateCode := by
  simp [lidoCircuitBreakerCreationTemplate]

theorem full_create_input_length (args : ConstructorArgs) :
    (lidoCircuitBreakerFullCreateInput args).length =
      lidoCircuitBreakerCreationTemplate.length + constructorArgumentBytes := by
  simp [lidoCircuitBreakerFullCreateInput, abiEncodeConstructorArgs_length]

end LidoCircuitBreaker
end Blanc
