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

private def constructorScratch (runtimeLength : Nat) : Nat :=
  ((runtimeLength + 31) / 32) * 32

private def pushFixedNat (value : Nat) : Ninst :=
  pushDeployWord (Nat.toB256 value)

private def loadByteOffset (offset : Nat) : Line :=
  [pushFixedNat offset, mload]

private def storeByteOffset (offset : Nat) : Line :=
  [pushFixedNat offset, mstore]

private def constructorError (name : String) : Func :=
  Func.revData (customErrorData name)

private def patchArgumentIndex : ImmutableParameter → Nat
  | .admin => 0
  | .minPauseDuration => 1
  | .maxPauseDuration => 2
  | .minHeartbeatInterval => 3
  | .maxHeartbeatInterval => 4

private def patchFieldLine
    (scratch : Nat) (field : ImmutableParameter) : Line :=
  (immutableWordOffsets field).flatMap fun offset =>
    loadByteOffset (scratch + 32 * patchArgumentIndex field) ++
      storeByteOffset offset

private def patchRuntimeLine (scratch : Nat) : Line :=
  immutableParameters.flatMap (patchFieldLine scratch)

private def constructorBody
    (runtimeOffset argsOffset runtimeLength : Nat) : Func :=
  let scratch := constructorScratch runtimeLength
  let eventScratch := scratch + constructorArgumentBytes
  -- The full input must contain the complete static seven-word head.  Extra
  -- trailing creation data is accepted, as by Solidity's static decoder.
  pushFixedNat (argsOffset + constructorArgumentBytes) ::: codesize ::: lt :::
  ((.call 1) <?>
    -- Copy the compiled zero-parameter runtime and the seven argument words.
    (pushFixedNat runtimeLength ::: pushFixedNat runtimeOffset :::
      pushFixedNat 0 ::: codecopy :::
      pushFixedNat constructorArgumentBytes ::: pushFixedNat argsOffset :::
      pushFixedNat scratch ::: codecopy :::
      -- The only address word must be canonical before source-level checks.
      loadByteOffset scratch +++ checkNonAddress +++
      ((.call 1) <?>
        (loadByteOffset scratch +++ iszero :::
          ((.call 2) <?>
            (loadByteOffset (scratch + 32) +++ iszero :::
              ((.call 3) <?>
                (loadByteOffset (scratch + 64) +++
                  loadByteOffset (scratch + 32) +++ gt :::
                  ((.call 4) <?>
                    (loadByteOffset (scratch + 96) +++ iszero :::
                      ((.call 5) <?>
                        (loadByteOffset (scratch + 128) +++
                          loadByteOffset (scratch + 96) +++ gt :::
                          ((.call 6) <?>
                            (loadByteOffset (scratch + 32) +++
                              loadByteOffset (scratch + 160) +++ lt :::
                              ((.call 7) <?>
                                (loadByteOffset (scratch + 64) +++
                                  loadByteOffset (scratch + 160) +++ gt :::
                                  ((.call 8) <?>
                                    (loadByteOffset (scratch + 96) +++
                                      loadByteOffset (scratch + 192) +++ lt :::
                                      ((.call 9) <?>
                                        (loadByteOffset (scratch + 128) +++
                                          loadByteOffset (scratch + 192) +++ gt :::
                                          ((.call 10) <?>
                                            (patchRuntimeLine scratch +++
                                              -- CircuitBreakerInitialized.
                                              loadByteOffset scratch +++
                                              pushB256 circuitBreakerInitializedEvent :::
                                              logWith 1
                                                (Nat.toB256 ((scratch + 32) / 32)) 4 +++
                                              -- PauseDurationUpdated(0, initial).
                                              pushB256 0 :::
                                              storeByteOffset eventScratch +++
                                              loadByteOffset (scratch + 160) +++
                                              storeByteOffset (eventScratch + 32) +++
                                              pushB256 pauseDurationUpdatedEvent :::
                                              logWith 0
                                                (Nat.toB256 (eventScratch / 32)) 2 +++
                                              loadByteOffset (scratch + 160) +++
                                              pushB256 pauseDurationSlot ::: sstore :::
                                              -- HeartbeatIntervalUpdated(0, initial).
                                              pushB256 0 :::
                                              storeByteOffset eventScratch +++
                                              loadByteOffset (scratch + 192) +++
                                              storeByteOffset (eventScratch + 32) +++
                                              pushB256 heartbeatIntervalUpdatedEvent :::
                                              logWith 0
                                                (Nat.toB256 (eventScratch / 32)) 2 +++
                                              loadByteOffset (scratch + 192) +++
                                              pushB256 heartbeatIntervalSlot ::: sstore :::
                                              pushFixedNat runtimeLength :::
                                              pushB256 0 ::: Func.ret))))))))))))))))))))))

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

/-- Constructor instructions.  All internal offsets use PUSH32, so the
provisional sizing pass and final pass have the same compiler shape. -/
def lidoCircuitBreakerInitPrefix : Bytes :=
  let prefixLength := provisionalConstructorPrefix.length
  (Prog.compile
    (constructorProgram prefixLength
      (prefixLength + runtimeTemplateCode.length)
      runtimeTemplateCode.length)).getD []

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
