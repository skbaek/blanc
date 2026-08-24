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

/-! ## Proof-only constructor coordinates

The executable constructor helpers above remain private.  Deployment proofs
consume only these one-way aliases, which add a derived proof surface without
changing the original declaration identities or the compiled artifact. -/

abbrev DeploymentProof.constructorRuntimeBaseForProof : Nat := constructorRuntimeBase
abbrev DeploymentProof.constructorEventScratchForProof : Nat → Nat := constructorEventScratch
abbrev DeploymentProof.pushFixedNatForProof : Nat → Ninst := pushFixedNat
abbrev DeploymentProof.pushCompactNatForProof : Nat → Ninst := pushCompactNat
abbrev DeploymentProof.loadArgumentIndexForProof : Nat → Line := loadArgumentIndex
abbrev DeploymentProof.storeByteOffsetForProof : Nat → Line := storeByteOffset
abbrev DeploymentProof.constructorErrorForProof : String → Func := constructorError
abbrev DeploymentProof.patchArgumentIndexForProof : ImmutableParameter → Nat :=
  patchArgumentIndex
abbrev DeploymentProof.patchFieldLineForProof : Nat → ImmutableParameter → Line :=
  patchFieldLine
abbrev DeploymentProof.patchRuntimeLineForProof : Nat → Line := patchRuntimeLine
abbrev DeploymentProof.constructorBodyForProof : Nat → Nat → Nat → Func :=
  constructorBody
abbrev DeploymentProof.constructorProgramForProof : Nat → Nat → Nat → Prog :=
  constructorProgram
abbrev DeploymentProof.provisionalConstructorPrefixForProof : Bytes :=
  provisionalConstructorPrefix

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

private abbrev ConstructorEffectCounts := Nat × Nat × Nat

private def ConstructorEffectCounts.add
    (left right : ConstructorEffectCounts) : ConstructorEffectCounts :=
  (left.1 + right.1,
   left.2.1 + right.2.1,
   left.2.2 + right.2.2)

private def constructorInstructionEffectCounts :
    Ninst → ConstructorEffectCounts
  | .reg .sstore => (1, 0, 0)
  | .reg .tstore => (0, 1, 0)
  | .exec _ => (0, 0, 1)
  | _ => (0, 0, 0)

private theorem constructorInstructionEffectCounts_reg (regular : Rinst) :
    constructorInstructionEffectCounts (.reg regular) =
      match regular with
      | .sstore => (1, 0, 0)
      | .tstore => (0, 1, 0)
      | _ => (0, 0, 0) := by
  cases regular <;> rfl

private theorem constructorInstructionEffectCounts_exec (execution : Xinst) :
    constructorInstructionEffectCounts (.exec execution) = (0, 0, 1) := by
  rfl

private theorem constructorInstructionEffectCounts_push
    (bytes : Bytes) (bound : bytes.length ≤ 32) :
    constructorInstructionEffectCounts (.push bytes bound) = (0, 0, 0) := by
  rfl

private theorem constructorInstructionEffectCounts_pushDeployWord
    (word : B256) :
    constructorInstructionEffectCounts (pushDeployWord word) = (0, 0, 0) := by
  exact constructorInstructionEffectCounts_push _ _

private theorem constructorInstructionEffectCounts_pushB256
    (word : B256) :
    constructorInstructionEffectCounts (pushB256 word) = (0, 0, 0) := by
  exact constructorInstructionEffectCounts_push _ _

private theorem constructorInstructionEffectCounts_pushCompactNat
    (value : Nat) :
    constructorInstructionEffectCounts (pushCompactNat value) = (0, 0, 0) := by
  exact constructorInstructionEffectCounts_pushB256 _

private theorem constructorInstructionEffectCounts_pushFixedNat
    (value : Nat) :
    constructorInstructionEffectCounts (pushFixedNat value) = (0, 0, 0) := by
  unfold pushFixedNat
  split <;> exact constructorInstructionEffectCounts_push _ _

private def constructorFuncEffectCounts : Func → ConstructorEffectCounts
  | .last _ => (0, 0, 0)
  | .next instruction rest =>
      (constructorInstructionEffectCounts instruction).add
        (constructorFuncEffectCounts rest)
  | .branch left right =>
      (constructorFuncEffectCounts left).add
        (constructorFuncEffectCounts right)
  | .call _ => (0, 0, 0)

private def constructorEffectCountsSum :
    List ConstructorEffectCounts → ConstructorEffectCounts
  | [] => (0, 0, 0)
  | counts :: rest => counts.add (constructorEffectCountsSum rest)

private def constructorLineEffectCounts (line : Line) :
    ConstructorEffectCounts :=
  constructorEffectCountsSum
    (line.map constructorInstructionEffectCounts)

private theorem constructorEffectCountsSum_append
    (left right : List ConstructorEffectCounts) :
    constructorEffectCountsSum (left ++ right) =
      (constructorEffectCountsSum left).add
        (constructorEffectCountsSum right) := by
  induction left with
  | nil =>
      simp [constructorEffectCountsSum, ConstructorEffectCounts.add]
  | cons counts left ih =>
      simp [constructorEffectCountsSum, ConstructorEffectCounts.add,
        ih, Nat.add_assoc]

private theorem constructorFuncEffectCounts_prepend
    (line : Line) (rest : Func) :
    constructorFuncEffectCounts (line +++ rest) =
      (constructorLineEffectCounts line).add
        (constructorFuncEffectCounts rest) := by
  induction line with
  | nil =>
      simp [prepend, constructorLineEffectCounts,
        constructorEffectCountsSum, ConstructorEffectCounts.add]
  | cons instruction line ih =>
      simp [prepend, constructorLineEffectCounts,
        constructorEffectCountsSum, constructorFuncEffectCounts,
        ConstructorEffectCounts.add, ih, Nat.add_assoc]

private theorem constructorLineEffectCounts_append
    (left right : Line) :
    constructorLineEffectCounts (left ++ right) =
      (constructorLineEffectCounts left).add
        (constructorLineEffectCounts right) := by
  unfold constructorLineEffectCounts
  rw [List.map_append, constructorEffectCountsSum_append]

private theorem constructorPatchFieldLineEffectCounts
    (runtimeBase : Nat) (field : ImmutableParameter) :
    constructorLineEffectCounts (patchFieldLine runtimeBase field) =
      (0, 0, 0) := by
  unfold patchFieldLine
  generalize immutableWordOffsets field = offsets
  induction offsets with
  | nil =>
      simp [constructorLineEffectCounts, constructorEffectCountsSum]
  | cons offset offsets ih =>
      simp only [List.flatMap_cons]
      rw [constructorLineEffectCounts_append, ih]
      simp [
        loadArgumentIndex, storeByteOffset,
        constructorLineEffectCounts, constructorEffectCountsSum,
        constructorInstructionEffectCounts_reg,
        constructorInstructionEffectCounts_pushCompactNat,
        constructorInstructionEffectCounts_pushFixedNat,
        ConstructorEffectCounts.add]

private theorem constructorPatchRuntimeLineEffectCounts
    (runtimeBase : Nat) :
    constructorLineEffectCounts (patchRuntimeLine runtimeBase) =
      (0, 0, 0) := by
  unfold patchRuntimeLine
  generalize immutableParameters = fields
  induction fields with
  | nil =>
      simp [constructorLineEffectCounts, constructorEffectCountsSum]
  | cons field fields ih =>
      simp only [List.flatMap_cons]
      rw [constructorLineEffectCounts_append,
        constructorPatchFieldLineEffectCounts, ih]
      rfl

private theorem constructorPatchRuntimeEffectCounts
    (runtimeBase : Nat) :
    constructorEffectCountsSum
        ((patchRuntimeLine runtimeBase).map
          constructorInstructionEffectCounts) = (0, 0, 0) := by
  simpa [constructorLineEffectCounts] using
    constructorPatchRuntimeLineEffectCounts runtimeBase

private def constructorProgramEffectCounts (program : Prog) :
    ConstructorEffectCounts :=
  (constructorFuncEffectCounts program.main).add
    (constructorEffectCountsSum
      (program.aux.map constructorFuncEffectCounts))

private theorem constructorFuncEffectCounts_eq (body : Func) :
    constructorFuncEffectCounts body =
      (sourceSstoreSiteCount body,
       sourceTstoreSiteCount body,
       sourceExternalCallSiteCount body) := by
  induction body with
  | last outcome => rfl
  | next instruction rest ih =>
      cases instruction with
      | reg regular =>
          cases regular <;>
            simp [constructorFuncEffectCounts,
              constructorInstructionEffectCounts,
              ConstructorEffectCounts.add, sourceSstoreSiteCount,
              sourceTstoreSiteCount, sourceExternalCallSiteCount, ih]
      | exec execution =>
          simp [constructorFuncEffectCounts,
            constructorInstructionEffectCounts,
            ConstructorEffectCounts.add, sourceSstoreSiteCount,
            sourceTstoreSiteCount, sourceExternalCallSiteCount, ih]
      | push bytes bound =>
          simp [constructorFuncEffectCounts,
            constructorInstructionEffectCounts,
            ConstructorEffectCounts.add, sourceSstoreSiteCount,
            sourceTstoreSiteCount, sourceExternalCallSiteCount, ih]
  | branch left right ihLeft ihRight =>
      simp [constructorFuncEffectCounts, ConstructorEffectCounts.add,
        sourceSstoreSiteCount, sourceTstoreSiteCount,
        sourceExternalCallSiteCount, ihLeft, ihRight]
  | call index => rfl

private theorem constructorEffectCountsSum_eq (bodies : List Func) :
    constructorEffectCountsSum
        (bodies.map constructorFuncEffectCounts) =
      ((bodies.map sourceSstoreSiteCount).sum,
       (bodies.map sourceTstoreSiteCount).sum,
       (bodies.map sourceExternalCallSiteCount).sum) := by
  induction bodies with
  | nil => rfl
  | cons body rest ih =>
      simp [constructorEffectCountsSum, ConstructorEffectCounts.add,
        constructorFuncEffectCounts_eq, ih]

private theorem constructorProgramEffectCounts_eq (program : Prog) :
    constructorProgramEffectCounts program =
      (programSiteCount sourceSstoreSiteCount program,
       programSiteCount sourceTstoreSiteCount program,
       programSiteCount sourceExternalCallSiteCount program) := by
  simp [constructorProgramEffectCounts, ConstructorEffectCounts.add,
    constructorFuncEffectCounts_eq, constructorEffectCountsSum_eq,
    programSiteCount]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
theorem constructor_program_site_counts_exact :
    constructorProgramSiteCounts = (2, 0, 0) := by
  unfold constructorProgramSiteCounts
  rw [← constructorProgramEffectCounts_eq]
  simp [constructorProgramEffectCounts,
    lidoCircuitBreakerConstructorProgram, constructorProgram,
    constructorBody, constructorEventScratch,
    loadArgumentIndex, storeByteOffset,
    constructorError, constructorFuncEffectCounts,
    constructorInstructionEffectCounts_reg,
    constructorInstructionEffectCounts_push,
    constructorInstructionEffectCounts_pushB256,
    constructorInstructionEffectCounts_pushCompactNat,
    constructorInstructionEffectCounts_pushFixedNat,
    constructorEffectCountsSum,
    constructorFuncEffectCounts_prepend, constructorLineEffectCounts,
    constructorPatchRuntimeEffectCounts,
    ConstructorEffectCounts.add,
    Func.rev, Func.revSelector, Func.ret, checkNonAddress, logWith,
    pushAddressMask]

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
