-- LidoCircuitBreakerDeploymentMessage.lean : public constructor effects and
-- direct creation-message settlement.
--
-- The execution-heavy constructor walk stays in `DeploymentTrace`. This owner
-- consumes its named post-frame projections through an import boundary before
-- crossing Jaune's creation-message code-deposit path.

import Blanc.LidoCircuitBreakerDeploymentTrace
import Blanc.LidoCircuitBreakerHistoryChain

namespace Blanc

open Jaune

namespace LidoCircuitBreaker

/-! ## Exact successful constructor effect checkpoint -/

theorem officialConstructorPost_state
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).state =
      (base.state.setStorVal sevm.currentTarget pauseDurationSlot
        officialConstructorArgs.initialPauseDuration).setStorVal
          sevm.currentTarget heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).state = _
  exact officialConstructorEffectBase_state sevm base

theorem officialConstructorPost_refundCounter
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).refundCounter =
      base.refundCounter := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).refundCounter = _
  exact officialConstructorEffectBase_refundCounter sevm base

theorem officialConstructorPost_returnData
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).returnData = base.returnData := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).returnData = _
  exact officialConstructorEffectBase_returnData sevm base

theorem officialConstructorPost_error
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).error = base.error := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).error = _
  exact officialConstructorEffectBase_error sevm base

theorem officialConstructorPost_accountsToDelete
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).accountsToDelete =
      base.accountsToDelete := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).accountsToDelete = _
  exact officialConstructorEffectBase_accountsToDelete sevm base

theorem officialConstructorPost_createdAccounts
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).createdAccounts =
      base.createdAccounts := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).createdAccounts = _
  exact officialConstructorEffectBase_createdAccounts sevm base

theorem officialConstructorPost_accessedAddresses
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).accessedAddresses =
      base.accessedAddresses := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).accessedAddresses = _
  exact officialConstructorEffectBase_accessedAddresses sevm base

theorem officialConstructorPost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).accessedStorageKeys =
      (base.accessedStorageKeys.insert
        (sevm.currentTarget, pauseDurationSlot)).insert
          (sevm.currentTarget, heartbeatIntervalSlot) := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).accessedStorageKeys = _
  exact officialConstructorEffectBase_accessedStorageKeys sevm base

theorem officialConstructorPost_transientStorage
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).transientStorage =
      base.transientStorage := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).transientStorage = _
  exact officialConstructorEffectBase_transientStorage sevm base

/-- Body-pinned successful effect and return checkpoints for the exact
constructor post-frame. The site-count field is computed from the actual
constructor `Prog`, so its zero transient/external counts are not inferred
from the final state alone. -/
structure OfficialConstructorEffectCheckpoints
    (sevm : Sevm) (base post : Devm) (G : Nat) : Prop where
  exactPost : post = officialConstructorPost sevm base G
  state : post.state =
    (base.state.setStorVal sevm.currentTarget pauseDurationSlot
      officialConstructorArgs.initialPauseDuration).setStorVal
        sevm.currentTarget heartbeatIntervalSlot
        officialConstructorArgs.initialHeartbeatInterval
  storage : Devm.getStor post sevm.currentTarget =
    ((Devm.getStor base sevm.currentTarget).set pauseDurationSlot
      officialConstructorArgs.initialPauseDuration).set
        heartbeatIntervalSlot
        officialConstructorArgs.initialHeartbeatInterval
  logs : post.logs = base.logs ++ officialConstructorLogs sevm.currentTarget
  stack : post.stack = []
  memory : post.memory = officialConstructorFinalMemory
  gasLeft : post.gasLeft = G
  output : post.output = lidoCircuitBreakerCode officialParams
  refundCounter : post.refundCounter = base.refundCounter
  returnData : post.returnData = base.returnData
  error : post.error = base.error
  accountsToDelete : post.accountsToDelete = base.accountsToDelete
  createdAccounts : post.createdAccounts = base.createdAccounts
  accessedAddresses : post.accessedAddresses = base.accessedAddresses
  accessedStorageKeys : post.accessedStorageKeys =
    (base.accessedStorageKeys.insert
      (sevm.currentTarget, pauseDurationSlot)).insert
        (sevm.currentTarget, heartbeatIntervalSlot)
  transientStorage : post.transientStorage = base.transientStorage
  siteCounts : constructorProgramSiteCounts = (2, 0, 0)
  persistentInventory : constructorPersistentWriteInventory =
    [(⟨"constructor.pauseDuration", 0⟩, .configuration),
      (⟨"constructor.heartbeatInterval", 1⟩, .configuration)]
  transientInventory : constructorTransientWriteInventory = []
  externalCallInventory : constructorExternalCallInventory = []

/-- The named exact post-frame inhabits every body-pinned effect checkpoint. -/
theorem officialConstructorPost_effectCheckpoints
    (sevm : Sevm) (base : Devm) (G : Nat) :
    OfficialConstructorEffectCheckpoints sevm base
      (officialConstructorPost sevm base G) G := by
  exact {
    exactPost := rfl
    state := officialConstructorPost_state sevm base G
    storage := officialConstructorPost_getStor sevm base G
    logs := officialConstructorPost_logs sevm base G
    stack := officialConstructorPost_stack sevm base G
    memory := officialConstructorPost_memory sevm base G
    gasLeft := officialConstructorPost_gasLeft sevm base G
    output := officialConstructorPost_output sevm base G
    refundCounter := officialConstructorPost_refundCounter sevm base G
    returnData := officialConstructorPost_returnData sevm base G
    error := officialConstructorPost_error sevm base G
    accountsToDelete := officialConstructorPost_accountsToDelete sevm base G
    createdAccounts := officialConstructorPost_createdAccounts sevm base G
    accessedAddresses := officialConstructorPost_accessedAddresses sevm base G
    accessedStorageKeys :=
      officialConstructorPost_accessedStorageKeys sevm base G
    transientStorage := officialConstructorPost_transientStorage sevm base G
    siteCounts := constructor_program_site_counts_exact
    persistentInventory := rfl
    transientInventory := rfl
    externalCallInventory := rfl }

/-! ## Public body-pinned constructor trace -/

/-- Successful validation is recorded together with the exact compiled walk
that reaches the constructor poststate. The individual facts follow the source
order: the canonical-address mask check, then the nine
`ConstructorArgs.validationError?` checks. -/
structure OfficialValidationCheckpoints
    (sevm : Sevm) (base post : Devm) (G : Nat) : Prop where
  run : Prog.RunCompiled sevm
    (base.setMach ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩)
    lidoCircuitBreakerConstructorProgram post
  effectEntry : Func.RunCompiled
    (lidoCircuitBreakerConstructorProgram.main ::
      lidoCircuitBreakerConstructorProgram.aux)
    sevm
    (base.setMach
      ⟨[(224 : B256), (616 : B256), (4282 : B256)],
        officialConstructorDecodedMemory, G + 49961⟩)
    officialConstructorEffectBody post
  inputLength : sevm.code.size = 5122
  decodedArguments : ∀ i : Fin 7,
    Bytes.toB256
        ((officialConstructorDecodedMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i
  canonicalAdmin : addressMask &&& officialParams.admin = 0
  adminNonzero : officialParams.admin ≠ 0
  minPauseNonzero : officialParams.minPauseDuration ≠ 0
  pauseBounds : officialParams.minPauseDuration.toNat ≤
    officialParams.maxPauseDuration.toNat
  minHeartbeatNonzero : officialParams.minHeartbeatInterval ≠ 0
  heartbeatBounds : officialParams.minHeartbeatInterval.toNat ≤
    officialParams.maxHeartbeatInterval.toNat
  initialPauseAboveMin : officialParams.minPauseDuration.toNat ≤
    officialConstructorArgs.initialPauseDuration.toNat
  initialPauseBelowMax : officialConstructorArgs.initialPauseDuration.toNat ≤
    officialParams.maxPauseDuration.toNat
  initialHeartbeatAboveMin : officialParams.minHeartbeatInterval.toNat ≤
    officialConstructorArgs.initialHeartbeatInterval.toNat
  initialHeartbeatBelowMax :
    officialConstructorArgs.initialHeartbeatInterval.toNat ≤
      officialParams.maxHeartbeatInterval.toNat

/-- The exact constructor source shape and all twelve compiler-table call sites.
These calls are internal error arms skipped by the successful run, not external
EVM calls. -/
structure OfficialConstructorErrorArmLayout : Prop where
  body : constructorBody 616 4898 4282 = officialConstructorValidationBody
  main : lidoCircuitBreakerConstructorProgram.main =
    Ninst.callvalue ::: Ninst.iszero :::
      (officialConstructorValidationBody <?> (.call 1))
  aux : lidoCircuitBreakerConstructorProgram.aux =
    [Func.rev,
      constructorError "AdminZero",
      constructorError "MinPauseDurationZero",
      constructorError "MinPauseDurationExceedsMax",
      constructorError "MinHeartbeatIntervalZero",
      constructorError "MinHeartbeatIntervalExceedsMax",
      constructorError "PauseDurationBelowMin",
      constructorError "PauseDurationAboveMax",
      constructorError "HeartbeatIntervalBelowMin",
      constructorError "HeartbeatIntervalAboveMax"]
  sites : officialConstructorTableCallIndices =
    [1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem officialConstructorErrorArmLayout :
    OfficialConstructorErrorArmLayout :=
  ⟨constructorBody_official_eq,
    lidoCircuitBreakerConstructorProgram_main_official,
    lidoCircuitBreakerConstructorProgram_aux_official,
    officialConstructorTableCallIndices_exact⟩

/-- Public execution trace for the exact official constructor. Argument facts
alone cannot inhabit this relation: it also requires the gas-exact compiled
walk, its effect-entry continuation, and the actual appended-code `exec`
equation. -/
structure OfficialConstructorExecutionTrace
    (ca : Adr) (sevm : Sevm) (base post : Devm) (G : Nat) : Prop where
  target_eq : sevm.currentTarget = ca
  fullInput : sevm.code.toList = officialFullCreateInput
  prefixCompile : Prog.compile lidoCircuitBreakerConstructorProgram =
    some lidoCircuitBreakerInitPrefix
  validationCheckpoints : OfficialValidationCheckpoints sevm base post G
  errorArmLayout : OfficialConstructorErrorArmLayout
  effectCheckpoints : OfficialConstructorEffectCheckpoints sevm base post G
  exec :
    Jaune.exec ⟨0, sevm,
        base.setMach
          ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩⟩ =
      .ok post

/-- The body-pinned public trace, derived from the fresh-frame constructor run
and its named effect-entry continuation. -/
theorem officialConstructorExecutionTrace_fresh
    {ca : Adr} {sevm : Sevm} {base : Devm} {G : Nat}
    (htarget : sevm.currentTarget = ca)
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
    OfficialConstructorExecutionTrace ca sevm base
      (officialConstructorPost sevm base G) G := by
  have hpauseCold' : (sevm.currentTarget, pauseDurationSlot) ∉
      (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys := by
    rw [officialConstructorPauseLoggedBase_accessedStorageKeys]
    exact hpauseCold
  have hpauseCurrent' :
      (officialConstructorPauseLoggedBase sevm base).getStorVal
        sevm.currentTarget pauseDurationSlot = 0 := by
    rw [officialConstructorPauseLoggedBase_getStorVal]
    exact hpauseCurrent
  have hheartbeatCold' : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys := by
    rw [officialConstructorHeartbeatLoggedBase_accessedStorageKeys]
    apply not_mem_hashSet_insert hheartbeatCold
    intro hpair
    have hslots : pauseDurationSlot = heartbeatIntervalSlot :=
      congrArg Prod.snd hpair
    exact (show pauseDurationSlot ≠ heartbeatIntervalSlot by decide) hslots
  have hheartbeatCurrent' :
      (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
        sevm.currentTarget heartbeatIntervalSlot = 0 := by
    change (Devm.getStor
      (officialConstructorHeartbeatLoggedBase sevm base)
        sevm.currentTarget).get heartbeatIntervalSlot = 0
    rw [officialConstructorHeartbeatLoggedBase_getStor,
      Stor.get_set_ne _
        (show pauseDurationSlot ≠ heartbeatIntervalSlot by decide)]
    exact hheartbeatCurrent
  have heffect := officialConstructorEffectBody_runCompiled
    (fs := lidoCircuitBreakerConstructorProgram.main ::
      lidoCircuitBreakerConstructorProgram.aux)
    (G := G) hcode hpauseCold' hpauseOriginal hpauseCurrent'
    hheartbeatCold' hheartbeatOriginal hheartbeatCurrent' hstatic
  have hrun := officialConstructorProgram_runCompiled_fresh
    (G := G) hvalue hcode hpauseCold hpauseOriginal hpauseCurrent
    hheartbeatCold hheartbeatOriginal hheartbeatCurrent hstatic
  have hexec := officialConstructor_exec_fresh
    (G := G) hvalue hcode hpauseCold hpauseOriginal hpauseCurrent
    hheartbeatCold hheartbeatOriginal hheartbeatCurrent hstatic
  refine {
    target_eq := htarget
    fullInput := hcode
    prefixCompile := lidoCircuitBreakerConstructorProgram_compile
    validationCheckpoints := ?_
    errorArmLayout := officialConstructorErrorArmLayout
    effectCheckpoints := officialConstructorPost_effectCheckpoints sevm base G
    exec := hexec }
  exact {
    run := hrun
    effectEntry := heffect
    inputLength := by
      rw [ByteArray.size_eq_length_toList, hcode,
        officialFullCreateInput_length_exact]
    decodedArguments := officialConstructorDecodedMemory_read_argument
    canonicalAdmin := by decide +kernel
    adminNonzero := by decide +kernel
    minPauseNonzero := by decide +kernel
    pauseBounds := by decide +kernel
    minHeartbeatNonzero := by decide +kernel
    heartbeatBounds := by decide +kernel
    initialPauseAboveMin := by decide +kernel
    initialPauseBelowMax := by decide +kernel
    initialHeartbeatAboveMin := by decide +kernel
    initialHeartbeatBelowMax := by decide +kernel }

/-! ## Empty Registry seed from the executed configuration writes -/

/-- Starting from the creation frame's actual empty target storage, the two
constructor configuration writes leave every Registry region witnessed by the
empty entry list. -/
theorem officialConstructorPost_emptyRegistryWitness
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hempty : Devm.getStor base sevm.currentTarget = Stor.empty) :
    RegistryWitness
      (logicalStorageOfStor
        (Devm.getStor (officialConstructorPost sevm base G)
          sevm.currentTarget)) [] := by
  rw [officialConstructorPost_getStor, hempty]
  change RegistryWitness
    (logicalStorageOfStor
      ((Stor.empty.set (slot configRegion 0)
          officialConstructorArgs.initialPauseDuration).set
        (slot configRegion 1)
        officialConstructorArgs.initialHeartbeatInterval)) []
  have hbase : RegistryWitness (logicalStorageOfStor Stor.empty) [] := by
    change RegistryWitness ({ read := fun _ => 0 } : LogicalStorage) []
    exact emptyWitness
  simpa only [pauseDurationSlot, heartbeatIntervalSlot] using
    ((hbase.config_set
      (payload := (0 : B256))
      (value := officialConstructorArgs.initialPauseDuration)
      (by simpa only [B256.toNat_zero] using
        (show 0 < 2 ^ 252 by norm_num))).config_set
        (payload := (1 : B256))
        (value := officialConstructorArgs.initialHeartbeatInterval)
        (by change 1 < 2 ^ 252; norm_num))

/-- The same execution-derived empty witness, existentially packaged as the
landed Registry coherence invariant. -/
theorem officialConstructorPost_registryCoherent
    (sevm : Sevm) (base : Devm) (G : Nat)
    (hempty : Devm.getStor base sevm.currentTarget = Stor.empty) :
    RegistryCoherent
      (Devm.getStor (officialConstructorPost sevm base G)
        sevm.currentTarget) :=
  ⟨[], officialConstructorPost_emptyRegistryWitness sevm base G hempty⟩

end LidoCircuitBreaker

end Blanc
