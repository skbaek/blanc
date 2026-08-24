-- LidoCircuitBreakerDeploymentMessage.lean : public constructor effects and
-- direct creation-message settlement.
--
-- The execution-heavy constructor walk stays in `DeploymentTrace`. This owner
-- consumes its named post-frame projections through an import boundary before
-- crossing Jaune's creation-message code-deposit path.

import Blanc.LidoCircuitBreakerDeploymentTrace
import Blanc.LidoCircuitBreakerHistoryChain
import Blanc.DeploymentMessage

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

/-! ## Direct creation-message gas and runtime certificates -/

/-- The official runtime has the exact length returned by the constructor.
This derives the length from the already certified memory read instead of
reevaluating the concrete runtime compiler. -/
theorem lidoCircuitBreakerCode_official_length :
    (lidoCircuitBreakerCode officialParams).length = 4282 := by
  rw [← officialConstructorFinalMemory_read_runtime]
  simp only [Mem.read]
  rw [Array.sliceD_eq_map, List.length_map, List.length_range]

/-- The emitted official runtime starts with the compiler table's leading
`JUMPDEST`, so successful CREATE code-deposit charging cannot take the
forbidden-`0xEF` branch. -/
theorem lidoCircuitBreakerCode_official_cons :
    ∃ tail, lidoCircuitBreakerCode officialParams =
      Jinst.jumpdest.toUInt8 :: tail := by
  have hcompile := lidoCircuitBreakerCode_compile officialParams
  unfold Prog.compile at hcompile
  rcases Table.compile_cons_eq_some hcompile with
    ⟨compiledMain, compiledAux, _hmain, _haux, hbytes⟩
  refine ⟨compiledMain ++ compiledAux, ?_⟩
  exact hbytes

/-- Gas charged when the 4,282-byte official runtime is installed. -/
def officialCodeDepositGas : Nat :=
  (lidoCircuitBreakerCode officialParams).length * gasCodeDeposit

theorem officialCodeDepositGas_eq : officialCodeDepositGas = 856400 := by
  unfold officialCodeDepositGas
  rw [lidoCircuitBreakerCode_official_length]
  rfl

/-- Exact successful-path charge inside the direct creation message: compiled
constructor execution plus runtime code deposit. -/
def officialCreateMessageGasAccounting : Nat :=
  officialConstructorRequiredGas + officialCodeDepositGas

theorem officialCreateMessageGasAccounting_eq :
    officialCreateMessageGasAccounting = 906729 := by
  unfold officialCreateMessageGasAccounting
  rw [officialCodeDepositGas_eq]
  rfl

private theorem officialCreateMessageGas_sub_certificate
    (gas : Nat) (hgas : officialCreateMessageGasAccounting ≤ gas) :
    officialCodeDepositGas ≤ gas - officialConstructorRequiredGas ∧
      (gas - officialConstructorRequiredGas) - officialCodeDepositGas =
        gas - officialCreateMessageGasAccounting := by
  rw [officialCreateMessageGasAccounting_eq] at hgas ⊢
  rw [officialCodeDepositGas_eq]
  unfold officialConstructorRequiredGas
  omega

private theorem chargeCodeGas_official_output
    {rules : ForkRules} {d : Devm}
    (houtput : d.output = lidoCircuitBreakerCode officialParams)
    (hgas : officialCodeDepositGas ≤ d.gasLeft)
    (hmax : 4282 ≤ rules.code.maxCodeSize) :
    processCreateMessage.chargeCodeGas rules d =
      .ok (d.setMach
        ⟨d.stack, d.memory, d.gasLeft - officialCodeDepositGas⟩) := by
  rw [officialCodeDepositGas_eq] at hgas ⊢
  obtain ⟨tail, hcons⟩ := lidoCircuitBreakerCode_official_cons
  have hlen := lidoCircuitBreakerCode_official_length
  unfold processCreateMessage.chargeCodeGas
  rw [houtput, hcons]
  rw [hcons] at hlen
  simp only [List.length_cons] at hlen
  simp only [List.length_cons, hlen, gasCodeDeposit]
  rw [chargeGas_eq_ok hgas]
  change
    ((if rules.code.maxCodeSize < 4282 then
      Except.error ⟨.halt (.outOfGas .none), _⟩
    else Except.ok _) : Execution) = Except.ok _
  rw [if_neg (by omega)]

private structure OfficialConstructorRawCheckpoint
    (msg : Msg) (raw : Devm) : Type where
  benv : Benv
  residualGas : Nat
  transfer :
    (processCreateMessage.msg msg).benvAfterTransfer = .ok benv
  residualGas_eq :
    residualGas = msg.gas - officialConstructorRequiredGas
  post_eq :
    raw = officialConstructorPost
      (initSevm ((processCreateMessage.msg msg).withBenv benv))
      (initDevm ((processCreateMessage.msg msg).withBenv benv)) residualGas
  process : processMessage (processCreateMessage.msg msg) = .ok raw
  trace : OfficialConstructorExecutionTrace msg.currentTarget
    (initSevm ((processCreateMessage.msg msg).withBenv benv))
    (initDevm ((processCreateMessage.msg msg).withBenv benv)) raw residualGas
  baseStorage :
    (initDevm ((processCreateMessage.msg msg).withBenv benv)).state.getStor
      msg.currentTarget = Stor.empty

private theorem processMessage_official_constructor_checkpoint
    (msg : Msg)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code.toList = officialFullCreateInput)
    (hgas : officialConstructorRequiredGas ≤ msg.gas)
    (hpauseCold : (msg.currentTarget, pauseDurationSlot) ∉
      msg.accessedStorageKeys)
    (hpauseOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        pauseDurationSlot = 0)
    (hheartbeatCold : (msg.currentTarget, heartbeatIntervalSlot) ∉
      msg.accessedStorageKeys)
    (hheartbeatOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        heartbeatIntervalSlot = 0)
    (hstatic : msg.isStatic = false) :
    Nonempty (Σ raw, OfficialConstructorRawCheckpoint msg raw) := by
  let prepared := processCreateMessage.msg msg
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := prepared) hvalue
  let seeded := prepared.withBenv benv
  let sevm := initSevm seeded
  let base := initDevm seeded
  let G := msg.gas - officialConstructorRequiredGas
  have hGadd : G + officialConstructorRequiredGas = msg.gas := by
    dsimp only [G]
    omega
  have hstat : sevm.benvStat = msg.benv.stat := by
    calc
      sevm.benvStat = seeded.benv.stat := rfl
      _ = benv.stat := rfl
      _ = prepared.benv.stat := benvAfterTransfer_stat htransfer
      _ = msg.benv.stat := by rfl
  have htarget : sevm.currentTarget = msg.currentTarget := by
    calc
      sevm.currentTarget = seeded.currentTarget := rfl
      _ = prepared.currentTarget := rfl
      _ = msg.currentTarget := rfl
  have hseedValue : sevm.value = 0 := by
    calc
      sevm.value = seeded.value := rfl
      _ = prepared.value := rfl
      _ = msg.value := rfl
      _ = 0 := hvalue
  have hseedCode : sevm.code.toList = officialFullCreateInput := by
    calc
      sevm.code.toList = seeded.code.toList := rfl
      _ = prepared.code.toList := rfl
      _ = msg.code.toList := rfl
      _ = officialFullCreateInput := hcode
  have hseedStatic : sevm.isStatic = false := by
    calc
      sevm.isStatic = seeded.isStatic := rfl
      _ = prepared.isStatic := rfl
      _ = msg.isStatic := rfl
      _ = false := hstatic
  have hpreparedCodeAddress : prepared.codeAddress = .none := by
    calc
      prepared.codeAddress = msg.codeAddress := rfl
      _ = .none := hcodeAddress
  have hbaseKeys : base.accessedStorageKeys = msg.accessedStorageKeys := by
    calc
      base.accessedStorageKeys = seeded.accessedStorageKeys := rfl
      _ = prepared.accessedStorageKeys := rfl
      _ = msg.accessedStorageKeys := rfl
  have hpreparedStorage :
      prepared.benv.state.getStor msg.currentTarget = Stor.empty := by
    simpa only [prepared] using
      processCreateMessage_msg_getStor_currentTarget msg
  have hbenvStorage :
      benv.state.getStor msg.currentTarget = Stor.empty := by
    rw [congrFun (benvAfterTransfer_getStor_eq htransfer)
      msg.currentTarget]
    exact hpreparedStorage
  have hbaseStorage :
      base.state.getStor msg.currentTarget = Stor.empty := by
    change benv.state.getStor msg.currentTarget = Stor.empty
    exact hbenvStorage
  have hpauseCold' : (sevm.currentTarget, pauseDurationSlot) ∉
      base.accessedStorageKeys := by
    rw [htarget, hbaseKeys]
    exact hpauseCold
  have hheartbeatCold' : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys := by
    rw [htarget, hbaseKeys]
    exact hheartbeatCold
  have hpauseOriginal' :
      getOrigStorVal sevm sevm.currentTarget pauseDurationSlot = 0 := by
    unfold getOrigStorVal getOrigAcct
    rw [htarget, hstat]
    exact hpauseOriginal
  have hheartbeatOriginal' :
      getOrigStorVal sevm sevm.currentTarget heartbeatIntervalSlot = 0 := by
    unfold getOrigStorVal getOrigAcct
    rw [htarget, hstat]
    exact hheartbeatOriginal
  have hpauseCurrent :
      base.getStorVal sevm.currentTarget pauseDurationSlot = 0 := by
    rw [htarget]
    change (base.state.getStor msg.currentTarget).get pauseDurationSlot = 0
    rw [hbaseStorage]
    rfl
  have hheartbeatCurrent :
      base.getStorVal sevm.currentTarget heartbeatIntervalSlot = 0 := by
    rw [htarget]
    change
      (base.state.getStor msg.currentTarget).get heartbeatIntervalSlot = 0
    rw [hbaseStorage]
    rfl
  let raw := officialConstructorPost sevm base G
  have htrace : OfficialConstructorExecutionTrace msg.currentTarget
      sevm base raw G := by
    dsimp only [raw]
    exact officialConstructorExecutionTrace_fresh htarget hseedValue
      hseedCode hpauseCold' hpauseOriginal' hpauseCurrent
      hheartbeatCold' hheartbeatOriginal' hheartbeatCurrent hseedStatic
  have hstart :
      initEvm seeded =
        ⟨0, sevm,
          base.setMach
            ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩⟩ := by
    rw [hGadd]
    rfl
  have hexec : exec (initEvm seeded) = .ok raw := by
    rw [hstart]
    exact htrace.exec
  have hrawError : raw.error = .none := by
    calc
      raw.error = base.error := by
        dsimp only [raw]
        exact officialConstructorPost_error sevm base G
      _ = .none := by rfl
  have hprocess : processMessage prepared = .ok raw := by
    apply processMessage_ok_of_exec htransfer hpreparedCodeAddress
    · simpa only [seeded] using hexec
    · exact hrawError
  refine ⟨⟨raw, {
    benv := benv
    residualGas := G
    transfer := ?_
    residualGas_eq := rfl
    post_eq := rfl
    process := ?_
    trace := ?_
    baseStorage := ?_ }⟩⟩
  · simpa only [prepared] using htransfer
  · simpa only [prepared] using hprocess
  · simpa only [prepared, seeded, sevm, base] using htrace
  · simpa only [prepared, seeded, base] using hbaseStorage

/-! ## Public direct creation-message result -/

/-- The raw constructor result, successful code-deposit charge, and final code
installation are retained as one connected witness. This prevents raw `exec`
success from being confused with successful CREATE settlement. -/
structure OfficialCreateMessageExecution
    (ca : Adr) (msg : Msg) (post : Devm) : Prop where
  pipeline : ∃ (benv : Benv) (raw charged : Devm) (G : Nat),
    (processCreateMessage.msg msg).benvAfterTransfer = .ok benv ∧
    G = msg.gas - officialConstructorRequiredGas ∧
    processMessage (processCreateMessage.msg msg) = .ok raw ∧
    OfficialConstructorExecutionTrace ca
      (initSevm ((processCreateMessage.msg msg).withBenv benv))
      (initDevm ((processCreateMessage.msg msg).withBenv benv)) raw G ∧
    processCreateMessage.chargeCodeGas msg.benv.stat.rules raw = .ok charged ∧
    post = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩

/-- Exact settled result of the official zero-value direct creation message. -/
structure OfficialCreateMessageResult
    (ca : Adr) (msg : Msg) (post : Devm) : Prop where
  target_eq : msg.currentTarget = ca
  run : processCreateMessage msg = .ok post
  trace : OfficialCreateMessageExecution ca msg post
  installed : some (post.getCode ca).toList =
    Prog.compile (runtime officialParams)
  storage : post.state.getStor ca =
    ((Stor.empty.set pauseDurationSlot
      officialConstructorArgs.initialPauseDuration).set
        heartbeatIntervalSlot
        officialConstructorArgs.initialHeartbeatInterval)
  pauseDuration : post.getStorVal ca pauseDurationSlot =
    officialConstructorArgs.initialPauseDuration
  heartbeatInterval : post.getStorVal ca heartbeatIntervalSlot =
    officialConstructorArgs.initialHeartbeatInterval
  emptyRegistry : RegistryWitness
    (logicalStorageOfStor (post.state.getStor ca)) []
  coherent : RegistryCoherent (post.state.getStor ca)
  logs : post.logs = officialConstructorLogs ca
  returnData : post.output = lidoCircuitBreakerCode officialParams
  frameReturnData : post.returnData = []
  gasLeft : post.gasLeft = msg.gas - officialCreateMessageGasAccounting
  error : post.error = .none
  refundCounter : post.refundCounter = 0
  accountsToDelete : post.accountsToDelete = .emptyWithCapacity
  stable : RegistryStable officialParams ca post.state

private structure OfficialChargedCreateCheckpoint
    (msg : Msg) (benv : Benv) (raw charged : Devm) (G : Nat) : Prop where
  transfer :
    (processCreateMessage.msg msg).benvAfterTransfer = .ok benv
  residualGas : G = msg.gas - officialConstructorRequiredGas
  process : processMessage (processCreateMessage.msg msg) = .ok raw
  trace : OfficialConstructorExecutionTrace msg.currentTarget
    (initSevm ((processCreateMessage.msg msg).withBenv benv))
    (initDevm ((processCreateMessage.msg msg).withBenv benv)) raw G
  charge : processCreateMessage.chargeCodeGas msg.benv.stat.rules raw =
    .ok charged
  rawError : raw.error = .none
  output : charged.output = lidoCircuitBreakerCode officialParams
  storage : charged.state.getStor msg.currentTarget =
    ((Stor.empty.set pauseDurationSlot
      officialConstructorArgs.initialPauseDuration).set
        heartbeatIntervalSlot
        officialConstructorArgs.initialHeartbeatInterval)
  pauseDuration : charged.getStorVal msg.currentTarget pauseDurationSlot =
    officialConstructorArgs.initialPauseDuration
  heartbeatInterval :
    charged.getStorVal msg.currentTarget heartbeatIntervalSlot =
      officialConstructorArgs.initialHeartbeatInterval
  emptyRegistry : RegistryWitness
    (logicalStorageOfStor (charged.state.getStor msg.currentTarget)) []
  coherent : RegistryCoherent (charged.state.getStor msg.currentTarget)
  logs : charged.logs = officialConstructorLogs msg.currentTarget
  frameReturnData : charged.returnData = []
  error : charged.error = .none
  refundCounter : charged.refundCounter = 0
  accountsToDelete : charged.accountsToDelete = .emptyWithCapacity
  gasLeft : charged.gasLeft =
    msg.gas - officialCreateMessageGasAccounting

private theorem officialCreateMessageResult_of_charged
    (msg : Msg) {benv : Benv} {raw charged : Devm} {G : Nat}
    (h : OfficialChargedCreateCheckpoint msg benv raw charged G) :
    ∃ post, OfficialCreateMessageResult msg.currentTarget msg post := by
  let post := charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩
  have hrun : processCreateMessage msg = .ok post := by
    simpa only [post] using
      processCreateMessage_ok_of_processMessage_and_charge msg h.process
        h.rawError h.charge
  have hpostStorage : post.state.getStor msg.currentTarget =
      ((Stor.empty.set pauseDurationSlot
        officialConstructorArgs.initialPauseDuration).set
          heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval) := by
    dsimp only [post]
    rw [Devm.setCode_state]
    change
      ((charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).get msg.currentTarget).stor = _
    rw [State.setCode_get_stor]
    exact h.storage
  have hpostPause : post.getStorVal msg.currentTarget pauseDurationSlot =
      officialConstructorArgs.initialPauseDuration := by
    change
      (post.state.getStor msg.currentTarget).get pauseDurationSlot = _
    rw [hpostStorage]
    rw [Stor.get_set_ne _
      (show heartbeatIntervalSlot ≠ pauseDurationSlot by decide),
      Stor.get_set_self]
  have hpostHeartbeat :
      post.getStorVal msg.currentTarget heartbeatIntervalSlot =
        officialConstructorArgs.initialHeartbeatInterval := by
    change
      (post.state.getStor msg.currentTarget).get heartbeatIntervalSlot = _
    rw [hpostStorage, Stor.get_set_self]
  have hpostWitness : RegistryWitness
      (logicalStorageOfStor (post.state.getStor msg.currentTarget)) [] := by
    dsimp only [post]
    rw [Devm.setCode_state]
    change RegistryWitness
      (logicalStorageOfStor
        (((charged.state.setCode msg.currentTarget
          ⟨⟨charged.output⟩⟩).get msg.currentTarget).stor)) []
    rw [State.setCode_get_stor]
    exact h.emptyRegistry
  have hpostCoherent :
      RegistryCoherent (post.state.getStor msg.currentTarget) := by
    dsimp only [post]
    rw [Devm.setCode_state]
    change RegistryCoherent
      (((charged.state.setCode msg.currentTarget
        ⟨⟨charged.output⟩⟩).get msg.currentTarget).stor)
    rw [State.setCode_get_stor]
    exact h.coherent
  have hpostLogs : post.logs = officialConstructorLogs msg.currentTarget := by
    change charged.logs = officialConstructorLogs msg.currentTarget
    exact h.logs
  have hpostOutput :
      post.output = lidoCircuitBreakerCode officialParams := by
    change charged.output = lidoCircuitBreakerCode officialParams
    exact h.output
  have hpostReturnData : post.returnData = [] := by
    change charged.returnData = []
    exact h.frameReturnData
  have hpostError : post.error = .none := by
    change charged.error = .none
    exact h.error
  have hpostRefund : post.refundCounter = 0 := by
    change charged.refundCounter = 0
    exact h.refundCounter
  have hpostDelete : post.accountsToDelete = .emptyWithCapacity := by
    change charged.accountsToDelete = .emptyWithCapacity
    exact h.accountsToDelete
  have hpostGas :
      post.gasLeft = msg.gas - officialCreateMessageGasAccounting := by
    change charged.gasLeft = msg.gas - officialCreateMessageGasAccounting
    exact h.gasLeft
  have hpostCodeArray : post.getCode msg.currentTarget =
      ⟨⟨lidoCircuitBreakerCode officialParams⟩⟩ := by
    dsimp only [post]
    unfold Devm.getCode Devm.getAcct
    rw [Devm.setCode_state]
    unfold State.setCode
    rw [State.get_set_self]
    simp only [h.output]
  have hpostCodeList :
      (post.getCode msg.currentTarget).toList =
        lidoCircuitBreakerCode officialParams := by
    rw [hpostCodeArray, ByteArray.toList_eq_toList_data]
  have hinstalled : some (post.getCode msg.currentTarget).toList =
      Prog.compile (runtime officialParams) := by
    calc
      some (post.getCode msg.currentTarget).toList =
          some (lidoCircuitBreakerCode officialParams) :=
        congrArg some hpostCodeList
      _ = Prog.compile (runtime officialParams) :=
        (lidoCircuitBreakerCode_compile officialParams).symm
  have hpipeline :
      OfficialCreateMessageExecution msg.currentTarget msg post := by
    exact ⟨⟨benv, raw, charged, G, h.transfer, h.residualGas, h.process,
      h.trace, h.charge, rfl⟩⟩
  refine ⟨post, {
    target_eq := rfl
    run := hrun
    trace := hpipeline
    installed := hinstalled
    storage := hpostStorage
    pauseDuration := hpostPause
    heartbeatInterval := hpostHeartbeat
    emptyRegistry := hpostWitness
    coherent := hpostCoherent
    logs := hpostLogs
    returnData := hpostOutput
    frameReturnData := hpostReturnData
    gasLeft := hpostGas
    error := hpostError
    refundCounter := hpostRefund
    accountsToDelete := hpostDelete
    stable := ⟨hinstalled, hpostCoherent⟩ }⟩

/-- The exact official constructor crosses ordinary CREATE settlement, pays
the named execution-plus-deposit gas charge, installs the compiled runtime, and
establishes the empty Registry checkpoint at the computed target. -/
theorem processCreateMessage_establishes_officialRegistryStable
    (msg : Msg)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code.toList = officialFullCreateInput)
    (hgas : officialCreateMessageGasAccounting ≤ msg.gas)
    (hmax : 4282 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hpauseCold : (msg.currentTarget, pauseDurationSlot) ∉
      msg.accessedStorageKeys)
    (hpauseOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        pauseDurationSlot = 0)
    (hheartbeatCold : (msg.currentTarget, heartbeatIntervalSlot) ∉
      msg.accessedStorageKeys)
    (hheartbeatOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        heartbeatIntervalSlot = 0)
    (hstatic : msg.isStatic = false) :
    ∃ post, OfficialCreateMessageResult msg.currentTarget msg post := by
  have hconstructorGas : officialConstructorRequiredGas ≤ msg.gas := by
    have htotal := hgas
    rw [officialCreateMessageGasAccounting_eq] at htotal
    unfold officialConstructorRequiredGas
    omega
  obtain ⟨⟨raw, checkpoint⟩⟩ :=
    processMessage_official_constructor_checkpoint msg hvalue hcodeAddress
      hcode hconstructorGas hpauseCold hpauseOriginal hheartbeatCold
      hheartbeatOriginal hstatic
  rcases checkpoint with
    ⟨benv, G, htransfer, hGeq, hrawEq, hprocess, htrace, hbaseStorage⟩
  let prepared := processCreateMessage.msg msg
  let seeded := prepared.withBenv benv
  let sevm := initSevm seeded
  let base := initDevm seeded
  have hrawEq' : raw = officialConstructorPost sevm base G := by
    simpa only [prepared, seeded, sevm, base] using hrawEq
  have htrace' : OfficialConstructorExecutionTrace msg.currentTarget
      sevm base raw G := by
    simpa only [prepared, seeded, sevm, base] using htrace
  have hbaseStorage' :
      base.state.getStor msg.currentTarget = Stor.empty := by
    simpa only [prepared, seeded, base] using hbaseStorage
  have hbaseStorageSevm :
      Devm.getStor base sevm.currentTarget = Stor.empty := by
    change base.state.getStor sevm.currentTarget = Stor.empty
    rw [htrace'.target_eq]
    exact hbaseStorage'
  have hrawOutput :
      raw.output = lidoCircuitBreakerCode officialParams := by
    rw [hrawEq']
    exact officialConstructorPost_output sevm base G
  have hrawStorage : raw.state.getStor msg.currentTarget =
      ((Stor.empty.set pauseDurationSlot
        officialConstructorArgs.initialPauseDuration).set
          heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval) := by
    rw [← htrace'.target_eq]
    change Devm.getStor raw sevm.currentTarget = _
    rw [hrawEq', officialConstructorPost_getStor, hbaseStorageSevm]
  have hrawPause :
      raw.getStorVal msg.currentTarget pauseDurationSlot =
        officialConstructorArgs.initialPauseDuration := by
    rw [← htrace'.target_eq, hrawEq']
    exact officialConstructorPost_pauseDuration sevm base G
  have hrawHeartbeat :
      raw.getStorVal msg.currentTarget heartbeatIntervalSlot =
        officialConstructorArgs.initialHeartbeatInterval := by
    rw [← htrace'.target_eq, hrawEq']
    exact officialConstructorPost_heartbeatInterval sevm base G
  have hrawWitness : RegistryWitness
      (logicalStorageOfStor (raw.state.getStor msg.currentTarget)) [] := by
    rw [← htrace'.target_eq, hrawEq']
    exact officialConstructorPost_emptyRegistryWitness sevm base G
      hbaseStorageSevm
  have hrawCoherent :
      RegistryCoherent (raw.state.getStor msg.currentTarget) := by
    rw [← htrace'.target_eq, hrawEq']
    exact officialConstructorPost_registryCoherent sevm base G
      hbaseStorageSevm
  have hbaseLogs : base.logs = [] := by rfl
  have hrawLogs : raw.logs = officialConstructorLogs msg.currentTarget := by
    calc
      raw.logs = base.logs ++ officialConstructorLogs sevm.currentTarget := by
        rw [hrawEq']
        exact officialConstructorPost_logs sevm base G
      _ = officialConstructorLogs msg.currentTarget := by
        rw [hbaseLogs, List.nil_append, htrace'.target_eq]
  have hrawReturnData : raw.returnData = [] := by
    calc
      raw.returnData = base.returnData := by
        rw [hrawEq']
        exact officialConstructorPost_returnData sevm base G
      _ = [] := by rfl
  have hrawError : raw.error = .none := by
    calc
      raw.error = base.error := by
        rw [hrawEq']
        exact officialConstructorPost_error sevm base G
      _ = .none := by rfl
  have hrawRefund : raw.refundCounter = 0 := by
    calc
      raw.refundCounter = base.refundCounter := by
        rw [hrawEq']
        exact officialConstructorPost_refundCounter sevm base G
      _ = 0 := by rfl
  have hrawDelete : raw.accountsToDelete = .emptyWithCapacity := by
    calc
      raw.accountsToDelete = base.accountsToDelete := by
        rw [hrawEq']
        exact officialConstructorPost_accountsToDelete sevm base G
      _ = .emptyWithCapacity := by rfl
  have hrawGas :
      raw.gasLeft = msg.gas - officialConstructorRequiredGas := by
    calc
      raw.gasLeft = G := by
        rw [hrawEq']
        exact officialConstructorPost_gasLeft sevm base G
      _ = msg.gas - officialConstructorRequiredGas := hGeq
  obtain ⟨hdepositAfterConstructor, hgasAfterDeposit⟩ :=
    officialCreateMessageGas_sub_certificate msg.gas hgas
  have hdeposit : officialCodeDepositGas ≤ raw.gasLeft := by
    rw [hrawGas]
    exact hdepositAfterConstructor
  let chargedMach : Mach :=
    ⟨raw.stack, raw.memory, raw.gasLeft - officialCodeDepositGas⟩
  let charged := raw.setMach chargedMach
  have hcharge :
      processCreateMessage.chargeCodeGas msg.benv.stat.rules raw =
        .ok charged := by
    simpa only [charged, chargedMach] using
      chargeCodeGas_official_output hrawOutput hdeposit hmax
  have hmach : Devm.MachFrame raw charged := by
    change Devm.MachFrame raw (raw.setMach chargedMach)
    exact Devm.machFrame_setMach raw chargedMach
  have hchargedOutput :
      charged.output = lidoCircuitBreakerCode officialParams :=
    hmach.output.symm.trans hrawOutput
  have hchargedStorage : charged.state.getStor msg.currentTarget =
      ((Stor.empty.set pauseDurationSlot
        officialConstructorArgs.initialPauseDuration).set
          heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval) := by
    rw [← hmach.state]
    exact hrawStorage
  have hchargedPause :
      charged.getStorVal msg.currentTarget pauseDurationSlot =
        officialConstructorArgs.initialPauseDuration := by
    change
      (charged.state.getStor msg.currentTarget).get pauseDurationSlot = _
    rw [← hmach.state]
    exact hrawPause
  have hchargedHeartbeat :
      charged.getStorVal msg.currentTarget heartbeatIntervalSlot =
        officialConstructorArgs.initialHeartbeatInterval := by
    change
      (charged.state.getStor msg.currentTarget).get heartbeatIntervalSlot = _
    rw [← hmach.state]
    exact hrawHeartbeat
  have hchargedWitness : RegistryWitness
      (logicalStorageOfStor (charged.state.getStor msg.currentTarget)) [] := by
    rw [← hmach.state]
    exact hrawWitness
  have hchargedCoherent :
      RegistryCoherent (charged.state.getStor msg.currentTarget) := by
    rw [← hmach.state]
    exact hrawCoherent
  have hchargedLogs :
      charged.logs = officialConstructorLogs msg.currentTarget :=
    hmach.logs.symm.trans hrawLogs
  have hchargedReturnData : charged.returnData = [] :=
    hmach.returnData.symm.trans hrawReturnData
  have hchargedError : charged.error = .none :=
    hmach.error.symm.trans hrawError
  have hchargedRefund : charged.refundCounter = 0 :=
    hmach.refundCounter.symm.trans hrawRefund
  have hchargedDelete : charged.accountsToDelete = .emptyWithCapacity :=
    hmach.accountsToDelete.symm.trans hrawDelete
  have hchargedMachGas :
      chargedMach.gasLeft =
        raw.gasLeft - officialCodeDepositGas := by rfl
  have hchargedGas :
      charged.gasLeft = msg.gas - officialCreateMessageGasAccounting := by
    calc
      charged.gasLeft = chargedMach.gasLeft := by
        change (raw.setMach chargedMach).gasLeft = chargedMach.gasLeft
        exact Devm.gasLeft_setMach
      _ = raw.gasLeft - officialCodeDepositGas := hchargedMachGas
      _ = (msg.gas - officialConstructorRequiredGas) -
          officialCodeDepositGas := by rw [hrawGas]
      _ = msg.gas - officialCreateMessageGasAccounting := hgasAfterDeposit
  apply officialCreateMessageResult_of_charged msg
  exact {
    transfer := htransfer
    residualGas := hGeq
    process := hprocess
    trace := htrace
    charge := hcharge
    rawError := hrawError
    output := hchargedOutput
    storage := hchargedStorage
    pauseDuration := hchargedPause
    heartbeatInterval := hchargedHeartbeat
    emptyRegistry := hchargedWitness
    coherent := hchargedCoherent
    logs := hchargedLogs
    frameReturnData := hchargedReturnData
    error := hchargedError
    refundCounter := hchargedRefund
    accountsToDelete := hchargedDelete
    gasLeft := hchargedGas }

end LidoCircuitBreaker

end Blanc
