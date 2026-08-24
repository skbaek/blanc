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
