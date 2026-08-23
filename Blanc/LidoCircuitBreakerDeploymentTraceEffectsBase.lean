-- LidoCircuitBreakerDeploymentTraceEffectsBase.lean : named constructor effect model and shared execution boundaries.

import Blanc.LidoCircuitBreakerDeploymentTraceRuntime

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

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

theorem officialConstructorHeartbeatLoggedBase_getStor
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
  change Devm.getStor
      (officialConstructorColdStore sevm
        (officialConstructorHeartbeatLoggedBase sevm base)
        heartbeatIntervalSlot
        officialConstructorArgs.initialHeartbeatInterval)
      sevm.currentTarget = _
  unfold officialConstructorColdStore
  rw [setStorVal_getStor_self]
  apply congrArg (fun s : Stor =>
    s.set heartbeatIntervalSlot
      officialConstructorArgs.initialHeartbeatInterval)
  change Devm.getStor
      (addAccessedStorageKey
        (officialConstructorHeartbeatLoggedBase sevm base)
        sevm.currentTarget heartbeatIntervalSlot)
      sevm.currentTarget = _
  rw [addAccessedStorageKey_getStor]
  exact officialConstructorHeartbeatLoggedBase_getStor sevm base

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
  unfold officialConstructorEffectBase
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

end LidoCircuitBreaker

end Blanc
