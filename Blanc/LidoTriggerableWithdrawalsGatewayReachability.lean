import Blanc.ForwardLog
import Blanc.ForwardStorageAccess
import Blanc.LidoTriggerableWithdrawalsGatewayPauseFor
import Blanc.LidoTriggerableWithdrawalsGatewayRoleRoute

/-!
# Constructive Triggerable Withdrawals Gateway reachability

This module constructs successful compiled executions of the gateway's exact
`pauseFor(uint256)` and `isPaused()` entries.  Unlike the semantic modules it
imports, the results here are forward witnesses: no evaluator result or
hypothesised run is used as evidence.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

private theorem accessedStorageKeys_setMach
    {base : Devm} {mach : Mach} :
    (base.setMach mach).accessedStorageKeys = base.accessedStorageKeys := rfl

private theorem addAccessedStorageKey_setMach
    {base : Devm} {mach : Mach} {a : Adr} {k : B256} :
    addAccessedStorageKey (base.setMach mach) a k =
      (addAccessedStorageKey base a k).setMach mach := rfl

private theorem getStorVal_addAccessedStorageKey
    {base : Devm} {a a' : Adr} {k k' : B256} :
    (addAccessedStorageKey base a k).getStorVal a' k' =
      base.getStorVal a' k' := rfl

private theorem addAccessedStorageKey_error_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).error = base.error := rfl

private theorem addAccessedStorageKey_output_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).output = base.output := rfl

private theorem addAccessedStorageKey_returnData_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).returnData = base.returnData := rfl

private theorem addAccessedStorageKey_logs_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).logs = base.logs := rfl

private theorem addAccessedStorageKey_accountsToDelete_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).accountsToDelete =
      base.accountsToDelete := rfl

private theorem addAccessedStorageKey_refundCounter_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).refundCounter =
      base.refundCounter := rfl

private theorem addAccessedStorageKey_transientStorage_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).transientStorage =
      base.transientStorage := rfl

private theorem addAccessedStorageKey_accessedAddresses_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).accessedAddresses =
      base.accessedAddresses := rfl

private theorem addAccessedStorageKey_state_local
    (base : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey base a k).state = base.state := rfl

private theorem addAccessedStorageKey_getCode_local
    (base : Devm) (a : Adr) (k : B256) (x : Adr) :
    (addAccessedStorageKey base a k).getCode x = base.getCode x := rfl

private theorem afterSstore_returnData_local
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).returnData = base.returnData := by
  unfold afterSstore
  split <;> rfl

private theorem afterSstore_transientStorage_local
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).transientStorage =
      base.transientStorage := by
  unfold afterSstore
  split <;> rfl

private theorem afterSstore_state_local
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).state =
      base.state.setStorVal sevm.currentTarget key value := by
  unfold afterSstore
  split <;> rfl

/-- The three successful `onlyRole(PAUSE_ROLE)` reads, in source order. -/
def pauseRoleWarm (sevm : Sevm) (base : Devm) : Devm :=
  addAccessedStorageKey
    (addAccessedStorageKey
      (addAccessedStorageKey base sevm.currentTarget
        (roleLookupIndexSlot pauseRole sevm.caller.toB256))
      sevm.currentTarget
        (roleLookupRoleSlot pauseRole sevm.caller.toB256))
    sevm.currentTarget
      (roleLookupAccountSlot pauseRole sevm.caller.toB256)

/-- The resume slot is warmed after the authorization reads and before the
selected `SSTORE`.  Naming this carrier keeps later exact-state projections
small enough to elaborate under the repository's default limits. -/
def pauseResumeWarm (sevm : Sevm) (base : Devm) : Devm :=
  addAccessedStorageKey (pauseRoleWarm sevm base)
    sevm.currentTarget resumeSinceSlot

private theorem pauseResumeWarm_error (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).error = base.error := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_error_local]

private theorem pauseResumeWarm_output (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).output = base.output := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_output_local]

private theorem pauseResumeWarm_returnData (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).returnData = base.returnData := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_returnData_local]

private theorem pauseResumeWarm_logs (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).logs = base.logs := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_logs_local]

private theorem pauseResumeWarm_accountsToDelete
    (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).accountsToDelete = base.accountsToDelete := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_accountsToDelete_local]

private theorem pauseResumeWarm_refundCounter
    (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).refundCounter = base.refundCounter := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_refundCounter_local]

private theorem pauseResumeWarm_transientStorage
    (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).transientStorage = base.transientStorage := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_transientStorage_local]

private theorem pauseResumeWarm_accessedAddresses
    (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).accessedAddresses = base.accessedAddresses := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_accessedAddresses_local]

private theorem pauseResumeWarm_state (sevm : Sevm) (base : Devm) :
    (pauseResumeWarm sevm base).state = base.state := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_state_local]

private theorem pauseResumeWarm_getCode
    (sevm : Sevm) (base : Devm) (a : Adr) :
    (pauseResumeWarm sevm base).getCode a = base.getCode a := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    addAccessedStorageKey_getCode_local]

private theorem pauseResumeWarm_getStorVal
    (sevm : Sevm) (base : Devm) (a : Adr) (key : B256) :
    (pauseResumeWarm sevm base).getStorVal a key = base.getStorVal a key := by
  simp only [pauseResumeWarm, pauseRoleWarm,
    getStorVal_addAccessedStorageKey]

/-- Persistent-state/refund carrier immediately after the finite write. -/
def pauseStored (sevm : Sevm) (base : Devm) (duration : B256) : Devm :=
  afterSstore sevm (pauseResumeWarm sevm base)
    resumeSinceSlot (duration + sevm.benvStat.time)

/-- Exact finite-pause event.  Keeping the hash-bearing value behind a named
definition prevents unrelated carrier projections from normalizing Keccak. -/
def pauseEvent (sevm : Sevm) (duration : B256) : Log :=
  ⟨sevm.currentTarget,
    [signatureHash "Paused" [.uint256]], duration.toBytes⟩

/-- Event carrier immediately after the finite write. -/
def pauseLogged (sevm : Sevm) (base : Devm) (duration : B256) : Devm :=
  (pauseStored sevm base duration).addLog (pauseEvent sevm duration)

private theorem setMach_error_local (base : Devm) (mach : Mach) :
    (base.setMach mach).error = base.error := rfl

private theorem setMach_output_local (base : Devm) (mach : Mach) :
    (base.setMach mach).output = base.output := rfl

private theorem setMach_returnData_local (base : Devm) (mach : Mach) :
    (base.setMach mach).returnData = base.returnData := rfl

private theorem setMach_logs_local (base : Devm) (mach : Mach) :
    (base.setMach mach).logs = base.logs := rfl

private theorem setMach_accountsToDelete_local (base : Devm) (mach : Mach) :
    (base.setMach mach).accountsToDelete = base.accountsToDelete := rfl

private theorem setMach_refundCounter_local (base : Devm) (mach : Mach) :
    (base.setMach mach).refundCounter = base.refundCounter := rfl

private theorem setMach_transientStorage_local (base : Devm) (mach : Mach) :
    (base.setMach mach).transientStorage = base.transientStorage := rfl

private theorem setMach_accessedAddresses_local (base : Devm) (mach : Mach) :
    (base.setMach mach).accessedAddresses = base.accessedAddresses := rfl

private theorem setMach_accessedStorageKeys_local (base : Devm) (mach : Mach) :
    (base.setMach mach).accessedStorageKeys = base.accessedStorageKeys := rfl

private theorem setMach_state_local (base : Devm) (mach : Mach) :
    (base.setMach mach).state = base.state := rfl

private theorem setMach_getCode_local (base : Devm) (mach : Mach) (a : Adr) :
    (base.setMach mach).getCode a = base.getCode a := rfl

private theorem setMach_getStorVal_local
    (base : Devm) (mach : Mach) (a : Adr) (key : B256) :
    (base.setMach mach).getStorVal a key = base.getStorVal a key := rfl

private theorem addLog_error_local (base : Devm) (event : Log) :
    (base.addLog event).error = base.error := rfl

private theorem addLog_output_local (base : Devm) (event : Log) :
    (base.addLog event).output = base.output := rfl

private theorem addLog_returnData_local (base : Devm) (event : Log) :
    (base.addLog event).returnData = base.returnData := rfl

private theorem addLog_logs_local (base : Devm) (event : Log) :
    (base.addLog event).logs = base.logs ++ [event] := rfl

private theorem addLog_accountsToDelete_local (base : Devm) (event : Log) :
    (base.addLog event).accountsToDelete = base.accountsToDelete := rfl

private theorem addLog_refundCounter_local (base : Devm) (event : Log) :
    (base.addLog event).refundCounter = base.refundCounter := rfl

private theorem addLog_transientStorage_local (base : Devm) (event : Log) :
    (base.addLog event).transientStorage = base.transientStorage := rfl

private theorem addLog_accessedAddresses_local (base : Devm) (event : Log) :
    (base.addLog event).accessedAddresses = base.accessedAddresses := rfl

private theorem addLog_accessedStorageKeys_local (base : Devm) (event : Log) :
    (base.addLog event).accessedStorageKeys = base.accessedStorageKeys := rfl

private theorem addLog_state_local (base : Devm) (event : Log) :
    (base.addLog event).state = base.state := rfl

private theorem addLog_getCode_local
    (base : Devm) (event : Log) (a : Adr) :
    (base.addLog event).getCode a = base.getCode a := rfl

private theorem addLog_getStorVal_local
    (base : Devm) (event : Log) (a : Adr) (key : B256) :
    (base.addLog event).getStorVal a key = base.getStorVal a key := rfl

/-- Exact finite-pause child post state, including all warmed role/slot keys,
the storage/refund update, the emitted event, final memory, and residual gas. -/
def pauseFinitePost (sevm : Sevm) (base : Devm)
    (duration : B256) (G : Nat) : Devm :=
  (pauseLogged sevm base duration).setMach
    ⟨[], Mem.empty.write 0 duration.toBytes, G⟩

/-- Exact infinite-sentinel child post state.  Unlike the finite post, the
stored word is the sentinel itself rather than timestamp arithmetic. -/
def pauseSentinelPost (sevm : Sevm) (base : Devm) (G : Nat) : Devm :=
  ((afterSstore sevm (pauseResumeWarm sevm base) resumeSinceSlot
      pauseInfinitely).addLog (pauseEvent sevm pauseInfinitely)).setMach
    ⟨[], Mem.empty.write 0 pauseInfinitely.toBytes, G⟩

private theorem pauseStored_error
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).error = base.error := by
  rw [pauseStored, afterSstore_error, pauseResumeWarm_error]

private theorem pauseStored_output
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).output = base.output := by
  rw [pauseStored, afterSstore_output, pauseResumeWarm_output]

private theorem pauseStored_returnData
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).returnData = base.returnData := by
  rw [pauseStored, afterSstore_returnData_local, pauseResumeWarm_returnData]

private theorem pauseStored_logs
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).logs = base.logs := by
  rw [pauseStored, afterSstore_logs, pauseResumeWarm_logs]

private theorem pauseStored_accountsToDelete
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).accountsToDelete =
      base.accountsToDelete := by
  rw [pauseStored, afterSstore_accountsToDelete,
    pauseResumeWarm_accountsToDelete]

private theorem pauseStored_refundCounter
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).refundCounter =
      sstoreNewRefundCounter (duration + sevm.benvStat.time)
        (getOrigStorVal sevm sevm.currentTarget resumeSinceSlot)
        (base.getStorVal sevm.currentTarget resumeSinceSlot)
        base.refundCounter := by
  rw [pauseStored, afterSstore_refundCounter,
    pauseResumeWarm_getStorVal, pauseResumeWarm_refundCounter]

private theorem pauseStored_transientStorage
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).transientStorage =
      base.transientStorage := by
  rw [pauseStored, afterSstore_transientStorage_local,
    pauseResumeWarm_transientStorage]

private theorem pauseStored_accessedAddresses
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).accessedAddresses =
      base.accessedAddresses := by
  rw [pauseStored, afterSstore_accessedAddresses,
    pauseResumeWarm_accessedAddresses]

private theorem pauseStored_state
    (sevm : Sevm) (base : Devm) (duration : B256) :
    (pauseStored sevm base duration).state =
      base.state.setStorVal sevm.currentTarget resumeSinceSlot
        (duration + sevm.benvStat.time) := by
  rw [pauseStored, afterSstore_state_local, pauseResumeWarm_state]

private theorem pauseStored_getCode
    (sevm : Sevm) (base : Devm) (duration : B256) (a : Adr) :
    (pauseStored sevm base duration).getCode a = base.getCode a := by
  rw [pauseStored, afterSstore_getCode, pauseResumeWarm_getCode]

@[simp] theorem pauseFinitePost_gasLeft
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).gasLeft = G := rfl

@[simp] theorem pauseFinitePost_error
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).error = base.error := by
  rw [pauseFinitePost, setMach_error_local, pauseLogged,
    addLog_error_local, pauseStored_error]

@[simp] theorem pauseFinitePost_output
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).output = base.output := by
  rw [pauseFinitePost, setMach_output_local, pauseLogged,
    addLog_output_local, pauseStored_output]

@[simp] theorem pauseFinitePost_returnData
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).returnData = base.returnData := by
  rw [pauseFinitePost, setMach_returnData_local, pauseLogged,
    addLog_returnData_local, pauseStored_returnData]

@[simp] theorem pauseFinitePost_logs
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).logs =
      base.logs ++ [pauseEvent sevm duration] := by
  rw [pauseFinitePost, setMach_logs_local, pauseLogged, addLog_logs_local,
    pauseStored_logs]

@[simp] theorem pauseFinitePost_accountsToDelete
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).accountsToDelete =
      base.accountsToDelete := by
  rw [pauseFinitePost, setMach_accountsToDelete_local, pauseLogged,
    addLog_accountsToDelete_local, pauseStored_accountsToDelete]

@[simp] theorem pauseFinitePost_refundCounter
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).refundCounter =
      sstoreNewRefundCounter (duration + sevm.benvStat.time)
        (getOrigStorVal sevm sevm.currentTarget resumeSinceSlot)
        (base.getStorVal sevm.currentTarget resumeSinceSlot)
        base.refundCounter := by
  rw [pauseFinitePost, setMach_refundCounter_local, pauseLogged,
    addLog_refundCounter_local, pauseStored_refundCounter]

@[simp] theorem pauseFinitePost_transientStorage
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).transientStorage =
      base.transientStorage := by
  rw [pauseFinitePost, setMach_transientStorage_local, pauseLogged,
    addLog_transientStorage_local, pauseStored_transientStorage]

@[simp] theorem pauseFinitePost_accessedAddresses
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).accessedAddresses =
      base.accessedAddresses := by
  rw [pauseFinitePost, setMach_accessedAddresses_local, pauseLogged,
    addLog_accessedAddresses_local, pauseStored_accessedAddresses]

theorem pauseFinitePost_state
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).state =
      base.state.setStorVal sevm.currentTarget resumeSinceSlot
        (duration + sevm.benvStat.time) := by
  rw [pauseFinitePost, setMach_state_local, pauseLogged, addLog_state_local,
    pauseStored_state]

theorem pauseFinitePost_getCode
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) (a : Adr) :
    (pauseFinitePost sevm base duration G).getCode a = base.getCode a := by
  rw [pauseFinitePost, setMach_getCode_local, pauseLogged,
    addLog_getCode_local, pauseStored_getCode]

theorem pauseFinitePost_stored
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).getStorVal
      sevm.currentTarget resumeSinceSlot = duration + sevm.benvStat.time := by
  rw [pauseFinitePost, setMach_getStorVal_local, pauseLogged,
    addLog_getStorVal_local]
  show (Devm.getStor (pauseStored sevm base duration)
    sevm.currentTarget).get resumeSinceSlot = _
  rw [pauseStored, afterSstore_getStor_self, Stor.get_set_self]

theorem pauseFinitePost_warm
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (sevm.currentTarget, resumeSinceSlot) ∈
      (pauseFinitePost sevm base duration G).accessedStorageKeys := by
  rw [pauseFinitePost, setMach_accessedStorageKeys_local, pauseLogged,
    addLog_accessedStorageKeys_local]
  rw [pauseStored, afterSstore_accessedStorageKeys]
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      (pauseResumeWarm sevm base).accessedStorageKeys := by
    unfold pauseResumeWarm
    exact Std.HashSet.mem_insert_self
  unfold sloadAccessedStorageKeys
  rw [if_pos hwarm]
  exact hwarm

theorem pauseFinitePost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) :
    (pauseFinitePost sevm base duration G).accessedStorageKeys =
      (pauseResumeWarm sevm base).accessedStorageKeys := by
  rw [pauseFinitePost, setMach_accessedStorageKeys_local, pauseLogged,
    addLog_accessedStorageKeys_local, pauseStored,
    afterSstore_accessedStorageKeys]
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      (pauseResumeWarm sevm base).accessedStorageKeys := by
    unfold pauseResumeWarm
    exact Std.HashSet.mem_insert_self
  unfold sloadAccessedStorageKeys
  rw [if_pos hwarm]

@[simp] theorem pauseSentinelPost_gasLeft
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).gasLeft = G := rfl

@[simp] theorem pauseSentinelPost_error
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).error = base.error := by
  rw [pauseSentinelPost, setMach_error_local, addLog_error_local,
    afterSstore_error, pauseResumeWarm_error]

@[simp] theorem pauseSentinelPost_output
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).output = base.output := by
  rw [pauseSentinelPost, setMach_output_local, addLog_output_local,
    afterSstore_output, pauseResumeWarm_output]

@[simp] theorem pauseSentinelPost_returnData
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).returnData = base.returnData := by
  rw [pauseSentinelPost, setMach_returnData_local, addLog_returnData_local,
    afterSstore_returnData_local, pauseResumeWarm_returnData]

@[simp] theorem pauseSentinelPost_logs
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).logs =
      base.logs ++ [pauseEvent sevm pauseInfinitely] := by
  rw [pauseSentinelPost, setMach_logs_local, addLog_logs_local,
    afterSstore_logs, pauseResumeWarm_logs]

@[simp] theorem pauseSentinelPost_accountsToDelete
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).accountsToDelete =
      base.accountsToDelete := by
  rw [pauseSentinelPost, setMach_accountsToDelete_local,
    addLog_accountsToDelete_local, afterSstore_accountsToDelete,
    pauseResumeWarm_accountsToDelete]

@[simp] theorem pauseSentinelPost_refundCounter
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).refundCounter =
      sstoreNewRefundCounter pauseInfinitely
        (getOrigStorVal sevm sevm.currentTarget resumeSinceSlot)
        (base.getStorVal sevm.currentTarget resumeSinceSlot)
        base.refundCounter := by
  rw [pauseSentinelPost, setMach_refundCounter_local,
    addLog_refundCounter_local, afterSstore_refundCounter,
    pauseResumeWarm_getStorVal, pauseResumeWarm_refundCounter]

@[simp] theorem pauseSentinelPost_transientStorage
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).transientStorage =
      base.transientStorage := by
  rw [pauseSentinelPost, setMach_transientStorage_local,
    addLog_transientStorage_local, afterSstore_transientStorage_local,
    pauseResumeWarm_transientStorage]

@[simp] theorem pauseSentinelPost_accessedAddresses
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).accessedAddresses =
      base.accessedAddresses := by
  rw [pauseSentinelPost, setMach_accessedAddresses_local,
    addLog_accessedAddresses_local, afterSstore_accessedAddresses,
    pauseResumeWarm_accessedAddresses]

theorem pauseSentinelPost_state
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).state =
      base.state.setStorVal sevm.currentTarget resumeSinceSlot
        pauseInfinitely := by
  rw [pauseSentinelPost, setMach_state_local, addLog_state_local,
    afterSstore_state_local, pauseResumeWarm_state]

theorem pauseSentinelPost_getCode
    (sevm : Sevm) (base : Devm) (G : Nat) (a : Adr) :
    (pauseSentinelPost sevm base G).getCode a = base.getCode a := by
  rw [pauseSentinelPost, setMach_getCode_local, addLog_getCode_local,
    afterSstore_getCode, pauseResumeWarm_getCode]

theorem pauseSentinelPost_stored
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).getStorVal
      sevm.currentTarget resumeSinceSlot = pauseInfinitely := by
  rw [pauseSentinelPost, setMach_getStorVal_local, addLog_getStorVal_local]
  show (Devm.getStor
    (afterSstore sevm (pauseResumeWarm sevm base) resumeSinceSlot
      pauseInfinitely) sevm.currentTarget).get resumeSinceSlot = _
  rw [afterSstore_getStor_self, Stor.get_set_self]

theorem pauseSentinelPost_warm
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (sevm.currentTarget, resumeSinceSlot) ∈
      (pauseSentinelPost sevm base G).accessedStorageKeys := by
  rw [pauseSentinelPost, setMach_accessedStorageKeys_local,
    addLog_accessedStorageKeys_local, afterSstore_accessedStorageKeys]
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      (pauseResumeWarm sevm base).accessedStorageKeys := by
    unfold pauseResumeWarm
    exact Std.HashSet.mem_insert_self
  unfold sloadAccessedStorageKeys
  rw [if_pos hwarm]
  exact hwarm

theorem pauseSentinelPost_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (pauseSentinelPost sevm base G).accessedStorageKeys =
      (pauseResumeWarm sevm base).accessedStorageKeys := by
  rw [pauseSentinelPost, setMach_accessedStorageKeys_local,
    addLog_accessedStorageKeys_local, afterSstore_accessedStorageKeys]
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      (pauseResumeWarm sevm base).accessedStorageKeys := by
    unfold pauseResumeWarm
    exact Std.HashSet.mem_insert_self
  unfold sloadAccessedStorageKeys
  rw [if_pos hwarm]

/-! ## The authorization prefix -/

/-- The exact successful `onlyRole(PAUSE_ROLE)` prefix costs `6439` gas when
its three lookup keys are cold.  The continuation receives all three warmed
keys and an otherwise unchanged frame. -/
theorem pauseOnlyRole_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hindex : base.getStorVal sevm.currentTarget
      (roleLookupIndexSlot pauseRole sevm.caller.toB256) = 1)
    (hrole : base.getStorVal sevm.currentTarget
      (roleLookupRoleSlot pauseRole sevm.caller.toB256) = pauseRole)
    (haccount : base.getStorVal sevm.currentTarget
      (roleLookupAccountSlot pauseRole sevm.caller.toB256) =
        canonicalAccount sevm.caller.toB256)
    (hcoldIndex : (sevm.currentTarget,
      roleLookupIndexSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (hcoldRole : (sevm.currentTarget,
      roleLookupRoleSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey base sevm.currentTarget
          (roleLookupIndexSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hcoldAccount : (sevm.currentTarget,
      roleLookupAccountSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
          (roleLookupRoleSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hbody : Func.RunCompiledTo fs sevm
      ((addAccessedStorageKey
          (addAccessedStorageKey
            (addAccessedStorageKey base sevm.currentTarget
              (roleLookupIndexSlot pauseRole sevm.caller.toB256))
            sevm.currentTarget
              (roleLookupRoleSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
            (roleLookupAccountSlot pauseRole sevm.caller.toB256)).setMach
        ⟨[], Mem.empty, G⟩) body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 6439⟩)
      (onlyRole pauseRole body) ex := by
  unfold onlyRole roleRecordCheck roleAccountCheck roleKeyForCaller
  func_run (40)
    [addressMask &&& sevm.caller.toB256,
      (addressMask &&& sevm.caller.toB256) ^^^ pauseRole,
      low252Mask &&&
        ((addressMask &&& sevm.caller.toB256) ^^^ pauseRole),
      regionWord roleLookupIndexRegion ||| low252Mask &&&
        ((addressMask &&& sevm.caller.toB256) ^^^ pauseRole),
      0,
      addressMask &&& sevm.caller.toB256,
      (addressMask &&& sevm.caller.toB256) ^^^ pauseRole,
      low252Mask &&&
        ((addressMask &&& sevm.caller.toB256) ^^^ pauseRole),
      regionWord roleLookupRoleRegion ||| low252Mask &&&
        ((addressMask &&& sevm.caller.toB256) ^^^ pauseRole),
      1,
      addressMask &&& sevm.caller.toB256,
      (addressMask &&& sevm.caller.toB256) ^^^ pauseRole,
      low252Mask &&&
        ((addressMask &&& sevm.caller.toB256) ^^^ pauseRole),
      regionWord roleLookupAccountRegion ||| low252Mask &&&
        ((addressMask &&& sevm.caller.toB256) ^^^ pauseRole),
      addressMask &&& sevm.caller.toB256,
      1]
  case h_cold =>
    simpa only [accessedStorageKeys_setMach, roleKeyWord_eq,
      roleLookupIndexSlot] using hcoldIndex
  case h_val =>
    simp only [Devm.getStorVal_setMach, roleKeyWord_eq]
    change (base.getStorVal sevm.currentTarget
      (roleLookupIndexSlot pauseRole sevm.caller.toB256) =? 0) = 0
    rw [hindex]
    decide
  case h_cold =>
    simpa only [addAccessedStorageKey_setMach,
      accessedStorageKeys_setMach, roleKeyWord_eq,
      roleLookupIndexSlot, roleLookupRoleSlot] using hcoldRole
  case h_val =>
    simp only [addAccessedStorageKey_setMach,
      Devm.getStorVal_setMach, getStorVal_addAccessedStorageKey,
      roleKeyWord_eq]
    change (pauseRole =? base.getStorVal sevm.currentTarget
      (roleLookupRoleSlot pauseRole sevm.caller.toB256)) = 1
    rw [hrole]
    simp [B256.eqCheck]
  case h_cold =>
    simpa only [addAccessedStorageKey_setMach,
      accessedStorageKeys_setMach, roleKeyWord_eq,
      roleLookupIndexSlot, roleLookupRoleSlot,
      roleLookupAccountSlot] using hcoldAccount
  case h_val =>
    simp only [addAccessedStorageKey_setMach,
      Devm.getStorVal_setMach, getStorVal_addAccessedStorageKey,
      roleKeyWord_eq]
    unfold roleLookupAccountSlot at haccount
    rw [haccount]
    have hcanon : addressMask &&& sevm.caller.toB256 =
        canonicalAccount sevm.caller.toB256 := by
      unfold canonicalAccount
      exact B256.and_comm _ _
    simp [B256.eqCheck, hcanon]
  case h_arm =>
    have hgas : G + 6439 - 6439 = G := by omega
    simpa only [addAccessedStorageKey_setMach,
      Devm.setMach_setMach, hgas, roleKeyWord_eq,
      roleLookupIndexSlot, roleLookupRoleSlot,
      roleLookupAccountSlot] using hbody

/-! ## The pause event tail -/

/-- Emit the gateway's exact `Paused(uint256)` log from an abstract one-word
memory image.  Naming the memory is the term-size boundary: it avoids reducing
the concrete 32-byte write in every later state. -/
private theorem pauseEvent_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {duration : B256} {G : Nat}
    (hstatic : sevm.isStatic = false)
    (hsize : memory.size = 32)
    (hread : (memory.read 0 32).1 = duration.toBytes) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 1014⟩)
      (([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop) (.ok post) := by
  obtain ⟨logged, _, _, _, _, _, _, _, _, _, hlift⟩ :=
    Func.runCompiledTo_log_step_exists (fs := fs) (sevm := sevm)
      (devm := base.setMach
        ⟨[(0 : B256), (32 : B256),
          signatureHash "Paused" [.uint256]], memory, G + 1006⟩)
      (n := (0 : Fin 4).succ)
      (i := (0 : B256)) (sz := (32 : B256))
      (topics := [signatureHash "Paused" [.uint256]]) (s := [])
      (c := 1006) (G := G) (M := memory) (M' := memory)
      (payload := duration.toBytes) (rest := Func.stop)
      rfl rfl hstatic rfl
      (by
        rw [show (0 : B256).toNat = 0 by decide,
          show (32 : B256).toNat = 32 by decide,
          Devm.extCost_word_word hsize]
        decide)
      (by
        simpa only [show (0 : B256).toNat = 0 by decide,
          show (32 : B256).toNat = 32 by decide] using hread)
      (by
        apply Mem.read_snd_eq_self
        apply memExtSize_of_le
        · rw [hsize]
        · rw [hsize]
          decide)
      (by simp only [Devm.gasLeft_setMach])
  refine ⟨logged.setMach ⟨[], memory, G⟩, ?_⟩
  unfold logWith
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1011)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1008)
      (pushCost_of_ne_zero (by decide))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]
        omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gBase) (G := G + 1006) pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by
        simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]
        omega)
  simp only [Devm.setMach_setMach]
  exact hlift (Func.RunCompiledTo.last rfl)

/-- Exact-state variant of the event tail.  The abstract-memory boundary is
retained, but the post state is named so a parent `CALL` crossing can consume
the child's world and meta projections constructively. -/
private theorem pauseEvent_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {duration : B256} {G : Nat}
    (hstatic : sevm.isStatic = false)
    (hsize : memory.size = 32)
    (hread : (memory.read 0 32).1 = duration.toBytes) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 1014⟩)
      (([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop)
      (.ok ((base.addLog
        ⟨sevm.currentTarget,
          [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
            ⟨[], memory, G⟩)) := by
  unfold logWith
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1011)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1008)
      (pushCost_of_ne_zero (by decide))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gBase) (G := G + 1006) pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach, Devm.gasLeft_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_log_of
      (n := (0 : Fin 4).succ) (i := (0 : B256)) (sz := (32 : B256))
      (topics := [signatureHash "Paused" [.uint256]]) (s := [])
      (c := 1006) (G := G) (M := memory) (data := duration.toBytes)
      rfl rfl hstatic
      (by
        rw [show (0 : B256).toNat = 0 by decide,
          show (32 : B256).toNat = 32 by decide,
          Devm.extCost_word_word hsize]
        decide)
      (by simpa only [Devm.memory_setMach,
          show (0 : B256).toNat = 0 by decide,
          show (32 : B256).toNat = 32 by decide] using hread)
      (by
        simp only [Devm.memory_setMach]
        apply Mem.read_snd_eq_self
        apply memExtSize_of_le
        · rw [hsize]
        · rw [hsize]
          decide)
      (by simp only [Devm.gasLeft_setMach])
  exact Func.RunCompiledTo.last rfl

/-- Store the non-indexed event word and emit `Paused(uint256)`.  The calldata
load and one-word memory expansion add `14` gas to the abstract event tail. -/
private theorem pauseFiniteLogTail_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 1028⟩)
      ((arg 0 ++ mstoreAt 0 ++
        [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop) (.ok post) := by
  obtain ⟨post, eventRun⟩ := pauseEvent_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (memory := Mem.empty.write 0 duration.toBytes)
    (duration := duration) (G := G) hstatic Mem.size_write_word
    Mem.read_write_word
  refine ⟨post, ?_⟩
  unfold arg cdl
  func_run (2)
  rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
  apply Func.runCompiledTo_mstoreAt
      (memory := Mem.empty) (stack := []) (value := duration)
      (word := 0) (G := G + 1014) (pushGas := gBase)
      (extGas := gMemory) (body :=
        ([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop)
  · exact pushCost_zero
  · simp
  · intro S G'
    exact Devm.extCost_empty_word
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide,
      gBase, gVerylow, gMemory] using eventRun

private theorem pauseFiniteLogTail_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 1028⟩)
      ((arg 0 ++ mstoreAt 0 ++
        [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop)
      (.ok ((base.addLog
        ⟨sevm.currentTarget,
          [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
            ⟨[], Mem.empty.write 0 duration.toBytes, G⟩)) := by
  have eventRun := pauseEvent_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (memory := Mem.empty.write 0 duration.toBytes)
    (duration := duration) (G := G) hstatic Mem.size_write_word
    Mem.read_write_word
  unfold arg cdl
  func_run (2)
  rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
  apply Func.runCompiledTo_mstoreAt
      (memory := Mem.empty) (stack := []) (value := duration)
      (word := 0) (G := G + 1014) (pushGas := gBase)
      (extGas := gMemory) (body :=
        ([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop)
  · exact pushCost_zero
  · simp
  · intro S G'
    exact Devm.extCost_empty_word
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide,
      gBase, gVerylow, gMemory] using eventRun

/-- The finite branch's store is warm because the guard has just read the same
slot, and the control starts from zero in both the current and original world.
Keeping this instruction behind its own theorem prevents the selected storage
carrier from being expanded through the later log walk. -/
private theorem pauseFiniteSstore_runCompiled
    {sevm : Sevm} {base : Devm} {value : B256} {G : Nat}
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hvalueNonzero : value ≠ 0) :
    Ninst.RunCompiled sevm
      (base.setMach
        ⟨[resumeSinceSlot, value], Mem.empty, G + 20000⟩)
      Ninst.sstore
      ((afterSstore sevm base resumeSinceSlot value).setMach
        ⟨[], Mem.empty, G⟩) := by
  have hcost : sstoreCost sevm
      base resumeSinceSlot value = 20000 := by
    unfold sstoreCost
    simp only [hwarm, if_pos, Nat.zero_add, horiginal, hresume]
    rw [sstoreValueCost, if_pos ⟨rfl, hvalueNonzero.symm⟩, if_pos rfl]
    norm_num [gasStorageSet]
  simpa only [hcost] using
    (Ninst.runCompiled_sstore_selected_setMach
      (sevm := sevm) (base := base) (key := resumeSinceSlot)
      (value := value) (stack := []) (memory := Mem.empty) (G := G)
      (by norm_num [hcost, gCallStipend]) hstatic)

/-- Install the finite resume timestamp, then execute the calldata/event tail.
The guard's preceding `SLOAD` has already warmed `resumeSinceSlot`, so the
zero-to-nonzero `SSTORE` charge is exactly `20000`. -/
private theorem pauseFiniteWrite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration value : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hvalueNonzero : value ≠ 0) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[value], Mem.empty, G + 21031⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sstore] ++
        arg 0 ++ mstoreAt 0 ++
        [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop) (.ok post) := by
  obtain ⟨post, tailRun⟩ := pauseFiniteLogTail_runCompiledTo
    (fs := fs) (sevm := sevm)
    (base := afterSstore sevm base resumeSinceSlot value)
    (duration := duration) (G := G) harg hstatic
  refine ⟨post, ?_⟩
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21028)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact pauseFiniteSstore_runCompiled
      (G := G + 1028) hresume horiginal hwarm hstatic hvalueNonzero
  exact tailRun

private theorem pauseFiniteWrite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration value : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hvalueNonzero : value ≠ 0) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[value], Mem.empty, G + 21031⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sstore] ++
        arg 0 ++ mstoreAt 0 ++
        [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop)
      (.ok (((afterSstore sevm base resumeSinceSlot value).addLog
        ⟨sevm.currentTarget,
          [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
            ⟨[], Mem.empty.write 0 duration.toBytes, G⟩)) := by
  have tailRun := pauseFiniteLogTail_exact_runCompiledTo
    (fs := fs) (sevm := sevm)
    (base := afterSstore sevm base resumeSinceSlot value)
    (duration := duration) (G := G) harg hstatic
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21028)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact pauseFiniteSstore_runCompiled
      (G := G + 1028) hresume horiginal hwarm hstatic hvalueNonzero
  exact tailRun

/-! ## The finite-duration body -/

/-- Execute the checked finite-duration arm.  Its arithmetic/source prefix and
zero branch cost `32` gas; the exact write-and-log suffix above costs `21031`.
The strict timestamp inequality is precisely the successful no-overflow arm. -/
private theorem pauseForFinite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21063⟩)
      pauseForFinite (.ok post) := by
  have hvalueNonzero : duration + sevm.benvStat.time ≠ 0 := by
    intro hzero
    rw [hzero] at htime
    have hn := B256.toNat_lt_toNat htime
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  obtain ⟨post, writeRun⟩ := pauseFiniteWrite_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (value := duration + sevm.benvStat.time)
    (G := G) harg hresume horiginal hwarm hstatic hvalueNonzero
  refine ⟨post, ?_⟩
  unfold pauseForFinite arg cdl
  func_run (7) [duration + sevm.benvStat.time, 0]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
  case h_val =>
    simp [B256.gtCheck, not_lt_of_ge (le_of_lt htime)]
  func_run (1)
  exact writeRun

/-- Lift the finite body through the successful nonzero and non-sentinel
duration guards.  The two tests and their selected branches cost `47` gas. -/
private theorem pauseForUnpausedFinite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21110⟩)
      pauseForUnpaused (.ok post) := by
  obtain ⟨post, finiteRun⟩ := pauseForFinite_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (G := G) harg hresume horiginal hwarm hstatic htime
  refine ⟨post, ?_⟩
  unfold pauseForUnpaused arg cdl
  func_run (3) [0]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck, hduration]
  func_run (1)
  func_run (4) [0]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck, Ne.symm hfinite]
  func_run (1)
  exact finiteRun

/-! ## The pause-state guard -/

/-- From a cold zero resume slot, execute the exact unpaused guard and enter
the finite-duration body.  The cold `SLOAD`, five surrounding instructions,
and selected nonzero branch cost `2125` gas. -/
private theorem pauseForGuardFinite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 23235⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
        (pauseForUnpaused <?> .call resumedExpectedSlot)) (.ok post) := by
  let warm := addAccessedStorageKey base sevm.currentTarget resumeSinceSlot
  have hresumeWarm : warm.getStorVal sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [warm, getStorVal_addAccessedStorageKey] using hresume
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      warm.accessedStorageKeys := by
    unfold warm
    change (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys.insert (sevm.currentTarget, resumeSinceSlot)
    exact Std.HashSet.mem_insert_self
  obtain ⟨post, unpausedRun⟩ := pauseForUnpausedFinite_runCompiledTo
    (fs := fs) (sevm := sevm) (base := warm)
    (duration := duration) (G := G) harg hresumeWarm horiginal hwarm hstatic
    hduration hfinite htime
  have hnotlt : ¬ sevm.benvStat.time < (0 : B256) := by
    intro h
    have hn := B256.toNat_lt_toNat h
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  refine ⟨post, ?_⟩
  func_run (5) [0, 1]
  case h_val =>
    rw [Devm.getStorVal_setMach, hresume]
    simp [B256.ltCheck, hnotlt]
  func_run (1)
  change Func.RunCompiledTo fs sevm
    (warm.setMach ⟨[], Mem.empty, G + 23235 - 2125⟩)
    pauseForUnpaused (.ok post)
  have hgas : G + 23235 - 2125 = G + 21110 := by omega
  rw [hgas]
  exact unpausedRun

/-! ## Authorization and ABI-length guard -/

/-- Compose the successful role-record walk with the finite pause guard. -/
private theorem pauseForAuthorizedFinite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (hindex : base.getStorVal sevm.currentTarget
      (roleLookupIndexSlot pauseRole sevm.caller.toB256) = 1)
    (hrole : base.getStorVal sevm.currentTarget
      (roleLookupRoleSlot pauseRole sevm.caller.toB256) = pauseRole)
    (haccount : base.getStorVal sevm.currentTarget
      (roleLookupAccountSlot pauseRole sevm.caller.toB256) =
        canonicalAccount sevm.caller.toB256)
    (hcoldIndex : (sevm.currentTarget,
      roleLookupIndexSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (hcoldRole : (sevm.currentTarget,
      roleLookupRoleSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey base sevm.currentTarget
          (roleLookupIndexSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hcoldAccount : (sevm.currentTarget,
      roleLookupAccountSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
          (roleLookupRoleSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (addAccessedStorageKey
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
            (roleLookupRoleSlot pauseRole sevm.caller.toB256))
        sevm.currentTarget
          (roleLookupAccountSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 29674⟩)
      (onlyRole pauseRole <|
        ([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot)) (.ok post) := by
  let roleWarm := addAccessedStorageKey
    (addAccessedStorageKey
      (addAccessedStorageKey base sevm.currentTarget
        (roleLookupIndexSlot pauseRole sevm.caller.toB256))
      sevm.currentTarget
        (roleLookupRoleSlot pauseRole sevm.caller.toB256))
    sevm.currentTarget
      (roleLookupAccountSlot pauseRole sevm.caller.toB256)
  have hresumeWarm : roleWarm.getStorVal sevm.currentTarget
      resumeSinceSlot = 0 := by
    simpa only [roleWarm, getStorVal_addAccessedStorageKey] using hresume
  obtain ⟨post, guardRun⟩ := pauseForGuardFinite_runCompiledTo
    (fs := fs) (sevm := sevm) (base := roleWarm)
    (duration := duration) (G := G) harg hresumeWarm horiginal hcoldResume
    hstatic hduration hfinite htime
  refine ⟨post, ?_⟩
  exact pauseOnlyRole_runCompiledTo hindex hrole haccount hcoldIndex hcoldRole
    hcoldAccount (by simpa only [roleWarm] using guardRun)

private theorem pauseForFinite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21063⟩)
      pauseForFinite
      (.ok (((afterSstore sevm base resumeSinceSlot
        (duration + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget,
            [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
              ⟨[], Mem.empty.write 0 duration.toBytes, G⟩)) := by
  have hvalueNonzero : duration + sevm.benvStat.time ≠ 0 := by
    intro hzero
    rw [hzero] at htime
    have hn := B256.toNat_lt_toNat htime
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  have writeRun := pauseFiniteWrite_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (value := duration + sevm.benvStat.time)
    (G := G) harg hresume horiginal hwarm hstatic hvalueNonzero
  unfold pauseForFinite arg cdl
  func_run (7) [duration + sevm.benvStat.time, 0]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
  case h_val =>
    simp [B256.gtCheck, not_lt_of_ge (le_of_lt htime)]
  func_run (1)
  exact writeRun

private theorem pauseForUnpausedFinite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21110⟩)
      pauseForUnpaused
      (.ok (((afterSstore sevm base resumeSinceSlot
        (duration + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget,
            [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
              ⟨[], Mem.empty.write 0 duration.toBytes, G⟩)) := by
  have finiteRun := pauseForFinite_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (G := G) harg hresume horiginal hwarm hstatic htime
  unfold pauseForUnpaused arg cdl
  func_run (3) [0]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck, hduration]
  func_run (1)
  func_run (4) [0]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck, Ne.symm hfinite]
  func_run (1)
  exact finiteRun

private theorem pauseForGuardFinite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 23235⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
        (pauseForUnpaused <?> .call resumedExpectedSlot))
      (.ok (((afterSstore sevm
        (addAccessedStorageKey base sevm.currentTarget resumeSinceSlot)
        resumeSinceSlot (duration + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget,
            [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
              ⟨[], Mem.empty.write 0 duration.toBytes, G⟩)) := by
  let warm := addAccessedStorageKey base sevm.currentTarget resumeSinceSlot
  have hresumeWarm : warm.getStorVal sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [warm, getStorVal_addAccessedStorageKey] using hresume
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      warm.accessedStorageKeys := by
    unfold warm
    change (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys.insert (sevm.currentTarget, resumeSinceSlot)
    exact Std.HashSet.mem_insert_self
  have unpausedRun := pauseForUnpausedFinite_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := warm)
    (duration := duration) (G := G) harg hresumeWarm horiginal hwarm hstatic
    hduration hfinite htime
  have hnotlt : ¬ sevm.benvStat.time < (0 : B256) := by
    intro h
    have hn := B256.toNat_lt_toNat h
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  func_run (5) [0, 1]
  case h_val =>
    rw [Devm.getStorVal_setMach, hresume]
    simp [B256.ltCheck, hnotlt]
  func_run (1)
  change Func.RunCompiledTo fs sevm
    (warm.setMach ⟨[], Mem.empty, G + 23235 - 2125⟩)
    pauseForUnpaused _
  have hgas : G + 23235 - 2125 = G + 21110 := by omega
  rw [hgas]
  exact unpausedRun

private theorem pauseForAuthorizedFinite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (hindex : base.getStorVal sevm.currentTarget
      (roleLookupIndexSlot pauseRole sevm.caller.toB256) = 1)
    (hrole : base.getStorVal sevm.currentTarget
      (roleLookupRoleSlot pauseRole sevm.caller.toB256) = pauseRole)
    (haccount : base.getStorVal sevm.currentTarget
      (roleLookupAccountSlot pauseRole sevm.caller.toB256) =
        canonicalAccount sevm.caller.toB256)
    (hcoldIndex : (sevm.currentTarget,
      roleLookupIndexSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (hcoldRole : (sevm.currentTarget,
      roleLookupRoleSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey base sevm.currentTarget
          (roleLookupIndexSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hcoldAccount : (sevm.currentTarget,
      roleLookupAccountSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
          (roleLookupRoleSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm sevm base).accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 29674⟩)
      (onlyRole pauseRole <|
        ([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot))
      (.ok (pauseFinitePost sevm base duration G)) := by
  have hresumeWarm : (pauseRoleWarm sevm base).getStorVal
      sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [pauseRoleWarm, getStorVal_addAccessedStorageKey] using hresume
  have guardRun := pauseForGuardFinite_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := pauseRoleWarm sevm base)
    (duration := duration) (G := G) harg hresumeWarm horiginal hcoldResume
    hstatic hduration hfinite htime
  exact pauseOnlyRole_runCompiledTo hindex hrole haccount hcoldIndex hcoldRole
    hcoldAccount (by
      simpa only [pauseFinitePost, pauseLogged, pauseStored, pauseResumeWarm,
        pauseRoleWarm, pauseEvent] using guardRun)

/-- The successful one-word ABI length guard costs `21` gas. -/
private theorem pauseForFiniteBody_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {G : Nat}
    (hsize : sevm.data.length.toB256 <? 36 = 0)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (onlyRole pauseRole <|
        ([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot)) (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21⟩) pauseFor (.ok post) := by
  unfold pauseFor requireStaticArgs
  func_run (4) [0]
  case h_arm =>
    have hgas : G + 21 - 21 = G := by omega
    rw [hgas]
    exact hbody

/-! ## Exact runtime route -/

private theorem nonpayableZero_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {body : Func} {post : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩) body (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 19⟩)
      (nonpayable body) (.ok post) := by
  unfold nonpayable
  func_run (3) [1]
  case h_val => simp [hvalue, B256.eqCheck]
  simpa only [Devm.setMach_setMach,
    show G + 19 - 19 = G by omega] using hbody

/-- The selected first entry of the production linear dispatcher costs `25`
gas, including the final selector pop. -/
private theorem pauseForFirstDispatch_runCompiledTo
    {dp : DeployParams} {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {G : Nat}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayable pauseFor) (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selPauseFor], Mem.empty, G + 25⟩)
      (linearDispatchWith fallbackSlot (funcs dp)) (.ok post) := by
  unfold funcs linearDispatchWith
  func_run (5) [1]
  exact hbody

private theorem fsig_prepend_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {selector : B256} {post : Devm} {G : Nat} {tail : Func}
    (hselector : Sevm.selector sevm = selector)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], Mem.empty, G⟩) tail (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 11⟩)
      (fsig +++ tail) (.ok post) := by
  unfold fsig cdl shiftRight
  func_run (4) [selector]
  exact hbody

private theorem pauseForRuntimeMain_runCompiledTo
    {dp : DeployParams} {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseFor)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayable pauseFor) (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 57⟩)
      (runtimeMain dp) (.ok post) := by
  have hdispatch := pauseForFirstDispatch_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G) hbody
  have hsig := fsig_prepend_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (selector := selPauseFor) (G := G + 25)
    hselector (by
      have hgas : G + 25 + 11 - 11 = G + 25 := by omega
      simpa only [Devm.setMach_setMach, hgas] using hdispatch)
  unfold runtimeMain
  func_run (4) [0]
  case h_arm =>
    have hgas : G + 57 - 21 = G + 36 := by omega
    rw [hgas]
    exact hsig

/-- Lift a successful finite `pauseFor` body through nonpayability, the exact
first selector route, the short-calldata guard, and the program entry burn.
The runtime overhead outside `pauseFor` is `77` gas. -/
theorem pauseForFinite_runtime_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseFor)
    (hsize : sevm.data.length.toB256 <? 36 = 0)
    (hvalue : sevm.value = 0)
    (hindex : base.getStorVal sevm.currentTarget
      (roleLookupIndexSlot pauseRole sevm.caller.toB256) = 1)
    (hrole : base.getStorVal sevm.currentTarget
      (roleLookupRoleSlot pauseRole sevm.caller.toB256) = pauseRole)
    (haccount : base.getStorVal sevm.currentTarget
      (roleLookupAccountSlot pauseRole sevm.caller.toB256) =
        canonicalAccount sevm.caller.toB256)
    (hcoldIndex : (sevm.currentTarget,
      roleLookupIndexSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (hcoldRole : (sevm.currentTarget,
      roleLookupRoleSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey base sevm.currentTarget
          (roleLookupIndexSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hcoldAccount : (sevm.currentTarget,
      roleLookupAccountSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
          (roleLookupRoleSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (addAccessedStorageKey
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
            (roleLookupRoleSlot pauseRole sevm.caller.toB256))
        sevm.currentTarget
          (roleLookupAccountSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, G + 29772⟩)
      (runtime dp) (.ok (pauseFinitePost sevm base duration G)) := by
  let fs := (runtime dp).main :: (runtime dp).aux
  have authorizedRun := pauseForAuthorizedFinite_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (G := G) hindex hrole haccount hcoldIndex hcoldRole
    hcoldAccount harg hresume horiginal (by
      simpa only [pauseRoleWarm] using hcoldResume) hstatic hduration hfinite htime
  have pauseRun := pauseForFiniteBody_runCompiledTo
    (hsize := hsize) (hbody := authorizedRun)
  have wrappedRun := nonpayableZero_runCompiledTo hvalue pauseRun
  have mainRun := pauseForRuntimeMain_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G + 29714) hguard hselector (by
      have hgas : G + 29714 = G + 29695 + 19 := by omega
      simpa only [Devm.setMach_setMach, hgas] using wrappedRun)
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, G + 29771⟩)
    (G := G + 29771) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · simpa only [runtime, fs, Devm.setMach_setMach,
      show G + 29714 + 57 = G + 29771 by omega] using mainRun

/-- Total execution wrapper used by an enclosing `CALL`: the code witness is
supplied independently by the installer, while the child execution itself is
the constructive runtime walk above. -/
theorem pauseForFinite_exec
    (m : Msg) (dp : DeployParams) (duration : B256) (G : Nat)
    (hcompile : some m.code.toList = Prog.compile (runtime dp))
    (hdata : m.data = pauseForCalldata duration)
    (hgas : m.gas = G + 29772)
    (hvalue : m.value = 0)
    (hindex : (initDevm m).getStorVal (initSevm m).currentTarget
      (roleLookupIndexSlot pauseRole (initSevm m).caller.toB256) = 1)
    (hrole : (initDevm m).getStorVal (initSevm m).currentTarget
      (roleLookupRoleSlot pauseRole (initSevm m).caller.toB256) = pauseRole)
    (haccount : (initDevm m).getStorVal (initSevm m).currentTarget
      (roleLookupAccountSlot pauseRole (initSevm m).caller.toB256) =
        canonicalAccount (initSevm m).caller.toB256)
    (hcoldIndex : ((initSevm m).currentTarget,
      roleLookupIndexSlot pauseRole (initSevm m).caller.toB256) ∉
        (initDevm m).accessedStorageKeys)
    (hcoldRole : ((initSevm m).currentTarget,
      roleLookupRoleSlot pauseRole (initSevm m).caller.toB256) ∉
        (addAccessedStorageKey (initDevm m) (initSevm m).currentTarget
          (roleLookupIndexSlot pauseRole
            (initSevm m).caller.toB256)).accessedStorageKeys)
    (hcoldAccount : ((initSevm m).currentTarget,
      roleLookupAccountSlot pauseRole (initSevm m).caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey (initDevm m) (initSevm m).currentTarget
            (roleLookupIndexSlot pauseRole (initSevm m).caller.toB256))
          (initSevm m).currentTarget
          (roleLookupRoleSlot pauseRole
            (initSevm m).caller.toB256)).accessedStorageKeys)
    (hresume : (initDevm m).getStorVal (initSevm m).currentTarget
      resumeSinceSlot = 0)
    (horiginal : getOrigStorVal (initSevm m) (initSevm m).currentTarget
      resumeSinceSlot = 0)
    (hcoldResume : ((initSevm m).currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm (initSevm m) (initDevm m)).accessedStorageKeys)
    (hstatic : (initSevm m).isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : (initSevm m).benvStat.time <
      duration + (initSevm m).benvStat.time) :
    exec (initEvm m) =
      .ok (pauseFinitePost (initSevm m) (initDevm m) duration G) := by
  have hdata' : (initSevm m).data = pauseForCalldata duration := hdata
  have hguard : (initSevm m).data.length.toB256 <? (4 : B256) = 0 := by
    rw [hdata', pauseForCalldata_length]
    decide
  have hselector : Sevm.selector (initSevm m) = selPauseFor := by
    apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selPauseFor) (tail := duration.toBytes)
    · rfl
    · simpa [pauseForCalldata] using hdata'
  have hsize : (initSevm m).data.length.toB256 <? 36 = 0 := by
    rw [hdata', pauseForCalldata_length]
    decide
  have harg : Sevm.dataWord (initSevm m) 4 = duration := by
    apply dataWord_of_append
      (pre := abiSelectorBytes selPauseFor) (post := [])
    · rw [abiSelectorBytes_length]
      rfl
    · simpa [pauseForCalldata] using hdata'
  have walk := pauseForFinite_runtime_runCompiledTo
    (dp := dp) (sevm := initSevm m) (base := initDevm m)
    (duration := duration) (G := G) hguard hselector hsize hvalue
    hindex hrole haccount hcoldIndex hcoldRole hcoldAccount harg hresume
    horiginal (by simpa only [pauseRoleWarm] using hcoldResume) hstatic
    hduration hfinite htime
  have hbase : (initDevm m).setMach
      ⟨[], Mem.empty, G + 29772⟩ = initDevm m := by
    rw [← hgas]
    rfl
  rw [hbase] at walk
  exact Prog.exec_of_runCompiledTo walk hcompile

/-! ## Independent infinite-sentinel arm -/

private theorem pauseSentinelEventTail_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 1025⟩)
      ((emitOneWord (signatureHash "Paused" [.uint256]) pauseInfinitely) +++
        Func.stop) (.ok post) := by
  obtain ⟨post, eventRun⟩ := pauseEvent_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (memory := Mem.empty.write 0 pauseInfinitely.toBytes)
    (duration := pauseInfinitely) (G := G) hstatic Mem.size_write_word
    Mem.read_write_word
  refine ⟨post, ?_⟩
  unfold emitOneWord
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1022)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.runCompiledTo_mstoreAt
      (memory := Mem.empty) (stack := []) (value := pauseInfinitely)
      (word := 0) (G := G + 1014) (pushGas := gBase)
      (extGas := gMemory) (body :=
        ([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop)
  · exact pushCost_zero
  · simp
  · intro S G'
    exact Devm.extCost_empty_word
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide,
      gBase, gVerylow, gMemory] using eventRun

private theorem pauseSentinelEventTail_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 1025⟩)
      ((emitOneWord (signatureHash "Paused" [.uint256]) pauseInfinitely) +++
        Func.stop)
      (.ok ((base.addLog (pauseEvent sevm pauseInfinitely)).setMach
        ⟨[], Mem.empty.write 0 pauseInfinitely.toBytes, G⟩)) := by
  have eventRun := pauseEvent_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (memory := Mem.empty.write 0 pauseInfinitely.toBytes)
    (duration := pauseInfinitely) (G := G) hstatic Mem.size_write_word
    Mem.read_write_word
  unfold emitOneWord
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1022)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.runCompiledTo_mstoreAt
      (memory := Mem.empty) (stack := []) (value := pauseInfinitely)
      (word := 0) (G := G + 1014) (pushGas := gBase)
      (extGas := gMemory) (body :=
        ([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop)
  · exact pushCost_zero
  · simp
  · intro S G'
    exact Devm.extCost_empty_word
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide,
      gBase, gVerylow, gMemory, pauseEvent] using eventRun

/-- The sentinel store and its fixed event consume exactly `21031` gas. -/
private theorem pauseForSentinel_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21031⟩)
      pauseForSentinel (.ok post) := by
  obtain ⟨post, eventRun⟩ := pauseSentinelEventTail_runCompiledTo
    (fs := fs) (sevm := sevm)
    (base := afterSstore sevm base resumeSinceSlot pauseInfinitely)
    (G := G) hstatic
  refine ⟨post, ?_⟩
  unfold pauseForSentinel emitOneWord
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21028)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21025)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact pauseFiniteSstore_runCompiled
      (G := G + 1025) hresume horiginal hwarm hstatic
      (by decide +kernel)
  exact eventRun

private theorem pauseForSentinel_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21031⟩)
      pauseForSentinel
      (.ok (((afterSstore sevm base resumeSinceSlot pauseInfinitely).addLog
        (pauseEvent sevm pauseInfinitely)).setMach
          ⟨[], Mem.empty.write 0 pauseInfinitely.toBytes, G⟩)) := by
  have eventRun := pauseSentinelEventTail_exact_runCompiledTo
    (fs := fs) (sevm := sevm)
    (base := afterSstore sevm base resumeSinceSlot pauseInfinitely)
    (G := G) hstatic
  unfold pauseForSentinel emitOneWord
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21028)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21025)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach]
  apply Func.RunCompiledTo.next
  · exact pauseFiniteSstore_runCompiled
      (G := G + 1025) hresume horiginal hwarm hstatic
      (by decide +kernel)
  exact eventRun

/-- Select the sentinel arm after the successful nonzero test.  Its positive
sentinel branch is one gas dearer than the finite zero branch, so the two
guards cost `48` gas. -/
private theorem pauseForUnpausedSentinel_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21079⟩)
      pauseForUnpaused (.ok post) := by
  obtain ⟨post, sentinelRun⟩ := pauseForSentinel_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base) (G := G)
    hresume horiginal hwarm hstatic
  refine ⟨post, ?_⟩
  unfold pauseForUnpaused arg cdl
  func_run (3) [0]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    decide +kernel
  func_run (1)
  func_run (4) [1]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck]
  func_run (1)
  exact sentinelRun

private theorem pauseForUnpausedSentinel_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21079⟩)
      pauseForUnpaused
      (.ok (((afterSstore sevm base resumeSinceSlot pauseInfinitely).addLog
        (pauseEvent sevm pauseInfinitely)).setMach
          ⟨[], Mem.empty.write 0 pauseInfinitely.toBytes, G⟩)) := by
  have sentinelRun := pauseForSentinel_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base) (G := G)
    hresume horiginal hwarm hstatic
  unfold pauseForUnpaused arg cdl
  func_run (3) [0]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    decide +kernel
  func_run (1)
  func_run (4) [1]
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck]
  func_run (1)
  exact sentinelRun

private theorem pauseForGuardSentinel_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 23204⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
        (pauseForUnpaused <?> .call resumedExpectedSlot)) (.ok post) := by
  let warm := addAccessedStorageKey base sevm.currentTarget resumeSinceSlot
  have hresumeWarm : warm.getStorVal sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [warm, getStorVal_addAccessedStorageKey] using hresume
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      warm.accessedStorageKeys := by
    unfold warm
    change (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys.insert (sevm.currentTarget, resumeSinceSlot)
    exact Std.HashSet.mem_insert_self
  obtain ⟨post, unpausedRun⟩ := pauseForUnpausedSentinel_runCompiledTo
    (fs := fs) (sevm := sevm) (base := warm) (G := G)
    harg hresumeWarm horiginal hwarm hstatic
  have hnotlt : ¬ sevm.benvStat.time < (0 : B256) := by
    intro h
    have hn := B256.toNat_lt_toNat h
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  refine ⟨post, ?_⟩
  func_run (5) [0, 1]
  case h_val =>
    rw [Devm.getStorVal_setMach, hresume]
    simp [B256.ltCheck, hnotlt]
  func_run (1)
  change Func.RunCompiledTo fs sevm
    (warm.setMach ⟨[], Mem.empty, G + 23204 - 2125⟩)
    pauseForUnpaused (.ok post)
  have hgas : G + 23204 - 2125 = G + 21079 := by omega
  rw [hgas]
  exact unpausedRun

private theorem pauseForGuardSentinel_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 23204⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
        (pauseForUnpaused <?> .call resumedExpectedSlot))
      (.ok (((afterSstore sevm
        (addAccessedStorageKey base sevm.currentTarget resumeSinceSlot)
        resumeSinceSlot pauseInfinitely).addLog
          (pauseEvent sevm pauseInfinitely)).setMach
            ⟨[], Mem.empty.write 0 pauseInfinitely.toBytes, G⟩)) := by
  let warm := addAccessedStorageKey base sevm.currentTarget resumeSinceSlot
  have hresumeWarm : warm.getStorVal sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [warm, getStorVal_addAccessedStorageKey] using hresume
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      warm.accessedStorageKeys := by
    unfold warm
    change (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys.insert (sevm.currentTarget, resumeSinceSlot)
    exact Std.HashSet.mem_insert_self
  have unpausedRun := pauseForUnpausedSentinel_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := warm) (G := G)
    harg hresumeWarm horiginal hwarm hstatic
  have hnotlt : ¬ sevm.benvStat.time < (0 : B256) := by
    intro h
    have hn := B256.toNat_lt_toNat h
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  func_run (5) [0, 1]
  case h_val =>
    rw [Devm.getStorVal_setMach, hresume]
    simp [B256.ltCheck, hnotlt]
  func_run (1)
  change Func.RunCompiledTo fs sevm
    (warm.setMach ⟨[], Mem.empty, G + 23204 - 2125⟩)
    pauseForUnpaused _
  have hgas : G + 23204 - 2125 = G + 21079 := by omega
  rw [hgas]
  exact unpausedRun

private theorem pauseForAuthorizedSentinel_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hindex : base.getStorVal sevm.currentTarget
      (roleLookupIndexSlot pauseRole sevm.caller.toB256) = 1)
    (hrole : base.getStorVal sevm.currentTarget
      (roleLookupRoleSlot pauseRole sevm.caller.toB256) = pauseRole)
    (haccount : base.getStorVal sevm.currentTarget
      (roleLookupAccountSlot pauseRole sevm.caller.toB256) =
        canonicalAccount sevm.caller.toB256)
    (hcoldIndex : (sevm.currentTarget,
      roleLookupIndexSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (hcoldRole : (sevm.currentTarget,
      roleLookupRoleSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey base sevm.currentTarget
          (roleLookupIndexSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hcoldAccount : (sevm.currentTarget,
      roleLookupAccountSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
          (roleLookupRoleSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm sevm base).accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 29643⟩)
      (onlyRole pauseRole <|
        ([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot))
      (.ok (pauseSentinelPost sevm base G)) := by
  have hresumeWarm : (pauseRoleWarm sevm base).getStorVal
      sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [pauseRoleWarm, getStorVal_addAccessedStorageKey] using hresume
  have guardRun := pauseForGuardSentinel_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := pauseRoleWarm sevm base)
    (G := G) harg hresumeWarm horiginal hcoldResume hstatic
  exact pauseOnlyRole_runCompiledTo hindex hrole haccount hcoldIndex hcoldRole
    hcoldAccount (by
      simpa only [pauseSentinelPost, pauseResumeWarm, pauseRoleWarm,
        pauseEvent] using guardRun)

/-- Independent successful runtime witness for the infinite sentinel.  Its
exact derived charge is `29741`, 31 below the finite-duration arm. -/
theorem pauseForSentinel_runtime_exact_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseFor)
    (hsize : sevm.data.length.toB256 <? 36 = 0)
    (hvalue : sevm.value = 0)
    (hindex : base.getStorVal sevm.currentTarget
      (roleLookupIndexSlot pauseRole sevm.caller.toB256) = 1)
    (hrole : base.getStorVal sevm.currentTarget
      (roleLookupRoleSlot pauseRole sevm.caller.toB256) = pauseRole)
    (haccount : base.getStorVal sevm.currentTarget
      (roleLookupAccountSlot pauseRole sevm.caller.toB256) =
        canonicalAccount sevm.caller.toB256)
    (hcoldIndex : (sevm.currentTarget,
      roleLookupIndexSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (hcoldRole : (sevm.currentTarget,
      roleLookupRoleSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey base sevm.currentTarget
          (roleLookupIndexSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hcoldAccount : (sevm.currentTarget,
      roleLookupAccountSlot pauseRole sevm.caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
          (roleLookupRoleSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (addAccessedStorageKey
        (addAccessedStorageKey
          (addAccessedStorageKey base sevm.currentTarget
            (roleLookupIndexSlot pauseRole sevm.caller.toB256))
          sevm.currentTarget
            (roleLookupRoleSlot pauseRole sevm.caller.toB256))
        sevm.currentTarget
          (roleLookupAccountSlot pauseRole
            sevm.caller.toB256)).accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, G + 29741⟩)
      (runtime dp) (.ok (pauseSentinelPost sevm base G)) := by
  let fs := (runtime dp).main :: (runtime dp).aux
  have authorizedRun := pauseForAuthorizedSentinel_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base) (G := G)
    hindex hrole haccount hcoldIndex hcoldRole hcoldAccount harg hresume
    horiginal (by simpa only [pauseRoleWarm] using hcoldResume) hstatic
  have pauseRun := pauseForFiniteBody_runCompiledTo
    (hsize := hsize) (hbody := authorizedRun)
  have wrappedRun := nonpayableZero_runCompiledTo hvalue pauseRun
  have mainRun := pauseForRuntimeMain_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G + 29683) hguard hselector (by
      have hgas : G + 29683 = G + 29664 + 19 := by omega
      simpa only [Devm.setMach_setMach, hgas] using wrappedRun)
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, G + 29740⟩)
    (G := G + 29740) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · simpa only [runtime, fs, Devm.setMach_setMach,
      show G + 29683 + 57 = G + 29740 by omega] using mainRun

/-- Total execution wrapper for the infinite-sentinel child called by the
composed circuit-breaker route. -/
theorem pauseForSentinel_exec
    (m : Msg) (dp : DeployParams) (G : Nat)
    (hcompile : some m.code.toList = Prog.compile (runtime dp))
    (hdata : m.data = pauseForCalldata pauseInfinitely)
    (hgas : m.gas = G + 29741)
    (hvalue : m.value = 0)
    (hindex : (initDevm m).getStorVal (initSevm m).currentTarget
      (roleLookupIndexSlot pauseRole (initSevm m).caller.toB256) = 1)
    (hrole : (initDevm m).getStorVal (initSevm m).currentTarget
      (roleLookupRoleSlot pauseRole (initSevm m).caller.toB256) = pauseRole)
    (haccount : (initDevm m).getStorVal (initSevm m).currentTarget
      (roleLookupAccountSlot pauseRole (initSevm m).caller.toB256) =
        canonicalAccount (initSevm m).caller.toB256)
    (hcoldIndex : ((initSevm m).currentTarget,
      roleLookupIndexSlot pauseRole (initSevm m).caller.toB256) ∉
        (initDevm m).accessedStorageKeys)
    (hcoldRole : ((initSevm m).currentTarget,
      roleLookupRoleSlot pauseRole (initSevm m).caller.toB256) ∉
        (addAccessedStorageKey (initDevm m) (initSevm m).currentTarget
          (roleLookupIndexSlot pauseRole
            (initSevm m).caller.toB256)).accessedStorageKeys)
    (hcoldAccount : ((initSevm m).currentTarget,
      roleLookupAccountSlot pauseRole (initSevm m).caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey (initDevm m) (initSevm m).currentTarget
            (roleLookupIndexSlot pauseRole (initSevm m).caller.toB256))
          (initSevm m).currentTarget
          (roleLookupRoleSlot pauseRole
            (initSevm m).caller.toB256)).accessedStorageKeys)
    (hresume : (initDevm m).getStorVal (initSevm m).currentTarget
      resumeSinceSlot = 0)
    (horiginal : getOrigStorVal (initSevm m) (initSevm m).currentTarget
      resumeSinceSlot = 0)
    (hcoldResume : ((initSevm m).currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm (initSevm m) (initDevm m)).accessedStorageKeys)
    (hstatic : (initSevm m).isStatic = false) :
    exec (initEvm m) =
      .ok (pauseSentinelPost (initSevm m) (initDevm m) G) := by
  have hdata' : (initSevm m).data =
      pauseForCalldata pauseInfinitely := hdata
  have hguard : (initSevm m).data.length.toB256 <? (4 : B256) = 0 := by
    rw [hdata', pauseForCalldata_length]
    decide
  have hselector : Sevm.selector (initSevm m) = selPauseFor := by
    apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selPauseFor) (tail := pauseInfinitely.toBytes)
    · rfl
    · simpa [pauseForCalldata] using hdata'
  have hsize : (initSevm m).data.length.toB256 <? 36 = 0 := by
    rw [hdata', pauseForCalldata_length]
    decide
  have harg : Sevm.dataWord (initSevm m) 4 = pauseInfinitely := by
    apply dataWord_of_append
      (pre := abiSelectorBytes selPauseFor) (post := [])
    · rw [abiSelectorBytes_length]
      rfl
    · simpa [pauseForCalldata] using hdata'
  have walk := pauseForSentinel_runtime_exact_runCompiledTo
    (dp := dp) (sevm := initSevm m) (base := initDevm m) (G := G)
    hguard hselector hsize hvalue hindex hrole haccount hcoldIndex hcoldRole
    hcoldAccount harg hresume horiginal
    (by simpa only [pauseRoleWarm] using hcoldResume) hstatic
  have hbase : (initDevm m).setMach
      ⟨[], Mem.empty, G + 29741⟩ = initDevm m := by
    rw [← hgas]
    rfl
  rw [hbase] at walk
  exact Prog.exec_of_runCompiledTo walk hcompile

/-! ## Exact `isPaused()` query -/

private theorem withOutput_getStorVal (devm : Devm) (out : Bytes)
    (owner : Adr) (key : B256) :
    (devm.withOutput out).getStorVal owner key = devm.getStorVal owner key :=
  rfl

private theorem memRead_getStorVal (devm : Devm) (index size : Nat)
    (owner : Adr) (key : B256) :
    (devm.memRead index size).2.getStorVal owner key =
      devm.getStorVal owner key := rfl

private theorem withOutput_gasLeft (devm : Devm) (out : Bytes) :
    (devm.withOutput out).gasLeft = devm.gasLeft := rfl

private theorem memRead_gasLeft (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.gasLeft = devm.gasLeft := rfl

/-- The exact query body costs `121` gas with a warm resume slot and returns
the canonical true word.  The extra one gas versus the control stub is the
production gateway's nonzero tagged storage slot. -/
private theorem isPaused_true_warm_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {storedUntil : B256} {G : Nat}
    (hstored : base.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post, Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 121⟩)
        isPaused (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.meta = (base.withOutput (1 : B256).toBytes).meta ∧
      post.world = base.world := by
  unfold isPaused returnWord mstoreAt returnMemoryRange pushList
  apply Exists.intro
  constructor
  · func_run [1, 3]
    case h_val =>
      rw [Devm.getStorVal_setMach, hstored]
      simp [B256.ltCheck, hpaused]
    case h_ext => exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_ret_word (i := 0) (sz := 32) (s := [])
        (e := 0) (G := G) (out := (1 : B256).toBytes)
      · rfl
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide,
          show ((0 : B256) * 32).toNat = 0 by decide]
        exact Devm.extCost_word_word Mem.size_write_word
      · simp only [Devm.gasLeft_setMach]
        omega
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide]
        exact Devm.memRead_word_fst
          (by rw [show ((0 : B256) * 32).toNat = 0 by decide]; rfl)
  · refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
    · rw [withOutput_getStorVal, memRead_getStorVal,
        Devm.getStorVal_setMach, Devm.getStorVal_setMach, hstored]
    · rw [withOutput_gasLeft, memRead_gasLeft,
        Devm.gasLeft_setMach]
    · rfl
    · rfl

private theorem isPausedSecondDispatch_runCompiledTo
    {dp : DeployParams} {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {G : Nat}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayable isPaused) (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selIsPaused], Mem.empty, G + 47⟩)
      (linearDispatchWith fallbackSlot (funcs dp)) (.ok post) := by
  unfold funcs linearDispatchWith
  func_run (9) [0, 1]
  exact hbody

private theorem isPausedRuntimeMain_runCompiledTo
    {dp : DeployParams} {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selIsPaused)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (nonpayable isPaused) (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 79⟩)
      (runtimeMain dp) (.ok post) := by
  have hdispatch := isPausedSecondDispatch_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G) hbody
  have hsig := fsig_prepend_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (selector := selIsPaused) (G := G + 47)
    hselector (by
      have hgas : G + 47 + 11 - 11 = G + 47 := by omega
      simpa only [Devm.setMach_setMach, hgas] using hdispatch)
  unfold runtimeMain
  func_run (4) [0]
  case h_arm =>
    have hgas : G + 79 - 21 = G + 58 := by omega
    rw [hgas]
    exact hsig

/-- A warm successful `isPaused()` runtime call consumes exactly `220` gas
and returns canonical true without changing the stored resume word. -/
theorem isPaused_true_warm_runtime_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {storedUntil : B256} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selIsPaused)
    (hvalue : sevm.value = 0)
    (hstored : base.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post, Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + 220⟩)
        (runtime dp) (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.meta = (base.withOutput (1 : B256).toBytes).meta ∧
      post.world = base.world := by
  let fs := (runtime dp).main :: (runtime dp).aux
  obtain ⟨post, queryRun, output, stored, gas, error, hmeta, world⟩ :=
    isPaused_true_warm_runCompiledTo
      (fs := fs) (sevm := sevm) (base := base)
      (storedUntil := storedUntil) (G := G) hstored hwarm hpaused
  have wrappedRun := nonpayableZero_runCompiledTo hvalue queryRun
  have mainRun := isPausedRuntimeMain_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G + 140) hguard hselector (by
      have hgas : G + 140 = G + 121 + 19 := by omega
      simpa only [Devm.setMach_setMach, hgas] using wrappedRun)
  refine ⟨post, ?_, output, stored, gas, error, hmeta, world⟩
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, G + 219⟩)
    (G := G + 219) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · simpa only [runtime, fs, Devm.setMach_setMach,
      show G + 140 + 79 = G + 219 by omega] using mainRun

/-- Total-execution wrapper for an enclosing warm `STATICCALL`.  The program
walk remains the source of the result; the installed code witness only
connects that walk to `exec`. -/
theorem isPaused_true_warm_exec
    (m : Msg) (dp : DeployParams) (storedUntil : B256) (G : Nat)
    (hcompile : some m.code.toList = Prog.compile (runtime dp))
    (hdata : m.data = isPausedCalldata)
    (hgas : m.gas = G + 220)
    (hvalue : m.value = 0)
    (hstored : (initDevm m).getStorVal (initSevm m).currentTarget
      resumeSinceSlot = storedUntil)
    (hwarm : ((initSevm m).currentTarget, resumeSinceSlot) ∈
      (initDevm m).accessedStorageKeys)
    (hpaused : (initSevm m).benvStat.time < storedUntil) :
    ∃ post,
      exec (initEvm m) = .ok post ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal (initSevm m).currentTarget resumeSinceSlot =
        storedUntil ∧
      post.gasLeft = G ∧
      post.error = (initDevm m).error ∧
      post.meta = ((initDevm m).withOutput (1 : B256).toBytes).meta ∧
      post.world = (initDevm m).world := by
  have hdata' : (initSevm m).data = isPausedCalldata := hdata
  have hguard : (initSevm m).data.length.toB256 <? (4 : B256) = 0 := by
    rw [hdata', isPausedCalldata_length]
    decide
  have hselector : Sevm.selector (initSevm m) = selIsPaused := by
    apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selIsPaused) (tail := [])
    · rfl
    · simpa [isPausedCalldata] using hdata'
  obtain ⟨post, walk, output, stored, gas, error, hmeta, world⟩ :=
    isPaused_true_warm_runtime_runCompiledTo
      (dp := dp) (sevm := initSevm m) (base := initDevm m)
      (storedUntil := storedUntil) (G := G) hguard hselector hvalue
      hstored hwarm hpaused
  have hbase : (initDevm m).setMach
      ⟨[], Mem.empty, G + 220⟩ = initDevm m := by
    rw [← hgas]
    rfl
  rw [hbase] at walk
  exact ⟨post, Prog.exec_of_runCompiledTo walk hcompile, output, stored,
    gas, error, hmeta, world⟩

/-- The same successful query from a cold resume slot costs exactly `2121`
gas in the body: precisely 2000 more than the warm case. -/
private theorem isPaused_true_cold_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {storedUntil : B256} {G : Nat}
    (hstored : base.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post, Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 2121⟩)
        isPaused (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.meta =
        ((addAccessedStorageKey base sevm.currentTarget resumeSinceSlot).withOutput
          (1 : B256).toBytes).meta ∧
      post.world = base.world := by
  unfold isPaused returnWord mstoreAt returnMemoryRange pushList
  apply Exists.intro
  constructor
  · func_run [1, 3]
    case h_val =>
      rw [Devm.getStorVal_setMach, hstored]
      simp [B256.ltCheck, hpaused]
    case h_ext => exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_ret_word (i := 0) (sz := 32) (s := [])
        (e := 0) (G := G) (out := (1 : B256).toBytes)
      · rfl
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide,
          show ((0 : B256) * 32).toNat = 0 by decide]
        exact Devm.extCost_word_word Mem.size_write_word
      · simp only [Devm.gasLeft_setMach]
        omega
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide]
        exact Devm.memRead_word_fst
          (by rw [show ((0 : B256) * 32).toNat = 0 by decide]; rfl)
  · refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
    · rw [withOutput_getStorVal, memRead_getStorVal,
        Devm.getStorVal_setMach, Devm.getStorVal_setMach,
        getStorVal_addAccessedStorageKey, Devm.getStorVal_setMach, hstored]
    · rw [withOutput_gasLeft, memRead_gasLeft,
        Devm.gasLeft_setMach]
    · rfl
    · rfl

/-- A cold successful `isPaused()` runtime call consumes exactly `2220` gas,
establishing the selected warm/cold schedule boundary. -/
theorem isPaused_true_cold_runtime_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    {storedUntil : B256} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selIsPaused)
    (hvalue : sevm.value = 0)
    (hstored : base.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post, Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + 2220⟩)
        (runtime dp) (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil ∧
      post.gasLeft = G := by
  let fs := (runtime dp).main :: (runtime dp).aux
  obtain ⟨post, queryRun, output, stored, gas, _error, _hmeta, _world⟩ :=
    isPaused_true_cold_runCompiledTo
      (fs := fs) (sevm := sevm) (base := base)
      (storedUntil := storedUntil) (G := G) hstored hcold hpaused
  have wrappedRun := nonpayableZero_runCompiledTo hvalue queryRun
  have mainRun := isPausedRuntimeMain_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G + 2140) hguard hselector (by
      have hgas : G + 2140 = G + 2121 + 19 := by omega
      simpa only [Devm.setMach_setMach, hgas] using wrappedRun)
  refine ⟨post, ?_, output, stored, gas⟩
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, G + 2219⟩)
    (G := G + 2219) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · simpa only [runtime, fs, Devm.setMach_setMach,
      show G + 2140 + 79 = G + 2219 by omega] using mainRun

end LidoTriggerableWithdrawalsGateway
end Blanc
