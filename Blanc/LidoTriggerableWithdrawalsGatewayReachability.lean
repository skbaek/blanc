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

/-- The successful `onlyRole(PAUSE_ROLE)` membership read warms its single
nested-keccak slot. -/
def pauseRoleWarm (sevm : Sevm) (base : Devm) : Devm :=
  addAccessedStorageKey base sevm.currentTarget
    (roleMembershipSlot pauseRole sevm.caller.toB256)

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

/-- Exact two-word scratch image left by the successful `onlyRole(PAUSE_ROLE)`
key walk: the caller word below the role-data word.  The guard continuation
starts from this image rather than empty memory. -/
def pauseAuthScratch (caller : B256) : Mem :=
  ((((Mem.empty.write 0 pauseRole.toBytes).write 32
    accessControlRolesPosition.toBytes).write 32
    (roleDataSlot pauseRole).toBytes).write 0 caller.toBytes)

private theorem pauseAuthScratch_size (caller : B256) :
    (pauseAuthScratch caller).size = 64 := by
  unfold pauseAuthScratch
  simp only [Mem.size_write_word_at, Mem.empty]
  decide

/-- The inner key hash over the staged role words is the role-data slot.  The
forward walk leaves the hash as the evaluated application (a `B256` hint would
offer this equation to the walk's automatic value dischargers, whose attempt
exhausts the recursion budget); this lemma names it afterwards. -/
private theorem pauseKeyHash1 :
    Bytes.keccak (((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes).read (0 : B256).toNat
      (64 : B256).toNat).1 = roleDataSlot pauseRole := by
  have h0 : ((0 : B256) * 32).toNat = 0 := by decide
  have h32 : ((1 : B256) * 32).toNat = 32 := by decide
  have hi : (0 : B256).toNat = 0 := by decide
  have hsz : (64 : B256).toNat = 64 := by decide
  rw [h0, h32, hi, hsz]
  rw [Mem.read_two_word_writes Mem.wf_empty Mem.reads_empty]
  simp only [roleDataSlot]

/-- The inner key hash reads a window the staged image already covers, so the
post-read memory is the staged image.  The outer walk's memory terms all build
on this read; rewriting it first restores plain write chains. -/
private theorem pauseReadSnd :
    ((((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes).read
      (0 : B256).toNat (64 : B256).toNat).2) =
      (((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes)) := by
  have himg : (((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes)).size = 64 := by
    rw [Mem.size_write_word_at, Mem.size_write_word_at]
    decide
  have hi : (0 : B256).toNat = 0 := by decide
  have hsz : (64 : B256).toNat = 64 := by decide
  have hext : memExtSize
      (((Mem.empty.write ((0 : B256) * 32).toNat
        pauseRole.toBytes).write ((1 : B256) * 32).toNat
        accessControlRolesPosition.toBytes)).size
      (0 : B256).toNat (64 : B256).toNat =
      (((Mem.empty.write ((0 : B256) * 32).toNat
        pauseRole.toBytes).write ((1 : B256) * 32).toNat
        accessControlRolesPosition.toBytes)).size :=
    memExtSize_of_le (by rw [himg]) (by rw [himg, hi, hsz])
  exact Mem.read_snd_eq_self hext

/-- The outer key hash reads a window the staged four-word image already
covers, so the post-read memory is that image.  Used to match the final
state against `pauseAuthScratch` after the membership read. -/
private theorem pauseReadSndOuter (caller : B256) :
    ((((((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes).write ((1 : B256) * 32).toNat
      (roleDataSlot pauseRole).toBytes).write ((0 : B256) * 32).toNat
      caller.toBytes).read (0 : B256).toNat (64 : B256).toNat).2) =
      (((((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes).write ((1 : B256) * 32).toNat
      (roleDataSlot pauseRole).toBytes).write ((0 : B256) * 32).toNat
      caller.toBytes)) := by
  have himg : (((((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes).write ((1 : B256) * 32).toNat
      (roleDataSlot pauseRole).toBytes).write ((0 : B256) * 32).toNat
      caller.toBytes)).size = 64 := by
    rw [Mem.size_write_word_at, Mem.size_write_word_at,
      Mem.size_write_word_at, Mem.size_write_word_at]
    decide
  have hi : (0 : B256).toNat = 0 := by decide
  have hsz : (64 : B256).toNat = 64 := by decide
  have hext : memExtSize
      (((((Mem.empty.write ((0 : B256) * 32).toNat
        pauseRole.toBytes).write ((1 : B256) * 32).toNat
        accessControlRolesPosition.toBytes).write ((1 : B256) * 32).toNat
        (roleDataSlot pauseRole).toBytes).write ((0 : B256) * 32).toNat
        caller.toBytes)).size
      (0 : B256).toNat (64 : B256).toNat =
      (((((Mem.empty.write ((0 : B256) * 32).toNat
        pauseRole.toBytes).write ((1 : B256) * 32).toNat
        accessControlRolesPosition.toBytes).write ((1 : B256) * 32).toNat
        (roleDataSlot pauseRole).toBytes).write ((0 : B256) * 32).toNat
        caller.toBytes)).size :=
    memExtSize_of_le (by rw [himg]) (by rw [himg, hi, hsz])
  exact Mem.read_snd_eq_self hext

/-- The outer key hash over the caller word and the role-data word is the
role-membership slot.  It is stated over the *named* role-data word: the
forward walk rewrites `pauseKeyHash1` before staging the outer image. -/
private theorem pauseKeyHash2 (caller : B256) :
    Bytes.keccak (((((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes).write ((1 : B256) * 32).toNat
      (roleDataSlot pauseRole).toBytes).write ((0 : B256) * 32).toNat
      caller.toBytes).read (0 : B256).toNat
      (64 : B256).toNat).1 =
      roleMembershipSlot pauseRole caller := by
  have h0 : ((0 : B256) * 32).toNat = 0 := by decide
  have h32 : ((1 : B256) * 32).toNat = 32 := by decide
  have hi : (0 : B256).toNat = 0 := by decide
  have hsz : (64 : B256).toNat = 64 := by decide
  rw [hi, hsz, h0, h32]
  have hread : (((((Mem.empty.write 0
      pauseRole.toBytes).write 32
      accessControlRolesPosition.toBytes).write 32
      (roleDataSlot pauseRole).toBytes).write 0
      caller.toBytes).read 0 64).1 =
      caller.toBytes ++ (roleDataSlot pauseRole).toBytes :=
    Mem.read_two_word_writes_at_raw_right_first _ 0 _ _
  rw [hread]
  simp only [roleMembershipSlot]

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
    ⟨[], (pauseAuthScratch sevm.caller.toB256).write
      ((0 : B256) * 32).toNat duration.toBytes, G, (pauseLogged sevm base duration).stateGas⟩

/-- Exact infinite-sentinel child post state.  Unlike the finite post, the
stored word is the sentinel itself rather than timestamp arithmetic. -/
def pauseSentinelPost (sevm : Sevm) (base : Devm) (G : Nat) : Devm :=
  ((afterSstore sevm (pauseResumeWarm sevm base) resumeSinceSlot
      pauseInfinitely).addLog (pauseEvent sevm pauseInfinitely)).setMach
    ⟨[], (pauseAuthScratch sevm.caller.toB256).write
      ((0 : B256) * 32).toNat pauseInfinitely.toBytes, G, ((afterSstore sevm (pauseResumeWarm sevm base) resumeSinceSlot pauseInfinitely).addLog (pauseEvent sevm pauseInfinitely)).stateGas⟩

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
      sstoreNewRefundCounter sevm.benvStat.rules.gas (duration + sevm.benvStat.time)
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
      sstoreNewRefundCounter sevm.benvStat.rules.gas (duration + sevm.benvStat.time)
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
      sstoreNewRefundCounter sevm.benvStat.rules.gas pauseInfinitely
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

/-- The exact successful `onlyRole(PAUSE_ROLE)` prefix costs `2246` gas with a
cold membership slot: the two-word nested-keccak key walk, one cold `SLOAD`,
and the taken zero branch.  The continuation receives the warmed slot and the
exact two-word scratch image. -/
theorem pauseOnlyRole_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hmembership : base.getStorVal sevm.currentTarget
      (roleMembershipSlot pauseRole sevm.caller.toB256) ≠ 0)
    (hcold : (sevm.currentTarget,
      roleMembershipSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (hbody : Func.RunCompiledTo fs sevm
      ((addAccessedStorageKey base sevm.currentTarget
          (roleMembershipSlot pauseRole sevm.caller.toB256)).setMach
        ⟨[], pauseAuthScratch sevm.caller.toB256, G, (addAccessedStorageKey base sevm.currentTarget (roleMembershipSlot pauseRole sevm.caller.toB256)).stateGas⟩) body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 2246, base.stateGas⟩)
      (onlyRole pauseRole body) ex := by
  have h0 : ((0 : B256) * 32).toNat = 0 := by decide
  have h32 : ((1 : B256) * 32).toNat = 32 := by decide
  have hi : (0 : B256).toNat = 0 := by decide
  have hsz : (64 : B256).toNat = 64 := by decide
  unfold onlyRole viewRoleMembershipSlotFrom viewKeccakPairLinesRightFirst
    viewRoleDataSlotFrom viewKeccakPairLines mstoreAt
  -- Inner key walk through the role-data hash (9 steps).  The hash value is
  -- left as the evaluated application; `pauseKeyHash1` names it afterwards.
  func_run (9) [3, 3, 42]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_ext =>
    exact Devm.extCost_empty_word
  case h_ext =>
    have himg : (Mem.empty.write ((0 : B256) * 32).toNat
        pauseRole.toBytes).size = 32 := by
      rw [Mem.size_write_word_at]
      decide
    exact Devm.extCost_of_size himg (by decide)
  case h_cost =>
    rw [hi, hsz]
    have himg : (((Mem.empty.write ((0 : B256) * 32).toNat
        pauseRole.toBytes).write ((1 : B256) * 32).toNat
        accessControlRolesPosition.toBytes)).size = 64 := by
      rw [Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have he : calculateMemoryGasCost (memExtSize 64 0 64) -
        calculateMemoryGasCost 64 = 0 := by decide
    rw [Devm.extCost_of_size
      (N := ((Mem.empty.write ((0 : B256) * 32).toNat
        pauseRole.toBytes).write ((1 : B256) * 32).toNat
        accessControlRolesPosition.toBytes)) (i := 0) (sz := 64) (e := 0)
      himg he]
    decide
  -- Outer key walk through the membership hash (8 steps), named afterwards
  -- by `pauseKeyHash2`.
  func_run (2) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_ext =>
    have himg : (((Mem.empty.write ((0 : B256) * 32).toNat
        pauseRole.toBytes).write ((1 : B256) * 32).toNat
        accessControlRolesPosition.toBytes)).size = 64 := by
      rw [Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    rw [pauseReadSnd]
    exact Devm.extCost_zero_of_le (by omega) (by omega)
  -- Name the inner hash and restore plain writes before staging the outer
  -- walk: `func_run` over the evaluated application hits the `maxRecDepth`
  -- term-size ceiling (PROOF_RECIPES runcompiled-construction), while the
  -- named image walks exactly like the inner one.
  rw [pauseReadSnd, pauseKeyHash1]
  -- Abstract the staged image across the outer walk: `func_run` recurses over
  -- the concrete write tower past the default `maxRecDepth` (term-size
  -- breaker per PROOF_RECIPES runcompiled-construction, as in
  -- `pauseEvent_runCompiledTo`).  Size facts go through `hsize`; the key
  -- namings concretize via `hstaged` only where they must match.
  generalize hstaged : ((((Mem.empty.write ((0 : B256) * 32).toNat
      pauseRole.toBytes).write ((1 : B256) * 32).toNat
      accessControlRolesPosition.toBytes).write ((1 : B256) * 32).toNat
      (roleDataSlot pauseRole).toBytes)) = staged
  have hsize : staged.size = 64 := by
    rw [← hstaged, Mem.size_write_word_at, Mem.size_write_word_at,
      Mem.size_write_word_at]
    decide
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  -- Outer hash walk (5 steps) over the abstract image.
  func_run (5) [0, 42]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_ext =>
    exact Devm.extCost_zero_of_le (by omega) (by omega)
  case h_cost =>
    rw [hi, hsz]
    have himg : (staged.write ((0 : B256) * 32).toNat
        sevm.caller.toB256.toBytes).size = 64 := by
      rw [Mem.size_write_word_at, hsize, h0]
      decide
    have he : calculateMemoryGasCost (memExtSize 64 0 64) -
        calculateMemoryGasCost 64 = 0 := by decide
    rw [Devm.extCost_of_size
      (N := (staged.write ((0 : B256) * 32).toNat
        sevm.caller.toB256.toBytes)) (i := 0) (sz := 64) (e := 0)
      himg he]
    decide
  -- Name the outer key before the membership read: `func_run`'s cold/warm
  -- probe compares the key against `hcold` by defeq, and over the evaluated
  -- application that unfolding exceeds the default `maxRecDepth`.  The read
  -- content is established by plain rewriting (memory stays abstract), so
  -- the walk closes `h_cold` by `assumption` itself and hands back only the
  -- value and branch obligations.
  have hkeyread : (((staged.write ((0 : B256) * 32).toNat
      sevm.caller.toB256.toBytes).read (0 : B256).toNat
      (64 : B256).toNat).1) =
      sevm.caller.toB256.toBytes ++ (roleDataSlot pauseRole).toBytes := by
    rw [← hstaged, h0, h32, hi, hsz]
    exact Mem.read_two_word_writes_at_raw_right_first _ 0 _ _
  have hkeyname : Bytes.keccak (sevm.caller.toB256.toBytes ++
      (roleDataSlot pauseRole).toBytes) =
      roleMembershipSlot pauseRole sevm.caller.toB256 := by
    simp only [roleMembershipSlot]
  rw [hkeyread, hkeyname]
  clear hkeyread hkeyname hsize hi hsz
  -- Concretize the staged image ahead of the membership read, then clear
  -- its equation: the giant hypothesis breaks the walk's context scans
  -- past the default `maxRecDepth`, while the concrete goal walks fine.
  rw [← hstaged]
  clear hstaged staged
  -- Membership read, test, and taken zero branch.
  func_run (3) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    simp only [Devm.getStorVal_setMach, B256.eqCheck, hmembership]
    decide
  case h_arm =>
    have hgas : G + 2246 - 2246 = G := by omega
    have hsg : (addAccessedStorageKey base sevm.currentTarget
        (roleMembershipSlot pauseRole sevm.caller.toB256)).stateGas =
        base.stateGas := rfl
    rw [pauseReadSndOuter, h0, h32]
    simpa only [addAccessedStorageKey_setMach,
      Devm.setMach_setMach, Devm.stateGas_setMach, hgas, pauseAuthScratch,
      hsg] using hbody

/-! ## The pause event tail -/

/-- Emit the gateway's exact `Paused(uint256)` log from an abstract two-word
memory image.  Naming the memory is the term-size boundary: it avoids reducing
the concrete 64-byte scratch write in every later state. -/
private theorem pauseEvent_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {duration : B256} {G : Nat}
    (hstatic : sevm.isStatic = false)
    (hsize : memory.size = 64)
    (hread : (memory.read 0 32).1 = duration.toBytes) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 1014, base.stateGas⟩)
      (([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop) (.ok post) := by
  obtain ⟨logged, _, _, _, _, _, _, _, _, _, hlift⟩ :=
    Func.runCompiledTo_log_step_exists (fs := fs) (sevm := sevm)
      (devm := base.setMach
        ⟨[(0 : B256), (32 : B256),
          signatureHash "Paused" [.uint256]], memory, G + 1006, base.stateGas⟩)
      (n := (0 : Fin 4).succ)
      (i := (0 : B256)) (sz := (32 : B256))
      (topics := [signatureHash "Paused" [.uint256]]) (s := [])
      (c := 1006) (G := G) (M := memory) (M' := memory)
      (payload := duration.toBytes) (rest := Func.stop)
      rfl rfl hstatic rfl
      (by
        rw [show (0 : B256).toNat = 0 by decide,
          show (32 : B256).toNat = 32 by decide,
          Devm.extCost_of_size (N := memory) (i := 0) (sz := 32) (n := 64)
            (e := 0) hsize (by decide)]
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
  refine ⟨logged.setMach ⟨[], memory, G, logged.stateGas⟩, ?_⟩
  unfold logWith
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1011)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1008)
      (pushCost_of_ne_zero (by decide))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]
        omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gBase) (G := G + 1006) pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by
        simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]
        omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  exact hlift (Func.RunCompiledTo.last rfl)

/-- Exact-state variant of the event tail.  The abstract-memory boundary is
retained, but the post state is named so a parent `CALL` crossing can consume
the child's world and meta projections constructively. -/
private theorem pauseEvent_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {duration : B256} {G : Nat}
    (hstatic : sevm.isStatic = false)
    (hsize : memory.size = 64)
    (hread : (memory.read 0 32).1 = duration.toBytes) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 1014, base.stateGas⟩)
      (([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop)
      (.ok ((base.addLog
        ⟨sevm.currentTarget,
          [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
            ⟨[], memory, G, (base.addLog ⟨sevm.currentTarget, [signatureHash "Paused" [.uint256]], duration.toBytes⟩).stateGas⟩)) := by
  unfold logWith
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1011)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1008)
      (pushCost_of_ne_zero (by decide))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gBase) (G := G + 1006) pushCost_zero
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_log_of
      (n := (0 : Fin 4).succ) (i := (0 : B256)) (sz := (32 : B256))
      (topics := [signatureHash "Paused" [.uint256]]) (s := [])
      (c := 1006) (G := G) (M := memory) (data := duration.toBytes)
      rfl rfl hstatic
      (by
        rw [show (0 : B256).toNat = 0 by decide,
          show (32 : B256).toNat = 32 by decide,
          Devm.extCost_of_size (N := memory) (i := 0) (sz := 32) (n := 64)
            (e := 0) hsize (by decide)]
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
load and covered one-word store add `11` gas to the abstract event tail. -/
private theorem pauseFiniteLogTail_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 1025, base.stateGas⟩)
      ((arg 0 ++ mstoreAt 0 ++
        [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop) (.ok post) := by
  -- Abstract the scratch image: `func_run`'s tactic scans exceed the
  -- default `maxRecDepth` over the concrete write tower.
  generalize hstaged2 : (pauseAuthScratch sevm.caller.toB256) = staged2
  have hlen : duration.toBytes.length = 32 := B256.length_toBytes duration
  have hne : duration.toBytes ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hscratchread : (((staged2.write
      ((0 : B256) * 32).toNat duration.toBytes).read 0 32).1) =
      duration.toBytes := by
    rw [← hlen]
    exact Mem.read_write_zero _ hne
  have hscratchsize : ((staged2.write
      ((0 : B256) * 32).toNat duration.toBytes).size) = 64 := by
    have hscratch64 : staged2.size = 64 := by
      rw [← hstaged2]
      unfold pauseAuthScratch
      rw [Mem.size_write_word_at, Mem.size_write_word_at,
        Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have h0 : ((0 : B256) * 32).toNat = 0 := by decide
    rw [Mem.size_write_word_at, hscratch64, h0]
    decide
  obtain ⟨post, eventRun⟩ := pauseEvent_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (memory := (staged2.write
      ((0 : B256) * 32).toNat duration.toBytes))
    (duration := duration) (G := G) hstatic hscratchsize
    hscratchread
  -- Clear the concrete-tower facts before walking: they break the same
  -- scans.  The abstract continuation run stays.
  clear hlen hne hscratchread hscratchsize
  refine ⟨post, ?_⟩
  unfold arg cdl
  func_run (2)
  rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
  apply Func.runCompiledTo_mstoreAt
      (memory := staged2) (stack := []) (value := duration)
      (word := 0) (G := G + 1014) (pushGas := gBase)
      (extGas := 0) (body :=
        ([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop)
  · exact pushCost_zero
  · simp
  · intro S G'
    have hscratch64 : staged2.size = 64 := by
      rw [← hstaged2]
      unfold pauseAuthScratch
      rw [Mem.size_write_word_at, Mem.size_write_word_at,
        Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have h0 : ((0 : B256) * 32).toNat = 0 := by decide
    exact Devm.extCost_zero_of_le (by omega) (by omega)
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide,
      gBase, gVerylow] using eventRun

private theorem pauseFiniteLogTail_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 1025, base.stateGas⟩)
      ((arg 0 ++ mstoreAt 0 ++
        [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop)
      (.ok ((base.addLog
        ⟨sevm.currentTarget,
          [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
            ⟨[], (pauseAuthScratch sevm.caller.toB256).write
              ((0 : B256) * 32).toNat duration.toBytes, G, (base.addLog ⟨sevm.currentTarget, [signatureHash "Paused" [.uint256]], duration.toBytes⟩).stateGas⟩)) := by
  generalize hstaged2 : (pauseAuthScratch sevm.caller.toB256) = staged2
  have hlen : duration.toBytes.length = 32 := B256.length_toBytes duration
  have hne : duration.toBytes ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hscratchread : (((staged2.write
      ((0 : B256) * 32).toNat duration.toBytes).read 0 32).1) =
      duration.toBytes := by
    rw [← hlen]
    exact Mem.read_write_zero _ hne
  have hscratchsize : ((staged2.write
      ((0 : B256) * 32).toNat duration.toBytes).size) = 64 := by
    have hscratch64 : staged2.size = 64 := by
      rw [← hstaged2]
      unfold pauseAuthScratch
      rw [Mem.size_write_word_at, Mem.size_write_word_at,
        Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have h0 : ((0 : B256) * 32).toNat = 0 := by decide
    rw [Mem.size_write_word_at, hscratch64, h0]
    decide
  have eventRun := pauseEvent_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (memory := (staged2.write
      ((0 : B256) * 32).toNat duration.toBytes))
    (duration := duration) (G := G) hstatic hscratchsize
    hscratchread
  clear hlen hne hscratchread hscratchsize
  unfold arg cdl
  func_run (2)
  rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
  apply Func.runCompiledTo_mstoreAt
      (memory := staged2) (stack := []) (value := duration)
      (word := 0) (G := G + 1014) (pushGas := gBase)
      (extGas := 0) (body :=
        ([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop)
  · exact pushCost_zero
  · simp
  · intro S G'
    have hscratch64 : staged2.size = 64 := by
      rw [← hstaged2]
      unfold pauseAuthScratch
      rw [Mem.size_write_word_at, Mem.size_write_word_at,
        Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have h0 : ((0 : B256) * 32).toNat = 0 := by decide
    exact Devm.extCost_zero_of_le (by omega) (by omega)
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide,
      gBase, gVerylow] using eventRun

/-- The finite branch's store is warm because the guard has just read the same
slot, and the control starts from zero in both the current and original world.
Keeping this instruction behind its own theorem prevents the selected storage
carrier from being expanded through the later log walk. -/
private theorem pauseFiniteSstore_runCompiled
    {sevm : Sevm} {base : Devm} {memory : Mem} {value : B256} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hvalueNonzero : value ≠ 0) :
    Ninst.RunCompiled sevm
      (base.setMach
        ⟨[resumeSinceSlot, value], memory, G + 20000, base.stateGas⟩)
      Ninst.sstore
      ((afterSstore sevm base resumeSinceSlot value).setMach
        ⟨[], memory, G, base.stateGas⟩) := by
  have hcost : sstoreCost sevm
      base resumeSinceSlot value = 20000 := by
    unfold sstoreCost
    simp only [hwarm, if_pos, Nat.zero_add, horiginal, hresume]
    rw [sstoreValueCost, if_pos ⟨rfl, hvalueNonzero.symm⟩, if_pos rfl]
    norm_num [gasStorageSet]
  simpa only [hcost] using
    (Ninst.runCompiled_sstore_selected_setMach
      (sevm := sevm) (base := base) (key := resumeSinceSlot)
      (value := value) (stack := []) (memory := memory) (G := G)
      hfork (by norm_num [hcost, gCallStipend]) hstatic)

/-- Install the finite resume timestamp, then execute the calldata/event tail.
The guard's preceding `SLOAD` has already warmed `resumeSinceSlot`, so the
zero-to-nonzero `SSTORE` charge is exactly `20000`. -/
private theorem pauseFiniteWrite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {duration value : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hvalueNonzero : value ≠ 0) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[value], pauseAuthScratch sevm.caller.toB256,
        G + 21028, base.stateGas⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sstore] ++
        arg 0 ++ mstoreAt 0 ++
        [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop) (.ok post) := by
  generalize hstaged3 : (pauseAuthScratch sevm.caller.toB256) = staged3
  obtain ⟨post, tailRun⟩ := pauseFiniteLogTail_runCompiledTo
    (fs := fs) (sevm := sevm)
    (base := afterSstore sevm base resumeSinceSlot value)
    (duration := duration) (G := G) harg hstatic
  refine ⟨post, ?_⟩
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21025)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  rw [show G + 21025 = G + 1025 + 20000 from by omega]
  apply Func.RunCompiledTo.next
  · exact pauseFiniteSstore_runCompiled (hfork := hfork)
      (memory := staged3)
      (G := G + 1025) hresume horiginal hwarm hstatic hvalueNonzero
  rw [← hstaged3]
  have hsg : (afterSstore sevm base resumeSinceSlot value).stateGas =
      base.stateGas := afterSstore_stateGas
  rw [hsg] at tailRun
  exact tailRun

private theorem pauseFiniteWrite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {duration value : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hvalueNonzero : value ≠ 0) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[value], pauseAuthScratch sevm.caller.toB256,
        G + 21028, base.stateGas⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sstore] ++
        arg 0 ++ mstoreAt 0 ++
        [Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
        logWith 0 0 1) +++ Func.stop)
      (.ok (((afterSstore sevm base resumeSinceSlot value).addLog
        ⟨sevm.currentTarget,
          [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
            ⟨[], (pauseAuthScratch sevm.caller.toB256).write
              ((0 : B256) * 32).toNat duration.toBytes, G, ((afterSstore sevm base resumeSinceSlot value).addLog ⟨sevm.currentTarget, [signatureHash "Paused" [.uint256]], duration.toBytes⟩).stateGas⟩)) := by
  generalize hstaged3 : (pauseAuthScratch sevm.caller.toB256) = staged3
  have tailRun := pauseFiniteLogTail_exact_runCompiledTo
    (fs := fs) (sevm := sevm)
    (base := afterSstore sevm base resumeSinceSlot value)
    (duration := duration) (G := G) harg hstatic
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21025)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  rw [show G + 21025 = G + 1025 + 20000 from by omega]
  apply Func.RunCompiledTo.next
  · exact pauseFiniteSstore_runCompiled (hfork := hfork)
      (memory := staged3)
      (G := G + 1025) hresume horiginal hwarm hstatic hvalueNonzero
  rw [← hstaged3]
  have hsg : (afterSstore sevm base resumeSinceSlot value).stateGas =
      base.stateGas := afterSstore_stateGas
  rw [hsg] at tailRun
  exact tailRun

/-! ## The finite-duration body -/

/-- Execute the checked finite-duration arm.  Its arithmetic/source prefix and
zero branch cost `32` gas; the exact write-and-log suffix above costs `21031`.
The strict timestamp inequality is precisely the successful no-overflow arm. -/
private theorem pauseForFinite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 21060, base.stateGas⟩)
      pauseForFinite (.ok post) := by
  have hvalueNonzero : duration + sevm.benvStat.time ≠ 0 := by
    intro hzero
    rw [hzero] at htime
    have hn := B256.toNat_lt_toNat htime
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  -- Stage the scratch image opaquely for the whole walk: the concrete
  -- tower breaks the walk's defeq past `maxRecDepth` (as at 977), while
  -- a named equation breaks the hinted scans (as at 811-815).  Reverting
  -- the continuation first abstracts its type too, so no bridge is needed.
  have writeRun := pauseFiniteWrite_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (value := duration + sevm.benvStat.time)
    (G := G) harg hresume horiginal hwarm hstatic hvalueNonzero
  obtain ⟨post, writeRun⟩ := writeRun
  revert writeRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged3
  intro writeRun
  refine ⟨post, ?_⟩
  unfold pauseForFinite arg cdl
  func_run (3)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  -- Name the sum by rewriting: only the stack occurrence is normalized.
  nth_rewrite 1 [show 32 * (0 : B256) + 4 = 4 by decide]
  rw [harg]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  func_run (2) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    simp [B256.gtCheck, not_lt_of_ge (le_of_lt htime)]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  have hgas : G + 21060 - 32 = G + 21028 := by omega
  rw [hgas]
  unfold arg cdl at writeRun
  exact writeRun

/-- Lift the finite body through the successful nonzero and non-sentinel
duration guards.  The two tests and their selected branches cost `47` gas. -/
private theorem pauseForUnpausedFinite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
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
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 21107, base.stateGas⟩)
      pauseForUnpaused (.ok post) := by
  obtain ⟨post, finiteRun⟩ := pauseForFinite_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (G := G) harg hresume horiginal hwarm hstatic htime
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert finiteRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged4
  intro finiteRun
  refine ⟨post, ?_⟩
  unfold pauseForUnpaused arg cdl
  func_run (3) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck, hduration]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  func_run (4) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck, Ne.symm hfinite]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  have hgas : G + 21107 - 47 = G + 21060 := by omega
  rw [hgas]
  exact finiteRun

/-! ## The pause-state guard -/

/-- From a cold zero resume slot, execute the exact unpaused guard and enter
the finite-duration body.  The cold `SLOAD`, five surrounding instructions,
and selected nonzero branch cost `2125` gas. -/
private theorem pauseForGuardFinite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
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
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 23232, base.stateGas⟩)
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
  obtain ⟨post, unpausedRun⟩ := pauseForUnpausedFinite_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := warm)
    (duration := duration) (G := G) harg hresumeWarm horiginal hwarm hstatic
    hduration hfinite htime
  have hnotlt : ¬ sevm.benvStat.time < (0 : B256) := by
    intro h
    have hn := B256.toNat_lt_toNat h
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert unpausedRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged5
  intro unpausedRun
  refine ⟨post, ?_⟩
  func_run (5) [0, 1]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [Devm.getStorVal_setMach, hresume]
    simp [B256.ltCheck, hnotlt]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  change Func.RunCompiledTo fs sevm
    (warm.setMach ⟨[], staged5, G + 23232 - 2125, warm.stateGas⟩)
    pauseForUnpaused (.ok post)
  have hgas : G + 23232 - 2125 = G + 21107 := by omega
  rw [hgas]
  exact unpausedRun

/-! ## Authorization and ABI-length guard -/

/-- Compose the successful role-record walk with the finite pause guard. -/
private theorem pauseForAuthorizedFinite_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {duration : B256} {G : Nat}
    (hmembership : base.getStorVal sevm.currentTarget
      (roleMembershipSlot pauseRole sevm.caller.toB256) ≠ 0)
    (hcold : (sevm.currentTarget,
      roleMembershipSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm sevm base).accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 25478, base.stateGas⟩)
      (onlyRole pauseRole <|
        ([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot)) (.ok post) := by
  have hresumeWarm : (pauseRoleWarm sevm base).getStorVal sevm.currentTarget
      resumeSinceSlot = 0 := by
    simpa only [pauseRoleWarm, getStorVal_addAccessedStorageKey] using hresume
  obtain ⟨post, guardRun⟩ := pauseForGuardFinite_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := pauseRoleWarm sevm base)
    (duration := duration) (G := G) harg hresumeWarm horiginal hcoldResume
    hstatic hduration hfinite htime
  refine ⟨post, ?_⟩
  exact pauseOnlyRole_runCompiledTo (hfork := hfork) hmembership hcold
    (by simpa only [pauseRoleWarm] using guardRun)

private theorem pauseForFinite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {duration : B256} {G : Nat}
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 21060, base.stateGas⟩)
      pauseForFinite
      (.ok (((afterSstore sevm base resumeSinceSlot
        (duration + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget,
            [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
              ⟨[], (pauseAuthScratch sevm.caller.toB256).write
                ((0 : B256) * 32).toNat duration.toBytes, G, ((afterSstore sevm base resumeSinceSlot (duration + sevm.benvStat.time)).addLog ⟨sevm.currentTarget, [signatureHash "Paused" [.uint256]], duration.toBytes⟩).stateGas⟩)) := by
  have hvalueNonzero : duration + sevm.benvStat.time ≠ 0 := by
    intro hzero
    rw [hzero] at htime
    have hn := B256.toNat_lt_toNat htime
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  have writeRun := pauseFiniteWrite_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (value := duration + sevm.benvStat.time)
    (G := G) harg hresume horiginal hwarm hstatic hvalueNonzero
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert writeRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged6
  intro writeRun
  unfold pauseForFinite arg cdl
  func_run (7) [duration + sevm.benvStat.time, 0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
  case h_val =>
    simp [B256.gtCheck, not_lt_of_ge (le_of_lt htime)]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  have hgas : G + 21060 - 32 = G + 21028 := by omega
  rw [hgas]
  exact writeRun

private theorem pauseForUnpausedFinite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
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
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 21107, base.stateGas⟩)
      pauseForUnpaused
      (.ok (((afterSstore sevm base resumeSinceSlot
        (duration + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget,
            [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
              ⟨[], (pauseAuthScratch sevm.caller.toB256).write
                ((0 : B256) * 32).toNat duration.toBytes, G, ((afterSstore sevm base resumeSinceSlot (duration + sevm.benvStat.time)).addLog ⟨sevm.currentTarget, [signatureHash "Paused" [.uint256]], duration.toBytes⟩).stateGas⟩)) := by
  have finiteRun := pauseForFinite_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (G := G) harg hresume horiginal hwarm hstatic htime
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert finiteRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged7
  intro finiteRun
  unfold pauseForUnpaused arg cdl
  func_run (3) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck, hduration]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  func_run (4) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck, Ne.symm hfinite]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  have hgas : G + 21107 - 47 = G + 21060 := by omega
  rw [hgas]
  exact finiteRun

private theorem pauseForGuardFinite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
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
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 23232, base.stateGas⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
        (pauseForUnpaused <?> .call resumedExpectedSlot))
      (.ok (((afterSstore sevm
        (addAccessedStorageKey base sevm.currentTarget resumeSinceSlot)
        resumeSinceSlot (duration + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget,
            [signatureHash "Paused" [.uint256]], duration.toBytes⟩).setMach
              ⟨[], (pauseAuthScratch sevm.caller.toB256).write
                ((0 : B256) * 32).toNat duration.toBytes, G, ((afterSstore sevm (addAccessedStorageKey base sevm.currentTarget resumeSinceSlot) resumeSinceSlot (duration + sevm.benvStat.time)).addLog ⟨sevm.currentTarget, [signatureHash "Paused" [.uint256]], duration.toBytes⟩).stateGas⟩)) := by
  let warm := addAccessedStorageKey base sevm.currentTarget resumeSinceSlot
  have hresumeWarm : warm.getStorVal sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [warm, getStorVal_addAccessedStorageKey] using hresume
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      warm.accessedStorageKeys := by
    unfold warm
    change (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys.insert (sevm.currentTarget, resumeSinceSlot)
    exact Std.HashSet.mem_insert_self
  have unpausedRun := pauseForUnpausedFinite_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := warm)
    (duration := duration) (G := G) harg hresumeWarm horiginal hwarm hstatic
    hduration hfinite htime
  have hnotlt : ¬ sevm.benvStat.time < (0 : B256) := by
    intro h
    have hn := B256.toNat_lt_toNat h
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert unpausedRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged8
  intro unpausedRun
  func_run (5) [0, 1]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [Devm.getStorVal_setMach, hresume]
    simp [B256.ltCheck, hnotlt]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  change Func.RunCompiledTo fs sevm
    (warm.setMach ⟨[], staged8, G + 23232 - 2125, warm.stateGas⟩)
    pauseForUnpaused _
  have hgas : G + 23232 - 2125 = G + 21107 := by omega
  rw [hgas]
  exact unpausedRun

private theorem pauseForAuthorizedFinite_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {duration : B256} {G : Nat}
    (hmembership : base.getStorVal sevm.currentTarget
      (roleMembershipSlot pauseRole sevm.caller.toB256) ≠ 0)
    (hcold : (sevm.currentTarget,
      roleMembershipSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
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
      (base.setMach ⟨[], Mem.empty, G + 25478, base.stateGas⟩)
      (onlyRole pauseRole <|
        ([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot))
      (.ok (pauseFinitePost sevm base duration G)) := by
  have hresumeWarm : (pauseRoleWarm sevm base).getStorVal
      sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [pauseRoleWarm, getStorVal_addAccessedStorageKey] using hresume
  have guardRun := pauseForGuardFinite_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := pauseRoleWarm sevm base)
    (duration := duration) (G := G) harg hresumeWarm horiginal hcoldResume
    hstatic hduration hfinite htime
  exact pauseOnlyRole_runCompiledTo (hfork := hfork) hmembership hcold (by
    simpa only [pauseFinitePost, pauseLogged, pauseStored, pauseResumeWarm,
      pauseRoleWarm, pauseEvent] using guardRun)

/-- The successful one-word ABI length guard costs `21` gas. -/
private theorem pauseForFiniteBody_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {G : Nat}
    (hsize : sevm.data.length.toB256 <? 36 = 0)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩)
      (onlyRole pauseRole <|
        ([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot)) (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21, base.stateGas⟩) pauseFor (.ok post) := by
  unfold pauseFor requireStaticArgs
  func_run (4) [0]
  case h_arm =>
    have hgas : G + 21 - 21 = G := by omega
    rw [hgas]
    exact hbody

/-! ## Exact runtime route -/

/-- Skipping one dispatch route on selector mismatch costs `22` gas: the
duplicate, push, equality test, and the untaken branch. -/
private theorem routeSkipped_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {taken tail : Func} {G : Nat}
    (selector other : B256)
    (hne : selector ≠ other)
    (hpush : pushCost other.toBytes.sig = 3)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], Mem.empty, G, base.stateGas⟩)
      tail (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], Mem.empty, G + 22, base.stateGas⟩)
      (Ninst.dup 0 ::: Ninst.pushB256 other ::: Ninst.eq :::
        (taken <?> tail)) (.ok post) := by
  func_run (4) [0]
  case h_val =>
    simp [B256.eqCheck, Ne.symm hne]
  have hgas : G + 22 - 22 = G := by omega
  rw [hgas]
  exact htail

/-- Passing the shared nonpayable gate on zero call value costs `19` gas:
the call value load, zero test, and the taken branch. -/
private theorem callvalueGateTaken_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {tail : Func} {G : Nat}
    (selector : B256)
    (hvalue : sevm.value = 0)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], Mem.empty, G, base.stateGas⟩)
      tail (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], Mem.empty, G + 19, base.stateGas⟩)
      (Ninst.callvalue ::: Ninst.iszero :::
        (tail <?> Func.revert)) (.ok post) := by
  func_run (3) [1]
  case h_val =>
    rw [hvalue]
    decide +kernel
  have hgas : G + 19 - 19 = G := by omega
  rw [hgas]
  exact htail

/-- The selected first entry of the production linear dispatcher costs `25`
gas, including the final selector pop. -/
private theorem pauseForFirstDispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {G : Nat}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩)
      pauseFor (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selPauseFor], Mem.empty, G + 25, base.stateGas⟩)
      (linearDispatchWith fallbackSlot sharedNonpayableFuncs) (.ok post) := by
  unfold sharedNonpayableFuncs linearDispatchWith
  func_run (5) [1]
  exact hbody

private theorem fsig_prepend_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {selector : B256} {post : Devm} {G : Nat} {tail : Func}
    (hselector : Sevm.selector sevm = selector)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selector], Mem.empty, G, base.stateGas⟩) tail (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 11, base.stateGas⟩)
      (fsig +++ tail) (.ok post) := by
  unfold fsig cdl shiftRight
  func_run (4) [selector]
  exact hbody

/-- The `pauseFor` route through the production dispatcher costs `98` gas:
short-calldata guard (`21`), selector load (`11`), trigger-route test (`22`),
shared nonpayable gate (`19`), and the selected first entry (`25`). -/
private theorem pauseForRuntimeMain_runCompiledTo
    {dp : DeployParams} {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseFor)
    (hvalue : sevm.value = 0)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩)
      pauseFor (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 98, base.stateGas⟩)
      (runtimeMain dp) (.ok post) := by
  have hentry := pauseForFirstDispatch_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (G := G) hbody
  have hgate := callvalueGateTaken_runCompiledTo
    (selector := selPauseFor) (G := G + 25) hvalue hentry
  have htrigger := routeSkipped_runCompiledTo
    (taken := Ninst.pop ::: triggerFullWithdrawals dp)
    (selector := selPauseFor) (other := selTriggerFullWithdrawals)
    (G := G + 25 + 19) (by decide +kernel) (by decide +kernel) hgate
  have hsig := fsig_prepend_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (selector := selPauseFor) (G := G + 25 + 19 + 22)
    hselector htrigger
  unfold runtimeMain
  func_run (4) [0]
  case h_arm =>
    have hgas : G + 98 - 21 = G + 25 + 19 + 22 + 11 := by omega
    rw [hgas]
    exact hsig

/-- Lift a successful finite `pauseFor` body through the exact first selector
route, the shared nonpayable gate, the trigger-route test, the short-calldata
guard, and the program entry burn.  The runtime overhead outside `pauseFor`
is `99` gas. -/
theorem pauseForFinite_runtime_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {duration : B256} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseFor)
    (hsize : sevm.data.length.toB256 <? 36 = 0)
    (hvalue : sevm.value = 0)
    (hmembership : base.getStorVal sevm.currentTarget
      (roleMembershipSlot pauseRole sevm.caller.toB256) ≠ 0)
    (hcold : (sevm.currentTarget,
      roleMembershipSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = duration)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm sevm base).accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hfinite : duration ≠ pauseInfinitely)
    (htime : sevm.benvStat.time < duration + sevm.benvStat.time) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, G + 25598, base.stateGas⟩)
      (runtime dp) (.ok (pauseFinitePost sevm base duration G)) := by
  let fs := (runtime dp).main :: (runtime dp).aux
  have authorizedRun := pauseForAuthorizedFinite_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := base)
    (duration := duration) (G := G) hmembership hcold
    harg hresume horiginal hcoldResume hstatic hduration hfinite htime
  have pauseRun := pauseForFiniteBody_runCompiledTo
    (hsize := hsize) (hbody := authorizedRun)
  have mainRun := pauseForRuntimeMain_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G + 25499) hguard hselector hvalue pauseRun
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, G + 25597, base.stateGas⟩)
    (G := G + 25597) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · simpa only [runtime, fs, Devm.setMach_setMach, Devm.stateGas_setMach,
      show G + 25499 + 98 = G + 25597 by omega] using mainRun

/-- Total execution wrapper used by an enclosing `CALL`: the code witness is
supplied independently by the installer, while the child execution itself is
the constructive runtime walk above. -/
theorem pauseForFinite_exec
    (m : Msg) (dp : DeployParams) (duration : B256) (G : Nat)
    (hfork : CoveredFork (initSevm m).benvStat.fork)
    (hcompile : some m.code.toList = Prog.compile (runtime dp))
    (hdata : m.data = pauseForCalldata duration)
    (hgas : m.gas = G + 25598)
    (hvalue : m.value = 0)
    (hmembership : (initDevm m).getStorVal (initSevm m).currentTarget
      (roleMembershipSlot pauseRole (initSevm m).caller.toB256) ≠ 0)
    (hcold : ((initSevm m).currentTarget,
      roleMembershipSlot pauseRole (initSevm m).caller.toB256) ∉
        (initDevm m).accessedStorageKeys)
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
  have walk := pauseForFinite_runtime_runCompiledTo (hfork := hfork)
    (dp := dp) (sevm := initSevm m) (base := initDevm m)
    (duration := duration) (G := G) hguard hselector hsize hvalue
    hmembership hcold harg hresume
    horiginal hcoldResume hstatic
    hduration hfinite htime
  have hbase : (initDevm m).setMach
      ⟨[], Mem.empty, G + 25598, (initDevm m).stateGas⟩ = initDevm m := by
    rw [← hgas]
    rfl
  rw [hbase] at walk
  exact Prog.exec_of_runCompiledTo walk hcompile

/-! ## Independent infinite-sentinel arm -/

private theorem pauseSentinelEventTail_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 1022, base.stateGas⟩)
      ((emitOneWord (signatureHash "Paused" [.uint256]) pauseInfinitely) +++
        Func.stop) (.ok post) := by
  -- Abstract the scratch image (as in `pauseFiniteLogTail_runCompiledTo`).
  generalize hstagedS : (pauseAuthScratch sevm.caller.toB256) = staged9
  have hlen : pauseInfinitely.toBytes.length = 32 :=
    B256.length_toBytes pauseInfinitely
  have hne : pauseInfinitely.toBytes ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hscratchread : (((staged9.write
      ((0 : B256) * 32).toNat pauseInfinitely.toBytes).read 0 32).1) =
      pauseInfinitely.toBytes := by
    rw [← hlen]
    exact Mem.read_write_zero _ hne
  have hscratchsize : ((staged9.write
      ((0 : B256) * 32).toNat pauseInfinitely.toBytes).size) = 64 := by
    have hscratch64 : staged9.size = 64 := by
      rw [← hstagedS]
      unfold pauseAuthScratch
      rw [Mem.size_write_word_at, Mem.size_write_word_at,
        Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have h0 : ((0 : B256) * 32).toNat = 0 := by decide
    rw [Mem.size_write_word_at, hscratch64, h0]
    decide
  obtain ⟨post, eventRun⟩ := pauseEvent_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (memory := (staged9.write
      ((0 : B256) * 32).toNat pauseInfinitely.toBytes))
    (duration := pauseInfinitely) (G := G) hstatic hscratchsize
    hscratchread
  refine ⟨post, ?_⟩
  unfold emitOneWord
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1019)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  apply Func.runCompiledTo_mstoreAt
      (memory := staged9) (stack := []) (value := pauseInfinitely)
      (word := 0) (G := G + 1014) (pushGas := gBase)
      (extGas := 0) (body :=
        ([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop)
  · exact pushCost_zero
  · simp
  · intro S G'
    have hscratch64 : staged9.size = 64 := by
      rw [← hstagedS]
      unfold pauseAuthScratch
      rw [Mem.size_write_word_at, Mem.size_write_word_at,
        Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have h0 : ((0 : B256) * 32).toNat = 0 := by decide
    exact Devm.extCost_zero_of_le (by omega) (by omega)
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide,
      gBase, gVerylow] using eventRun

private theorem pauseSentinelEventTail_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 1022, base.stateGas⟩)
      ((emitOneWord (signatureHash "Paused" [.uint256]) pauseInfinitely) +++
        Func.stop)
      (.ok ((base.addLog (pauseEvent sevm pauseInfinitely)).setMach
        ⟨[], (pauseAuthScratch sevm.caller.toB256).write
          ((0 : B256) * 32).toNat pauseInfinitely.toBytes, G, (base.addLog (pauseEvent sevm pauseInfinitely)).stateGas⟩)) := by
  -- Abstract the scratch image (as in `pauseFiniteLogTail_runCompiledTo`).
  generalize hstagedS : (pauseAuthScratch sevm.caller.toB256) = staged9
  have hlen : pauseInfinitely.toBytes.length = 32 :=
    B256.length_toBytes pauseInfinitely
  have hne : pauseInfinitely.toBytes ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hscratchread : (((staged9.write
      ((0 : B256) * 32).toNat pauseInfinitely.toBytes).read 0 32).1) =
      pauseInfinitely.toBytes := by
    rw [← hlen]
    exact Mem.read_write_zero _ hne
  have hscratchsize : ((staged9.write
      ((0 : B256) * 32).toNat pauseInfinitely.toBytes).size) = 64 := by
    have hscratch64 : staged9.size = 64 := by
      rw [← hstagedS]
      unfold pauseAuthScratch
      rw [Mem.size_write_word_at, Mem.size_write_word_at,
        Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have h0 : ((0 : B256) * 32).toNat = 0 := by decide
    rw [Mem.size_write_word_at, hscratch64, h0]
    decide
  have eventRun := pauseEvent_exact_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (memory := (staged9.write
      ((0 : B256) * 32).toNat pauseInfinitely.toBytes))
    (duration := pauseInfinitely) (G := G) hstatic hscratchsize
    hscratchread
  unfold emitOneWord
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 1019)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  apply Func.runCompiledTo_mstoreAt
      (memory := staged9) (stack := []) (value := pauseInfinitely)
      (word := 0) (G := G + 1014) (pushGas := gBase)
      (extGas := 0) (body :=
        ([Ninst.pushB256 (signatureHash "Paused" [.uint256])] ++
          logWith 0 0 1) +++ Func.stop)
  · exact pushCost_zero
  · simp
  · intro S G'
    have hscratch64 : staged9.size = 64 := by
      rw [← hstagedS]
      unfold pauseAuthScratch
      rw [Mem.size_write_word_at, Mem.size_write_word_at,
        Mem.size_write_word_at, Mem.size_write_word_at]
      decide
    have h0 : ((0 : B256) * 32).toNat = 0 := by decide
    exact Devm.extCost_zero_of_le (by omega) (by omega)
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide,
      gBase, gVerylow, pauseEvent] using eventRun

/-- The sentinel store and its fixed event consume exactly `21028` gas. -/
private theorem pauseForSentinel_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 21028, base.stateGas⟩)
      pauseForSentinel (.ok post) := by
  obtain ⟨post, eventRun⟩ := pauseSentinelEventTail_runCompiledTo
    (fs := fs) (sevm := sevm)
    (base := afterSstore sevm base resumeSinceSlot pauseInfinitely)
    (G := G) hstatic
  refine ⟨post, ?_⟩
  unfold pauseForSentinel emitOneWord
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21025)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21022)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  rw [show G + 21022 = G + 1022 + 20000 from by omega]
  apply Func.RunCompiledTo.next
  · exact pauseFiniteSstore_runCompiled (hfork := hfork)
      (G := G + 1022) hresume horiginal hwarm hstatic
      (by decide +kernel)
  -- Collapse the push-lemma projection chain: over the folded scratch
  -- image the defeq would otherwise unfold past `maxRecDepth`.
  simp only [Devm.stack_setMach, Devm.memory_setMach]
  have hsg : (afterSstore sevm base resumeSinceSlot pauseInfinitely).stateGas =
      base.stateGas := afterSstore_stateGas
  rw [hsg] at eventRun
  exact eventRun

private theorem pauseForSentinel_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 21028, base.stateGas⟩)
      pauseForSentinel
      (.ok (((afterSstore sevm base resumeSinceSlot pauseInfinitely).addLog
        (pauseEvent sevm pauseInfinitely)).setMach
          ⟨[], (pauseAuthScratch sevm.caller.toB256).write
            ((0 : B256) * 32).toNat pauseInfinitely.toBytes, G, ((afterSstore sevm base resumeSinceSlot pauseInfinitely).addLog (pauseEvent sevm pauseInfinitely)).stateGas⟩)) := by
  have eventRun := pauseSentinelEventTail_exact_runCompiledTo
    (fs := fs) (sevm := sevm)
    (base := afterSstore sevm base resumeSinceSlot pauseInfinitely)
    (G := G) hstatic
  unfold pauseForSentinel emitOneWord
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21025)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256
      (c := gVerylow) (G := G + 21022)
      (pushCost_of_ne_zero (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)
  simp only [Devm.setMach_setMach, Devm.stateGas_setMach]
  rw [show G + 21022 = G + 1022 + 20000 from by omega]
  apply Func.RunCompiledTo.next
  · exact pauseFiniteSstore_runCompiled (hfork := hfork)
      (G := G + 1022) hresume horiginal hwarm hstatic
      (by decide +kernel)
  -- Collapse the push-lemma projection chain: over the folded scratch
  -- image the defeq would otherwise unfold past `maxRecDepth`.
  simp only [Devm.stack_setMach, Devm.memory_setMach]
  have hsg : (afterSstore sevm base resumeSinceSlot pauseInfinitely).stateGas =
      base.stateGas := afterSstore_stateGas
  rw [hsg] at eventRun
  exact eventRun

/-- Select the sentinel arm after the successful nonzero test.  Its positive
sentinel branch is one gas dearer than the finite zero branch, so the two
guards cost `48` gas. -/
private theorem pauseForUnpausedSentinel_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 21076, base.stateGas⟩)
      pauseForUnpaused (.ok post) := by
  obtain ⟨post, sentinelRun⟩ := pauseForSentinel_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := base) (G := G)
    hresume horiginal hwarm hstatic
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert sentinelRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged10
  intro sentinelRun
  refine ⟨post, ?_⟩
  unfold pauseForUnpaused arg cdl
  func_run (3) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    decide +kernel
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  func_run (4) [1]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  have hgas : G + 21076 - 48 = G + 21028 := by omega
  rw [hgas]
  exact sentinelRun

private theorem pauseForUnpausedSentinel_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 21076, base.stateGas⟩)
      pauseForUnpaused
      (.ok (((afterSstore sevm base resumeSinceSlot pauseInfinitely).addLog
        (pauseEvent sevm pauseInfinitely)).setMach
          ⟨[], (pauseAuthScratch sevm.caller.toB256).write
            ((0 : B256) * 32).toNat pauseInfinitely.toBytes, G, ((afterSstore sevm base resumeSinceSlot pauseInfinitely).addLog (pauseEvent sevm pauseInfinitely)).stateGas⟩)) := by
  have sentinelRun := pauseForSentinel_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := base) (G := G)
    hresume horiginal hwarm hstatic
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert sentinelRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged11
  intro sentinelRun
  unfold pauseForUnpaused arg cdl
  func_run (3) [0]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    decide +kernel
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  func_run (4) [1]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [show 32 * (0 : B256) + 4 = 4 by decide, harg]
    simp [B256.eqCheck]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  have hgas : G + 21076 - 48 = G + 21028 := by omega
  rw [hgas]
  exact sentinelRun

private theorem pauseForGuardSentinel_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post, Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 23201, base.stateGas⟩)
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
  obtain ⟨post, unpausedRun⟩ := pauseForUnpausedSentinel_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := warm) (G := G)
    harg hresumeWarm horiginal hwarm hstatic
  have hnotlt : ¬ sevm.benvStat.time < (0 : B256) := by
    intro h
    have hn := B256.toNat_lt_toNat h
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert unpausedRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged12
  intro unpausedRun
  refine ⟨post, ?_⟩
  func_run (5) [0, 1]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [Devm.getStorVal_setMach, hresume]
    simp [B256.ltCheck, hnotlt]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  change Func.RunCompiledTo fs sevm
    (warm.setMach ⟨[], staged12, G + 23201 - 2125, warm.stateGas⟩)
    pauseForUnpaused (.ok post)
  have hgas : G + 23201 - 2125 = G + 21076 := by omega
  rw [hgas]
  exact unpausedRun

private theorem pauseForGuardSentinel_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], pauseAuthScratch sevm.caller.toB256, G + 23201, base.stateGas⟩)
      (([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
        (pauseForUnpaused <?> .call resumedExpectedSlot))
      (.ok (((afterSstore sevm
        (addAccessedStorageKey base sevm.currentTarget resumeSinceSlot)
        resumeSinceSlot pauseInfinitely).addLog
          (pauseEvent sevm pauseInfinitely)).setMach
            ⟨[], (pauseAuthScratch sevm.caller.toB256).write
              ((0 : B256) * 32).toNat pauseInfinitely.toBytes, G, ((afterSstore sevm (addAccessedStorageKey base sevm.currentTarget resumeSinceSlot) resumeSinceSlot pauseInfinitely).addLog (pauseEvent sevm pauseInfinitely)).stateGas⟩)) := by
  let warm := addAccessedStorageKey base sevm.currentTarget resumeSinceSlot
  have hresumeWarm : warm.getStorVal sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [warm, getStorVal_addAccessedStorageKey] using hresume
  have hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      warm.accessedStorageKeys := by
    unfold warm
    change (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys.insert (sevm.currentTarget, resumeSinceSlot)
    exact Std.HashSet.mem_insert_self
  have unpausedRun := pauseForUnpausedSentinel_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := warm) (G := G)
    harg hresumeWarm horiginal hwarm hstatic
  have hnotlt : ¬ sevm.benvStat.time < (0 : B256) := by
    intro h
    have hn := B256.toNat_lt_toNat h
    rw [B256.toNat_zero] at hn
    exact Nat.not_lt_zero _ hn
  -- Stage opaquely (as in `pauseForFinite_runCompiledTo` above).
  revert unpausedRun
  generalize (pauseAuthScratch sevm.caller.toB256) = staged13
  intro unpausedRun
  func_run (5) [0, 1]
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  case h_val =>
    rw [Devm.getStorVal_setMach, hresume]
    simp [B256.ltCheck, hnotlt]
  func_run (1)
  repeat (case h_legacy => exact hfork.rules_stateGas_none)
  change Func.RunCompiledTo fs sevm
    (warm.setMach ⟨[], staged13, G + 23201 - 2125, warm.stateGas⟩)
    pauseForUnpaused _
  have hgas : G + 23201 - 2125 = G + 21076 := by omega
  rw [hgas]
  exact unpausedRun

private theorem pauseForAuthorizedSentinel_exact_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hmembership : base.getStorVal sevm.currentTarget
      (roleMembershipSlot pauseRole sevm.caller.toB256) ≠ 0)
    (hcold : (sevm.currentTarget,
      roleMembershipSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm sevm base).accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 25447, base.stateGas⟩)
      (onlyRole pauseRole <|
        ([Ninst.pushB256 resumeSinceSlot, Ninst.sload, Ninst.timestamp,
          Ninst.lt, Ninst.iszero]) +++
          (pauseForUnpaused <?> .call resumedExpectedSlot))
      (.ok (pauseSentinelPost sevm base G)) := by
  have hresumeWarm : (pauseRoleWarm sevm base).getStorVal
      sevm.currentTarget resumeSinceSlot = 0 := by
    simpa only [pauseRoleWarm, getStorVal_addAccessedStorageKey] using hresume
  have guardRun := pauseForGuardSentinel_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := pauseRoleWarm sevm base)
    (G := G) harg hresumeWarm horiginal hcoldResume hstatic
  exact pauseOnlyRole_runCompiledTo (hfork := hfork) hmembership hcold (by
    simpa only [pauseSentinelPost, pauseResumeWarm, pauseRoleWarm,
      pauseEvent] using guardRun)

/-- Independent successful runtime witness for the infinite sentinel.  Its
exact derived charge is `25567`, 31 below the finite-duration arm. -/
theorem pauseForSentinel_runtime_exact_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseFor)
    (hsize : sevm.data.length.toB256 <? 36 = 0)
    (hvalue : sevm.value = 0)
    (hmembership : base.getStorVal sevm.currentTarget
      (roleMembershipSlot pauseRole sevm.caller.toB256) ≠ 0)
    (hcold : (sevm.currentTarget,
      roleMembershipSlot pauseRole sevm.caller.toB256) ∉
        base.accessedStorageKeys)
    (harg : Sevm.dataWord sevm 4 = pauseInfinitely)
    (hresume : base.getStorVal sevm.currentTarget resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget resumeSinceSlot = 0)
    (hcoldResume : (sevm.currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm sevm base).accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, G + 25567, base.stateGas⟩)
      (runtime dp) (.ok (pauseSentinelPost sevm base G)) := by
  let fs := (runtime dp).main :: (runtime dp).aux
  have authorizedRun := pauseForAuthorizedSentinel_exact_runCompiledTo (hfork := hfork)
    (fs := fs) (sevm := sevm) (base := base) (G := G)
    hmembership hcold harg hresume
    horiginal hcoldResume hstatic
  have pauseRun := pauseForFiniteBody_runCompiledTo
    (hsize := hsize) (hbody := authorizedRun)
  have mainRun := pauseForRuntimeMain_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G + 25468) hguard hselector hvalue pauseRun
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, G + 25566, base.stateGas⟩)
    (G := G + 25566) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · simpa only [runtime, fs, Devm.setMach_setMach, Devm.stateGas_setMach,
      show G + 25468 + 98 = G + 25566 by omega] using mainRun

/-- Total execution wrapper for the infinite-sentinel child called by the
composed circuit-breaker route. -/
theorem pauseForSentinel_exec
    (m : Msg) (dp : DeployParams) (G : Nat)
    (hfork : CoveredFork (initSevm m).benvStat.fork)
    (hcompile : some m.code.toList = Prog.compile (runtime dp))
    (hdata : m.data = pauseForCalldata pauseInfinitely)
    (hgas : m.gas = G + 25567)
    (hvalue : m.value = 0)
    (hmembership : (initDevm m).getStorVal (initSevm m).currentTarget
      (roleMembershipSlot pauseRole (initSevm m).caller.toB256) ≠ 0)
    (hcold : ((initSevm m).currentTarget,
      roleMembershipSlot pauseRole (initSevm m).caller.toB256) ∉
        (initDevm m).accessedStorageKeys)
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
  have walk := pauseForSentinel_runtime_exact_runCompiledTo (hfork := hfork)
    (dp := dp) (sevm := initSevm m) (base := initDevm m) (G := G)
    hguard hselector hsize hvalue hmembership hcold harg hresume horiginal
    hcoldResume hstatic
  have hbase : (initDevm m).setMach
      ⟨[], Mem.empty, G + 25567, (initDevm m).stateGas⟩ = initDevm m := by
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
    (hfork : CoveredFork sevm.benvStat.fork)
    {storedUntil : B256} {G : Nat}
    (hstored : base.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post, Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 121, base.stateGas⟩)
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
    repeat (case h_legacy => exact hfork.rules_stateGas_none)
    case h_val =>
      rw [Devm.getStorVal_setMach, hstored]
      simp [B256.ltCheck, hpaused]
    case h_ext => exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_return_word (i := 0) (sz := 32) (s := [])
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
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {G : Nat}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩)
      isPaused (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[selIsPaused], Mem.empty, G + 47, base.stateGas⟩)
      (linearDispatchWith fallbackSlot sharedNonpayableFuncs) (.ok post) := by
  unfold sharedNonpayableFuncs linearDispatchWith
  func_run (9) [0, 1]
  exact hbody

/-- The `isPaused` route through the production dispatcher costs `120` gas:
short-calldata guard (`21`), selector load (`11`), trigger-route test (`22`),
shared nonpayable gate (`19`), and the selected second entry (`47`). -/
private theorem isPausedRuntimeMain_runCompiledTo
    {dp : DeployParams} {fs : List Func} {sevm : Sevm} {base : Devm}
    {post : Devm} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selIsPaused)
    (hvalue : sevm.value = 0)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩)
      isPaused (.ok post)) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 120, base.stateGas⟩)
      (runtimeMain dp) (.ok post) := by
  have hdispatch := isPausedSecondDispatch_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (G := G) hbody
  have hgate := callvalueGateTaken_runCompiledTo
    (selector := selIsPaused) (G := G + 47) hvalue hdispatch
  have htrigger := routeSkipped_runCompiledTo
    (taken := Ninst.pop ::: triggerFullWithdrawals dp)
    (selector := selIsPaused) (other := selTriggerFullWithdrawals)
    (G := G + 47 + 19) (by decide +kernel) (by decide +kernel) hgate
  have hsig := fsig_prepend_runCompiledTo
    (fs := fs) (sevm := sevm) (base := base)
    (selector := selIsPaused) (G := G + 47 + 19 + 22)
    hselector htrigger
  unfold runtimeMain
  func_run (4) [0]
  case h_arm =>
    have hgas : G + 120 - 21 = G + 47 + 19 + 22 + 11 := by omega
    rw [hgas]
    exact hsig

/-- A warm successful `isPaused()` runtime call consumes exactly `242` gas
and returns canonical true without changing the stored resume word. -/
theorem isPaused_true_warm_runtime_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {storedUntil : B256} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selIsPaused)
    (hvalue : sevm.value = 0)
    (hstored : base.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil)
    (hwarm : (sevm.currentTarget, resumeSinceSlot) ∈
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post, Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + 242, base.stateGas⟩)
        (runtime dp) (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil ∧
      post.gasLeft = G ∧
      post.error = base.error ∧
      post.meta = (base.withOutput (1 : B256).toBytes).meta ∧
      post.world = base.world := by
  let fs := (runtime dp).main :: (runtime dp).aux
  obtain ⟨post, queryRun, output, stored, gas, error, hmeta, world⟩ :=
    isPaused_true_warm_runCompiledTo (hfork := hfork)
      (fs := fs) (sevm := sevm) (base := base)
      (storedUntil := storedUntil) (G := G) hstored hwarm hpaused
  have mainRun := isPausedRuntimeMain_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G + 121) hguard hselector hvalue queryRun
  refine ⟨post, ?_, output, stored, gas, error, hmeta, world⟩
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, G + 241, base.stateGas⟩)
    (G := G + 241) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · simpa only [runtime, fs, Devm.setMach_setMach, Devm.stateGas_setMach,
      show G + 121 + 120 = G + 241 by omega] using mainRun

/-- Total-execution wrapper for an enclosing warm `STATICCALL`.  The program
walk remains the source of the result; the installed code witness only
connects that walk to `exec`. -/
theorem isPaused_true_warm_exec
    (m : Msg) (dp : DeployParams) (storedUntil : B256) (G : Nat)
    (hfork : CoveredFork (initSevm m).benvStat.fork)
    (hcompile : some m.code.toList = Prog.compile (runtime dp))
    (hdata : m.data = isPausedCalldata)
    (hgas : m.gas = G + 242)
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
    isPaused_true_warm_runtime_runCompiledTo (hfork := hfork)
      (dp := dp) (sevm := initSevm m) (base := initDevm m)
      (storedUntil := storedUntil) (G := G) hguard hselector hvalue
      hstored hwarm hpaused
  have hbase : (initDevm m).setMach
      ⟨[], Mem.empty, G + 242, (initDevm m).stateGas⟩ = initDevm m := by
    rw [← hgas]
    rfl
  rw [hbase] at walk
  exact ⟨post, Prog.exec_of_runCompiledTo walk hcompile, output, stored,
    gas, error, hmeta, world⟩

/-- The same successful query from a cold resume slot costs exactly `2121`
gas in the body: precisely 2000 more than the warm case. -/
private theorem isPaused_true_cold_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {storedUntil : B256} {G : Nat}
    (hstored : base.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post, Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 2121, base.stateGas⟩)
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
    repeat (case h_legacy => exact hfork.rules_stateGas_none)
    case h_val =>
      rw [Devm.getStorVal_setMach, hstored]
      simp [B256.ltCheck, hpaused]
    case h_ext => exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_return_word (i := 0) (sz := 32) (s := [])
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

/-- A cold successful `isPaused()` runtime call consumes exactly `2242` gas,
establishing the selected warm/cold schedule boundary. -/
theorem isPaused_true_cold_runtime_runCompiledTo
    {dp : DeployParams} {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {storedUntil : B256} {G : Nat}
    (hguard : sevm.data.length.toB256 <? (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selIsPaused)
    (hvalue : sevm.value = 0)
    (hstored : base.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil)
    (hcold : (sevm.currentTarget, resumeSinceSlot) ∉
      base.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil) :
    ∃ post, Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, G + 2242, base.stateGas⟩)
        (runtime dp) (.ok post) ∧
      post.output = (1 : B256).toBytes ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot = storedUntil ∧
      post.gasLeft = G := by
  let fs := (runtime dp).main :: (runtime dp).aux
  obtain ⟨post, queryRun, output, stored, gas, _error, _hmeta, _world⟩ :=
    isPaused_true_cold_runCompiledTo (hfork := hfork)
      (fs := fs) (sevm := sevm) (base := base)
      (storedUntil := storedUntil) (G := G) hstored hcold hpaused
  have mainRun := isPausedRuntimeMain_runCompiledTo
    (dp := dp) (fs := fs) (sevm := sevm) (base := base)
    (G := G + 2121) hguard hselector hvalue queryRun
  refine ⟨post, ?_, output, stored, gas⟩
  refine Prog.runCompiledTo_intro
    (mid := base.setMach ⟨[], Mem.empty, G + 2241, base.stateGas⟩)
    (G := G + 2241) ?_ rfl ?_
  · simp only [Devm.gasLeft_setMach, gJumpdest]
  · simpa only [runtime, fs, Devm.setMach_setMach, Devm.stateGas_setMach,
      show G + 2121 + 120 = G + 2241 by omega] using mainRun

end LidoTriggerableWithdrawalsGateway
end Blanc
