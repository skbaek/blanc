import Blanc.ForwardCall

/-!
# Selected storage-access projections

Contract-neutral access-set and gas carriers for a warm-or-cold `SLOAD`, plus
the unchanged-state projections commonly threaded through compiled loops.
-/

namespace Blanc

open Jaune

def sloadAccessedStorageKeys (target : Adr) (keys : KeySet)
    (key : B256) : KeySet :=
  if (⟨target, key⟩ : Adr × B256) ∈ keys then keys
  else keys.insert ⟨target, key⟩

def sloadCostOfKeys (target : Adr) (keys : KeySet)
    (key : B256) : Nat :=
  if (⟨target, key⟩ : Adr × B256) ∈ keys then gasWarmAccess
  else gasColdSload

theorem sloadCostOfKeys_eq_sloadCost
    (sevm : Sevm) (base : Devm) (key : B256) :
    sloadCostOfKeys sevm.currentTarget base.accessedStorageKeys key =
      sloadCost sevm base key := rfl

theorem afterSload_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).accessedStorageKeys =
      sloadAccessedStorageKeys sevm.currentTarget
        base.accessedStorageKeys key := by
  unfold afterSload sloadAccessedStorageKeys
  split <;> rfl

theorem afterSload_getStor
    (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    Devm.getStor (afterSload sevm base key) address =
      Devm.getStor base address := by
  unfold afterSload
  split <;> rfl

theorem afterSload_getCode
    (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    (afterSload sevm base key).getCode address = base.getCode address := by
  unfold afterSload
  split <;> rfl

theorem afterSload_accessedAddresses
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).accessedAddresses =
      base.accessedAddresses := by
  unfold afterSload
  split <;> rfl

theorem afterSload_logs
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).logs = base.logs := by
  unfold afterSload
  split <;> rfl

theorem afterSload_output
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).output = base.output := by
  unfold afterSload
  split <;> rfl

theorem afterSload_error
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).error = base.error := by
  unfold afterSload
  split <;> rfl

/-- Neither the refund-counter update nor the storage-cell write touches any
account's code, shown directly at the `State` level. -/
private theorem sstoreCore_getCode (devm : Devm) (rc : Int) (target : Adr)
    (key value : B256) (address : Adr) :
    ((devm.withRefundCounter rc).setStorVal target key value).getCode
      address = devm.getCode address := by
  show (((devm.withRefundCounter rc).state.setStorVal target key value).get
    address).code = ((devm.state.get address)).code
  by_cases h : target = address
  · subst h
    rw [State.setStorVal_get_self]
    rfl
  · rw [State.setStorVal_get_ne _ h]
    rfl

theorem afterSstore_getCode
    (sevm : Sevm) (base : Devm) (key value : B256) (address : Adr) :
    (afterSstore sevm base key value).getCode address =
      base.getCode address := by
  unfold afterSstore
  split
  · exact sstoreCore_getCode base _ _ _ _ _
  · exact sstoreCore_getCode _ _ _ _ _ _

theorem afterSstore_getStor_self
    (sevm : Sevm) (base : Devm) (key value : B256) :
    Devm.getStor (afterSstore sevm base key value) sevm.currentTarget =
      (Devm.getStor base sevm.currentTarget).set key value := by
  unfold afterSstore
  split
  · rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  · rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor,
      addAccessedStorageKey_getStor]

theorem afterSstore_getStor_ne
    (sevm : Sevm) (base : Devm) (key value : B256) (address : Adr)
    (haddress : sevm.currentTarget ≠ address) :
    Devm.getStor (afterSstore sevm base key value) address =
      Devm.getStor base address := by
  unfold afterSstore
  split
  · rw [setStorVal_getStor_ne haddress, Devm.withRefundCounter_getStor]
  · rw [setStorVal_getStor_ne haddress, Devm.withRefundCounter_getStor,
      addAccessedStorageKey_getStor]

theorem afterSstore_logs
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).logs = base.logs := by
  unfold afterSstore
  split <;> rfl

theorem afterSstore_refundCounter
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).refundCounter =
      sstoreNewRefundCounter sevm.benvStat.rules.gas value
        (base.getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) base.refundCounter := by
  unfold afterSstore
  split <;> rfl

theorem afterSstore_accountsToDelete
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).accountsToDelete =
      base.accountsToDelete := by
  unfold afterSstore
  split <;> rfl

theorem afterSstore_output
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).output = base.output := by
  unfold afterSstore
  split <;> rfl

theorem afterSstore_error
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).error = base.error := by
  unfold afterSstore
  split <;> rfl

/-! ### Created accounts and the machine original read

Jaune prices `SSTORE` from `Devm.getOrigStorVal`, which reads `0` at an account
created in this transaction and the transaction-start snapshot otherwise. These
laws carry that read across the selected storage steps. -/

/-- A selected `SLOAD` leaves the created-account set unchanged. -/
theorem afterSload_createdAccounts
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).createdAccounts = base.createdAccounts := by
  unfold afterSload
  split <;> rfl

/-- A selected `SSTORE` leaves the created-account set unchanged. -/
theorem afterSstore_createdAccounts
    (sevm : Sevm) (devm : Devm) (key value : B256) :
    (afterSstore sevm devm key value).createdAccounts =
      devm.createdAccounts := by
  unfold afterSstore
  split <;> rfl

/-- The machine original read agrees between two machines with the same
created-account set. -/
theorem getOrigStorVal_congr_created
    {sevm : Sevm} {d1 d2 : Devm} (adr : Adr) (key : B256)
    (hcreated : d1.createdAccounts = d2.createdAccounts) :
    d1.getOrigStorVal sevm adr key = d2.getOrigStorVal sevm adr key := by
  unfold Devm.getOrigStorVal
  rw [hcreated]

/-- At an account absent from `createdAccounts`, the machine original read is
the static snapshot read. -/
theorem getOrigStorVal_of_not_created {sevm : Sevm} {d : Devm} {adr : Adr}
    {key : B256} (h : adr ∉ d.createdAccounts) :
    d.getOrigStorVal sevm adr key = getOrigStorVal sevm adr key := by
  unfold Devm.getOrigStorVal
  rw [ite_eq_right h]

/-- A zero transaction-start snapshot word is also the machine's actual
original word: a created owner reads `0` regardless, and an existing owner reads
the snapshot. -/
theorem actualOrigStorVal_eq_zero_of_raw
    {sevm : Sevm} {d : Devm} {a : Adr} {key : B256}
    (h : getOrigStorVal sevm a key = 0) :
    d.getOrigStorVal sevm a key = 0 := by
  unfold Devm.getOrigStorVal
  split
  · rfl
  · exact h

/-- Warming a storage key does not change the machine original read. -/
theorem addAccessedStorageKey_getOrigStorVal (d : Devm) (owner : Adr)
    (k : B256) (sevm : Sevm) (a : Adr) (key : B256) :
    (addAccessedStorageKey d owner k).getOrigStorVal sevm a key =
      d.getOrigStorVal sevm a key := rfl

/-- The selected `SSTORE` charge depends on the pre-state only through its
accessed-key set, the target's storage, and its created-account set (an
account created in this transaction has original value zero), so any two
states agreeing on all three are charged identically. -/
theorem sstoreCost_congr {sevm : Sevm} {d1 d2 : Devm} (key value : B256)
    (hkeys : d1.accessedStorageKeys = d2.accessedStorageKeys)
    (hstor : Devm.getStor d1 sevm.currentTarget =
      Devm.getStor d2 sevm.currentTarget)
    (hcreated : d1.createdAccounts = d2.createdAccounts) :
    sstoreCost sevm d1 key value = sstoreCost sevm d2 key value := by
  unfold sstoreCost
  rw [hkeys]
  have horig : d1.getOrigStorVal sevm sevm.currentTarget key =
      d2.getOrigStorVal sevm sevm.currentTarget key := by
    unfold Devm.getOrigStorVal
    rw [hcreated]
  rw [horig]
  show _ + sstoreValueCost _
    ((Devm.getStor d1 sevm.currentTarget).get key) value = _
  rw [hstor]
  rfl

/-! ## Selected `SLOAD`: values, warmth, and key sets

A selected `SLOAD` changes only the accessed-key set, so storage, original and
transient reads pass through it, the read key is warm afterwards, and every
other key keeps its warm or cold status. -/

theorem not_mem_hashSet_insert {α : Type _} [BEq α] [Hashable α]
    [LawfulBEq α] {s : Std.HashSet α} {x p : α}
    (h : p ∉ s) (hne : x ≠ p) : p ∉ s.insert x := by
  intro hmem
  rcases Std.HashSet.mem_insert.mp hmem with he | hp
  · exact hne (eq_of_beq he)
  · exact h hp

theorem afterSload_getStorVal
    (sevm : Sevm) (base : Devm) (key : B256) (a : Adr) (k : B256) :
    (afterSload sevm base key).getStorVal a k =
      base.getStorVal a k := by
  unfold afterSload
  split_ifs <;> rfl

theorem afterSload_getOrigStorVal
    (sevm : Sevm) (base : Devm) (key : B256) (a : Adr) (k : B256) :
    (afterSload sevm base key).getOrigStorVal sevm a k =
      base.getOrigStorVal sevm a k := by
  unfold afterSload
  split_ifs <;> rfl

theorem afterSload_getTransVal (sevm : Sevm) (base : Devm)
    (key : B256) (a : Adr) (k : B256) :
    (afterSload sevm base key).getTransVal a k =
      base.getTransVal a k := by
  unfold afterSload
  split <;> rfl

theorem afterSload_warm
    (sevm : Sevm) (base : Devm) (key : B256) :
    (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      (afterSload sevm base key).accessedStorageKeys := by
  unfold afterSload
  split_ifs with hwarm
  · exact hwarm
  · change (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      base.accessedStorageKeys.insert ⟨sevm.currentTarget, key⟩
    exact Std.HashSet.mem_insert_self

theorem afterSload_preserves_warm
    (sevm : Sevm) (base : Devm) (readKey key : B256)
    (h : (sevm.currentTarget, key) ∈ base.accessedStorageKeys) :
    (sevm.currentTarget, key) ∈
      (afterSload sevm base readKey).accessedStorageKeys := by
  unfold afterSload
  split
  · exact h
  · exact Std.HashSet.mem_insert.mpr (Or.inr h)

theorem not_mem_afterSload {sevm : Sevm} {base : Devm}
    {readKey : B256} {p : Adr × B256}
    (h : p ∉ base.accessedStorageKeys)
    (hne : (sevm.currentTarget, readKey) ≠ p) :
    p ∉ (afterSload sevm base readKey).accessedStorageKeys := by
  unfold afterSload
  split
  · exact h
  · exact not_mem_hashSet_insert h hne

theorem afterSload_preserves_cold
    (sevm : Sevm) (base : Devm) (readKey key : B256)
    (hne : readKey ≠ key)
    (h : (sevm.currentTarget, key) ∉ base.accessedStorageKeys) :
    (sevm.currentTarget, key) ∉
      (afterSload sevm base readKey).accessedStorageKeys :=
  not_mem_afterSload h fun hp => hne (congrArg Prod.snd hp)

theorem afterSload_cold_keys (sevm : Sevm) (base : Devm)
    (key : B256)
    (h : (sevm.currentTarget, key) ∉ base.accessedStorageKeys) :
    (afterSload sevm base key).accessedStorageKeys =
      base.accessedStorageKeys.insert (sevm.currentTarget, key) := by
  unfold afterSload
  rw [ite_eq_right h]
  rfl

theorem afterSload_accessedStorageKeys_addLog
    (sevm : Sevm) (base : Devm) (l : Log) (k : B256) :
    (afterSload sevm (base.addLog l) k).accessedStorageKeys =
      (afterSload sevm base k).accessedStorageKeys := by
  unfold afterSload
  by_cases h : (sevm.currentTarget, k) ∈ base.accessedStorageKeys
  · rw [ite_eq_left (show (sevm.currentTarget, k) ∈
      (base.addLog l).accessedStorageKeys from h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (show ¬ (sevm.currentTarget, k) ∈
      (base.addLog l).accessedStorageKeys from h), ite_eq_right h]
    rfl

/-- The selected `SLOAD` charge reads the pre-state only through its
accessed-key set. -/
theorem sloadCost_congr
    (sevm : Sevm) (base base' : Devm) (k : B256)
    (h : base.accessedStorageKeys = base'.accessedStorageKeys) :
    sloadCost sevm base k = sloadCost sevm base' k := by
  unfold sloadCost
  rw [h]

end Blanc
