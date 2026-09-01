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

@[simp] theorem sloadCostOfKeys_eq_sloadCost
    (sevm : Sevm) (base : Devm) (key : B256) :
    sloadCostOfKeys sevm.currentTarget base.accessedStorageKeys key =
      sloadCost sevm base key := rfl

@[simp] theorem afterSload_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).accessedStorageKeys =
      sloadAccessedStorageKeys sevm.currentTarget
        base.accessedStorageKeys key := by
  unfold afterSload sloadAccessedStorageKeys
  split <;> rfl

@[simp] theorem afterSload_getStor
    (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    Devm.getStor (afterSload sevm base key) address =
      Devm.getStor base address := by
  unfold afterSload
  split <;> rfl

@[simp] theorem afterSload_getCode
    (sevm : Sevm) (base : Devm) (key : B256) (address : Adr) :
    (afterSload sevm base key).getCode address = base.getCode address := by
  unfold afterSload
  split <;> rfl

@[simp] theorem afterSload_accessedAddresses
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).accessedAddresses =
      base.accessedAddresses := by
  unfold afterSload
  split <;> rfl

@[simp] theorem afterSload_logs
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).logs = base.logs := by
  unfold afterSload
  split <;> rfl

@[simp] theorem afterSload_output
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).output = base.output := by
  unfold afterSload
  split <;> rfl

@[simp] theorem afterSload_error
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
  unfold State.setStorVal
  by_cases h : target = address
  · subst h
    rw [State.get_set_self]
    rfl
  · rw [State.get_set_ne _ h]
    rfl

@[simp] theorem afterSstore_getCode
    (sevm : Sevm) (base : Devm) (key value : B256) (address : Adr) :
    (afterSstore sevm base key value).getCode address =
      base.getCode address := by
  unfold afterSstore
  split
  · exact sstoreCore_getCode base _ _ _ _ _
  · exact sstoreCore_getCode _ _ _ _ _ _

@[simp] theorem afterSstore_accessedAddresses
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).accessedAddresses =
      base.accessedAddresses := by
  unfold afterSstore
  split <;> rfl

@[simp] theorem afterSstore_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).accessedStorageKeys =
      sloadAccessedStorageKeys sevm.currentTarget
        base.accessedStorageKeys key := by
  unfold afterSstore sloadAccessedStorageKeys
  split <;> rfl

@[simp] theorem afterSstore_getStor_self
    (sevm : Sevm) (base : Devm) (key value : B256) :
    Devm.getStor (afterSstore sevm base key value) sevm.currentTarget =
      (Devm.getStor base sevm.currentTarget).set key value := by
  unfold afterSstore
  split
  · rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor]
  · rw [setStorVal_getStor_self, Devm.withRefundCounter_getStor,
      addAccessedStorageKey_getStor]

@[simp] theorem afterSstore_getStor_ne
    (sevm : Sevm) (base : Devm) (key value : B256) (address : Adr)
    (haddress : sevm.currentTarget ≠ address) :
    Devm.getStor (afterSstore sevm base key value) address =
      Devm.getStor base address := by
  unfold afterSstore
  split
  · rw [setStorVal_getStor_ne haddress, Devm.withRefundCounter_getStor]
  · rw [setStorVal_getStor_ne haddress, Devm.withRefundCounter_getStor,
      addAccessedStorageKey_getStor]

@[simp] theorem afterSstore_logs
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).logs = base.logs := by
  unfold afterSstore
  split <;> rfl

@[simp] theorem afterSstore_refundCounter
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).refundCounter =
      sstoreNewRefundCounter value
        (getOrigStorVal sevm sevm.currentTarget key)
        (base.getStorVal sevm.currentTarget key) base.refundCounter := by
  unfold afterSstore
  split <;> rfl

@[simp] theorem afterSstore_accountsToDelete
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).accountsToDelete =
      base.accountsToDelete := by
  unfold afterSstore
  split <;> rfl

@[simp] theorem afterSstore_output
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).output = base.output := by
  unfold afterSstore
  split <;> rfl

@[simp] theorem afterSstore_error
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).error = base.error := by
  unfold afterSstore
  split <;> rfl

/-- The selected `SSTORE` charge depends on the pre-state only through its
accessed-key set and the target's storage, so any two states agreeing on both
are charged identically. -/
theorem sstoreCost_congr {sevm : Sevm} {d1 d2 : Devm} (key value : B256)
    (hkeys : d1.accessedStorageKeys = d2.accessedStorageKeys)
    (hstor : Devm.getStor d1 sevm.currentTarget =
      Devm.getStor d2 sevm.currentTarget) :
    sstoreCost sevm d1 key value = sstoreCost sevm d2 key value := by
  unfold sstoreCost
  rw [hkeys]
  show _ + sstoreValueCost _
    ((Devm.getStor d1 sevm.currentTarget).get key) value = _
  rw [hstor]
  rfl

end Blanc
