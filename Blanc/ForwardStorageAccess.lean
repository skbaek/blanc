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

end Blanc
