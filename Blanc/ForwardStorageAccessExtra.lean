import Blanc.ForwardCall
import Blanc.ForwardStorageAccess

/-!
# Selected storage-access projections

Contract-neutral access-set and gas carriers for a warm-or-cold `SLOAD`, plus
the unchanged-state projections commonly threaded through compiled loops.
-/

namespace Blanc

open Jaune

theorem afterSstore_accessedAddresses
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).accessedAddresses =
      base.accessedAddresses := by
  unfold afterSstore
  split <;> rfl

theorem afterSstore_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).accessedStorageKeys =
      sloadAccessedStorageKeys sevm.currentTarget
        base.accessedStorageKeys key := by
  unfold afterSstore sloadAccessedStorageKeys
  split <;> rfl

/-! ### Created accounts and the machine original read

Jaune prices `SSTORE` from `Devm.getOrigStorVal`, which reads `0` at an account
created in this transaction and the transaction-start snapshot otherwise. These
laws carry that read across the selected storage steps. -/

/-! ## Selected `SLOAD`: values, warmth, and key sets

A selected `SLOAD` changes only the accessed-key set, so storage, original and
transient reads pass through it, the read key is warm afterwards, and every
other key keeps its warm or cold status. -/

end Blanc
