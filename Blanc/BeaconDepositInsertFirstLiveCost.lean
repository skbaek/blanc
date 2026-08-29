import Blanc.BeaconDepositInsertIterKey
import Blanc.BeaconDepositInsertIterKeys
import Blanc.BeaconDepositInsertIterNode

/-! # Beacon deposit first-live insertion store cost -/

namespace Blanc.BeaconDeposit

open Jaune

/-- Exact terminal branch-write cost after `n` dead insertion steps, expressed
entirely through the pure insertion inputs and their accumulated node. -/
def insertionFirstLiveStoreCost (sevm : Sevm) (stor : Stor)
    (keys : KeySet) (height n : Nat) (node : B256) : Nat :=
  (if (⟨sevm.currentTarget, branchSlot (height + n)⟩ : Adr × B256) ∈
      insertionNatKeys sevm.currentTarget n height keys
    then 0 else gasColdSload) +
  sstoreValueCost
    (getOrigStorVal sevm sevm.currentTarget (branchSlot (height + n)))
    (stor.get (branchSlot (height + n)))
    (accumulatedNode Bytes.sha256 (accOfStor stor).branch height n node)

theorem insertionStoreCost_iter_eq_firstLive
    (sevm : Sevm) (stor : Stor) (keys : KeySet)
    (height n size : Nat) (node : B256)
    (hheight : height + n < 32) (hsize : size < 2 ^ 32) :
    insertionStoreCost sevm stor
        (insertionLoopIter sevm.currentTarget stor n
          (insertionNatState height size node keys)) =
      insertionFirstLiveStoreCost sevm stor keys height n node := by
  unfold insertionStoreCost insertionFirstLiveStoreCost
  rw [insertionLoopIter_key sevm.currentTarget stor n height size node keys
      hheight hsize,
    insertionLoopIter_keys sevm.currentTarget stor n height size node keys
      (by omega) hsize,
    insertionLoopIter_node sevm.currentTarget stor n height size node keys
      (by omega)]

end Blanc.BeaconDeposit
