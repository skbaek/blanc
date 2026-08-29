import Blanc.BeaconDepositInsertIterHeight

/-! # Beacon deposit insertion-fold storage-key projection -/

namespace Blanc.BeaconDeposit

open Jaune

theorem insertionLoopIter_key
    (owner : Adr) (stor : Stor) (k height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + k < 32)
    (hsize : size < 2 ^ 32) :
    (insertionLoopIter owner stor k
      (insertionNatState height size node keys)).key =
        branchSlot (height + k) := by
  unfold InsertionLoopState.key
  rw [insertionLoopIter_height owner stor k height size node keys
    (by omega) hsize]
  have hkey := insertionNatState_key (height + k) 0 node keys (by omega)
  simpa only [InsertionLoopState.key, insertionNatState] using hkey

end Blanc.BeaconDeposit
