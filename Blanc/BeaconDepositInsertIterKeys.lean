import Blanc.BeaconDepositInsertNat

/-! # Beacon deposit insertion-fold access-key projection -/

namespace Blanc.BeaconDeposit

open Jaune

theorem insertionLoopIter_keys
    (owner : Adr) (stor : Stor) (k height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + k ≤ 32)
    (hsize : size < 2 ^ 32) :
    (insertionLoopIter owner stor k
      (insertionNatState height size node keys)).keys =
        insertionNatKeys owner k height keys := by
  induction k generalizing height size node keys with
  | zero => rfl
  | succ k ih =>
      rw [insertionLoopIter]
      rw [insertionNatState_step owner stor height size node keys
        (by omega) hsize]
      simpa only [insertionNatKeys] using
        ih (height := height + 1) (size := size / 2)
          (node := hashPair Bytes.sha256 ((accOfStor stor).branch height)
            node)
          (keys := insertionReadKeys owner keys (branchSlot height))
          (by omega) (by omega)

end Blanc.BeaconDeposit
