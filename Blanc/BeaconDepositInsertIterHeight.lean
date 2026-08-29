import Blanc.BeaconDepositInsertNat

/-! # Beacon deposit insertion-fold height projection -/

namespace Blanc.BeaconDeposit

open Jaune

theorem insertionLoopIter_height
    (owner : Adr) (stor : Stor) (k height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + k ≤ 32)
    (hsize : size < 2 ^ 32) :
    (insertionLoopIter owner stor k
      (insertionNatState height size node keys)).height =
        Nat.toB256 (height + k) := by
  induction k generalizing height size node keys with
  | zero =>
      simp only [insertionLoopIter, insertionNatState, Nat.add_zero]
  | succ k ih =>
      rw [insertionLoopIter]
      rw [insertionNatState_step owner stor height size node keys
        (by omega) hsize]
      simpa only [Nat.add_assoc, Nat.one_add] using
        ih (height := height + 1) (size := size / 2)
          (node := hashPair Bytes.sha256 ((accOfStor stor).branch height)
            node)
          (keys := insertionReadKeys owner keys (branchSlot height))
          (by omega) (by omega)

end Blanc.BeaconDeposit
