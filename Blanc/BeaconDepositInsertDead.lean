import Blanc.BeaconDepositCorrectness
import Blanc.BeaconDepositInsertIterSize

/-!
# Beacon deposit insertion dead/live bridge

Translate the pure first-live bit predicate into the exact dead-prefix and
terminal-live predicates consumed by the compiled insertion carrier.
-/

namespace Blanc.BeaconDeposit

open Jaune

theorem insertionLoopDead_iff_iter_not_live
    (owner : Adr) (stor : Stor) (n : Nat) (s : InsertionLoopState) :
    InsertionLoopDead owner stor n s ↔
      ∀ j, j < n → ¬(insertionLoopIter owner stor j s).live := by
  induction n generalizing s with
  | zero =>
      simp only [InsertionLoopDead]
      constructor
      · intro _ j hj
        omega
      · intro _
        trivial
  | succ n ih =>
      simp only [InsertionLoopDead]
      constructor
      · rintro ⟨hzero, hrest⟩ j hj
        cases j with
        | zero =>
            simpa only [insertionLoopIter] using hzero
        | succ j =>
            have htail := (ih (s := s.step owner stor)).mp hrest j (by omega)
            simpa only [insertionLoopIter] using htail
      · intro hall
        constructor
        · simpa only [insertionLoopIter] using hall 0 (by omega)
        · apply (ih (s := s.step owner stor)).mpr
          intro j hj
          simpa only [insertionLoopIter] using hall (j + 1) (by omega)

theorem insertionLoopIter_live_iff
    (owner : Adr) (stor : Stor) (k height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + k ≤ 32)
    (hsize : size < 2 ^ 32) :
    (insertionLoopIter owner stor k
      (insertionNatState height size node keys)).live ↔
        size / 2 ^ k % 2 = 1 := by
  unfold InsertionLoopState.live
  rw [insertionLoopIter_size owner stor k height size node keys
    hheight hsize]
  have hlive := insertionNatState_live_iff
    (height + k) (size / 2 ^ k) node keys
    (lt_of_le_of_lt (Nat.div_le_self size (2 ^ k))
      (by omega : size < 2 ^ 256))
  simpa only [InsertionLoopState.live, insertionNatState] using hlive

theorem insertionLoopDead_insertionNatState_of_firstLive
    (owner : Adr) (stor : Stor) (n height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + n ≤ 32)
    (hsize : size < 2 ^ 32) (hfirst : FirstLive size n) :
    InsertionLoopDead owner stor n
      (insertionNatState height size node keys) := by
  apply (insertionLoopDead_iff_iter_not_live owner stor n
    (insertionNatState height size node keys)).mpr
  intro j hj
  rw [insertionLoopIter_live_iff owner stor j height size node keys
    (by omega) hsize]
  have hzero := hfirst.2 j hj
  omega

theorem insertionLoopIter_live_of_firstLive
    (owner : Adr) (stor : Stor) (n height size : Nat) (node : B256)
    (keys : KeySet) (hheight : height + n ≤ 32)
    (hsize : size < 2 ^ 32) (hfirst : FirstLive size n) :
    (insertionLoopIter owner stor n
      (insertionNatState height size node keys)).live :=
  (insertionLoopIter_live_iff owner stor n height size node keys
    hheight hsize).mpr hfirst.1

end Blanc.BeaconDeposit
