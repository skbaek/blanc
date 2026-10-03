import Blanc.ForwardStorageAccess

/-! Refund monotonicity for a store to an unchanged original slot. -/

namespace Blanc

open Jaune

/-- A first write to a slot cannot decrease an arbitrary refund counter. -/
theorem sstoreNewRefundCounter_ge_of_original_eq_current
    (gas : GasSchedule) (value current : B256) (rc : Int) :
    rc ≤ sstoreNewRefundCounter gas value current current rc := by
  unfold sstoreNewRefundCounter
  by_cases changed : current ≠ value
  · simp only [changed, ite_false]
    by_cases zero : current = 0
    · simp only [zero, ne_eq, not_true_eq_false, false_and, ite_false]
      omega
    · simp only [zero, ne_eq, not_false_eq_true, true_and, and_false, ite_false]
      split
      · omega
      · omega
  · simp only [changed, ite_false]
    omega

/-- The selected warm/cold store retains the scalar first-write guarantee. -/
theorem afterSstore_refundCounter_ge_of_original_eq_current
    (sevm : Sevm) (base : Devm) (key value : B256)
    (same : getOrigStorVal sevm sevm.currentTarget key =
      base.getStorVal sevm.currentTarget key) :
    base.refundCounter ≤ (afterSstore sevm base key value).refundCounter := by
  rw [afterSstore_refundCounter, same]
  exact sstoreNewRefundCounter_ge_of_original_eq_current _ _ _ _

/-- An `SSTORE` whose transaction-original value equals the value it finds, is zero, or
finds a nonzero value cannot take the clearing-reversal branch of the refund counter. -/
def RefundSafe (orig cur : B256) : Prop := orig = cur ∨ orig = 0 ∨ cur ≠ 0

theorem sstoreNewRefundCounter_ge_of_safe (gas : GasSchedule) (new orig cur : B256) (rc : Int)
    (safe : RefundSafe orig cur) : rc ≤ sstoreNewRefundCounter gas new orig cur rc := by
  rcases safe with same | zero | live
  · rw [same]
    exact sstoreNewRefundCounter_ge_of_original_eq_current gas new cur rc
  · unfold sstoreNewRefundCounter
    simp only [zero, ne_eq, not_true_eq_false, false_and, ite_false, gasStorageSet,
      gasWarmAccess, gasStorageUpdate, gasColdSload]
    split_ifs <;> omega
  · have hn : ¬ (orig ≠ 0 ∧ cur = 0) := fun h => live h.2
    unfold sstoreNewRefundCounter
    simp only [hn, ite_false, gasStorageSet, gasWarmAccess, gasStorageUpdate, gasColdSload]
    split_ifs <;> omega

theorem afterSstore_refundCounter_ge_of_safe (sevm : Sevm) (base : Devm) (key value : B256)
    (safe : RefundSafe (getOrigStorVal sevm sevm.currentTarget key)
      (base.getStorVal sevm.currentTarget key)) :
    base.refundCounter ≤ (afterSstore sevm base key value).refundCounter := by
  rw [afterSstore_refundCounter]
  exact sstoreNewRefundCounter_ge_of_safe _ _ _ _ _ safe

end Blanc
