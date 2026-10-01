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

end Blanc
