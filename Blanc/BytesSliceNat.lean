import Blanc.BytesWrite
import Jaune.Precompiles

/-! # Bounded natural-number reads from byte images -/

namespace Blanc

open Jaune

/-- An in-bounds parser read is the natural number of the corresponding padded slice. -/
theorem Bytes.sliceToNat_of_le (data : Bytes) (start width : Nat)
    (hfit : start + width ≤ data.length) :
    data.sliceToNat start width = Bytes.toNat (data.sliceD start width 0) := by
  have fits : width ≤ (data.drop start).length := by
    rw [List.length_drop]
    omega
  unfold Jaune.Bytes.sliceToNat List.sliceD
  generalize data.drop start = tail at fits ⊢
  cases tail with
  | nil =>
      have hwidth : width = 0 := by simpa only [List.length_nil, Nat.le_zero] using fits
      subst width
      rfl
  | cons x xs =>
      dsimp only
      rw [ite_eq_right (Nat.not_lt_of_ge fits), List.takeD_eq_take _ fits]

end Blanc
