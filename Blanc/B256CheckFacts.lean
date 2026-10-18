import Jaune.Machine

/-!
# Comparison flags from arithmetic facts

Contract-neutral facts about the EVM comparison words `B256.gtCheck` and `B256.ltCheck`, stated
over the operands' natural-number values, for walks that discharge a solc range check.
-/

namespace Blanc

open Jaune

/-- `GT` yields `0` when the left operand's value is at most the right's. -/
theorem B256.gtCheck_eq_zero_of_toNat_le {x y : B256} (h : x.toNat ≤ y.toNat) :
    B256.gtCheck x y = 0 := by
  rw [B256.gtCheck, ite_eq_right]
  intro hxy
  have hxy' := B256.toNat_lt_toNat hxy
  omega

end Blanc
