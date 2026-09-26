import Blanc.Lift.Curve3Crv.Layout

/-!
# The string slots are apart from each other and from the three word slots

A kernel decision on the two Keccak digests `keccak(0)` and `keccak(1)`, kept apart from the files
the language server elaborates.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

/-- The three word slots. -/
def vyWordSlots : List B256 := [vyDecimalsSlot, vySupplySlot, vyMinterSlot]

/-- The name's slots (length and two data words). -/
def vyNameSlots : List B256 := [vyNameBase, vyNameBase + Nat.toB256 1, vyNameBase + Nat.toB256 2]

/-- The symbol's slots (length and one data word). -/
def vySymbolSlots : List B256 := [vySymbolBase, vySymbolBase + Nat.toB256 1]

/-- The string slots are apart from the word slots and from each other's. -/
theorem vyStrSlots_apart :
    (∀ y ∈ vyNameSlots ++ vySymbolSlots, ∀ x ∈ vyWordSlots, y ≠ x) ∧
    (∀ y ∈ vyNameSlots, ∀ z ∈ vySymbolSlots, y ≠ z) := by
  decide +kernel

end Blanc.Lift.Curve3Crv
