import Jaune.Machine
import Jaune.WordFacts
import Blanc.MachineDataFacts

/-!
# Primitive machine-data facts

Contract-neutral word operations and persistent-storage observations, below
Blanc's execution-inversion and tactic layers. Consumers import this owner
directly; it is deliberately not reexported by CommonProofs or Ladder.
-/

namespace Blanc

open Jaune

/-- Multiplication by one preserves an EVM word. -/
theorem B256.mul_one (x : B256) : x * (1 : B256) = x := by
  apply B256.toNat_inj
  rw [B256.toNat_mul]
  have h1 : (1 : B256).toNat = 1 := by decide
  rw [h1, Nat.mul_one, Nat.lo_eq_of_lt x.toNat_lt]

end Blanc
