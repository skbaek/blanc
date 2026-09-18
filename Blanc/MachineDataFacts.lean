import Jaune.Machine

/-!
# Primitive machine-data facts

Contract-neutral word operations and persistent-storage observations, below
Blanc's execution-inversion and tactic layers. Consumers import this owner
directly; it is deliberately not reexported by CommonProofs or Ladder.
-/

namespace Blanc

open Jaune

local infix:70 " <? " => B256.ltCheck

/-- Multiplication on EVM words is commutative, including wrapping products. -/
theorem B256.mul_comm (x y : B256) : x * y = y * x := by
  apply B256.toNat_inj
  rw [B256.toNat_mul, B256.toNat_mul, Nat.mul_comm]

/-- A zero unsigned comparison flag rules out the corresponding strict order. -/
theorem B256.not_lt_of_ltCheck_eq_zero {x y : B256} (h : (x <? y) = 0) :
    ¬ x < y := by
  intro hlt
  rw [B256.ltCheck, if_pos hlt] at h
  exact absurd h (by decide +kernel)

/-- Equality of account states preserves a persistent-storage word at any key. -/
theorem Devm.getStorVal_of_state {s t : Devm} (h : s.state = t.state)
    (a : Adr) (k : B256) :
    Devm.getStorVal s a k = Devm.getStorVal t a k := by
  unfold Devm.getStorVal Devm.getAcct
  rw [h]

end Blanc
