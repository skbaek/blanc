import Blanc.FakeExponential

/-! Symbolic prefix lower bounds for the existing Nat recurrence. -/

namespace Blanc.FakeExponential

open Jaune

/-- If every divisor in a prefix permits growth by q, its last accumulator
already lower-bounds the complete nonnegative sum. -/
theorem accumulator_mul_pow_le {numerator denominator counter accumulator n q : Nat}
    (denominatorPos : 0 < denominator) (counterPos : 0 < counter)
    (growth : denominator * (counter + n) * q ≤ numerator) :
    accumulator * q ^ n ≤ fakeExpAux numerator denominator counter accumulator := by
  induction n generalizing counter accumulator with
  | zero =>
    rw [Nat.pow_zero, Nat.mul_one]
    exact accumulator_le numerator denominator counter accumulator
  | succ n ih =>
    by_cases zero : accumulator = 0
    · rw [zero, Nat.zero_mul, fakeExpAux_zero]
    · have divisorPos : 0 < denominator * counter := Nat.mul_pos denominatorPos counterPos
      have firstGrowth : denominator * counter * q ≤ numerator :=
        (Nat.mul_le_mul_right q (Nat.mul_le_mul_left denominator
          (Nat.le_add_right counter (n + 1)))).trans growth
      have nextLower : accumulator * q ≤
          accumulator * numerator / (denominator * counter) := by
        apply (Nat.le_div_iff_mul_le divisorPos).2
        calc
          accumulator * q * (denominator * counter) =
              accumulator * (denominator * counter * q) := by
            rw [Nat.mul_assoc, Nat.mul_comm q (denominator * counter), ← Nat.mul_assoc]
          _ ≤ accumulator * numerator := Nat.mul_le_mul_left accumulator firstGrowth
      have nextGrowth : denominator * (counter + 1 + n) * q ≤ numerator := by
        have indices : counter + 1 + n = counter + (n + 1) := by omega
        rw [indices]
        exact growth
      have tail := ih (counter := counter + 1)
        (accumulator := accumulator * numerator / (denominator * counter))
        (by omega) nextGrowth
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      calc
        accumulator * q ^ n * q = accumulator * q * q ^ n := by
          rw [Nat.mul_assoc, Nat.mul_comm (q ^ n) q, ← Nat.mul_assoc]
        _ ≤ (accumulator * numerator / (denominator * counter)) * q ^ n :=
          Nat.mul_le_mul_right (q ^ n) nextLower
        _ ≤ fakeExpAux numerator denominator (counter + 1)
            (accumulator * numerator / (denominator * counter)) := tail
        _ ≤ fakeExpAux numerator denominator counter accumulator := by
          rw [fakeExpAux_succ zero]
          exact Nat.le_add_left _ _

/-- Canonical initialization and positive final division preserve the bound. -/
theorem factor_mul_pow_le (factor numerator denominator n q : Nat)
    (denominatorPos : 0 < denominator)
    (growth : denominator * (1 + n) * q ≤ numerator) :
    factor * q ^ n ≤ fakeExp factor numerator denominator := by
  have lower := accumulator_mul_pow_le (accumulator := factor * denominator)
    denominatorPos (by decide) growth
  have divided := Nat.div_le_div_right lower (c := denominator)
  have product : factor * denominator * q ^ n = factor * q ^ n * denominator := by
    rw [Nat.mul_assoc, Nat.mul_comm denominator (q ^ n), ← Nat.mul_assoc]
  rw [product, Nat.mul_div_cancel _ denominatorPos] at divided
  exact divided

end Blanc.FakeExponential
