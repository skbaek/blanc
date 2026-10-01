import Jaune.Machine

/-!
Support for Jaune's natural-number integer exponential recurrence. Its loop
is already total by a lexicographic measure, rather than a fixed fuel bound.
This module makes no claim about finite-word arithmetic or bytecode execution.
-/

namespace Blanc.FakeExponential

open Jaune

/-- A finite trace of the loop, exposing its iteration count for gas proofs. -/
inductive Run (numerator denominator : Nat) : Nat → Nat → Nat → Nat → Prop
  | stop (i : Nat) : Run numerator denominator i 0 0 0
  | step {i accumulator iterations output : Nat} (positive : accumulator ≠ 0)
      (next : Run numerator denominator (i + 1)
        (accumulator * numerator / (denominator * i)) iterations output) :
      Run numerator denominator i accumulator (iterations + 1) (accumulator + output)

/-- Every input reaches zero after finitely many iterations; no guessed fuel. -/
theorem run_exists (numerator denominator i accumulator : Nat) :
    ∃ iterations, Run numerator denominator i accumulator iterations
      (fakeExpAux numerator denominator i accumulator) := by
  induction i, accumulator using fakeExpAux.induct numerator denominator with
  | case1 i =>
    rw [fakeExpAux_zero]
    exact ⟨0, Run.stop i⟩
  | case2 i accumulator positive ih =>
    obtain ⟨iterations, next⟩ := ih
    rw [fakeExpAux_succ positive]
    exact ⟨iterations + 1, Run.step positive next⟩

/-- A finite loop trace has exactly the canonical mathematical output. -/
theorem Run.output_eq {numerator denominator i accumulator iterations output : Nat}
    (run : Run numerator denominator i accumulator iterations output) :
    output = fakeExpAux numerator denominator i accumulator := by
  induction run with
  | stop i => exact (fakeExpAux_zero _ _ _).symm
  | step positive next ih => rw [fakeExpAux_succ positive, ih]

/-- The first accumulator is one of the nonnegative summands. -/
theorem accumulator_le (numerator denominator i accumulator : Nat) :
    accumulator ≤ fakeExpAux numerator denominator i accumulator := by
  by_cases zero : accumulator = 0
  · rw [zero, fakeExpAux_zero]
  · rw [fakeExpAux_succ zero]
    exact Nat.le_add_right _ _

/-- A positive denominator makes the final value at least the initial factor. -/
theorem factor_le (factor numerator denominator : Nat) (positive : 0 < denominator) :
    factor ≤ fakeExp factor numerator denominator := by
  have lower : factor * denominator / denominator ≤
      fakeExpAux numerator denominator 1 (factor * denominator) / denominator :=
    Nat.div_le_div_right (accumulator_le numerator denominator 1 (factor * denominator))
  rw [Nat.mul_div_cancel factor positive] at lower
  exact lower

/-- With zero numerator, only the initial accumulator contributes. -/
theorem accumulator_zero_numerator (denominator i accumulator : Nat) :
    fakeExpAux 0 denominator i accumulator = accumulator := by
  by_cases zero : accumulator = 0
  · rw [zero, fakeExpAux_zero]
  · rw [fakeExpAux_succ zero]
    simp only [Nat.mul_zero, Nat.zero_div, fakeExpAux_zero, Nat.add_zero]

/-- At zero excess the integer exponential is exactly its factor. -/
theorem value_zero_numerator (factor denominator : Nat) (positive : 0 < denominator) :
    fakeExp factor 0 denominator = factor := by
  change fakeExpAux 0 denominator 1 (factor * denominator) / denominator = factor
  rw [accumulator_zero_numerator, Nat.mul_div_cancel factor positive]

end Blanc.FakeExponential
