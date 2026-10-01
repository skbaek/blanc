import Jaune.Types

/-!
The unsigned finite-word integer-exponential loop. The output prefix,
accumulator, numerator, denominator and counter are all B256 values.
This module supplies a finite recurrence witness and its exact body count;
it asserts no Nat correspondence, bytecode refinement or gas bound.
-/

namespace Blanc.WordFakeExponential

open Jaune

/-- The accumulator update uses Jaune's unsigned word multiplication/division. -/
def nextAccumulator (numerator denominator counter accumulator : B256) : B256 :=
  (accumulator * numerator) / (denominator * counter)

/-- A finite loop trace, carrying the number of active bodies and final sum. -/
inductive Run (numerator denominator : B256) : B256 → B256 → B256 → Nat → B256 → Prop
  | stop (counter output : B256) : Run numerator denominator counter 0 output 0 output
  | step {counter accumulator output iterations finalOutput}
      (active : accumulator ≠ 0)
      (next : Run numerator denominator (counter + 1)
        (nextAccumulator numerator denominator counter accumulator)
        (output + accumulator) iterations finalOutput) :
      Run numerator denominator counter accumulator output (iterations + 1) finalOutput

/-- Countdown to a zero counter, whose division-by-zero body stops the loop. -/
def measure (counter accumulator : B256) : Nat :=
  if accumulator = 0 then 0 else
    if counter = 0 then 1 else 2 ^ 256 - counter.toNat + 1

/-- A zero word counter makes the next accumulator zero. -/
theorem nextAccumulator_zero_counter (numerator denominator accumulator : B256) :
    nextAccumulator numerator denominator 0 accumulator = 0 := by
  unfold nextAccumulator
  have zeroProduct : denominator * (0 : B256) = 0 := by
    change (denominator.toNat * 0).toB256 = 0
    rw [Nat.mul_zero]
    rfl
  change (B256.divMod (accumulator * numerator) (denominator * 0)).fst = 0
  rw [zeroProduct, B256.divMod, ite_eq_left rfl]

/-- Every active word body strictly decreases the countdown. -/
theorem measure_next_lt (numerator denominator counter accumulator : B256)
    (active : accumulator ≠ 0) :
    measure (counter + 1) (nextAccumulator numerator denominator counter accumulator) <
      measure counter accumulator := by
  unfold measure
  rw [ite_eq_right active]
  by_cases stopped : nextAccumulator numerator denominator counter accumulator = 0
  · rw [ite_eq_left stopped]
    split <;> omega
  · by_cases zeroCounter : counter = 0
    · subst counter
      exact (stopped (nextAccumulator_zero_counter numerator denominator accumulator)).elim
    · rw [ite_eq_right stopped, ite_eq_right zeroCounter]
      have counterBound := B256.toNat_lt counter
      by_cases wrapped : counter + 1 = 0
      · rw [ite_eq_left wrapped]
        omega
      · rw [ite_eq_right wrapped]
        have increment := B256.toNat_add counter 1
        change (counter + 1).toNat = (counter.toNat + 1) % (2 ^ 256) at increment
        have nonzero : (counter + 1).toNat ≠ 0 := by
          intro zeroNat
          apply wrapped
          exact B256.toNat_inj _ _ zeroNat
        have fits : counter.toNat + 1 < 2 ^ 256 := by
          by_contra tooLarge
          have boundary : counter.toNat + 1 = 2 ^ 256 := by omega
          rw [boundary, Nat.mod_self] at increment
          exact nonzero increment
        rw [Nat.mod_eq_of_lt fits] at increment
        omega

/-- Every word state has a finite run, with body count bounded by the countdown. -/
theorem run_exists (numerator denominator counter accumulator output : B256) :
    ∃ iterations finalOutput,
      Run numerator denominator counter accumulator output iterations finalOutput ∧
        iterations ≤ measure counter accumulator := by
  generalize countdown : measure counter accumulator = bound
  induction bound using Nat.strong_induction_on generalizing counter accumulator output with
  | h bound ih =>
    by_cases stopped : accumulator = 0
    · subst accumulator
      exact ⟨0, output, Run.stop counter output, Nat.zero_le bound⟩
    · have decreases := measure_next_lt numerator denominator counter accumulator stopped
      rw [countdown] at decreases
      obtain ⟨iterations, finalOutput, next, countBound⟩ :=
        ih _ decreases (counter + 1)
          (nextAccumulator numerator denominator counter accumulator)
          (output + accumulator) rfl
      exact ⟨iterations + 1, finalOutput, Run.step stopped next, by omega⟩

/-- The body count and final word sum are uniquely determined by the initial state. -/
theorem Run.deterministic {numerator denominator counter accumulator output : B256}
    {iterations₁ iterations₂ : Nat} {finalOutput₁ finalOutput₂ : B256}
    (first : Run numerator denominator counter accumulator output iterations₁ finalOutput₁)
    (second : Run numerator denominator counter accumulator output iterations₂ finalOutput₂) :
    iterations₁ = iterations₂ ∧ finalOutput₁ = finalOutput₂ := by
  induction first generalizing iterations₂ finalOutput₂ with
  | stop counter output =>
    cases second with
    | stop => exact ⟨rfl, rfl⟩
    | step active next => exact (active rfl).elim
  | step active next ih =>
    cases second with
    | stop => exact (active rfl).elim
    | step otherActive otherNext =>
      obtain ⟨countEq, outputEq⟩ := ih otherNext
      exact ⟨congrArg (· + 1) countEq, outputEq⟩

/-- One count/output pair describes every finite run from the given word state. -/
theorem run_exists_unique (numerator denominator counter accumulator output : B256) :
    ∃! result : Nat × B256,
      Run numerator denominator counter accumulator output result.1 result.2 := by
  obtain ⟨iterations, finalOutput, run, _⟩ :=
    run_exists numerator denominator counter accumulator output
  refine ⟨(iterations, finalOutput), run, ?_⟩
  rintro ⟨otherIterations, otherOutput⟩ otherRun
  obtain ⟨rfl, rfl⟩ := otherRun.deterministic run
  rfl

end Blanc.WordFakeExponential
