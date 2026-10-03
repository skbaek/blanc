import Blanc.WordFakeExponential
import Blanc.WordArithmetic

namespace Blanc.WordFakeExponential

open Jaune

private theorem nextAccumulator_le_half
    (numerator accumulator : B256) (denominator counter : Nat)
    (denominatorPositive : 0 < denominator) (counterPositive : 0 < counter)
    (divisorBound : denominator * counter < 2 ^ 256)
    (dominates : 2 * numerator.toNat ≤ denominator * counter) :
    (nextAccumulator numerator denominator.toB256 counter.toB256 accumulator).toNat ≤
      accumulator.toNat / 2 := by
  have denominatorBound : denominator < 2 ^ 256 :=
    (Nat.le_mul_of_pos_right denominator counterPositive).trans_lt divisorBound
  have counterBound : counter < 2 ^ 256 :=
    (Nat.le_mul_of_pos_left counter denominatorPositive).trans_lt divisorBound
  have divisorEq : (denominator.toB256 * counter.toB256).toNat =
      denominator * counter := by
    rw [B256.toNat_mul_mod, B256.toNat_toB256_of_lt denominatorBound,
      B256.toNat_toB256_of_lt counterBound, Nat.mod_eq_of_lt divisorBound]
  have quotientBound : (accumulator * numerator).toNat /
      (denominator.toB256 * counter.toB256).toNat < 2 ^ 256 :=
    (Nat.div_le_self _ _).trans_lt (B256.toNat_lt (accumulator * numerator))
  rw [nextAccumulator, wordDiv_eq_toB256_div,
    B256.toNat_toB256_of_lt quotientBound, divisorEq, B256.toNat_mul_mod]
  by_cases numeratorZero : numerator.toNat = 0
  · simp only [numeratorZero, Nat.mul_zero, Nat.zero_mod, Nat.zero_div]
    exact Nat.zero_le _
  · have numeratorPositive : 0 < numerator.toNat := by omega
    calc
      accumulator.toNat * numerator.toNat % 2 ^ 256 / (denominator * counter)
          ≤ accumulator.toNat * numerator.toNat / (denominator * counter) :=
        Nat.div_le_div_right (Nat.mod_le _ _)
      _ ≤ accumulator.toNat * numerator.toNat / (2 * numerator.toNat) :=
        Nat.div_le_div_left dominates (Nat.mul_pos (by decide) numeratorPositive)
      _ = accumulator.toNat / 2 :=
        Nat.mul_div_mul_right _ _ numeratorPositive

private theorem halving_tail_bound
    (remaining counter denominator : Nat) (numerator accumulator output : B256)
    {iterations : Nat} {finalOutput : B256}
    (run : Run numerator denominator.toB256 counter.toB256
      accumulator output iterations finalOutput)
    (counterPositive : 0 < counter) (denominatorPositive : 0 < denominator)
    (divisorMargin : denominator * (counter + remaining) < 2 ^ 256)
    (dominates : 2 * numerator.toNat ≤ denominator * counter)
    (vanished : accumulator.toNat / 2 ^ remaining = 0) :
    iterations ≤ remaining := by
  induction remaining generalizing counter accumulator output iterations with
  | zero =>
    simp only [Nat.pow_zero, Nat.div_one] at vanished
    have accumulatorZero : accumulator = 0 := by
      apply B256.toNat_inj
      exact vanished
    cases run with
    | stop => exact Nat.le_refl 0
    | step active next => exact False.elim (active accumulatorZero)
  | succ remaining ih =>
    cases run with
    | stop => exact Nat.zero_le _
    | @step _ _ _ iterations _ active next =>
      have divisorBound : denominator * counter < 2 ^ 256 :=
        (Nat.mul_le_mul_left denominator (by omega :
          counter ≤ counter + (remaining + 1))).trans_lt divisorMargin
      have halves := nextAccumulator_le_half numerator accumulator denominator counter
        denominatorPositive counterPositive divisorBound dominates
      have nextVanished :
          (nextAccumulator numerator denominator.toB256 counter.toB256 accumulator).toNat /
            2 ^ remaining = 0 := by
        have bound := Nat.div_le_div_right (c := 2 ^ remaining) halves
        rw [div_two_div_pow, vanished] at bound
        exact Nat.eq_zero_of_le_zero bound
      rw [toB256_add_one] at next
      have tailBound := ih (counter + 1)
        (nextAccumulator numerator denominator.toB256 counter.toB256 accumulator)
        (output + accumulator) next (by omega)
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using divisorMargin)
        (dominates.trans (Nat.mul_le_mul_left denominator (by omega))) nextVanished
      omega

/-- After an arbitrary warm-up prefix, a sufficiently large exact divisor
halves each active accumulator. The word width then permits at most 256
further active updates. No width bound on numerator products or output sums
is needed. -/
theorem Run.iterations_le_of_halving_horizon
    (counter denominator horizon : Nat)
    {numerator accumulator output finalOutput : B256} {iterations : Nat}
    (run : Run numerator denominator.toB256 counter.toB256
      accumulator output iterations finalOutput)
    (counterPositive : 0 < counter) (denominatorPositive : 0 < denominator)
    (divisorMargin : denominator * (counter + horizon + 256) < 2 ^ 256)
    (dominates : 2 * numerator.toNat ≤ denominator * (counter + horizon)) :
    iterations ≤ horizon + 256 := by
  induction horizon generalizing counter accumulator output iterations with
  | zero =>
    exact halving_tail_bound 256 counter denominator numerator accumulator output run
      counterPositive denominatorPositive
      (by simpa only [Nat.add_zero] using divisorMargin)
      (by simpa only [Nat.add_zero] using dominates)
      (Nat.div_eq_of_lt (B256.toNat_lt accumulator))
  | succ horizon ih =>
    cases run with
    | stop => exact Nat.zero_le _
    | @step _ _ _ iterations _ active next =>
      rw [toB256_add_one] at next
      have tailBound := ih (counter + 1) next (by omega)
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using divisorMargin)
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using dominates)
      omega

end Blanc.WordFakeExponential
