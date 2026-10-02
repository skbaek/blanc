import Blanc.WordFakeExponential
import Jaune.MulDiv

/-!
Fuelled natural-number evaluation of the unsigned-word exponential loop.

The evaluator uses natural numbers only.  Every word multiplication and
addition is represented by an explicit reduction modulo `2^256`; the only
word-to-Nat facts below are the small arithmetic bridges from Jaune.
-/

namespace Blanc.WordFakeExponentialEval

open Jaune

def modulus : Nat := 2 ^ 256

def nextNat (numerator denominator counter accumulator : Nat) : Nat :=
  ((accumulator * numerator) % modulus) /
    ((denominator * counter) % modulus)

def addNat (left right : Nat) : Nat :=
  (left + right) % modulus

def incNat (counter : Nat) : Nat :=
  (counter + 1) % modulus

/-- Evaluate a word recurrence for at most `fuel` active bodies. -/
def runFuel : Nat → Nat → Nat → Nat → Nat → Nat →
    Option (Nat × Nat)
  | 0, _, _, _, accumulator, output =>
      if accumulator = 0 then some (0, output) else none
  | fuel + 1, numerator, denominator, counter, accumulator, output =>
      if accumulator = 0 then some (0, output)
      else
        match runFuel fuel numerator denominator (incNat counter)
          (nextNat numerator denominator counter accumulator)
          (addNat output accumulator) with
        | none => none
        | some (iterations, finalOutput) => some (iterations + 1, finalOutput)

theorem nextNat_toNat (numerator denominator counter accumulator : B256)
    (h : denominator * counter ≠ 0) :
    nextNat numerator.toNat denominator.toNat counter.toNat accumulator.toNat =
      (WordFakeExponential.nextAccumulator numerator denominator counter accumulator).toNat := by
  unfold nextNat WordFakeExponential.nextAccumulator
  rw [B256.toNat_div h, B256.toNat_mul_mod, B256.toNat_mul_mod]
  simp only [modulus]

theorem nextNat_toNat_zero (numerator denominator counter accumulator : B256)
    (h : denominator * counter = 0) :
    nextNat numerator.toNat denominator.toNat counter.toNat accumulator.toNat =
      (WordFakeExponential.nextAccumulator numerator denominator counter accumulator).toNat := by
  have hnat : (denominator * counter).toNat = 0 := by
    rw [h, B256.toNat_zero]
  have hnat' : denominator.toNat * counter.toNat % 2 ^ 256 = 0 := by
    rw [← B256.toNat_mul_mod, hnat]
  unfold nextNat modulus
  rw [hnat']
  have hnext :
      WordFakeExponential.nextAccumulator numerator denominator counter accumulator = 0 := by
    unfold WordFakeExponential.nextAccumulator
    change (B256.divMod (accumulator * numerator) (denominator * counter)).fst = 0
    unfold B256.divMod
    rw [ite_eq_left h]
  rw [hnext, B256.toNat_zero]
  simp only [Nat.div_zero]

theorem addNat_toNat (left right : B256) :
    addNat left.toNat right.toNat = (left + right).toNat := by
  unfold addNat
  rw [B256.toNat_add]
  simp only [Nat.lo_eq, modulus]

theorem incNat_toNat (counter : B256) :
    incNat counter.toNat = (counter + 1).toNat := by
  unfold incNat
  rw [B256.toNat_add]
  simp only [B256.toNat_one, Nat.lo_eq, modulus]

theorem runFuel_of_run
    {numerator denominator counter accumulator output finalOutput : B256}
    {iterations : Nat}
    {fuel : Nat}
    (run : WordFakeExponential.Run numerator denominator counter accumulator output
      iterations finalOutput)
    (enough : iterations ≤ fuel) :
    runFuel fuel numerator.toNat denominator.toNat counter.toNat accumulator.toNat output.toNat =
      some (iterations, finalOutput.toNat) := by
  induction run generalizing fuel with
  | stop counter output =>
    cases fuel with
    | zero => rfl
    | succ fuel => rfl
  | @step counter accumulator output iterations finalOutput active next ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have activeNat : accumulator.toNat ≠ 0 := by
        intro zero
        apply active
        apply B256.toNat_inj
        rw [zero, B256.toNat_zero]
      have nextNatEq := nextNat_toNat numerator denominator counter accumulator
      have addNatEq := addNat_toNat output accumulator
      have incNatEq := incNat_toNat counter
      by_cases divisor : denominator * counter = 0
      · rw [runFuel, ite_eq_right activeNat, incNatEq,
          nextNat_toNat_zero numerator denominator counter accumulator divisor,
          addNatEq]
        rw [ih (by omega)]
      · rw [runFuel, ite_eq_right activeNat, incNatEq,
          nextNatEq divisor, addNatEq]
        rw [ih (by omega)]

end Blanc.WordFakeExponentialEval
