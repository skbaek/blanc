import Blanc.FakeExponential
import Blanc.WordFakeExponential
import Blanc.WordArithmetic

/-!
A sufficient, explicit no-wrap domain relating the accepted Nat exponential
trace to the accepted unsigned-word trace. Bounds follow a finite Nat run and
its initial output prefix. There is no reachability claim or maximal-domain
characterization, and no new exponential semantics.
-/

namespace Blanc.FakeExponentialWordCorrespondence

open Jaune

/-- Sufficient sum/product bounds, indexed by the existing Nat trace.
Cast addition already commutes with counter increment, even across wrap. -/
inductive NoWrap {numerator denominator : Nat} :
    {counter accumulator iterations output : Nat} →
      FakeExponential.Run numerator denominator counter accumulator iterations output → Nat → Prop
  | stop (counter sumPrefix : Nat) (sumBound : sumPrefix < 2 ^ 256) :
      NoWrap (FakeExponential.Run.stop counter) sumPrefix
  | step {counter accumulator iterations output sumPrefix : Nat}
      {active : accumulator ≠ 0}
      {next : FakeExponential.Run numerator denominator (counter + 1)
        (accumulator * numerator / (denominator * counter)) iterations output}
      (sumBound : sumPrefix + accumulator < 2 ^ 256)
      (productBound : accumulator * numerator < 2 ^ 256)
      (divisorBound : denominator * counter < 2 ^ 256)
      (safeNext : NoWrap next (sumPrefix + accumulator)) :
      NoWrap (FakeExponential.Run.step active next) sumPrefix

private theorem toB256_mul (a b : Nat) :
    a.toB256 * b.toB256 = (a * b).toB256 := by
  apply B256.toNat_inj
  simp only [B256.toNat_mul, B256.toNat_toB256, Nat.lo_eq]
  exact (Nat.mul_mod a b (2 ^ 256)).symm

private theorem nextAccumulator_cast (numerator denominator counter accumulator : Nat)
    (productBound : accumulator * numerator < 2 ^ 256)
    (divisorBound : denominator * counter < 2 ^ 256) :
    WordFakeExponential.nextAccumulator numerator.toB256 denominator.toB256
        counter.toB256 accumulator.toB256 =
      (accumulator * numerator / (denominator * counter)).toB256 := by
  unfold WordFakeExponential.nextAccumulator
  rw [toB256_mul accumulator numerator, toB256_mul denominator counter,
    wordDiv_eq_toB256_div, B256.toNat_toB256_of_lt productBound,
    B256.toNat_toB256_of_lt divisorBound]

/-- The final prefixed Nat sum fits one word throughout the named domain. -/
theorem NoWrap.final_sum_lt {numerator denominator counter accumulator iterations output sumPrefix : Nat}
    {run : FakeExponential.Run numerator denominator counter accumulator iterations output}
    (safe : NoWrap run sumPrefix) : sumPrefix + output < 2 ^ 256 := by
  induction safe with
  | stop counter sumPrefix sumBound =>
    simpa only [Nat.add_zero] using sumBound
  | step sumBound productBound divisorBound safeNext ih =>
    rw [← Nat.add_assoc]
    exact ih

/-- The Nat trace and its word image have exactly the same body count and sum. -/
theorem NoWrap.to_word_run {numerator denominator counter accumulator iterations output sumPrefix : Nat}
    {run : FakeExponential.Run numerator denominator counter accumulator iterations output}
    (safe : NoWrap run sumPrefix) :
    WordFakeExponential.Run numerator.toB256 denominator.toB256 counter.toB256
      accumulator.toB256 sumPrefix.toB256 iterations (sumPrefix + output).toB256 := by
  induction safe with
  | stop counter sumPrefix sumBound =>
    rw [Nat.add_zero]
    exact WordFakeExponential.Run.stop _ _
  | @step counter accumulator iterations output sumPrefix active next
      sumBound productBound divisorBound safeNext ih =>
    have accumulatorBound : accumulator < 2 ^ 256 := by omega
    have prefixBound : sumPrefix < 2 ^ 256 := by omega
    have wordActive : accumulator.toB256 ≠ 0 := by
      intro zeroWord
      have zeroNat := congrArg B256.toNat zeroWord
      rw [B256.toNat_toB256_of_lt accumulatorBound, B256.toNat_zero] at zeroNat
      exact active zeroNat
    rw [← Nat.add_assoc]
    apply WordFakeExponential.Run.step wordActive
    rw [toB256_add_one, nextAccumulator_cast numerator denominator counter accumulator
      productBound divisorBound, wordAdd_eq_toB256_add,
      B256.toNat_toB256_of_lt prefixBound, B256.toNat_toB256_of_lt accumulatorBound]
    exact ih

/-- Every word run from the image state has the Nat count and canonical prefixed sum. -/
theorem NoWrap.word_result {numerator denominator counter accumulator iterations output sumPrefix : Nat}
    {run : FakeExponential.Run numerator denominator counter accumulator iterations output}
    (safe : NoWrap run sumPrefix) {wordIterations : Nat} {wordOutput : B256}
    (wordRun : WordFakeExponential.Run numerator.toB256 denominator.toB256 counter.toB256
      accumulator.toB256 sumPrefix.toB256 wordIterations wordOutput) :
    wordIterations = iterations ∧
      wordOutput.toNat = sumPrefix + fakeExpAux numerator denominator counter accumulator := by
  obtain ⟨countEq, sumEq⟩ := wordRun.deterministic safe.to_word_run
  refine ⟨countEq, ?_⟩
  rw [sumEq, B256.toNat_toB256_of_lt safe.final_sum_lt, run.output_eq]

/-- Canonical initialization and final division give the Nat `fakeExp` value.
The denominator width is explicit; no reachability or contract constants are assumed. -/
theorem NoWrap.fakeExp_eq {factor numerator denominator iterations output : Nat}
    {run : FakeExponential.Run numerator denominator 1 (factor * denominator) iterations output}
    (safe : NoWrap run 0) (denominatorBound : denominator < 2 ^ 256)
    {wordIterations : Nat} {wordOutput : B256}
    (wordRun : WordFakeExponential.Run numerator.toB256 denominator.toB256 1
      (factor.toB256 * denominator.toB256) 0 wordIterations wordOutput) :
    wordIterations = iterations ∧
      (wordOutput / denominator.toB256).toNat = fakeExp factor numerator denominator := by
  rw [toB256_mul] at wordRun
  obtain ⟨countEq, sumEq⟩ := safe.word_result wordRun
  refine ⟨countEq, ?_⟩
  rw [wordDiv_eq_toB256_div, B256.toNat_toB256_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (B256.toNat_lt wordOutput))]
  rw [sumEq, Nat.zero_add, B256.toNat_toB256_of_lt denominatorBound]
  rfl

end Blanc.FakeExponentialWordCorrespondence
