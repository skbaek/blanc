import Blanc.FakeExponentialGrowth
import Blanc.FakeExponentialWordCorrespondence
import Blanc.FakeExponentialWordDomain
import Blanc.WordFakeExponentialBound

/-!
# Word against natural request fee, at fraction 17

The system request contracts run the word recurrence at factor 1 and fraction 17 over an excess
word, and quote its quotient. These results compare that quotient with `fake_exponential(1, excess,
17)` over the excess alone: where the excess came from, and any queue model, is the caller's.
No history or reachable-domain claim is made.
-/

namespace Blanc.RequestFeeWord

open Jaune

/-- A conservative growth threshold, not the maximal correspondence domain. -/
def natFeeExcessCeiling : Nat := 17 * 17 * 2 ^ 16

private theorem fee_ge_word_limit (excess : Nat)
    (large : natFeeExcessCeiling ≤ excess) :
    2 ^ 256 ≤ fakeExp 1 excess 17 := by
  have lower := FakeExponential.factor_mul_pow_le 1 excess 17 16 (2 ^ 16)
    (by decide) large
  rw [Nat.one_mul, ← Nat.pow_mul] at lower
  exact lower

/-- A finite Nat trace of the fee with the accepted prefixed no-wrap bounds. -/
def NoWrapDomain (excess : B256) (iterations : Nat) : Prop :=
  ∃ output, ∃ run : FakeExponential.Run excess.toNat 17 1 17 iterations output,
    FakeExponentialWordCorrespondence.NoWrap run 0

/-- The sufficient no-wrap domain necessarily lies below the growth ceiling. -/
theorem NoWrapDomain.excess_lt {excess : B256} {iterations : Nat}
    (domain : NoWrapDomain excess iterations) : excess.toNat < natFeeExcessCeiling := by
  by_contra notSmall
  have large : natFeeExcessCeiling ≤ excess.toNat := by omega
  have feeLower := fee_ge_word_limit excess.toNat large
  obtain ⟨output, run, safe⟩ := domain
  have sumLt := safe.final_sum_lt
  rw [Nat.zero_add, run.output_eq] at sumLt
  change fakeExpAux excess.toNat 17 1 17 < 2 ^ 256 at sumLt
  have feeLt : fakeExp 1 excess.toNat 17 < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) sumLt
  omega

/-- Every executed word trace has this Nat trace's count and the natural fee. -/
theorem NoWrapDomain.word_result {excess : B256} {iterations wordIterations : Nat}
    {wordOutput : B256} (domain : NoWrapDomain excess iterations)
    (wordRun : WordFakeExponential.Run excess 17 1 17 0 wordIterations wordOutput) :
    wordIterations = iterations ∧
      (wordOutput / (17 : B256)).toNat = fakeExp 1 excess.toNat 17 ∧
      wordOutput / (17 : B256) = (fakeExp 1 excess.toNat 17).toB256 := by
  obtain ⟨output, run, safe⟩ := domain
  have imageRun : WordFakeExponential.Run excess.toNat.toB256 (17 : Nat).toB256 1
      ((1 : Nat).toB256 * (17 : Nat).toB256) 0 wordIterations wordOutput := by
    rw [toB256_toNat]
    exact wordRun
  have same := safe.fakeExp_eq (factor := 1) (by decide) imageRun
  have feeEq : (wordOutput / (17 : B256)).toNat = fakeExp 1 excess.toNat 17 := same.2
  refine ⟨same.1, feeEq, ?_⟩
  rw [← feeEq, toB256_toNat]

/-- Natural-fee payment by a word-sized value forces excess below the same ceiling,
independently of any no-wrap or representation hypothesis. -/
theorem excess_lt_of_paid {excess : Nat} (value : B256)
    (paid : fakeExp 1 excess 17 ≤ value.toNat) : excess < natFeeExcessCeiling := by
  by_contra notSmall
  have large : natFeeExcessCeiling ≤ excess := by omega
  have feeLower := fee_ge_word_limit excess large
  have valueLt := B256.toNat_lt value
  omega

/-- Above the ceiling every word-sized quotient is strictly below the natural fee.
This is a symbolic separation, not a reachable execution claim. -/
theorem word_fee_lt_of_large_excess {excess : Nat} (output : B256)
    (large : natFeeExcessCeiling ≤ excess) :
    (output / (17 : B256)).toNat < fakeExp 1 excess 17 :=
  Nat.lt_of_lt_of_le (B256.toNat_lt _) (fee_ge_word_limit excess large)

private theorem small_run_window {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output)
    (small : excess.toNat < natFeeExcessCeiling) :
    17 * 17 * (1 + iterations) ≤ 2 ^ 256 := by
  have margin : 17 * (1 + 2 * natFeeExcessCeiling + 256) < 2 ^ 256 := by decide
  have dominates : 2 * excess.toNat ≤ 17 * (1 + 2 * natFeeExcessCeiling) := by omega
  have count := run.iterations_le_of_halving_horizon 1 17 (2 * natFeeExcessCeiling)
    (by decide) (by decide) margin dominates
  have fixed : 17 * 17 * (1 + 2 * natFeeExcessCeiling + 256) ≤ 2 ^ 256 := by decide
  have window : 1 + iterations ≤ 1 + 2 * natFeeExcessCeiling + 256 := by
    exact (Nat.add_le_add_left count 1).trans_eq (Nat.add_assoc _ _ _).symm
  exact (Nat.mul_le_mul_left (17 * 17) window).trans fixed

/-- The word fee equals the natural fee exactly on the no-wrap domain, with the same
executed iteration count. -/
theorem word_fee_eq_iff {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    (output / (17 : B256)).toNat = fakeExp 1 excess.toNat 17 ↔ NoWrapDomain excess iterations := by
  by_cases small : excess.toNat < natFeeExcessCeiling
  · have exactDomain := FakeExponentialWordDomain.Run.quotient_eq_iff_noWrap
      run (by decide) (by decide) (small_run_window run small)
    change (output / (17 : B256)).toNat = fakeExpAux excess.toNat 17 1 17 / 17 ↔
      NoWrapDomain excess iterations
    exact exactDomain
  · have mismatch := word_fee_lt_of_large_excess output (not_lt.mp small)
    constructor
    · intro equality
      omega
    · intro domain
      exact absurd domain.excess_lt small

/-- For every executed word run, the natural fee is an upper bound on the word fee,
including outside the exact equality domain. -/
theorem word_fee_le {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output) :
    (output / (17 : B256)).toNat ≤ fakeExp 1 excess.toNat 17 := by
  by_cases small : excess.toNat < natFeeExcessCeiling
  · exact FakeExponentialWordDomain.Run.quotient_le run
      (by decide) (by decide) (small_run_window run small)
  · exact (word_fee_lt_of_large_excess output (not_lt.mp small)).le

/-- A no-wrap checker for the natural recurrence, run from a sum prefix. -/
def noWrapCheck (numerator : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, accumulator, sum => accumulator == 0 && decide (sum < 2 ^ 256)
  | fuel + 1, counter, accumulator, sum =>
    if accumulator = 0 then decide (sum < 2 ^ 256)
    else
      decide (sum + accumulator < 2 ^ 256) && decide (accumulator * numerator < 2 ^ 256) &&
        decide (17 * counter < 2 ^ 256) &&
        noWrapCheck numerator fuel (counter + 1) (accumulator * numerator / (17 * counter))
          (sum + accumulator)

/-- A passing check is a Nat trace with the no-wrap bounds. -/
theorem noWrap_of_check {numerator fuel counter accumulator sum : Nat}
    (h : noWrapCheck numerator fuel counter accumulator sum = true) :
    ∃ iterations output, ∃ run : FakeExponential.Run numerator 17 counter accumulator iterations output,
      FakeExponentialWordCorrespondence.NoWrap run sum := by
  induction fuel generalizing counter accumulator sum with
  | zero =>
    simp only [noWrapCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, hs⟩ := h
    exact ⟨0, 0, .stop counter, .stop counter sum hs⟩
  | succ fuel ih =>
    by_cases ha : accumulator = 0
    · subst ha
      simp only [noWrapCheck, ite_true, decide_eq_true_eq] at h
      exact ⟨0, 0, .stop counter, .stop counter sum h⟩
    · simp only [noWrapCheck, ha, ite_false, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      obtain ⟨iterations, output, run, safe⟩ := ih h4
      exact ⟨_, _, .step ha run, .step (active := ha) h1 h2 h3 safe⟩

end Blanc.RequestFeeWord
