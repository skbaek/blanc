import Blanc.RequestFeeWordDomain
import Blanc.WordFakeExponentialBound

/-!
# How long the request contracts' fee loop runs

At factor 1 and fraction 17, the word recurrence on an excess at most 2892 takes at most 462 iterations, and takes
exactly 462 at 2892, so the bound is tight. It returns `fake_exponential(1, excess, 17)` there. So on that domain the
run's existence, its length and its value are all facts, and statements need not take the run as a premise.

Above 2892: 462 is false (`word_run_3000`). The iteration count is at most `2 * excess / 17 + 256` for any excess below
`2 ^ 250`. Above `2 ^ 250` the only fact stated is that a run exists (`WordFakeExponential.run_exists`); no useful bound
is stated. The excess is a plain word here: where it comes from is the caller's.
-/

namespace Blanc.RequestFeeWord

open Jaune

/-- A passing check at fuel `fuel` is a Nat trace of at most `fuel` iterations. -/
theorem noWrap_of_check_le {numerator fuel counter accumulator sum : Nat}
    (h : noWrapCheck numerator fuel counter accumulator sum = true) :
    ∃ iterations output, iterations ≤ fuel ∧
      ∃ run : FakeExponential.Run numerator 17 counter accumulator iterations output,
        FakeExponentialWordCorrespondence.NoWrap run sum := by
  induction fuel generalizing counter accumulator sum with
  | zero =>
    simp only [noWrapCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨rfl, hs⟩ := h
    exact ⟨0, 0, Nat.le_refl _, .stop counter, .stop counter sum hs⟩
  | succ fuel ih =>
    by_cases ha : accumulator = 0
    · subst ha
      simp only [noWrapCheck, ite_true, decide_eq_true_eq] at h
      exact ⟨0, 0, Nat.zero_le _, .stop counter, .stop counter sum h⟩
    · simp only [noWrapCheck, ha, ite_false, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      obtain ⟨iterations, output, hle, run, safe⟩ := ih h4
      exact ⟨_, _, Nat.succ_le_succ hle, .step ha run, .step (active := ha) h1 h2 h3 safe⟩

/-- Every excess through 2892 passes the no-wrap check within 462 iterations. -/
theorem noWrapCheck_462 : (List.range 2893).all (fun e => noWrapCheck e 462 1 17 0) = true := by
  decide +kernel

/-- **The fee loop on the domain.** On an excess at most 2892, the word recurrence runs, in at most 462 iterations, and
quotes `fake_exponential(1, excess, 17)`. -/
theorem fee_run {e : B256} (he : e.toNat ≤ 2892) :
    ∃ n out, n ≤ 462 ∧ WordFakeExponential.Run e 17 1 17 0 n out ∧
      (out / (17 : B256)).toNat = fakeExp 1 e.toNat 17 ∧ out / (17 : B256) = (fakeExp 1 e.toNat 17).toB256 := by
  obtain ⟨i, o, hle, run, safe⟩ :=
    noWrap_of_check_le (List.all_eq_true.mp noWrapCheck_462 e.toNat (List.mem_range.mpr (by omega)))
  obtain ⟨n, out, wordRun, -⟩ := WordFakeExponential.run_exists e 17 1 17 0
  have domain : NoWrapDomain e i := ⟨o, run, safe⟩
  obtain ⟨hn, hv, hq⟩ := domain.word_result wordRun
  exact ⟨n, out, hn ▸ hle, wordRun, hv, hq⟩

/-- The word recurrence at excess 2892: 462 steps. -/
theorem word_run_2892 : WordFakeExponential.Run (2892 : Nat).toB256 17 1 17 0 462
    (1293016615363553351305261411891033154262342899586402592153715843914719896707 : Nat).toB256 :=
  WordFakeExponentialEval.run_of_runFuel (fuel := 512) (by decide +kernel)

/-- **462 is tight.** Every word recurrence on excess 2892 takes exactly 462 iterations. -/
theorem iterations_2892 {n : Nat} {out : B256} (run : WordFakeExponential.Run (2892 : Nat).toB256 17 1 17 0 n out) :
    n = 462 :=
  (run.deterministic word_run_2892).1

/-- The word recurrence at excess 3000: 472 steps, past the domain's 462. -/
theorem word_run_3000 : WordFakeExponential.Run (3000 : Nat).toB256 17 1 17 0 472
    (1329405829931347457214487620812284486152978277224439161222822320272854268043 : Nat).toB256 :=
  WordFakeExponentialEval.run_of_runFuel (fuel := 512) (by decide +kernel)

/-- **Above the domain, a linear bound.** For any excess below `2 ^ 250`, the word recurrence takes at most
`2 * excess / 17 + 256` iterations. -/
theorem iterations_le_linear {e : B256} {n : Nat} {out : B256} (he : e.toNat < 2 ^ 250)
    (run : WordFakeExponential.Run e 17 1 17 0 n out) : n ≤ 2 * e.toNat / 17 + 256 := by
  have hsum : 17 * (1 + 2 * e.toNat / 17 + 256) < 2 ^ 256 := by
    have htop : (2 : Nat) ^ 256 = 64 * 2 ^ 250 := by decide
    have hbig : 4369 ≤ (2 : Nat) ^ 250 := by decide
    rw [htop]
    generalize (2 : Nat) ^ 250 = w at he hbig
    omega
  exact run.iterations_le_of_halving_horizon 1 17 (2 * e.toNat / 17) (by decide) (by decide) hsum (by omega)

/-- `fake_exponential(1, e, 17)` is at least 1: the fee is at least 1 wei at any excess, in naturals. -/
theorem fakeExp_pos (e : Nat) : 1 ≤ fakeExp 1 e 17 := by
  have := FakeExponential.factor_mul_pow_le 1 e 17 0 0 (by decide) (by simp only [Nat.mul_zero, Nat.zero_le])
  simpa only [Nat.pow_zero, Nat.mul_one] using this

end Blanc.RequestFeeWord
