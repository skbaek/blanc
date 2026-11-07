import Blanc.RequestFeeWord
import Blanc.FakeExponentialEval
import Blanc.WordFakeExponentialEval

/-!
# Where the request contracts' word fee is the natural fee

At factor 1 and fraction 17, the quotient of the word recurrence equals `fake_exponential(1, excess, 17)` at every
excess up to 2892, and not at 2893, where the first product passes the word. Both are checked by the kernel. The
excess is a plain number here: where it comes from is the caller's.
-/

namespace Blanc.RequestFeeWord

open Jaune

/-- Every excess through 2892 passes the no-wrap check. -/
theorem noWrapCheck_through : (List.range 2893).all (fun e => noWrapCheck e 512 1 17 0) = true := by
  decide +kernel

/-- **The no-wrap domain holds** at every excess through 2892. -/
theorem noWrapDomain_of_le {e : Nat} (he : e ≤ 2892) : ∃ iterations, NoWrapDomain e.toB256 iterations := by
  obtain ⟨iterations, output, run, safe⟩ :=
    noWrap_of_check (List.all_eq_true.mp noWrapCheck_through e (List.mem_range.mpr (by omega)))
  refine ⟨iterations, output, ?_⟩
  rw [B256.toNat_toB256_of_lt (by omega)]
  exact ⟨run, safe⟩

/-- **Word and natural fee agree through 2892.** Any executed word recurrence on an excess at most 2892 quotes
`fake_exponential(1, excess, 17)`. -/
theorem word_fee_eq_natural {e iterations : Nat} {output : B256} (he : e ≤ 2892)
    (run : WordFakeExponential.Run e.toB256 17 1 17 0 iterations output) :
    (output / (17 : B256)).toNat = fakeExp 1 e 17 := by
  obtain ⟨_, domain⟩ := noWrapDomain_of_le he
  have := (domain.word_result run).2.1
  rwa [B256.toNat_toB256_of_lt (by omega)] at this

/-- The word recurrence at excess 2893: 457 steps, against the natural recurrence's 462. -/
theorem word_run_2893 : WordFakeExponential.Run (2893 : Nat).toB256 17 1 17 0 457
    (545485220060489857066268109499810576327418688227975047986437738206577926843 : Nat).toB256 :=
  WordFakeExponentialEval.run_of_runFuel (fuel := 512) (by decide +kernel)

/-- The natural fee at excess 2893. -/
theorem natural_fee_2893 :
    fakeExp 1 2893 17 = 80668064690921409049190791237320678716946849613533250306370202067869504081 := by
  have h : FakeExponentialEval.runFuel 512 2893 17 1 17 =
      some (462, 1371357099745663953836243451034451538188096443430065255208293435153781569388) := by
    decide +kernel
  have out := (FakeExponentialEval.run_of_runFuel h).output_eq
  show fakeExpAux 2893 17 1 17 / 17 = _
  rw [← out]

/-- **Word and natural fee differ at 2893.** Every executed word recurrence on excess 2893 quotes something other
than `fake_exponential(1, 2893, 17)`, which is the first excess where this happens. -/
theorem word_fee_ne_natural_2893 {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run (2893 : Nat).toB256 17 1 17 0 iterations output) :
    (output / (17 : B256)).toNat ≠ fakeExp 1 2893 17 := by
  obtain ⟨-, rfl⟩ := run.deterministic word_run_2893
  rw [natural_fee_2893]
  decide +kernel

end Blanc.RequestFeeWord
