import Blanc.FakeExponentialWordDomain
import Blanc.WordFakeExponentialBound
import Blanc.Lift.WithdrawalRequest.NatFeeBound

/-! Exact fee equality domain for an existing executed word trace.
No history, reachable-domain membership or Nat payment is assumed or derived. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

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

/-- The actual word fee equals the unchanged Nat model fee exactly on the
existing no-wrap domain, with the same executed iteration count. -/
theorem word_fee_eq_iff_natFeeDomain {excess : B256} {iterations : Nat}
    {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output)
    (model : Blanc.WithdrawalRequest.State) (excessEq : model.excess = excess.toNat) :
    (output / (17 : B256)).toNat = Blanc.WithdrawalRequest.fee model ↔
      NatFeeDomain excess iterations := by
  by_cases small : excess.toNat < natFeeExcessCeiling
  · have exactDomain := FakeExponentialWordDomain.Run.quotient_eq_iff_noWrap
      run (by decide) (by decide) (small_run_window run small)
    rw [Blanc.WithdrawalRequest.fee, excessEq]
    change (output / (17 : B256)).toNat = fakeExpAux excess.toNat 17 1 17 / 17 ↔
      NatFeeDomain excess iterations
    exact exactDomain
  · have large : natFeeExcessCeiling ≤ model.excess := by rw [excessEq]; omega
    have mismatch := word_fee_lt_nat_of_large_excess model output large
    constructor
    · intro equality
      omega
    · intro domain
      have bound := domain.excess_lt
      omega

/-- For every executed canonical word run, the Nat model fee is a sufficient
upper bound on the word fee, including outside the exact equality domain. -/
theorem word_fee_le_nat {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output)
    (model : Blanc.WithdrawalRequest.State) (excessEq : model.excess = excess.toNat) :
    (output / (17 : B256)).toNat ≤ Blanc.WithdrawalRequest.fee model := by
  by_cases small : excess.toNat < natFeeExcessCeiling
  · have lower := FakeExponentialWordDomain.Run.quotient_le run
      (by decide) (by decide) (small_run_window run small)
    rw [Blanc.WithdrawalRequest.fee, excessEq]
    exact lower
  · have large : natFeeExcessCeiling ≤ model.excess := by rw [excessEq]; omega
    exact (word_fee_lt_nat_of_large_excess model output large).le

end Blanc.Lift.WithdrawalRequest
