import Blanc.Lift.WithdrawalRequest.NatFeeBound

/-! Exact fee equality domain for an existing executed word trace.
No history, reachable-domain membership or Nat payment is assumed or derived. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- The actual word fee equals the unchanged Nat model fee exactly on the
existing no-wrap domain, with the same executed iteration count. -/
theorem word_fee_eq_iff_natFeeDomain {excess : B256} {iterations : Nat}
    {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output)
    (model : Blanc.WithdrawalRequest.State) (excessEq : model.excess = excess.toNat) :
    (output / (17 : B256)).toNat = Blanc.WithdrawalRequest.fee model ↔
      NatFeeDomain excess iterations := by
  rw [Blanc.WithdrawalRequest.fee, excessEq]
  exact RequestFeeWord.word_fee_eq_iff run

/-- For every executed canonical word run, the Nat model fee is a sufficient
upper bound on the word fee, including outside the exact equality domain. -/
theorem word_fee_le_nat {excess : B256} {iterations : Nat} {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output)
    (model : Blanc.WithdrawalRequest.State) (excessEq : model.excess = excess.toNat) :
    (output / (17 : B256)).toNat ≤ Blanc.WithdrawalRequest.fee model := by
  rw [Blanc.WithdrawalRequest.fee, excessEq]
  exact RequestFeeWord.word_fee_le run

end Blanc.Lift.WithdrawalRequest
