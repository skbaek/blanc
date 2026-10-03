import Blanc.FakeExponentialGrowth
import Blanc.Lift.WithdrawalRequest.NatFee

/-! Necessary symbolic fee bounds. No reachable-domain or actual word/Nat
divergence witness is constructed here. -/

namespace Blanc.Lift.WithdrawalRequest

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

/-- The sufficient no-wrap domain necessarily lies below the growth ceiling. -/
theorem NatFeeDomain.excess_lt {excess : B256} {iterations : Nat}
    (domain : NatFeeDomain excess iterations) : excess.toNat < natFeeExcessCeiling := by
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

/-- Above the ceiling every word-sized quotient is strictly below the Nat
model fee. This is a symbolic separation, not a reachable execution claim. -/
theorem word_fee_lt_nat_of_large_excess (model : Blanc.WithdrawalRequest.State)
    (output : B256) (large : natFeeExcessCeiling ≤ model.excess) :
    (output / (17 : B256)).toNat < Blanc.WithdrawalRequest.fee model := by
  have feeLower := fee_ge_word_limit model.excess large
  exact Nat.lt_of_lt_of_le (B256.toNat_lt _) feeLower

end Blanc.Lift.WithdrawalRequest
