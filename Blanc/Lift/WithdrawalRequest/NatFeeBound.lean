import Blanc.Lift.WithdrawalRequest.NatFee

/-! Necessary symbolic fee bounds. No reachable-domain or actual word/Nat
divergence witness is constructed here. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- The sufficient no-wrap domain necessarily lies below the growth ceiling. -/
theorem NatFeeDomain.excess_lt {excess : B256} {iterations : Nat}
    (domain : NatFeeDomain excess iterations) : excess.toNat < RequestFeeWord.natFeeExcessCeiling :=
  RequestFeeWord.NoWrapDomain.excess_lt domain

/-- Nat payment by a word-sized value forces excess below the same ceiling,
independently of any no-wrap or representation hypothesis. -/
theorem nat_paid_excess_lt (model : Blanc.WithdrawalRequest.State) (value : B256)
    (paid : Blanc.WithdrawalRequest.fee model ≤ value.toNat) :
    model.excess < RequestFeeWord.natFeeExcessCeiling :=
  RequestFeeWord.excess_lt_of_paid value paid

/-- Above the ceiling every word-sized quotient is strictly below the Nat
model fee. This is a symbolic separation, not a reachable execution claim. -/
theorem word_fee_lt_nat_of_large_excess (model : Blanc.WithdrawalRequest.State)
    (output : B256) (large : RequestFeeWord.natFeeExcessCeiling ≤ model.excess) :
    (output / (17 : B256)).toNat < Blanc.WithdrawalRequest.fee model :=
  RequestFeeWord.word_fee_lt_of_large_excess output large

end Blanc.Lift.WithdrawalRequest
