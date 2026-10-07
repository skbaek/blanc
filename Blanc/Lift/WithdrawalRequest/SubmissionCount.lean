import Blanc.Lift.WithdrawalRequest.BalanceHistory
import Blanc.ExecutionBodyGas

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace

/-- Each retained frame contributes at most one submission-payment tag.
This counts occurrences, including repeated frames, rather than distinct states. -/
theorem submissionFramePayments_length_le (frames : List Exec.Frame) :
    (frames.flatMap submissionFramePayments).length ≤ frames.length := by
  induction frames with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.le_refl]
  | cons frame frames ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    by_cases submission : submissionPaymentFrame frame
    · simp only [submissionFramePayments, ite_eq_left submission,
        List.length_cons, List.length_nil]
      omega
    · simp only [submissionFramePayments, ite_eq_right submission, List.length_nil]
      omega

end Blanc.Lift.WithdrawalRequest
