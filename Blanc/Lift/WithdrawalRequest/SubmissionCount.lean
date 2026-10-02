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

/-- Submission-payment occurrences in the entire actual block fit in 64 bits.
All four system-message subtrees are included; no code or domain premise
is needed for this count. It is a per-block bound, not a reset-interval bound. -/
theorem block_submission_count_lt {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    (trace.settledFrames.flatMap submissionFramePayments).length < 2 ^ 64 := by
  exact Nat.lt_of_le_of_lt (submissionFramePayments_length_le trace.settledFrames)
    trace.settledFrames_length_lt

end Blanc.Lift.WithdrawalRequest
