import Blanc.ExecutionRequestSegments
import Blanc.Lift.WithdrawalRequest.SubmissionCount

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace

/-- Submission-payment occurrences between consecutive whole protocol withdrawal
subtrees fit within the sum of two actual full-block bounds. This includes the
previous consolidation suffix and next beacon/history/transaction prefix;
it does not identify an internal count-slot reset or prove Nat admission. -/
theorem consecutive_withdrawal_submission_count_lt
    {cfg : ChainConfig} {pre middle post : BlockChain}
    (first : ConfiguredBlockTrace cfg pre middle)
    (second : ConfiguredBlockTrace cfg middle post) :
    ((first.afterWithdrawalFrames ++ second.beforeWithdrawalFrames).flatMap
      submissionFramePayments).length < 2 * 2 ^ 64 := by
  have previous := block_submission_count_lt first
  have next := block_submission_count_lt second
  have combined : ((first.settledFrames ++ second.settledFrames).flatMap
      submissionFramePayments).length < 2 * 2 ^ 64 := by
    simp only [List.flatMap_append, List.length_append]
    omega
  rw [consecutive_withdrawal_segments first second] at combined
  simp only [List.flatMap_append, List.length_append] at combined ⊢
  omega

end Blanc.Lift.WithdrawalRequest
