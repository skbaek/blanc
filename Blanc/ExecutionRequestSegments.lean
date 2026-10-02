import Blanc.ExecutionTraceSettledFrames

namespace Blanc.ExecutionTrace

open Jaune

/-- Settled frames preceding the complete protocol withdrawal-message subtree. -/
def ConfiguredBlockTrace.beforeWithdrawalFrames {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) : List Exec.Frame :=
  trace.bodyTrace.beacon.settledFrames ++ trace.bodyTrace.history.settledFrames ++
    trace.bodyTrace.transactions.settledFrames

/-- Settled frames following the complete protocol withdrawal-message subtree. -/
def ConfiguredBlockTrace.afterWithdrawalFrames {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) : List Exec.Frame :=
  trace.bodyTrace.requests.consolidation.settledFrames

/-- Two consecutive actual blocks retain the previous consolidation suffix and
next beacon/history/transaction prefix between their withdrawal subtrees.
These are whole-subtree cuts, not internal storage-reset instruction cuts. -/
theorem consecutive_withdrawal_segments {cfg : ChainConfig} {pre middle post : BlockChain}
    (first : ConfiguredBlockTrace cfg pre middle)
    (second : ConfiguredBlockTrace cfg middle post) :
    first.settledFrames ++ second.settledFrames =
      first.beforeWithdrawalFrames ++ first.bodyTrace.requests.withdrawal.settledFrames ++
      (first.afterWithdrawalFrames ++ second.beforeWithdrawalFrames) ++
      second.bodyTrace.requests.withdrawal.settledFrames ++ second.afterWithdrawalFrames := by
  simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
    RequestsTrace.settledFrames, ConfiguredBlockTrace.beforeWithdrawalFrames,
    ConfiguredBlockTrace.afterWithdrawalFrames, List.append_assoc]

end Blanc.ExecutionTrace
