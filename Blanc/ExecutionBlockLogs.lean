import Blanc.ExecutionSettledReceiptLogs
import Blanc.ExecutionStagedBodyTrace

/-! Original transaction logs in the final block output. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- Both enabled and disabled request stages preserve transaction block logs. -/
theorem RequestStageTrace.blockLogs_eq
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    bout'.blockLogs = bout.blockLogs := by
  cases trace with
  | skipped => rfl
  | called _ requests _ => exact requests.receiptsTrie_and_blockLogs_eq.2

/-- Withdrawals, requests and final access accounting preserve the transaction logs. -/
theorem StagedBodyTrace.blockLogs_eq_transactionBout
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    bout.blockLogs = trace.transactionBout.blockLogs := by
  have withdrawal : trace.withdrawalBout.blockLogs = trace.transactionBout.blockLogs := by
    have run := congrArg (fun p : State × BlockOutput => p.2.blockLogs) trace.withdrawalsRun
    unfold withdrawalsPass at run
    split at run <;> exact run.symm
  have final := congrArg BlockOutput.blockLogs trace.finalBout_eq
  exact final.symm.trans (trace.requests.blockLogs_eq.trans withdrawal)

end Blanc.ExecutionTrace
