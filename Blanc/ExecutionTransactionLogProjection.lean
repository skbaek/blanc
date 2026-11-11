import Blanc.TransactionHistoricalForward
import Blanc.ExecutionTrace

/-! Exact log and receipt projections of retained transactions, using selected settlement. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- The actual retained transaction appends its message logs and inserts its exact receipt.
The selected refund quotient and touched-account sweep remain unchanged. -/
theorem TransactionTrace.logs_receipt
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (hbal : benv.stat.rules.bal = none) :
    bout'.blockLogs = bout.blockLogs ++ trace.messageOut.logs ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
          trace.messageOut.logs) := by
  obtain ⟨refund, refundEq, _⟩ := trace.exists_selectedFinalStateForm hsg
  have valid : validateTransaction benv.stat.rules tx 0 =
      .ok (trace.intrinsicGas, trace.calldataFloorGasCost) := by
    rw [validateTransaction_sender_congr_none (s1 := 0)
      (s2 := trace.validationSender) hsg]
    exact trace.validation
  obtain ⟨actualBout, result, _, _, _, receipt, logs⟩ :=
    processTransaction_of_stages_selected_receipts hsg hbal valid trace.checked
      trace.debit trace.prepared trace.message.result refundEq
  have eq := Prod.mk.inj (Except.ok.inj (trace.result.symm.trans result))
  rw [← eq.2] at logs receipt
  exact ⟨logs, receipt⟩

/-- The exact concatenation of message-output logs in this retained transaction list. -/
def ApplyTransactionsTrace.messageLogs
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) : List Log :=
  match trace with
  | .nil _ _ => []
  | .cons head tail => head.messageOut.logs ++ tail.messageLogs

/-- No transaction's message logs are lost or reordered by the actual list wrapper. -/
theorem ApplyTransactionsTrace.blockLogs_eq_messageLogs
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (hbal : benv.stat.rules.bal = none) :
    finalBout.blockLogs = bout.blockLogs ++ trace.messageLogs := by
  induction trace with
  | nil => exact (List.append_nil _).symm
  | cons head tail ih =>
    rw [ih hsg hbal, (head.logs_receipt hsg hbal).1]
    exact List.append_assoc _ _ _

end Blanc.ExecutionTrace
