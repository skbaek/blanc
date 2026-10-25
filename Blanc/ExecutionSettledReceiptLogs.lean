import Blanc.Lift.CallerProvenance
import Blanc.TransactionForwardH

/-!
# Receipts of the actual selected transaction settlement

Receipt values retain the actual transaction status and cumulative gas used.
The selected refund quotient, calldata floor and touched-account sweep remain
unchanged. This module does not prove chain inclusion or later-key persistence.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The actual transaction inserts its own message receipt under the selected
historical settlement rules. No fixed refund quotient or sweep policy is used. -/
theorem TransactionTrace.receipt_of_selected_settlement
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        trace.messageOut.logs) := by
  obtain ⟨refund, hrefund, _⟩ := trace.exists_selectedFinalStateForm hsg
  have valid : validateTransaction benv.stat.rules tx 0 =
      .ok (trace.intrinsicGas, trace.calldataFloorGasCost) := by
    rw [validateTransaction_sender_congr_none hsg (s1 := 0) (s2 := trace.validationSender)]
    exact trace.validation
  have checked := trace.checked
  have debit := trace.debit
  have prepared := trace.prepared
  have message := trace.message.result
  have result := trace.result
  have hsg' : benv.beginTransaction.stat.rules.stateGas = none := hsg
  unfold processTransaction at result
  simp only [bind, Except.bind] at result
  rw [recoverValidationSender_of_stateGas_none tx hsg'] at result
  simp only [BenvStat.rules, Benv.beginTransaction, transactionPreludeBout,
    transactionBlobGasFee, transactionTenv, Except.mapError] at valid checked debit prepared hsg hsg' result
  simp only [valid, checked, debit, prepared, Option.toExcept,
    allocateEvmGas, hsg, message, hrefund, settleSelfdestructs] at result
  have output := (Prod.mk.inj (Except.ok.inj result)).2
  have trie := congrArg BlockOutput.receiptsTrie output
  have cumulative := congrArg BlockOutput.cumulativeGasUsed output
  rw [← trie, ← cumulative]
  exact Std.TreeMap.getElem?_insert_self

end Blanc.ExecutionTrace
