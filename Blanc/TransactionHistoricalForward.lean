import Blanc.TransactionForwardH

/-! Forward transaction settlement from the selected historical rule set.
The refund quotient and touched-account sweep remain those of the supplied environment. -/

namespace Blanc

open Jaune ExecutionTrace

/-- Transaction gas under the selected refund quotient and calldata floor. -/
def selectedTxGasUsed (quotient gas calldataFloor gasLeft refund : Nat) : Nat :=
  max (gas - gasLeft - min ((gas - gasLeft) / quotient) refund) calldataFloor

/-- The two fee credits, SELFDESTRUCT deletions and selected touched-account sweep. -/
def selectedTxFinalState (benv : Benv) (tx : Tx) (sender : Adr)
    (effectiveGasPrice gasUsed : Nat) (mpost : State) (mout : MsgCallOutput) : State :=
  sweepTouchedAccounts benv.stat.rules mout.touchedAccounts.toList
    (mout.accountsToDelete.toList.foldl destroyAccount
      ((mpost.addBal sender ((tx.gas - gasUsed) * effectiveGasPrice).toB256).addBal
        benv.stat.coinbase (gasUsed * (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256))

/-- Forward settlement with the actual selected quotient, sweep, gas counters and receipt.
No assumption about modern refund or touched-account rules is used. -/
theorem processTransaction_of_stages_selected_receipts
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {intrinsicGas calldataFloorGas : Nat} {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    {debit : State} {msg : Msg} {mpost : State} {mout : MsgCallOutput} {refund : Nat}
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    (hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas))
    (hchecked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed))
    (hdebit : (benv.state.incrNonce sender).subBal sender
      (tx.gas * effectiveGasPrice + transactionBlobGasFee benv tx).toB256 = some debit)
    (hprepared : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index sender effectiveGasPrice intrinsicGas
        blobVersionedHashes) tx = .ok msg)
    (hcall : processMessageCall msg = .ok (mpost, mout))
    (hrefund : Int.toNat? mout.refundCounter = some refund) :
    let gasUsed := selectedTxGasUsed benv.stat.rules.settle.refundQuotient
      tx.gas calldataFloorGas mout.gasLeft refund
    ∃ bout', processTransaction benv bout tx index =
        .ok (selectedTxFinalState benv tx sender effectiveGasPrice gasUsed mpost mout, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + gasUsed ∧
      bout'.blockGasUsed = bout.blockGasUsed + gasUsed ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx mout.error bout'.cumulativeGasUsed mout.logs) ∧
      bout'.blockLogs = bout.blockLogs ++ mout.logs := by
  dsimp only
  have hsg' : benv.beginTransaction.stat.rules.stateGas = none := hsg
  unfold processTransaction
  simp only [bind, Except.bind]
  rw [recoverValidationSender_of_stateGas_none tx hsg']
  simp only [BenvStat.rules, Benv.beginTransaction, transactionPreludeBout, transactionBlobGasFee,
    transactionTenv, Except.mapError] at hvalid hchecked hdebit hprepared hsg hbal hsg' ⊢
  simp only [hvalid, hchecked, hdebit, hprepared, Option.toExcept, allocateEvmGas, hsg, hcall, hrefund]
  apply Exists.intro
  simp only [selectedTxFinalState, selectedTxGasUsed, BenvStat.rules, settleSelfdestructs,
    hsg, hbal, settleTransactionGas]
  exact ⟨rfl, rfl, rfl, rfl, Std.TreeMap.getElem?_insert_self, rfl⟩

end Blanc

