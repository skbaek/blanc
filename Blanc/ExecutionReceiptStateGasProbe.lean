import Blanc.Corpus.Freeze.DepositCells
import Blanc.Lift.SystemCallAmsterdam
import Blanc.ExecutionSettledReceiptLogs

/-!
# Bounded D-S10 receipt probe

Probe artifacts only. Amsterdam's EIP-7708 transfer logs prevent an unfiltered lift of the
legacy root-log equality. The frozen deposit selector excludes them by emitting address.
This file does not prove D-S10 or the state-gas frame-to-receipt correspondence.
-/

namespace Blanc.ExecutionTrace.D10Probe

open Jaune Blanc
open Blanc.Corpus.Freeze.Deposit

/-- The frozen deposit selector erases an EIP-7708 transfer log, wherever it occurs. -/
theorem depositLogs_transfer_prefix (sender recipient : Adr) (value : B256) (logs : List Log) :
    depositLogs (transferLog sender recipient value :: logs) = depositLogs logs := by
  have skipped : decide ((transferLog sender recipient value).address = depositAddr ∧
      (transferLog sender recipient value).topics[0]? = some depositEventSignatureHash) = false := by
    rw [decide_eq_false_iff_not]
    intro selected
    exact (by decide : transferLogAddress ≠ depositAddr) selected.1
  simp only [depositLogs, List.filter_cons, skipped, Bool.false_eq_true, ite_false]

/-- Frame-entry transfer logs never count as a deposit event, on any fork. -/
theorem depositLogs_initDevm (msg : Msg) : depositLogs (initDevm msg).logs = [] := by
  unfold initDevm
  split
  · rfl
  · split
    · unfold Devm.emitTransferLog
      split
      · rfl
      · exact depositLogs_transfer_prefix _ _ _ []
    · rfl

/-- The unfiltered empty-entry-log premise cannot be reused for positive Amsterdam transfers. -/
theorem initDevm_logs_nonempty {msg : Msg} (fork : msg.benv.stat.fork = .amsterdam)
    (transfer : msg.shouldTransferValue = true) (distinct : msg.caller ≠ msg.currentTarget)
    (nonzero : msg.value ≠ 0) : (initDevm msg).logs ≠ [] := by
  rw [Lift.initDevm_logs_transfer fork transfer distinct nonzero]
  exact List.cons_ne_nil _ _

/-- The actual producer inserts the actual message output's receipt and logs on every fork,
including state gas. No legacy `MessageCallTrace` or gas-settlement premise is assumed. -/
theorem transaction_receipt_exact {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (run : processTransaction benv bout tx index = .ok (state, bout')) :
    ∃ sender msg messageState messageOut,
      transactionMessage benv bout tx index = .ok (sender, msg) ∧
      processMessageCall msg = .ok (messageState, messageOut) ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx messageOut.error bout'.cumulativeGasUsed messageOut.logs) ∧
      bout'.blockLogs = bout.blockLogs ++ messageOut.logs := by
  unfold processTransaction at run
  dsimp only at run
  obtain ⟨prelude, hprelude, run⟩ := Except.bind_eq_ok run
  cases hprelude
  obtain ⟨validationSender, hrec, run⟩ := Except.bind_eq_ok run
  obtain ⟨⟨intrinsic, floor⟩, hvalid, run⟩ := Except.bind_eq_ok run
  obtain ⟨⟨sender, price, hashes, blob⟩, hchecked, run⟩ := Except.bind_eq_ok run
  obtain ⟨debit, hdebit, run⟩ := Except.bind_eq_ok run
  obtain ⟨msg, hprepared, run⟩ := Except.bind_eq_ok run
  obtain ⟨⟨messageState, messageOut⟩, hmessage, run⟩ := Except.bind_eq_ok run
  rw [Except.mapError_eq_ok_iff] at hmessage
  obtain ⟨counter, _, run⟩ := Except.bind_eq_ok run
  obtain ⟨bout₂, hbout₂, run⟩ := Except.bind_eq_ok run
  obtain ⟨bout₃, hbout₃, run⟩ := Except.bind_eq_ok run
  cases hbout₂
  cases hbout₃
  simp only [Except.ok.injEq, Prod.mk.injEq] at run
  refine ⟨sender, msg, messageState, messageOut, ?_, hmessage, ?_, ?_⟩
  · unfold transactionMessage
    dsimp only
    simp only [bind, Except.bind]
    rw [hrec]
    dsimp only
    rw [hvalid]
    dsimp only
    rw [show checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx = _
      from hchecked]
    dsimp only
    rw [show ((benv.beginTransaction.state.incrNonce sender).subBal sender
      (tx.gas * price + transactionBlobGasFee benv.beginTransaction tx).toB256).toExcept _ = _
      from hdebit]
    dsimp only
    rw [show prepareMessage _ (transactionTenvAt benv.beginTransaction tx index sender price intrinsic hashes)
      tx = _ from hprepared]
  · rw [← run.2]
    exact Std.TreeMap.getElem?_insert_self
  · rw [← run.2]
    rfl

end Blanc.ExecutionTrace.D10Probe
