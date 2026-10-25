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

/-- A failed complete call settlement contributes no settled root, even if
its internal result still carries raw logs. -/
theorem ProcessMessageTrace.settledRoots_eq_nil_of_error
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    (failed : post.error.isNone = false) : trace.settledRoots = [] := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => rfl
  | @some pc sevm pre raw run =>
      have settled := (RunFrame.some_inv process).2
      have rejected : Frame.settlementCommits (Frame.ofCall msg) raw ≠ true := by
        simp only [Frame.settlementCommits, ← settled, failed]
        decide
      simp only [ProcessMessageTrace.settledRoots, ite_eq_right rejected]

/-- Failed CREATE settlement contributes no root, including a clean raw
constructor whose code-deposit settlement sets an error. -/
theorem ProcessCreateMessageTrace.settledRoots_eq_nil_of_error
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    (failed : post.error.isNone = false) : trace.settledRoots = [] := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none => rfl
  | @some pc sevm pre raw run =>
      have settled := (RunFrame.some_inv process).2
      have rejected : Frame.settlementCommits (Frame.ofCreate msg) raw ≠ true := by
        simp only [Frame.settlementCommits, ← settled, failed]
        decide
      simp only [ProcessCreateMessageTrace.settledRoots, ite_eq_right rejected]

private theorem createRun_logs_error
    {msg : Msg} {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = true)
    (collision : messageCreateCollision msg = false)
    (core : processCreateMessage msg = .ok evm)
    (result : processMessageCall msg = .ok (state, out)) :
    out.error = evm.error ∧ out.logs = (if evm.error.isNone then evm.logs else []) := by
  unfold processMessageCall processMessageCall.create at result
  simp only [target, ↓reduceIte, hsg] at result
  unfold messageCreateCollision at collision
  simp only [collision, Bool.false_eq_true, ↓reduceIte, core,
    Except.bimap, id, bind, Except.bind] at result
  split at result
  · rename_i clean
    obtain ⟨refund, _, output⟩ := Except.bind_eq_ok result
    cases output
    simp only [clean, ↓reduceIte, and_self]
  · rename_i failed
    cases result
    simp only [ite_eq_right failed, and_self]

private theorem callRun_logs_error
    {msg delegated execMsg : Msg} {refund : Nat}
    {evm : Devm} {state : State} {out : MsgCallOutput}
    (hsg : msg.benv.stat.rules.stateGas = none)
    (target : msg.target.isNone = false)
    (delegation : messageCallDelegation msg = .ok (delegated, refund))
    (execMsgEq : execMsg = messageCallExecutionMessage delegated)
    (core : processMessage execMsg = .ok evm)
    (result : processMessageCall msg = .ok (state, out)) :
    out.error = evm.error ∧ out.logs = (if evm.error.isNone then evm.logs else []) := by
  unfold processMessageCall processMessageCall.call at result
  simp only [target, Bool.false_eq_true, ↓reduceIte, hsg] at result
  rw [show processMessageCall.legacyAuthorization msg = .ok (delegated, refund)
    from delegation] at result
  simp only [Except.bind_ok] at result
  have coreExec : processMessage (messageCallExecutionMessage delegated) = .ok evm :=
    (congrArg processMessage execMsgEq).symm.trans core
  obtain ⟨actual, mapped, tail⟩ := Except.bind_eq_ok result
  have same : actual = evm := Except.ok.inj
    ((Except.bimap_id_eq_ok mapped).symm.trans coreExec)
  subst actual
  split at tail
  · rename_i clean
    obtain ⟨refund, _, output⟩ := Except.bind_eq_ok tail
    cases output
    simp only [clean, ↓reduceIte, and_self]
  · rename_i failed
    cases tail
    simp only [ite_eq_right failed, and_self]

/-- A failed top-level output has neither receipt logs nor complete-settlement
roots. The CREATE branch tests the final code-deposit outcome. -/
theorem MessageCallTrace.logs_and_settledRoots_eq_nil_of_error
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (failed : out.error.isNone = false) :
    out.logs = [] ∧ trace.settledRoots = [] := by
  cases trace with
  | createCollision target collision result =>
      unfold processMessageCall processMessageCall.create at result
      simp only [target, ↓reduceIte, hsg] at result
      unfold messageCreateCollision at collision
      simp only [collision, ↓reduceIte, pure] at result
      have output := (Prod.mk.inj (Except.ok.inj result)).2
      exact ⟨(congrArg MsgCallOutput.logs output).symm, rfl⟩
  | createRun target collision evm core retained result =>
      obtain ⟨error, logs⟩ := createRun_logs_error hsg target collision core result
      have coreFailed : evm.error.isNone = false := by rw [← error]; exact failed
      refine ⟨?_, retained.settledRoots_eq_nil_of_error coreFailed⟩
      rw [logs, coreFailed]
      rfl
  | callRun target delegated refund delegation execMsg execMsgEq evm core retained result =>
      obtain ⟨error, logs⟩ := callRun_logs_error hsg target delegation execMsgEq core result
      have coreFailed : evm.error.isNone = false := by rw [← error]; exact failed
      refine ⟨?_, retained.settledRoots_eq_nil_of_error coreFailed⟩
      rw [logs, coreFailed]
      rfl

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
