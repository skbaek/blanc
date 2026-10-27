import Blanc.Lift.CallerProvenance
import Blanc.TransactionForward
import Blanc.ExecutionMessageEffects
import Blanc.Lift.CommittedLogs
import Blanc.RlpConcrete
import Blanc.ExecutionStagedBodyTrace

/-!
# Receipts of the actual selected transaction settlement

Receipt values retain the actual transaction status and cumulative gas used.
The selected refund quotient, calldata floor and touched-account sweep remain
unchanged. Later transactions preserve a receipt when their encoded index keys
are distinct from its key. This module does not prove chain inclusion.
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

/-- A clean complete settlement retains its root log sequence exactly once. -/
theorem ProcessMessageTrace.logs_eq_settledRoots_of_clean
    {msg : Msg} {post : Devm} (trace : ProcessMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = none)
    (clean : post.error.isNone = true) :
    post.logs = trace.settledRoots.flatMap (fun root => root.post.logs) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      change RunFrame (Frame.ofCall msg) none (.ok post) at process
      cases enter : (Frame.ofCall msg).enter with
      | done result =>
          simp only [RunFrame, enter, true_and] at process
          subst result
          exact Frame.enter_done_clean_logs_noStateGas hsg enter clean
      | run evm =>
          simp only [RunFrame, enter, reduceCtorEq, false_and, exists_false] at process
  | @some pc sevm pre raw run =>
      have settled := (RunFrame.some_inv process).2
      have commits : Frame.settlementCommits (Frame.ofCall msg) raw = true := by
        simp only [Frame.settlementCommits, ← settled, clean]
      have rawCommits := Frame.raw_commits_of_settlementCommits commits
      cases raw with
      | error error => simp only [Execution.commits, Bool.false_eq_true] at rawCommits
      | ok rawPost =>
          have logs := Frame.settle_logs_of_ok settled.symm
          simpa only [ProcessMessageTrace.settledRoots, commits, ↓reduceIte,
            RetainedXlot.settledRoots, rawCommits, ↓reduceDIte, Exec.Frame.ofRun,
            Exec.Frame.post, Execution.committedPost, List.flatMap_cons,
            List.flatMap_nil, List.append_nil] using logs

/-- A clean complete settlement retains its root log sequence exactly once. -/
theorem ProcessCreateMessageTrace.logs_eq_settledRoots_of_clean
    {msg : Msg} {post : Devm} (trace : ProcessCreateMessageTrace msg (.ok post))
    (hsg : msg.benv.stat.rules.stateGas = none)
    (clean : post.error.isNone = true) :
    post.logs = trace.settledRoots.flatMap (fun root => root.post.logs) := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
      change RunFrame (Frame.ofCreate msg) none (.ok post) at process
      cases enter : (Frame.ofCreate msg).enter with
      | done result =>
          simp only [RunFrame, enter, true_and] at process
          subst result
          exact Frame.enter_done_clean_logs_noStateGas hsg enter clean
      | run evm =>
          simp only [RunFrame, enter, reduceCtorEq, false_and, exists_false] at process
  | @some pc sevm pre raw run =>
      have settled := (RunFrame.some_inv process).2
      have commits : Frame.settlementCommits (Frame.ofCreate msg) raw = true := by
        simp only [Frame.settlementCommits, ← settled, clean]
      have rawCommits := Frame.raw_commits_of_settlementCommits commits
      cases raw with
      | error error => simp only [Execution.commits, Bool.false_eq_true] at rawCommits
      | ok rawPost =>
          have logs := Frame.settle_logs_of_ok settled.symm
          simpa only [ProcessCreateMessageTrace.settledRoots, commits, ↓reduceIte,
            RetainedXlot.settledRoots, rawCommits, ↓reduceDIte, Exec.Frame.ofRun,
            Exec.Frame.post, Execution.committedPost, List.flatMap_cons,
            List.flatMap_nil, List.append_nil] using logs

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

/-- The actual message wrapper emits exactly the complete-settlement root logs.
Each root's post already includes its retained descendants, so roots are folded once. -/
theorem MessageCallTrace.logs_eq_settledRoots
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (hsg : msg.benv.stat.rules.stateGas = none) :
    out.logs = trace.settledRoots.flatMap (fun root => root.post.logs) := by
  cases status : out.error.isNone with
  | false =>
      obtain ⟨logs, roots⟩ := trace.logs_and_settledRoots_eq_nil_of_error hsg status
      rw [logs, roots]
      rfl
  | true =>
      cases trace with
      | createCollision target collision result =>
          unfold processMessageCall processMessageCall.create at result
          simp only [target, ↓reduceIte, hsg] at result
          unfold messageCreateCollision at collision
          simp only [collision, ↓reduceIte, pure] at result
          have output := (Prod.mk.inj (Except.ok.inj result)).2
          exact (congrArg MsgCallOutput.logs output).symm
      | createRun target collision evm core retained result =>
          obtain ⟨error, logs⟩ := createRun_logs_error hsg target collision core result
          have clean : evm.error.isNone = true := by rw [← error]; exact status
          rw [logs, clean]
          exact retained.logs_eq_settledRoots_of_clean hsg clean
      | callRun target delegated refund delegation execMsg execMsgEq evm core retained result =>
          obtain ⟨error, logs⟩ := callRun_logs_error hsg target delegation execMsgEq core result
          have clean : evm.error.isNone = true := by rw [← error]; exact status
          have execHsg : execMsg.benv.stat.rules.stateGas = none := by
            rw [execMsgEq, messageCallExecutionMessage_benv_stat,
              messageCallDelegation_benv_stat delegation]
            exact hsg
          rw [logs, clean]
          exact retained.logs_eq_settledRoots_of_clean execHsg clean

/-- The actual transaction inserts its own message receipt under the selected
historical settlement rules and appends those same logs to the block output.
No fixed refund quotient or sweep policy is used. -/
theorem TransactionTrace.receipt_and_blockLogs_of_selected_settlement
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        trace.messageOut.logs) ∧
      bout'.blockLogs = bout.blockLogs ++ trace.messageOut.logs := by
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
  constructor
  · rw [← trie, ← cumulative]
    exact Std.TreeMap.getElem?_insert_self
  · exact (congrArg BlockOutput.blockLogs output).symm

/-- The receipt projection of the original selected settlement. -/
theorem TransactionTrace.receipt_of_selected_settlement
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        trace.messageOut.logs) :=
  (trace.receipt_and_blockLogs_of_selected_settlement hsg).1

/-- The actual receipt stores the retained root logs once, with its actual
status, cumulative gas and selected transaction-index key. -/
theorem TransactionTrace.receipt_of_settledRoots
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        (trace.settledRoots.flatMap (fun root => root.post.logs))) := by
  have msgHsg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact hsg
  rw [TransactionTrace.settledRoots, ← trace.message.logs_eq_settledRoots msgHsg]
  exact trace.receipt_of_selected_settlement hsg

/-- An actual transaction preserves every receipt at a different encoded key.
This uses the existing all-fork insertion theorem, with no settlement restriction. -/
theorem TransactionTrace.receipt_preserved_of_key_ne
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {key : Bytes} (different : BLT.toBytes (.bytes index.toBytes) ≠ key) :
    bout'.receiptsTrie[key]? = bout.receiptsTrie[key]? := by
  obtain ⟨receipt, inserted⟩ := processTransaction_receiptsTrie trace.result
  change bout'.receiptsTrie = _ at inserted
  rw [inserted, Std.TreeMap.getElem?_insert]
  split
  · rename_i same
    exact False.elim (different (Std.LawfulEqCmp.eq_of_compare same))
  · rfl

/-- An actual suffix replay preserves a chosen receipt if no suffix transaction
uses its encoded key. Index separation must be proved by the caller. -/
theorem ApplyTransactionsTrace.receipt_preserved_of_keys_ne
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    {key : Bytes}
    (different : ∀ item ∈ txs, BLT.toBytes (.bytes item.1.toBytes) ≠ key) :
    finalBout.receiptsTrie[key]? = bout.receiptsTrie[key]? := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      have headDifferent := different _ (List.mem_cons_self ..)
      have tailDifferent := fun item member => different item (List.mem_cons_of_mem _ member)
      exact (ih tailDifferent).trans (head.receipt_preserved_of_key_ne headDifferent)

/-- The receipt of this exact transaction survives its actual suffix replay.
Its cumulative gas remains the value at this transaction's settlement. -/
theorem TransactionTrace.receipt_of_settledRoots_after_suffix
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {txs : List (Nat × Tx)} {finalBenv : Benv} {finalBout : BlockOutput}
    (suffix : ApplyTransactionsTrace txs (benv.withState state) bout' finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (different : ∀ item ∈ txs, BLT.toBytes (.bytes item.1.toBytes) ≠
      BLT.toBytes (.bytes index.toBytes)) :
    finalBout.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        (trace.settledRoots.flatMap (fun root => root.post.logs))) := by
  rw [suffix.receipt_preserved_of_keys_ne different]
  exact trace.receipt_of_settledRoots hsg

/-- For a positive index below 128, actual later indices suffice: encoded-key
separation follows from Jaune's codec, even for arbitrarily large suffix indices. -/
theorem TransactionTrace.receipt_of_settledRoots_after_later_indices
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {txs : List (Nat × Tx)} {finalBenv : Benv} {finalBout : BlockOutput}
    (suffix : ApplyTransactionsTrace txs (benv.withState state) bout' finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (positive : 0 < index) (small : index < 128)
    (later : ∀ item ∈ txs, index < item.1) :
    finalBout.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        (trace.settledRoots.flatMap (fun root => root.post.logs))) := by
  apply trace.receipt_of_settledRoots_after_suffix suffix hsg
  intro item member
  exact RlpConcrete.receipt_key_ne_of_small positive small (by have := later item member; omega)

/-- Request processing changes request bytes and access accounting only;
the actual receipt trie and block logs are preserved, including with enabled requests. -/
theorem RequestsTrace.receiptsTrie_and_blockLogs_eq
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    bout'.receiptsTrie = bout.receiptsTrie ∧ bout'.blockLogs = bout.blockLogs := by
  have run := trace.run
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt at run
  obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
  dsimp only at run
  obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
  cases run
  exact ⟨rfl, rfl⟩

/-- Request processing preserves the actual receipt trie. -/
theorem RequestsTrace.receiptsTrie_eq
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') :
    bout'.receiptsTrie = bout.receiptsTrie :=
  trace.receiptsTrie_and_blockLogs_eq.1

/-- Both the enabled and disabled request stages preserve the actual trie. -/
theorem RequestStageTrace.receiptsTrie_eq
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    bout'.receiptsTrie = bout.receiptsTrie := by
  cases trace with
  | skipped => rfl
  | called _ requests _ => exact requests.receiptsTrie_eq

/-- The actual withdrawal, request and finalization fields transport the
transaction-final receipt trie to the full body's final block output. -/
theorem StagedBodyTrace.receiptsTrie_eq_transactionBout
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    bout.receiptsTrie = trace.transactionBout.receiptsTrie := by
  have withdrawal : trace.withdrawalBout.receiptsTrie =
      trace.transactionBout.receiptsTrie := by
    have run := congrArg (fun p : State × BlockOutput => p.2.receiptsTrie)
      trace.withdrawalsRun
    unfold withdrawalsPass at run
    split at run <;> exact run.symm
  have final := congrArg BlockOutput.receiptsTrie trace.finalBout_eq
  exact final.symm.trans (trace.requests.receiptsTrie_eq.trans withdrawal)

end Blanc.ExecutionTrace
