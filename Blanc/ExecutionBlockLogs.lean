import Blanc.ExecutionHistoryReceiptLogs

/-! Original transaction logs in the final block output, including exact receipt intervals. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- Transaction settlement appends exactly the retained root posts, folded once. -/
theorem TransactionTrace.blockLogs_eq
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    bout'.blockLogs = bout.blockLogs ++ trace.settledRoots.flatMap (fun R => R.post.logs) := by
  have msgHsg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    exact hsg
  rw [TransactionTrace.settledRoots, ← trace.message.logs_eq_settledRoots msgHsg]
  exact (trace.receipt_and_blockLogs_of_selected_settlement hsg).2

/-- The original transaction spine appends its retained logs in execution order. -/
theorem ApplyTransactionsTrace.blockLogs_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) :
    finalBout.blockLogs = bout.blockLogs ++ trace.settledRoots.flatMap (fun R => R.post.logs) := by
  induction trace with
  | nil => simp only [ApplyTransactionsTrace.settledRoots, List.flatMap_nil, List.append_nil]
  | cons head tail ih =>
      rw [ih hsg, head.blockLogs_eq hsg]
      simp only [ApplyTransactionsTrace.settledRoots, List.flatMap_append, List.append_assoc]

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

/-- The actual final body logs contain exactly its transaction settlement logs.
System-call roots are not added to this population. -/
theorem StagedBodyTrace.blockLogs_eq_transactionRoots
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none) :
    bout.blockLogs = trace.transactions.settledRoots.flatMap (fun R => R.post.logs) := by
  rw [trace.blockLogs_eq_transactionBout, trace.transactions.blockLogs_eq hsg]
  rfl

/-- Every log of the actual selected transaction reaches the original final block. -/
theorem ConfiguredBlockTraceIn.mem_blockLogs_of_txSplit
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (hsg : block.fork.ruleSet.stateGas = none) {entry : Log}
    (member : entry ∈ cut.head.settledRoots.flatMap (fun R => R.post.logs)) :
    entry ∈ block.blockOutput.blockLogs := by
  rw [block.bodyTrace.blockLogs_eq_transactionBout]
  have headSg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    exact hsg
  rw [cut.after.blockLogs_eq headSg, cut.head.blockLogs_eq headSg]
  exact List.mem_append_left _ (List.mem_append_right _ member)

/-- An actual indexed receipt contributes only logs present in the original block output. -/
theorem ConfiguredBlockTraceIn.mem_blockLogs_of_receipt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : block.fork.ruleSet.stateGas = none) {index : Nat}
    (bound : index < block.bodyTrace.decodedTxs.length) {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt)
    {entry : Log} (member : entry ∈ receipt.2.logs) :
    entry ∈ block.blockOutput.blockLogs := by
  have indexed : index < block.bodyTrace.decodedTxs.putIndex.length := by
    rwa [indexedTransactions_length]
  let cut := block.bodyTrace.transactions.splitAt index indexed
  have cutLookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt := by
    rw [cut.putIndex_eq.1]
    exact lookup
  rw [block.txSplit_logs_eq_of_receipt cut hsg cutLookup] at member
  exact block.mem_blockLogs_of_txSplit cut hsg member

/-- Any exact receipt interval is contained in the original final block logs.
This connects prefix/suffix continuity predicates to the block's bloom commitment. -/
theorem ConfiguredBlockTraceIn.mem_blockLogs_of_mem_receiptLogsBetween
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : block.fork.ruleSet.stateGas = none) {lo hi : Nat} {entry : Log}
    (member : entry ∈ block.receiptLogsBetween lo hi) :
    entry ∈ block.blockOutput.blockLogs := by
  obtain ⟨index, bound, member⟩ := List.mem_flatMap.mp member
  have actual := List.mem_range.mp bound
  by_cases range : lo ≤ index ∧ index < hi
  · rw [ite_eq_left range] at member
    cases lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? with
    | none => simp only [lookup, Option.toList_none, List.flatMap_nil, List.not_mem_nil] at member
    | some receipt =>
        simp only [lookup, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
          List.append_nil] at member
        exact block.mem_blockLogs_of_receipt hsg actual lookup member
  · simp only [ite_eq_right range, List.not_mem_nil] at member

end Blanc.ExecutionTrace
