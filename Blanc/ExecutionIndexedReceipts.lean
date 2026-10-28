import Blanc.ExecutionHistoryCommittedCuts
import Blanc.RlpBytesInjective

/-! Original indexed receipts and complete transaction-root log coverage. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- The original receipt survives any actual suffix whose indices differ.
Encoded-key separation is proved for every natural index, not supplied. -/
theorem TransactionTrace.receipt_of_settledRoots_after_distinct_indices
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {txs : List (Nat × Tx)} {finalBenv : Benv} {finalBout : BlockOutput}
    (suffix : ApplyTransactionsTrace txs (benv.withState state) bout' finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (different : ∀ item ∈ txs, item.1 ≠ index) :
    finalBout.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        (trace.settledRoots.flatMap (fun R => R.post.logs))) := by
  exact trace.receipt_of_settledRoots_after_suffix suffix hsg
    (fun item member => RlpConcrete.receipt_key_ne (different item member))

/-- The actual indexed cut's receipt persists at every position, including
zero. Its status and cumulative gas are those of this original transaction. -/
theorem ApplyTransactionsTrace.TxSplit.receipt_of_settledRoots
    {xs : List Tx} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace xs.putIndex benv bout finalBenv finalBout} {i : Nat}
    (cut : trace.TxSplit i) (hsg : benv.stat.rules.stateGas = none) :
    finalBout.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some (makeReceipt cut.tx cut.head.messageOut.error cut.txBout.cumulativeGasUsed
        (cut.head.settledRoots.flatMap (fun R => R.post.logs))) := by
  have headSg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    exact hsg
  apply cut.head.receipt_of_settledRoots_after_distinct_indices cut.after headSg
  intro item member
  have later := cut.later_indices item member
  omega

/-- Every actual indexed transaction receipt reaches the final staged output.
No bound on the selected index or any suffix index is needed. -/
theorem StagedBodyTrace.receipt_of_txSplit
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (body : StagedBodyTrace benv txs ommers wds state bout) {i : Nat}
    (cut : body.transactions.TxSplit i) (hsg : benv.stat.rules.stateGas = none) :
    bout.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some (makeReceipt cut.tx cut.head.messageOut.error cut.txBout.cumulativeGasUsed
        (cut.head.settledRoots.flatMap (fun R => R.post.logs))) := by
  rw [body.receiptsTrie_eq_transactionBout]
  exact cut.receipt_of_settledRoots hsg

/-- The original selected receipt at the actual configured block's output.
This is semantic receipt transport, not independent commitment authentication. -/
theorem ConfiguredBlockTraceIn.receipt_of_txSplit
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (hsg : block.fork.ruleSet.stateGas = none) :
    block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some (makeReceipt cut.tx cut.head.messageOut.error cut.txBout.cumulativeGasUsed
        (cut.head.settledRoots.flatMap (fun R => R.post.logs))) := by
  exact block.bodyTrace.receipt_of_txSplit cut hsg

/-- Success of this original indexed receipt identifies a clean message
result for the very same transaction. A processed transaction alone does not
establish this: its receipt may still record a reverted or halted execution. -/
theorem ConfiguredBlockTraceIn.txSplit_error_eq_none_of_receipt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (hsg : block.fork.ruleSet.stateGas = none) {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    cut.head.messageOut.error = none := by
  have same := Option.some.inj (lookup.symm.trans (block.receipt_of_txSplit cut hsg))
  have status := congrArg (fun value : Fin 5 × Receipt => value.2.succeeded) same
  change receipt.2.succeeded = cut.head.messageOut.error.isNone at status
  rw [succeeded] at status
  cases error : cut.head.messageOut.error with
  | none => rfl
  | some failure => rw [error] at status; cases status

/-- An independently identified receipt in this actual output carries exactly
this original transaction's outer retained-root logs, each folded once. -/
theorem ConfiguredBlockTraceIn.txSplit_logs_eq_of_receipt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (hsg : block.fork.ruleSet.stateGas = none) {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) :
    receipt.2.logs = cut.head.settledRoots.flatMap (fun R => R.post.logs) := by
  have same := Option.some.inj (lookup.symm.trans (block.receipt_of_txSplit cut hsg))
  exact congrArg (fun value : Fin 5 × Receipt => value.2.logs) same

/-- A log predicate on this actual receipt holds on every log of each
complete-settlement root of the original selected transaction. Reverted logs
and roots outside that transaction are not added to the population. -/
theorem ConfiguredBlockTraceIn.txSplit_root_logs_of_receipt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (hsg : block.fork.ruleSet.stateGas = none) {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (property : Log → Prop)
    (logs : ∀ entry ∈ receipt.2.logs, property entry) :
    ∀ R ∈ cut.head.settledRoots, ∀ entry ∈ R.post.logs, property entry := by
  intro R root entry member
  apply logs entry
  rw [block.txSplit_logs_eq_of_receipt cut hsg lookup]
  exact List.mem_flatMap.mpr ⟨R, root, member⟩

/-- Every outer retained root belongs to an actual indexed transaction cut.
This follows the original trace spine, including transactions with no roots. -/
theorem ApplyTransactionsTrace.exists_splitAt_of_mem_settledRoots
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) {R : Exec.Frame}
    (member : R ∈ trace.settledRoots) :
    ∃ (i : Nat) (lt : i < txs.length), R ∈ (trace.splitAt i lt).head.settledRoots := by
  induction trace with
  | nil => simp only [ApplyTransactionsTrace.settledRoots, List.not_mem_nil] at member
  | cons head tail ih =>
    change R ∈ head.settledRoots ++ tail.settledRoots at member
    rcases List.mem_append.mp member with first | rest
    · exact ⟨0, by simp only [List.length_cons]; omega, first⟩
    · obtain ⟨i, lt, found⟩ := ih rest
      exact ⟨i + 1, by simp only [List.length_cons]; omega, found⟩

/-- A predicate on every in-range actual receipt covers all retained roots of
this block when its system stages are disabled. Completeness includes index zero
and arbitrarily large positions; no per-root log premise is assumed. -/
theorem ConfiguredBlockTraceIn.root_logs_of_receipts
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : block.fork.ruleSet.stateGas = none)
    (disabled : block.bodyTrace.SystemStagesDisabled) (property : Log → Prop)
    (receipts : ∀ (i : Nat), i < block.bodyTrace.decodedTxs.putIndex.length →
      ∀ (receipt : Fin 5 × Receipt),
        block.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt →
        ∀ entry ∈ receipt.2.logs, property entry) :
    ∀ R ∈ block.settledRoots, ∀ entry ∈ R.post.logs, property entry := by
  intro R root entry member
  change R ∈ block.bodyTrace.settledRoots at root
  rw [block.bodyTrace.settledRoots_eq_transactions_of_disabled disabled] at root
  obtain ⟨i, lt, found⟩ := block.bodyTrace.transactions.exists_splitAt_of_mem_settledRoots root
  let cut := block.bodyTrace.transactions.splitAt i lt
  have lookup := block.receipt_of_txSplit cut hsg
  have keyEq := congrArg (fun index : Nat =>
    block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]?) cut.putIndex_eq.1
  have indexed := keyEq.symm.trans lookup
  exact block.txSplit_root_logs_of_receipt cut hsg lookup property
    (receipts i lt _ indexed) R found entry member

end Blanc.ExecutionTrace
