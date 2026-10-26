import Blanc.ExecutionIndexedReceipts
import Blanc.ExecutionTraceDeterminism

/-! Exact original transaction prefix and suffix receipt-log transport. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- The actual natural indices assigned by putIndex increase strictly. -/
theorem putIndex_aux_pairwise {α : Type} (xs : List α) (offset : Nat) :
    (Jaune.List.putIndex.aux offset xs).Pairwise (fun a b => a.1 < b.1) := by
  induction xs generalizing offset with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    change ((offset, x) :: Jaune.List.putIndex.aux (offset + 1) xs).Pairwise _
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih (offset + 1)⟩
    intro item member
    have lower := putIndex_aux_mem_drop_index_ge xs (offset + 1) 0 item member
    omega

/-- Every actual indexed item is below the exclusive end of its source list. -/
theorem putIndex_aux_mem_index_lt {α : Type} (xs : List α) (offset : Nat) :
    ∀ item ∈ Jaune.List.putIndex.aux offset xs, item.1 < offset + xs.length := by
  induction xs generalizing offset with
  | nil => intro item member; cases member
  | cons x xs ih =>
    intro item member
    change item ∈ (offset, x) :: Jaune.List.putIndex.aux (offset + 1) xs at member
    rcases List.mem_cons.mp member with rfl | rest
    · simp only [List.length_cons]; omega
    · have bound := ih (offset + 1) item rest
      simp only [List.length_cons]
      omega

/-- A consumed transaction segment is covered by its actual final receipts,
including their preservation through a later suffix. Only the consumed
segment's receipts must satisfy the predicate. -/
theorem ApplyTransactionsTrace.root_logs_of_receipts_after_suffix
    {xs ys : List (Nat × Tx)} {benv middle finalBenv : Benv}
    {bout middleBout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace xs benv bout middle middleBout)
    (suffix : ApplyTransactionsTrace ys middle middleBout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (ordered : (xs ++ ys).Pairwise (fun a b => a.1 < b.1))
    (property : Log → Prop)
    (receipts : ∀ item ∈ xs, ∀ receipt : Fin 5 × Receipt,
      finalBout.receiptsTrie[BLT.toBytes (.bytes item.1.toBytes)]? = some receipt →
      ∀ entry ∈ receipt.2.logs, property entry) :
    ∀ R ∈ trace.settledRoots, ∀ entry ∈ R.post.logs, property entry := by
  induction trace with
  | nil => intro R member; cases member
  | @cons index tx txs benv bout txState txBout middle middleBout head tail ih =>
    have order := List.pairwise_cons.mp ordered
    intro R root entry member
    change R ∈ head.settledRoots ++ tail.settledRoots at root
    rcases List.mem_append.mp root with first | rest
    · have lookup := head.receipt_of_settledRoots_after_distinct_indices
        (tail.append suffix) hsg (fun item member => by have := order.1 item member; omega)
      exact receipts (index, tx) (List.mem_cons_self ..) _ lookup entry
        (List.mem_flatMap.mpr ⟨R, first, member⟩)
    · exact ih suffix hsg order.2
        (fun item present => receipts item (List.mem_cons_of_mem _ present)) R rest entry member

/-- Only receipts strictly after the original cut are consumed. Later body
stages preserve the final trie; the selected transaction is outside this range. -/
theorem ConfiguredBlockTraceIn.after_txSplit_root_logs_of_receipts
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (hsg : block.fork.ruleSet.stateGas = none) (property : Log → Prop)
    (receipts : ∀ index, i < index → index < block.bodyTrace.decodedTxs.length →
      ∀ receipt : Fin 5 × Receipt,
        block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt →
        ∀ entry ∈ receipt.2.logs, property entry) :
    ∀ R ∈ cut.after.settledRoots, ∀ entry ∈ R.post.logs, property entry := by
  have order := (putIndex_aux_pairwise block.bodyTrace.decodedTxs 0).drop (i := i + 1)
  have afterSg : cut.afterBenv.stat.rules.stateGas = none := by
    rw [block.txSplit_stat cut]
    exact hsg
  apply cut.after.root_logs_of_receipts_after_suffix (.nil _ _) afterSg
    (by simpa only [List.append_nil, Jaune.List.putIndex] using order) property
  intro item member receipt lookup entry logged
  have later := cut.later_indices item member
  rw [cut.putIndex_eq.1] at later
  have upper := putIndex_aux_mem_index_lt block.bodyTrace.decodedTxs 0 item
    (List.mem_of_mem_drop member)
  have finalLookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes item.1.toBytes)]? =
      some receipt := by
    rw [block.bodyTrace.receiptsTrie_eq_transactionBout]
    exact lookup
  exact receipts item.1 later (by omega) receipt finalLookup entry logged

/-- Only receipts strictly before the original cut are consumed. The selected
transaction and actual suffix preserve those receipts but need no log predicate. -/
theorem ConfiguredBlockTraceIn.before_txSplit_root_logs_of_receipts
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (hsg : block.fork.ruleSet.stateGas = none) (property : Log → Prop)
    (receipts : ∀ index, index < i →
      ∀ receipt : Fin 5 × Receipt,
        block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? = some receipt →
        ∀ entry ∈ receipt.2.logs, property entry) :
    ∀ R ∈ cut.before.settledRoots, ∀ entry ∈ R.post.logs, property entry := by
  have order := putIndex_aux_pairwise block.bodyTrace.decodedTxs 0
  have joined : block.bodyTrace.decodedTxs.putIndex.take i ++
      ((cut.index, cut.tx) :: block.bodyTrace.decodedTxs.putIndex.drop (i + 1)) =
      block.bodyTrace.decodedTxs.putIndex := by
    rw [← cut.at_eq]
    exact List.take_append_drop i _
  apply cut.before.root_logs_of_receipts_after_suffix (.cons cut.head cut.after) hsg
    (by rw [joined]; exact order) property
  intro item member receipt lookup entry logged
  have selected : (cut.index, cut.tx) ∈ block.bodyTrace.decodedTxs.putIndex.drop i := by
    rw [cut.at_eq]
    exact List.mem_cons_self ..
  have before := order.rel_of_mem_take_of_mem_drop member selected
  change item.1 < cut.index at before
  rw [cut.putIndex_eq.1] at before
  have finalLookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes item.1.toBytes)]? =
      some receipt := by
    rw [block.bodyTrace.receiptsTrie_eq_transactionBout]
    exact lookup
  exact receipts item.1 before receipt finalLookup entry logged

end Blanc.ExecutionTrace
