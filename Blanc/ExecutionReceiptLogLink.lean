import Blanc.ExecutionParentLogAttribution
import Blanc.ExecutionIndexedReceipts
import Blanc.ExecutionMidHistoryIn

/-!
# A settled frame's log reaches its block's receipts

A reader sees receipts; a frame law speaks of a settled frame's `post.logs`. This is the link: every log in the endpoint
of a settled frame of a block's transaction stage is in a successful receipt of that block. So a log filter that finds
nothing over the block's receipts rules the log out of every such frame. System stages have no receipts, so their
frames are not covered.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Each settled frame of a transaction stage belongs to one actual indexed transaction. -/
theorem ApplyTransactionsTrace.exists_splitAt_of_mem_settledFrames
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) {frame : Exec.Frame}
    (member : frame ∈ trace.settledFrames) :
    ∃ (i : Nat) (lt : i < txs.length), frame ∈ (trace.splitAt i lt).head.settledFrames := by
  induction trace with
  | nil => simp only [ApplyTransactionsTrace.settledFrames, List.not_mem_nil] at member
  | cons head tail ih =>
    change frame ∈ head.settledFrames ++ tail.settledFrames at member
    rcases List.mem_append.mp member with first | rest
    · exact ⟨0, by simp only [List.length_cons]; omega, first⟩
    · obtain ⟨i, lt, found⟩ := ih rest
      exact ⟨i + 1, by simp only [List.length_cons]; omega, found⟩

/-- **A log of a settled frame of a block's transaction stage is in a successful receipt of that block.** -/
theorem ConfiguredBlockTraceIn.log_mem_receipt_of_settledFrame
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (hsg : block.fork.ruleSet.stateGas = none)
    {frame : Exec.Frame} (member : frame ∈ block.bodyTrace.transactions.settledFrames)
    {entry : Log} (event : entry ∈ frame.post.logs) :
    ∃ (i : Nat) (receipt : Fin 5 × Receipt),
      i < block.bodyTrace.decodedTxs.putIndex.length ∧
      block.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt ∧
      receipt.2.succeeded = true ∧ entry ∈ receipt.2.logs := by
  obtain ⟨i, lt, found⟩ := block.bodyTrace.transactions.exists_splitAt_of_mem_settledFrames member
  let cut := block.bodyTrace.transactions.splitAt i lt
  have lookup := block.receipt_of_txSplit cut hsg
  have keyEq := congrArg (fun index : Nat =>
    block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]?) cut.putIndex_eq.1
  have indexed := keyEq.symm.trans lookup
  have headSg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    exact hsg
  obtain ⟨r₀, lookup₀, ok, mem⟩ := cut.head.log_mem_receipt_of_settledFrame headSg found event
  have same := cut.head.receipt_of_settledRoots headSg
  rw [lookup₀] at same
  cases Option.some.inj same
  exact ⟨i, _, lt, indexed, ok, mem⟩

/-- **No log in a block's receipts satisfying `property` means none in its transaction stage's settled frames.** -/
theorem ConfiguredBlockTraceIn.no_log_of_receipts
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (hsg : block.fork.ruleSet.stateGas = none)
    (property : Log → Prop)
    (receipts : ∀ (i : Nat), i < block.bodyTrace.decodedTxs.putIndex.length →
      ∀ (receipt : Fin 5 × Receipt),
        block.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt →
        receipt.2.succeeded = true → ∀ entry ∈ receipt.2.logs, ¬ property entry) :
    ∀ frame ∈ block.bodyTrace.transactions.settledFrames, ∀ entry ∈ frame.post.logs, ¬ property entry := by
  intro frame member entry event
  obtain ⟨i, r, lt, lookup, ok, mem⟩ := block.log_mem_receipt_of_settledFrame hsg member event
  exact receipts i lt r lookup ok entry mem

/-- The settled frames of a mid history's transaction stages: its remainder's suffix, then each later block's. -/
def MidHistoryTraceIn.txFrames {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → List Exec.Frame
  | _, _, .tail _ cut => cut.after.settledFrames
  | _, _, .step prior block => prior.txFrames ++ block.bodyTrace.transactions.settledFrames

/-- **What a reader's filter says of a block**: no successful receipt of the block holds a log with `property`. -/
def ConfiguredBlockTraceIn.NoLogInReceipts {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (property : Log → Prop) : Prop :=
  ∀ (i : Nat), i < block.bodyTrace.decodedTxs.putIndex.length → ∀ (receipt : Fin 5 × Receipt),
    block.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt →
    receipt.2.succeeded = true → ∀ entry ∈ receipt.2.logs, ¬ property entry

/-- **What a reader's filter says of a mid history**: `NoLogInReceipts` for every block it touches. -/
def MidHistoryTraceIn.NoLogInReceipts {F : Fork → Prop} {cfg : ChainConfig} (property : Log → Prop) :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → Prop
  | _, _, .tail block _ => block.NoLogInReceipts property
  | _, _, .step prior block => prior.NoLogInReceipts property ∧ block.NoLogInReceipts property

/-- **Zero matching logs in a mid history's receipts means none in the settled frames of its transaction stages.** -/
theorem MidHistoryTraceIn.no_log_of_receipts {F : Fork → Prop} {cfg : ChainConfig}
    (hsg : ∀ {fork}, F fork → fork.ruleSet.stateGas = none) (property : Log → Prop)
    {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (receipts : trace.NoLogInReceipts property) :
    ∀ frame ∈ trace.txFrames, ∀ entry ∈ frame.post.logs, ¬ property entry := by
  induction trace with
  | tail block cut =>
    intro frame member
    have whole : frame ∈ block.bodyTrace.transactions.settledFrames := by
      rw [cut.settledFrames_eq]
      exact List.mem_append_right _ member
    exact block.no_log_of_receipts (hsg block.forkIn) property receipts frame whole
  | step prior block ih =>
    intro frame member
    rcases List.mem_append.mp member with early | late
    · exact ih receipts.1 frame early
    · exact block.no_log_of_receipts (hsg block.forkIn) property receipts.2 frame late

end Blanc.ExecutionTrace
