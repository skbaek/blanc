import Blanc.ExecutionHistoryCommittedCell
import Blanc.ExecutionMidHistoryIn

/-!
# Indexed complete-settlement root and cell cuts

Cuts use the actual transaction-list position. The canonical `splitAt` proof
supplies the root equation; equality of flattened frames is not used to infer
it. Before means before the selected transaction; after means its settled
post-state, the `afterBenv` endpoint of the existing cut.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The canonical positional cut splits complete-settlement roots exactly. -/
theorem ApplyTransactionsTrace.splitAt_settledRoots_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (i : Nat)
    (lt : i < txs.length) :
    trace.settledRoots = (trace.splitAt i lt).before.settledRoots ++
      (trace.splitAt i lt).head.settledRoots ++ (trace.splitAt i lt).after.settledRoots := by
  induction trace generalizing i with
  | nil => exact absurd lt (Nat.not_lt_zero i)
  | cons head tail ih =>
      cases i with
      | zero => rfl
      | succ i =>
          let cut := tail.splitAt i (Nat.lt_of_succ_lt_succ lt)
          change head.settledRoots ++ tail.settledRoots =
            (head.settledRoots ++ cut.before.settledRoots) ++
              cut.head.settledRoots ++ cut.after.settledRoots
          rw [ih i (Nat.lt_of_succ_lt_succ lt)]
          simp only [List.append_assoc]
          rfl

/-- The same canonical cut splits every actual transaction deletion exclusion. -/
theorem ApplyTransactionsTrace.splitAt_outputNotDeleted_iff
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (i : Nat)
    (lt : i < txs.length) (wa : Adr) :
    trace.OutputNotDeleted wa ↔
      (trace.splitAt i lt).before.OutputNotDeleted wa ∧
      wa ∉ (trace.splitAt i lt).head.messageOut.accountsToDelete ∧
      (trace.splitAt i lt).after.OutputNotDeleted wa := by
  induction trace generalizing i with
  | nil => exact absurd lt (Nat.not_lt_zero i)
  | cons head tail ih =>
      cases i with
      | zero =>
          change (wa ∉ head.messageOut.accountsToDelete ∧ tail.OutputNotDeleted wa) ↔
            True ∧ wa ∉ head.messageOut.accountsToDelete ∧ tail.OutputNotDeleted wa
          simp only [true_and]
      | succ i =>
          let cut := tail.splitAt i (Nat.lt_of_succ_lt_succ lt)
          change (wa ∉ head.messageOut.accountsToDelete ∧ tail.OutputNotDeleted wa) ↔
            (wa ∉ head.messageOut.accountsToDelete ∧ cut.before.OutputNotDeleted wa) ∧
              wa ∉ cut.head.messageOut.accountsToDelete ∧ cut.after.OutputNotDeleted wa
          rw [ih i (Nat.lt_of_succ_lt_succ lt)]
          simp only [and_assoc]
          rfl

/-- Flattening root posts once respects the exact canonical positional cut. -/
theorem ApplyTransactionsTrace.splitAt_rootLogs_eq
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (i : Nat)
    (lt : i < txs.length) :
    trace.settledRoots.flatMap (fun R => R.post.logs) =
      (trace.splitAt i lt).before.settledRoots.flatMap (fun R => R.post.logs) ++
      (trace.splitAt i lt).head.settledRoots.flatMap (fun R => R.post.logs) ++
      (trace.splitAt i lt).after.settledRoots.flatMap (fun R => R.post.logs) := by
  rw [trace.splitAt_settledRoots_eq i lt]
  simp only [List.flatMap_append]

/-- The selected transaction's before and settled-after cell endpoints are
identified by the canonical list position, even when its root list is empty. -/
theorem ApplyTransactionsTrace.splitAt_cell_boundaries
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (i : Nat)
    (lt : i < txs.length) (k : B256)
    (hsg : benv.stat.rules.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : trace.OutputNotDeleted wa)
    (roots : ∀ R ∈ trace.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    let cut := trace.splitAt i lt
    (cut.benv.state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      (cut.afterBenv.state.getStor wa).get k = (benv.state.getStor wa).get k ∧
      cut.benv.state.getCode wa = C ∧ cut.afterBenv.state.getCode wa = C := by
  let cut := trace.splitAt i lt
  have deleted := (trace.splitAt_outputNotDeleted_iff i lt wa).1 notDeleted
  have splitRoots : trace.settledRoots = cut.before.settledRoots ++
      cut.head.settledRoots ++ cut.after.settledRoots := trace.splitAt_settledRoots_eq i lt
  have beforeRoots : ∀ R ∈ cut.before.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k := by
    intro R member
    apply roots R
    rw [splitRoots]
    exact List.mem_append_left _ (List.mem_append_left _ member)
  have headRoots : ∀ R ∈ cut.head.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k := by
    intro R member
    apply roots R
    rw [splitRoots]
    exact List.mem_append_left _ (List.mem_append_right _ member)
  obtain ⟨beforeCell, beforeCode⟩ := cut.before.cell_eq_of_settledRoots k hsg hC hCne hCdel
    deleted.1 beforeRoots
  have headSg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    exact hsg
  obtain ⟨headCell, headCode⟩ := cut.head.cell_eq_of_settledRoots k headSg beforeCode
    hCne hCdel deleted.2.1 headRoots
  exact ⟨beforeCell, headCell.trans beforeCell, beforeCode, headCode⟩

/-- Complete-settlement roots in the exact post-transaction remainder. -/
def MidHistoryTraceIn.settledRoots {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} →
    MidHistoryTraceIn F cfg start future → List Exec.Frame
  | _, _, .tail block cut => cut.after.settledRoots ++ block.bodyTrace.requests.settledRoots
  | _, _, .step prior block => prior.settledRoots ++ block.settledRoots

/-- The same complete-settlement roots recompose when whole blocks are appended. -/
theorem MidHistoryTraceIn.append_settledRoots
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (history : ConfiguredHistoryTraceIn F cfg current future) :
    (mid.append history).settledRoots = mid.settledRoots ++ history.settledRoots := by
  induction history with
  | refl => simp only [MidHistoryTraceIn.append, ConfiguredHistoryTraceIn.settledRoots,
      List.append_nil]
  | step prior block ih =>
      simp only [MidHistoryTraceIn.append, MidHistoryTraceIn.settledRoots,
        ConfiguredHistoryTraceIn.settledRoots, ih, List.append_assoc]

/-- Exact root-log recomposition across a mid-history/whole-history join. -/
theorem MidHistoryTraceIn.append_rootLogs
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (history : ConfiguredHistoryTraceIn F cfg current future) :
    (mid.append history).settledRoots.flatMap (fun R => R.post.logs) =
      mid.settledRoots.flatMap (fun R => R.post.logs) ++
        history.settledRoots.flatMap (fun R => R.post.logs) := by
  rw [mid.append_settledRoots history, List.flatMap_append]

/-- A configured block's canonical indexed cut keeps the exact system prefix,
selected transaction and post-transaction remainder in order. -/
theorem ConfiguredBlockTraceIn.settledRoots_splitAt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (i : Nat)
    (lt : i < block.bodyTrace.decodedTxs.putIndex.length) :
    let cut := block.bodyTrace.transactions.splitAt i lt
    block.settledRoots = block.bodyTrace.beacon.settledRoots ++
      block.bodyTrace.history.settledRoots ++ cut.before.settledRoots ++
      cut.head.settledRoots ++ (MidHistoryTraceIn.tail block cut).settledRoots := by
  dsimp only
  rw [ConfiguredBlockTraceIn.settledRoots, StagedBodyTrace.settledRoots,
    block.bodyTrace.transactions.splitAt_settledRoots_eq i lt]
  simp only [MidHistoryTraceIn.settledRoots, List.append_assoc]

/-- Actual deletion exclusions for the suffix transactions and later blocks. -/
def MidHistoryTraceIn.OutputNotDeleted (wa : Adr) {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} →
    MidHistoryTraceIn F cfg start future → Prop
  | _, _, .tail _ cut => cut.after.OutputNotDeleted wa
  | _, _, .step prior block =>
      prior.OutputNotDeleted wa ∧ block.bodyTrace.transactions.OutputNotDeleted wa

/-- A history starting at the selected transaction's settled-after endpoint
transports its cell through the actual suffix, finalization and later blocks. -/
theorem MidHistoryTraceIn.cell_eq_of_settledRoots
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (history : MidHistoryTraceIn F cfg start future) (k : B256)
    (stateGas : ∀ fork, F fork → fork.ruleSet.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : history.OutputNotDeleted wa)
    (roots : ∀ R ∈ history.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (future.state.getStor wa).get k = (start.state.getStor wa).get k ∧
      future.state.getCode wa = C := by
  induction history with
  | tail block cut =>
      have suffixSg : cut.afterBenv.stat.rules.stateGas = none := by
        rw [block.txSplit_stat cut]
        exact stateGas block.fork block.forkIn
      obtain ⟨suffixCell, suffixCode⟩ := cut.after.cell_eq_of_settledRoots k suffixSg hC
        hCne hCdel notDeleted (fun R member => roots R (List.mem_append_left _ member))
      obtain ⟨tailCell, tailCode⟩ := block.bodyTrace.cell_eq_after_transactions_of_settledRoots
        k (stateGas block.fork block.forkIn) suffixCode hCne hCdel
        (fun R member => roots R (List.mem_append_right _ member))
      have postState := congrArg BlockChain.state block.postEq
      rw [postState]
      exact ⟨tailCell.trans suffixCell, tailCode⟩
  | step prior block ih =>
      simp only [MidHistoryTraceIn.OutputNotDeleted] at notDeleted
      obtain ⟨priorCell, priorCode⟩ := ih hC notDeleted.1
        (fun R member => roots R (List.mem_append_left _ member))
      obtain ⟨blockCell, blockCode⟩ := block.cell_eq_of_settledRoots k
        (stateGas block.fork block.forkIn) priorCode hCne hCdel notDeleted.2
        (fun R member => roots R (List.mem_append_right _ member))
      exact ⟨blockCell.trans priorCell, blockCode⟩

/-- Roots before the selected transaction: the actual system prefix followed
by the retained transaction prefix. This excludes the selected transaction. -/
def ConfiguredBlockTraceIn.rootsBeforeTxSplit
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) : List Exec.Frame :=
  block.bodyTrace.beacon.settledRoots ++ block.bodyTrace.history.settledRoots ++
    cut.before.settledRoots

/-- A canonical indexed block cut decomposes into before, selected transaction
and settled-after remainder, with no identification by empty raw lists. -/
theorem ConfiguredBlockTraceIn.settledRoots_before_head_after
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (i : Nat)
    (lt : i < block.bodyTrace.decodedTxs.putIndex.length) :
    let cut := block.bodyTrace.transactions.splitAt i lt
    block.settledRoots = block.rootsBeforeTxSplit cut ++ cut.head.settledRoots ++
      (MidHistoryTraceIn.tail block cut).settledRoots := by
  dsimp only [ConfiguredBlockTraceIn.rootsBeforeTxSplit]
  rw [block.settledRoots_splitAt i lt]

/-- The cell at the exact before-transaction boundary follows from laws on
that prefix alone. No root after the boundary, including the head, is assumed. -/
theorem ConfiguredBlockTraceIn.cell_eq_before_txSplit
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (k : B256)
    (hsg : block.fork.ruleSet.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : pre.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : cut.before.OutputNotDeleted wa)
    (roots : ∀ R ∈ block.rootsBeforeTxSplit cut,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (cut.benv.state.getStor wa).get k = (pre.state.getStor wa).get k ∧
      cut.benv.state.getCode wa = C := by
  have beaconRoots : ∀ R ∈ block.bodyTrace.beacon.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k :=
    fun R member => roots R (List.mem_append_left _ (List.mem_append_left _ member))
  have historyRoots : ∀ R ∈ block.bodyTrace.history.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k :=
    fun R member => roots R (List.mem_append_left _ (List.mem_append_right _ member))
  have beforeRoots : ∀ R ∈ cut.before.settledRoots,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k :=
    fun R member => roots R (List.mem_append_right _ member)
  obtain ⟨beaconCell, beaconCode⟩ := block.bodyTrace.beacon.cell_eq_of_settledRoots k hsg
    hC hCne hCdel beaconRoots
  obtain ⟨historyCell, historyCode⟩ := block.bodyTrace.history.cell_eq_of_settledRoots k hsg
    beaconCode hCne hCdel historyRoots
  obtain ⟨beforeCell, beforeCode⟩ := cut.before.cell_eq_of_settledRoots k hsg
    historyCode hCne hCdel notDeleted beforeRoots
  exact ⟨beforeCell.trans (historyCell.trans beaconCell), beforeCode⟩

/-- From a settled-after origin to a later exact before-transaction boundary,
only roots in the intervening mid history and final block prefix are needed. -/
theorem MidHistoryTraceIn.cell_eq_before_txSplit
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {pre post : BlockChain}
    (mid : MidHistoryTraceIn F cfg start pre)
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (k : B256)
    (stateGas : ∀ fork, F fork → fork.ruleSet.stateGas = none)
    {wa : Adr} {C : ByteArray} (hC : start.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C)
    (notDeleted : mid.OutputNotDeleted wa ∧ cut.before.OutputNotDeleted wa)
    (roots : ∀ R ∈ mid.settledRoots ++ block.rootsBeforeTxSplit cut,
      (R.post.getStor wa).get k = (R.pre.getStor wa).get k) :
    (cut.benv.state.getStor wa).get k = (start.state.getStor wa).get k ∧
      cut.benv.state.getCode wa = C := by
  obtain ⟨midCell, midCode⟩ := mid.cell_eq_of_settledRoots k stateGas hC hCne hCdel
    notDeleted.1 (fun R member => roots R (List.mem_append_left _ member))
  obtain ⟨beforeCell, beforeCode⟩ := block.cell_eq_before_txSplit cut k
    (stateGas block.fork block.forkIn) midCode hCne hCdel notDeleted.2
    (fun R member => roots R (List.mem_append_right _ member))
  exact ⟨beforeCell.trans midCell, beforeCode⟩

/-- The new mid-history roots agree with the existing retained-frame carrier.
The direction is derived structurally, not inverted from flattened frames. -/
theorem MidHistoryTraceIn.settledFrames_eq
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (history : MidHistoryTraceIn F cfg start future) :
    history.settledFrames = rootFrames history.settledRoots := by
  induction history with
  | tail block cut =>
      simp only [MidHistoryTraceIn.settledFrames, MidHistoryTraceIn.settledRoots,
        cut.after.settledFrames_eq, block.bodyTrace.requests.settledFrames_eq,
        rootFrames, List.flatMap_append]
  | step prior block ih =>
      simp only [MidHistoryTraceIn.settledFrames, MidHistoryTraceIn.settledRoots,
        ih, block.settledFrames_eq, rootFrames, List.flatMap_append]

end Blanc.ExecutionTrace
