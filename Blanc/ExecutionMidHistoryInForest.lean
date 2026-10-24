import Blanc.ExecutionMidHistoryInFacts
import Blanc.ExecutionInCodeImage
import Blanc.ExecutionSenderRootCallers
import Blanc.ExecutionHistoryInAppend

/-!
# Original retained roots and sender queries after a transaction cut

The mid history starts at the cut's actual afterBenv. Its roots and admitted sender occurrences
are the original transaction suffix and later blocks, with no new block-chain checkpoint.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The actual retained message roots after the cut, then in each later block. -/
def MidHistoryTraceIn.settledRoots {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} →
      MidHistoryTraceIn F cfg start future → List Exec.Frame
  | _, _, .tail block cut => cut.after.settledRoots ++ block.bodyTrace.requests.settledRoots
  | _, _, .step prior block => prior.settledRoots ++ block.settledRoots

/-- The original root expansion is the exact mid-history retained frame list. -/
theorem MidHistoryTraceIn.settledFrames_eq {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} (mid : MidHistoryTraceIn F cfg start future) :
    mid.settledFrames = rootFrames mid.settledRoots := by
  induction mid with
  | tail block cut =>
    simp only [MidHistoryTraceIn.settledFrames, MidHistoryTraceIn.settledRoots,
      rootFrames, List.flatMap_append]
    rw [cut.after.settledFrames_eq, block.bodyTrace.requests.settledFrames_eq]
  | step prior block ih =>
    simp only [MidHistoryTraceIn.settledFrames, MidHistoryTraceIn.settledRoots,
      rootFrames, List.flatMap_append]
    rw [ih, block.settledFrames_eq]

/-- A mid-history retained frame is an actual root or a child of an earlier retained frame. -/
theorem MidHistoryTraceIn.settledFrames_parentIn {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} (mid : MidHistoryTraceIn F cfg start future)
    {before after : List Exec.Frame} {G : Exec.Frame}
    (split : mid.settledFrames = before ++ G :: after) :
    G ∈ mid.settledRoots ∨ ∃ b₁ A b₂, before = b₁ ++ A :: b₂ ∧
      G ∈ Exec.childFrames A.run ∧ Exec.SpawnedBy A.sevm G ∧
      b₂.length < (Exec.descendantFrames A.run).length := by
  rw [mid.settledFrames_eq] at split
  exact (rootFrames_forest split).2

/-- Every actual admitted suffix transaction retains its original sender occurrence. -/
def MidHistoryTraceIn.senderOccurrences {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} →
      MidHistoryTraceIn F cfg start future → List SenderOccurrence
  | _, _, .tail _ cut => cut.after.senderOccurrences
  | _, _, .step prior block => prior.senderOccurrences ++ block.bodyTrace.transactions.senderOccurrences

/-- Project actual occurrences to recovery queries, preserving order and duplicates. -/
def MidHistoryTraceIn.senderQueries {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} (mid : MidHistoryTraceIn F cfg start future) :
    List SenderQuery := mid.senderOccurrences.map SenderOccurrence.query

/-- Every factored mid query has an original admitted occurrence witness. -/
theorem MidHistoryTraceIn.mem_senderQueries_iff {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} (mid : MidHistoryTraceIn F cfg start future)
    (query : SenderQuery) :
    query ∈ mid.senderQueries ↔
      ∃ occurrence ∈ mid.senderOccurrences, occurrence.query = query :=
  List.mem_map

private theorem senderQueries_eq_inputs
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    trace.senderQueries = txs.map (fun row =>
      (⟨benv.beginTransaction.stat.chainId, row.2⟩ : SenderQuery)) := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
    change SenderOccurrence.query (.ofTransaction head) :: tail.senderQueries = _
    rw [ih]
    rfl

/-- A genuine cut's after-trace has exactly the original query suffix, on the same chain id. -/
theorem ApplyTransactionsTrace.TxSplit.senderQueries_after
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout} {i : Nat}
    (cut : trace.TxSplit i) :
    cut.after.senderQueries = trace.senderQueries.drop (i + 1) := by
  rw [senderQueries_eq_inputs cut.after, senderQueries_eq_inputs trace]
  have chain : (cut.benv.withState cut.txState).beginTransaction.stat.chainId =
      benv.beginTransaction.stat.chainId := by
    change cut.benv.stat.chainId = benv.stat.chainId
    exact congrArg BenvStat.chainId cut.before.stat_eq
  rw [chain, List.map_drop]

/-- The tail retains every suffix transaction with its original index and full input. -/
theorem MidHistoryTraceIn.senderOccurrences_tail_indexed
    {F : Fork → Prop} {cfg : ChainConfig} {pre completed : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre completed) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    (MidHistoryTraceIn.tail block cut).senderOccurrences.map
      (fun occurrence => (occurrence.index, occurrence.tx)) =
        block.bodyTrace.decodedTxs.putIndex.drop (i + 1) :=
  cut.after.senderOccurrences_indexed

private theorem configured_senderQueries_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) :
    (first.append second).senderQueries = first.senderQueries ++ second.senderQueries := by
  induction second with
  | refl =>
    simp only [ConfiguredHistoryTraceIn.append, ConfiguredHistoryTraceIn.senderQueries,
      ConfiguredHistoryTraceIn.senderOccurrences, List.map_nil, List.append_nil]
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.append, ConfiguredHistoryTraceIn.senderQueries,
      ConfiguredHistoryTraceIn.senderOccurrences, List.map_append] at ih ⊢
    rw [ih, List.append_assoc]

/-- Later blocks append their complete admitted query lists in the original order. -/
theorem MidHistoryTraceIn.append_senderQueries
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (later : ConfiguredHistoryTraceIn F cfg current future) :
    (mid.append later).senderQueries = mid.senderQueries ++ later.senderQueries := by
  induction later with
  | refl =>
    simp only [MidHistoryTraceIn.append, ConfiguredHistoryTraceIn.senderQueries,
      ConfiguredHistoryTraceIn.senderOccurrences, List.map_nil, List.append_nil]
  | step prior block ih =>
    simp only [MidHistoryTraceIn.append, MidHistoryTraceIn.senderQueries,
      MidHistoryTraceIn.senderOccurrences, ConfiguredHistoryTraceIn.senderQueries,
      ConfiguredHistoryTraceIn.senderOccurrences, StagedBodyTrace.senderOccurrences,
      List.map_append] at ih ⊢
    rw [ih, List.append_assoc]

/-- The full query list is exactly its original prefix followed by the actual mid suffix. -/
theorem MidHistoryTraceIn.senderQueries_cut_prefix
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint pre completed future : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future) :
    ((prior.step block).append later).senderQueries =
      (prior.senderQueries ++ block.bodyTrace.transactions.senderQueries.take (i + 1)) ++
        ((MidHistoryTraceIn.tail block cut).append later).senderQueries := by
  rw [configured_senderQueries_append, MidHistoryTraceIn.append_senderQueries]
  have step : (prior.step block).senderQueries =
      prior.senderQueries ++ block.bodyTrace.transactions.senderQueries :=
    List.map_append
  rw [step]
  change (prior.senderQueries ++ block.bodyTrace.transactions.senderQueries) ++
      later.senderQueries = _ ++ (cut.after.senderQueries ++ later.senderQueries)
  rw [cut.senderQueries_after]
  simp only [List.append_assoc]
  apply congrArg (fun queries => prior.senderQueries ++ queries)
  rw [← List.append_assoc, List.take_append_drop]

/-- Every mid query is in the same full history's original complete query population. -/
theorem MidHistoryTraceIn.senderQueries_subset_full
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint pre completed future : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future) :
    ((MidHistoryTraceIn.tail block cut).append later).senderQueries ⊆
      ((prior.step block).append later).senderQueries := by
  intro query member
  rw [MidHistoryTraceIn.senderQueries_cut_prefix prior block cut later]
  exact List.mem_append_right _ member

/-- The full raw-frame list has the exact original mid list as an ordered suffix. -/
theorem MidHistoryTraceIn.rawFrames_cut_prefix
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint pre completed future : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future) :
    ((prior.step block).append later).rawFrames =
      (prior.rawFrames ++ block.bodyTrace.beacon.rawFrames ++
        block.bodyTrace.history.rawFrames ++ cut.before.rawFrames ++ cut.head.rawFrames) ++
        ((MidHistoryTraceIn.tail block cut).append later).rawFrames := by
  rw [ConfiguredHistoryTraceIn.rawFrames_append, MidHistoryTraceIn.append_rawFrames]
  change (prior.rawFrames ++ block.rawFrames) ++ later.rawFrames = _
  rw [block.rawFrames_txSplit cut]
  simp only [List.append_assoc]

/-- The same retained frames, with their original derivations, embed in the full history. -/
theorem MidHistoryTraceIn.settledFrames_cut_prefix
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint pre completed future : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future) :
    ((prior.step block).append later).settledFrames =
      (prior.settledFrames ++ block.bodyTrace.beacon.settledFrames ++
        block.bodyTrace.history.settledFrames ++ cut.before.settledFrames ++
        cut.head.settledFrames) ++
        ((MidHistoryTraceIn.tail block cut).append later).settledFrames := by
  rw [ConfiguredHistoryTraceIn.settledFrames_append, MidHistoryTraceIn.append_settledFrames]
  change (prior.settledFrames ++ block.settledFrames) ++ later.settledFrames = _
  rw [block.settledFrames_txSplit cut]
  simp only [List.append_assoc]

/-- Mid raw roots retain membership in the original full history for node/world facts. -/
theorem MidHistoryTraceIn.rawFrames_subset_full
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint pre completed future : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future) :
    ((MidHistoryTraceIn.tail block cut).append later).rawFrames ⊆
      ((prior.step block).append later).rawFrames := by
  intro root member
  rw [MidHistoryTraceIn.rawFrames_cut_prefix prior block cut later]
  exact List.mem_append_right _ member

/-- Mid retained frames remain the same retained frames of the original full history. -/
theorem MidHistoryTraceIn.settledFrames_subset_full
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint pre completed future : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn F cfg pre completed) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn F cfg completed future) :
    ((MidHistoryTraceIn.tail block cut).append later).settledFrames ⊆
      ((prior.step block).append later).settledFrames := by
  intro frame member
  rw [MidHistoryTraceIn.settledFrames_cut_prefix prior block cut later]
  exact List.mem_append_right _ member

/-- Actual admitted-query exclusion and a distinct system address exclude all mid roots. -/
theorem MidHistoryTraceIn.settledRoots_caller_ne_of_senderQueries
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start future) {a : Adr}
    (excluded : ∀ query ∈ mid.senderQueries, query.recover ≠ .ok a)
    (notSystem : a ≠ systemAddress) :
    ∀ R ∈ mid.settledRoots, R.sevm.caller ≠ a := by
  induction mid with
  | tail block cut =>
    intro R member
    rcases List.mem_append.mp member with transaction | request
    · exact cut.after.settledRoots_caller_ne_of_noSenderAt
        (cut.after.noSenderAt_of_senderQueries excluded) R transaction
    · rw [block.bodyTrace.requests.settledRoots_caller R request]
      exact Ne.symm notSystem
  | step prior block ih =>
    have queries : (MidHistoryTraceIn.step prior block).senderQueries =
        prior.senderQueries ++ block.bodyTrace.transactions.senderQueries := List.map_append
    rw [queries] at excluded
    intro R member
    rcases List.mem_append.mp member with earlier | inBlock
    · exact ih (fun query member => excluded query (List.mem_append_left _ member)) R earlier
    · apply block.bodyTrace.settledRoots_caller_ne_of_noSenderAt _ notSystem R inBlock
      exact block.bodyTrace.transactions.noSenderAt_of_senderQueries
        (fun query member => excluded query (List.mem_append_right _ member))

end Blanc.ExecutionTrace
