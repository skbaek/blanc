import Blanc.ExecutionTraceCallerExclusion
import Blanc.TransactionForward

/-!
# Actual admitted transaction sender occurrences

Every transaction head contributes its exact admission trace, regardless of
the later VM outcome. Selected histories project the complete ordered body
traversals. System messages are not signed-transaction sender occurrences.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The exact arguments of one transaction-sender recovery query. -/
structure SenderQuery where
  chainId : UInt64
  tx : Tx

def SenderQuery.recover (query : SenderQuery) := recoverSender query.chainId query.tx

/-- An admitted transaction with all input/output indices and its actual
admission evidence. Later VM rollback does not remove this occurrence. -/
structure SenderOccurrence where
  benv : Benv
  bout : BlockOutput
  tx : Tx
  index : Nat
  state : State
  finalBout : BlockOutput
  transaction : TransactionTrace benv bout tx index state finalBout

def SenderOccurrence.ofTransaction
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {finalBout : BlockOutput}
    (trace : TransactionTrace benv bout tx index state finalBout) : SenderOccurrence :=
  ⟨benv, bout, tx, index, state, finalBout, trace⟩

def SenderOccurrence.sender (occurrence : SenderOccurrence) : Adr :=
  occurrence.transaction.sender

def SenderOccurrence.query (occurrence : SenderOccurrence) : SenderQuery :=
  ⟨occurrence.benv.beginTransaction.stat.chainId, occurrence.tx⟩

/-- Successful admission recovers this occurrence's actual sender. -/
theorem SenderOccurrence.recovered (occurrence : SenderOccurrence) :
    occurrence.query.recover = .ok occurrence.sender :=
  Blanc.checkTransaction_sender occurrence.transaction.checked

theorem SenderOccurrence.sender_ne_of_excluded_query (occurrence : SenderOccurrence)
    {a : Adr} (exclude : occurrence.query.recover ≠ .ok a) : occurrence.sender ≠ a := by
  intro equal
  apply exclude
  simpa only [equal] using occurrence.recovered

/-- Every actual head is retained, in order, independently of its VM result. -/
def ApplyTransactionsTrace.senderOccurrences
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput} :
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → List SenderOccurrence
  | .nil .. => []
  | .cons head tail => .ofTransaction head :: tail.senderOccurrences

/-- Erasing only the admission payload returns the entire indexed input list.
In particular no failed VM outcome or duplicate transaction is filtered out. -/
theorem ApplyTransactionsTrace.senderOccurrences_indexed
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    trace.senderOccurrences.map (fun occurrence => (occurrence.index, occurrence.tx)) = txs := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      simp only [senderOccurrences, List.map_cons, SenderOccurrence.ofTransaction, ih]

/-- Completeness at every list position, with the original transaction index. -/
theorem ApplyTransactionsTrace.senderOccurrences_getElem?
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (position : Nat) :
    (trace.senderOccurrences[position]?).map
      (fun occurrence => (occurrence.index, occurrence.tx)) = txs[position]? := by
  simpa only [List.getElem?_map] using
    congrArg (fun entries => entries[position]?) trace.senderOccurrences_indexed

/-- Every indexed input transaction has its actual admitted occurrence witness. -/
theorem ApplyTransactionsTrace.exists_senderOccurrence
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    {entry : Nat × Tx} (member : entry ∈ txs) :
    ∃ occurrence ∈ trace.senderOccurrences, (occurrence.index, occurrence.tx) = entry := by
  rw [← trace.senderOccurrences_indexed] at member
  exact List.mem_map.mp member

def ApplyTransactionsTrace.senderQueries
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) : List SenderQuery :=
  trace.senderOccurrences.map SenderOccurrence.query

/-- Factoring queries preserves their position and original occurrence witness. -/
theorem ApplyTransactionsTrace.senderQueries_at
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    {position : Nat} {occurrence : SenderOccurrence}
    (atPosition : trace.senderOccurrences[position]? = some occurrence) :
    trace.senderQueries[position]? = some occurrence.query := by
  simp only [senderQueries, List.getElem?_map, atPosition, Option.map_some]

/-- Every factored query has its original admitted occurrence, including
repeated queries at different positions. -/
theorem ApplyTransactionsTrace.mem_senderQueries_iff
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (query : SenderQuery) :
    query ∈ trace.senderQueries ↔
      ∃ occurrence ∈ trace.senderOccurrences, occurrence.query = query :=
  List.mem_map

/-- The existing sender fold ranges over precisely the actual head/tail
occurrences, independently of VM execution success. -/
theorem ApplyTransactionsTrace.noSenderAt_iff_occurrences
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (a : Adr) :
    trace.NoSenderAt a ↔
      ∀ occurrence ∈ trace.senderOccurrences, occurrence.sender ≠ a := by
  induction trace with
  | nil =>
      constructor
      · intro _ occurrence member
        cases member
      · intro _
        trivial
  | cons head tail ih =>
      constructor
      · intro excluded occurrence member
        rcases List.mem_cons.mp member with atHead | later
        · subst occurrence
          exact excluded.1
        · exact ih.mp excluded.2 occurrence later
      · intro excluded
        constructor
        · exact excluded _ (List.mem_cons_self)
        · apply ih.mpr
          intro occurrence member
          exact excluded occurrence (List.mem_cons_of_mem _ member)

/-- Exact-query cryptographic exclusion supplies sender inequality through
the real admission check, not through an assumed sender oracle. -/
theorem ApplyTransactionsTrace.noSenderAt_of_senderQueries
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) {a : Adr}
    (exclude : ∀ query ∈ trace.senderQueries, query.recover ≠ .ok a) :
    trace.NoSenderAt a := by
  apply (trace.noSenderAt_iff_occurrences a).mpr
  intro occurrence member
  exact occurrence.sender_ne_of_excluded_query
    (exclude occurrence.query (List.mem_map.mpr ⟨occurrence, member, rfl⟩))

/-- The entire actual normal-transaction stage; no system caller is inserted. -/
def StagedBodyTrace.senderOccurrences
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) : List SenderOccurrence :=
  trace.transactions.senderOccurrences

/-- The stage projects exactly every decoded transaction with its original index. -/
theorem StagedBodyTrace.senderOccurrences_indexed
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    trace.senderOccurrences.map (fun occurrence => (occurrence.index, occurrence.tx)) =
      trace.decodedTxs.putIndex := trace.transactions.senderOccurrences_indexed

theorem StagedBodyTrace.senderOccurrences_getElem?
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (position : Nat) :
    (trace.senderOccurrences[position]?).map
      (fun occurrence => (occurrence.index, occurrence.tx)) =
        (trace.decodedTxs.putIndex)[position]? :=
  trace.transactions.senderOccurrences_getElem? position

/-- Project every admitted sender in the selected history's actual block order. -/
def ConfiguredHistoryTraceIn.senderOccurrences
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} :
    ConfiguredHistoryTraceIn F cfg checkpoint future → List SenderOccurrence
  | .refl .. => []
  | .step prior block => prior.senderOccurrences ++ block.bodyTrace.senderOccurrences

/-- Every occurrence in the new block is retained, and only the earlier
history and that complete body traversal contribute. This includes bodies
whose VM frame projections are empty. -/
theorem ConfiguredHistoryTraceIn.mem_senderOccurrences_step
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint current future : BlockChain}
    (prior : ConfiguredHistoryTraceIn F cfg checkpoint current)
    (block : ConfiguredBlockTraceIn F cfg current future) (occurrence : SenderOccurrence) :
    occurrence ∈ (ConfiguredHistoryTraceIn.step prior block).senderOccurrences ↔
      occurrence ∈ prior.senderOccurrences ∨ occurrence ∈ block.bodyTrace.senderOccurrences :=
  List.mem_append

def ConfiguredHistoryTraceIn.senderQueries
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) : List SenderQuery :=
  trace.senderOccurrences.map SenderOccurrence.query

theorem ConfiguredHistoryTraceIn.mem_senderQueries_iff
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (query : SenderQuery) :
    query ∈ trace.senderQueries ↔
      ∃ occurrence ∈ trace.senderOccurrences, occurrence.query = query :=
  List.mem_map

/-- Additive selected-domain sender exclusion over exactly its actual transaction folds. -/
def ConfiguredHistoryTraceIn.NoSenderAt (a : Adr)
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} :
    ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | .refl .. => True
  | .step prior block => prior.NoSenderAt a ∧ block.bodyTrace.transactions.NoSenderAt a

theorem ConfiguredHistoryTraceIn.noSenderAt_iff_occurrences
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (a : Adr) :
    trace.NoSenderAt a ↔
      ∀ occurrence ∈ trace.senderOccurrences, occurrence.sender ≠ a := by
  induction trace with
  | refl =>
      constructor
      · intro _ occurrence member
        cases member
      · intro _
        trivial
  | step prior block ih =>
      constructor
      · intro excluded occurrence member
        rcases List.mem_append.mp member with earlier | inBlock
        · exact ih.mp excluded.1 occurrence earlier
        · exact (block.bodyTrace.transactions.noSenderAt_iff_occurrences a).mp
            excluded.2 occurrence inBlock
      · intro excluded
        constructor
        · apply ih.mpr
          intro occurrence member
          exact excluded occurrence (List.mem_append_left _ member)
        · apply (block.bodyTrace.transactions.noSenderAt_iff_occurrences a).mpr
          intro occurrence member
          exact excluded occurrence (List.mem_append_right _ member)

/-- Actual-query exclusion yields the complete selected-history sender fold.
No fork-domain or cryptographic scope is widened by this projection. -/
theorem ConfiguredHistoryTraceIn.noSenderAt_of_senderQueries
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) {a : Adr}
    (exclude : ∀ query ∈ trace.senderQueries, query.recover ≠ .ok a) :
    trace.NoSenderAt a := by
  apply (trace.noSenderAt_iff_occurrences a).mpr
  intro occurrence member
  exact occurrence.sender_ne_of_excluded_query
    (exclude occurrence.query (List.mem_map.mpr ⟨occurrence, member, rfl⟩))

/-- Modern compatibility uses the supplied body's exact staged embedding. -/
def ConfiguredHistoryTrace.senderOccurrences
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List SenderOccurrence :=
  trace.toIn.senderOccurrences

theorem ConfiguredHistoryTrace.senderOccurrences_step
    {cfg : ChainConfig} {checkpoint current future : BlockChain}
    (prior : ConfiguredHistoryTrace cfg checkpoint current)
    (block : ConfiguredBlockTrace cfg current future) :
    (ConfiguredHistoryTrace.step prior block).senderOccurrences =
      prior.senderOccurrences ++ block.bodyTrace.transactions.senderOccurrences := rfl

def ConfiguredHistoryTrace.senderQueries
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List SenderQuery :=
  trace.toIn.senderQueries

/-- The new selected-domain fold agrees exactly with the existing modern
NoSenderAt definition; its sender population is not changed. -/
theorem ConfiguredHistoryTrace.toIn_noSenderAt_iff
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (a : Adr) :
    trace.toIn.NoSenderAt a ↔ trace.NoSenderAt a := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
      change (prior.toIn.NoSenderAt a ∧ block.bodyTrace.transactions.NoSenderAt a) ↔
        (prior.NoSenderAt a ∧ block.bodyTrace.transactions.NoSenderAt a)
      exact and_congr ih Iff.rfl

theorem ConfiguredHistoryTrace.noSenderAt_of_senderQueries
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {a : Adr}
    (exclude : ∀ query ∈ trace.senderQueries, query.recover ≠ .ok a) :
    trace.NoSenderAt a :=
  (trace.toIn_noSenderAt_iff a).mp (trace.toIn.noSenderAt_of_senderQueries exclude)

end Blanc.ExecutionTrace
