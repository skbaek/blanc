import Blanc.ExecutionInRawNodeOrigin
import Blanc.ExecutionHistoryCellProvenanceFrom

/-!
# How each raw node after a boundary is reached

`ConfiguredHistoryTraceIn.rawNodes_origin` reaches every raw node of an
In-history from earlier nodes anywhere in the chronology. After a committed
boundary (`ConfiguredHistoryTraceIn.BoundaryAt s pre`) the witnesses lie after
the boundary: the remaining chronology is itself an `OriginList`
(`ConfiguredHistoryTraceIn.BoundaryAt.origin`), because a boundary never falls
inside a transaction and every level's origin list is closed under `++`. So a
frame running after a boundary was entered after it
(`ConfiguredHistoryTraceIn.BoundaryAt.rawOrigin`).

`List.forall_split_of_positional` is the strong induction along positions for
a property of a node and its prefix (`List.forall_mem_of_positional` is the
prefix-free form).

Contract-neutral; no premise beyond the trace itself.

Reused (not copied): `ApplyTransactionsTrace.BoundaryAt.suffix`, the level
`rawNodes_origin` lemmas, `OriginList.append`, `OriginList.nil`.
-/

namespace Blanc

open Jaune

/-- **Strong induction along positions, with the prefix.** A property of a
node and the elements before it that holds at each position once it holds at
every strictly earlier position holds at every position. -/
theorem List.forall_split_of_positional {α : Type} {L : List α} {Q : List α → α → Prop}
    (step : ∀ before n after, L = before ++ n :: after →
      (∀ b₁ m b₂, before = b₁ ++ m :: b₂ → Q b₁ m) → Q before n) :
    ∀ before n after, L = before ++ n :: after → Q before n := by
  suffices h : ∀ k before n after, L = before ++ n :: after → before.length = k →
      Q before n from
    fun before n after split => h _ before n after split rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro before n after split hlen
    refine step before n after split fun b₁ m b₂ hb => ?_
    refine ih b₁.length ?_ b₁ m (b₂ ++ n :: after) ?_ rfl
    · rw [← hlen, hb]; simp only [List.length_append, List.length_cons]; omega
    · rw [split, hb]; simp only [List.append_assoc, List.cons_append]

namespace ExecutionTrace

/-- After a transaction boundary, the rest of the list's chronology is an origin list. -/
theorem ApplyTransactionsTrace.BoundaryAt.origin
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {s : State} {pre : List Exec.Deriv} (boundary : trace.BoundaryAt s pre) :
    ∃ rest, trace.rawNodes = pre ++ rest ∧ OriginList rest := by
  obtain ⟨_, _, _, tail, -, -, -, hnodes⟩ := boundary.suffix
  exact ⟨tail.rawNodes, hnodes, tail.rawNodes_origin⟩

/-- After a body boundary, the rest of the body's chronology is an origin list. -/
theorem StagedBodyTrace.BoundaryAt.origin {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    {trace : StagedBodyTrace benv txs ommers wds state bout}
    {s : State} {pre : List Exec.Deriv} (boundary : trace.BoundaryAt s pre) :
    ∃ rest, trace.rawNodes = pre ++ rest ∧ OriginList rest := by
  rcases boundary with ⟨-, hpre⟩ | ⟨rest, hb, hpre⟩
  · exact ⟨trace.rawNodes, by rw [hpre, List.nil_append], trace.rawNodes_origin⟩
  · obtain ⟨r, hr, hor⟩ := hb.origin
    refine ⟨r ++ trace.requests.rawNodes, ?_, hor.append trace.requests.rawNodes_origin⟩
    simp only [StagedBodyTrace.rawNodes]
    rw [hr, hpre]
    simp only [List.append_assoc]

/-- After a block boundary, the rest of the block's chronology is an origin list. -/
theorem ConfiguredBlockTraceIn.BoundaryAt.origin {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} {trace : ConfiguredBlockTraceIn F cfg pre post}
    {s : State} {nodes : List Exec.Deriv} (boundary : trace.BoundaryAt s nodes) :
    ∃ rest, trace.rawNodes = nodes ++ rest ∧ OriginList rest :=
  StagedBodyTrace.BoundaryAt.origin boundary

/-- **After a boundary of an In-history, the rest of the chronology is an origin
list**: every later raw node is reached from nodes after the boundary. -/
theorem ConfiguredHistoryTraceIn.BoundaryAt.origin
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future}
    {s : State} {pre : List Exec.Deriv} (boundary : history.BoundaryAt s pre) :
    ∃ rest, history.rawNodes = pre ++ rest ∧ OriginList rest := by
  induction history generalizing pre with
  | refl =>
      obtain ⟨-, hpre⟩ := boundary
      exact ⟨[], by rw [hpre]; rfl, OriginList.nil⟩
  | step prior block ih =>
      rcases boundary with hb | ⟨rest, hb, hpre⟩
      · obtain ⟨r, hr, hor⟩ := ih hb
        refine ⟨r ++ block.rawNodes, ?_, hor.append block.rawNodes_origin⟩
        simp only [ConfiguredHistoryTraceIn.rawNodes]
        rw [hr, List.append_assoc]
      · obtain ⟨r, hr, hor⟩ := ConfiguredBlockTraceIn.BoundaryAt.origin hb
        refine ⟨r, ?_, hor⟩
        simp only [ConfiguredHistoryTraceIn.rawNodes]
        rw [hr, hpre, List.append_assoc]

/-- **A node after a boundary is reached after it.** -/
theorem ConfiguredHistoryTraceIn.BoundaryAt.rawOrigin
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future}
    {s : State} {pre : List Exec.Deriv} (boundary : history.BoundaryAt s pre)
    {mid after : List Exec.Deriv} {n : Exec.Deriv}
    (split : history.rawNodes = pre ++ mid ++ n :: after) :
    RawOrigin mid n := by
  obtain ⟨rest, hrest, origin⟩ := boundary.origin
  rw [hrest, List.append_assoc] at split
  exact origin mid n after (List.append_cancel_left split)

end ExecutionTrace

end Blanc
