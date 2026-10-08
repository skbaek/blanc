import Blanc.ExecutionTraceFrames

/-! Exact cuts of the existing retained transaction trace. Indices are kept,
and raw roots are partitioned without a settlement filter. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- A take/drop cut with the actual intermediate environment and output. -/
structure ApplyTransactionsTrace.PrefixSplit
    {txs : List (Nat × Tx)} {startBenv finalBenv : Benv} {startBout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs startBenv startBout finalBenv finalBout) (n : Nat) where
  benv : Benv
  bout : BlockOutput
  before : ApplyTransactionsTrace (txs.take n) startBenv startBout benv bout
  suffix : ApplyTransactionsTrace (txs.drop n) benv bout finalBenv finalBout
  rawFrames_eq : trace.rawFrames = before.rawFrames ++ suffix.rawFrames

/-- Split at any position; beyond the length this is the full trace followed
by the empty trace. Both pieces are ordinary `ApplyTransactionsTrace`s. -/
noncomputable def ApplyTransactionsTrace.splitPrefix
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (n : Nat) :
    trace.PrefixSplit n := by
  induction trace generalizing n with
  | nil benv bout =>
      cases n <;> exact ⟨benv, bout, .nil benv bout, .nil benv bout, rfl⟩
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      cases n with
      | zero => exact ⟨benv, bout, .nil benv bout, .cons head tail, rfl⟩
      | succ n =>
          let cut := ih n
          refine ⟨cut.benv, cut.bout, .cons head cut.before, cut.suffix, ?_⟩
          simp only [ApplyTransactionsTrace.rawFrames, List.append_assoc]
          rw [cut.rawFrames_eq]
          rfl

/-- An empty retained transaction fold has identical start and end boundaries. -/
theorem ApplyTransactionsTrace.nil_boundary
    {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace [] benv bout finalBenv finalBout) :
    finalBenv = benv ∧ finalBout = bout := by
  cases trace
  exact ⟨rfl, rfl⟩

/-- The cut before any normal transaction is the supplied starting boundary. -/
theorem ApplyTransactionsTrace.PrefixSplit.zero_boundary
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    (cut : trace.PrefixSplit 0) : cut.benv = benv ∧ cut.bout = bout := by
  exact cut.before.nil_boundary

/-- Taking every transaction reaches exactly the trace's final boundary. -/
theorem ApplyTransactionsTrace.PrefixSplit.full_boundary
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    (cut : trace.PrefixSplit txs.length) : cut.benv = finalBenv ∧ cut.bout = finalBout := by
  have after := cut.suffix
  rw [List.drop_length] at after
  exact ⟨after.nil_boundary.1.symm, after.nil_boundary.2.symm⟩

/-- The first remaining indexed transaction is processed at the cut boundary,
with the exact result already retained by the original trace. -/
theorem ApplyTransactionsTrace.PrefixSplit.next_result
    {txs rest : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout} {n index : Nat} {tx : Tx}
    (cut : trace.PrefixSplit n) (next : txs.drop n = (index, tx) :: rest) :
    ∃ state out, processTransaction cut.benv cut.bout tx index = .ok (state, out) ∧
      Nonempty (ApplyTransactionsTrace rest (cut.benv.withState state) out finalBenv finalBout) := by
  have after := cut.suffix
  rw [next] at after
  cases after with
  | cons head tail => exact ⟨_, _, head.result, ⟨tail⟩⟩

end Blanc.ExecutionTrace
