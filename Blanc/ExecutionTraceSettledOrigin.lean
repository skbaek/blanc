import Blanc.ExecutionTraceSettledFrames

/-!
Settlement-retained invocation roots came from actual raw entries. These
adapters preserve the outer settlement filter and transport membership only;
they neither identify independent occurrences nor reconstruct full chronology.
-/

namespace Blanc.ExecutionTrace

open Jaune

private theorem ProcessMessageTrace.mem_rawFrames_of_mem_settledFrames
    (trace : ProcessMessageTrace msg out) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) : (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
    exact False.elim (List.not_mem_nil member)
  | @some pc sevm pre raw run =>
    change frame ∈ (if Frame.settlementCommits (Frame.ofCall msg) raw = true
      then Exec.committedFrames run else []) at member
    split at member
    · exact Exec.mem_rawFrameRoots_of_mem_committedFrames run frame member
    · exact False.elim (List.not_mem_nil member)

private theorem ProcessCreateMessageTrace.mem_rawFrames_of_mem_settledFrames
    (trace : ProcessCreateMessageTrace msg out) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) : (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  rcases trace with ⟨slot, retained, process⟩
  cases retained with
  | none =>
    exact False.elim (List.not_mem_nil member)
  | @some pc sevm pre raw run =>
    change frame ∈ (if Frame.settlementCommits (Frame.ofCreate msg) raw = true
      then Exec.committedFrames run else []) at member
    split at member
    · exact Exec.mem_rawFrameRoots_of_mem_committedFrames run frame member
    · exact False.elim (List.not_mem_nil member)

private theorem MessageCallTrace.mem_rawFrames_of_mem_settledFrames
    (trace : MessageCallTrace msg state out) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) : (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  cases trace with
  | createCollision target collision result =>
    exact False.elim (List.not_mem_nil member)
  | createRun target collision evm core coreTrace result =>
    exact coreTrace.mem_rawFrames_of_mem_settledFrames frame member
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
    exact coreTrace.mem_rawFrames_of_mem_settledFrames frame member

private theorem TransactionTrace.mem_rawFrames_of_mem_settledFrames
    (trace : TransactionTrace benv bout tx index state bout') (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) : (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames :=
  trace.message.mem_rawFrames_of_mem_settledFrames frame member

/-- Every settlement-committed transaction frame's invocation root belongs to
the actual raw transaction entries. Rollback filtering is retained; the result
is membership, with no uniqueness, injectivity or chronology claim. -/
theorem ApplyTransactionsTrace.mem_rawFrames_of_mem_settledFrames
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) : (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  induction trace with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
    simp only [ApplyTransactionsTrace.settledFrames, List.mem_append] at member
    simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
    rcases member with headMember | tailMember
    · exact Or.inl (head.mem_rawFrames_of_mem_settledFrames frame headMember)
    · exact Or.inr (ih tailMember)

/-- A settlement-retained system invocation came from an actual raw entry. -/
theorem SystemMessageTrace.mem_rawFrames_of_mem_settledFrames
    (trace : SystemMessageTrace benv target data state out) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames :=
  trace.message.mem_rawFrames_of_mem_settledFrames frame member

end Blanc.ExecutionTrace
