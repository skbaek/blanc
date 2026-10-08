import Blanc.Lift.UniswapV2Pair.PairPositionalEntry
import Blanc.Lift.UniswapV2Pair.MutablePositionalFold
import Blanc.Lift.UniswapV2Pair.LockedSupply

namespace Blanc.Lift.UniswapV2Pair

open Jaune

mutual
/-- Entry admission follows this same positional source derivation. Mutable
queues retain the exact located-entry transcript and recursively selected children. -/
inductive PairSourceAdmission :
    {root start : Exec.Deriv} → {index : Nat} →
    {segment : SegmentResult} → {transcript : Transcript} → {out : RunResult} →
    PositionalConsumes root start index segment transcript out → Prop
  | finished {root start : Exec.Deriv} {index : Nat} (frame : Frame) (bytes : Bytes)
      (free : ∀ node, Exec.Deriv.ParentPrefix start node →
        ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
      PairSourceAdmission (PositionalConsumes.finished (root := root) (index := index)
        frame bytes free)
  | failed {root start : Exec.Deriv} {index : Nat} (frame : Frame) (failure : Failure)
      (genuine : failure ≠ .incompleteTranscript)
      (free : ∀ node, Exec.Deriv.ParentPrefix start node →
        ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
      PairSourceAdmission (PositionalConsumes.failed (root := root) (index := index)
        frame failure genuine free)
  | nextCall {root start : Exec.Deriv} {index : Nat}
      {frame : Frame} {request : Request} {continuation : Continuation}
      {reply : ExternalResult} {turns tail : Transcript} {executed : TurnsResult} {out : RunResult}
      (observed : SourceCallAt root frame request reply index)
      (gap : Exec.Deriv.ExecFreeUntil start observed.call.occurrence.node)
      (present : (request.requiresCode && !reply.codeExists) = false)
      (noCodeTurns : reply.codeExists = false → turns = .done)
      (during : PositionalTurns frame request observed.paths turns executed)
      (rest : PositionalConsumes root observed.call.returned (index + 1)
        (resumeSegment
          (if reply.success then executed.frame else {executed.frame with current := frame.current})
          request continuation reply) tail out)
      (admittedRest : PairSourceAdmission rest) :
      PairSourceAdmission (PositionalConsumes.nextCall observed gap present noCodeTurns during rest)
  | nextMutableCall {root start : Exec.Deriv} {index : Nat}
      {frame : Frame} {request : Request} {continuation : Continuation}
      {reply : ExternalResult} {turns tail : Transcript} {executed : TurnsResult} {out : RunResult}
      {events : List (Log ⊕ Exec.LocatedFrame)}
      (observed : SourceCallAt root frame request reply index)
      (gap : Exec.Deriv.ExecFreeUntil start observed.call.occurrence.node)
      (queue : SourceSlotEvents observed.call frame.context.pair index events)
      (present : (request.requiresCode && !reply.codeExists) = false)
      (noCodeTurns : reply.codeExists = false → turns = .done)
      (during : PositionalMutableTurns frame request 0 events turns executed)
      (rest : PositionalConsumes root observed.call.returned (index + 1)
        (resumeSegment
          (if reply.success then executed.frame else {executed.frame with current := frame.current})
          request continuation reply) tail out)
      (selectedTurns : List MutableTurn)
      (mapped : selectedTurns.map MutableTurn.event = events)
      (transcriptEq : turns = mutableTranscript selectedTurns .done)
      (authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ selectedTurns →
        LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested)
      (admittedDuring : PairMutableAdmission during)
      (admittedRest : PairSourceAdmission rest) :
      PairSourceAdmission (PositionalConsumes.nextMutableCall observed gap queue present
        noCodeTurns during rest)

/-- Every invoked child's admission is indexed by the original fold's same
selected positional proof, at the exact incoming checkpoint and child context. -/
inductive PairMutableAdmission :
    {frame : Frame} → {request : Request} → {turn : Nat} →
    {events : List (Log ⊕ Exec.LocatedFrame)} → {transcript : Transcript} → {out : TurnsResult} →
    PositionalMutableTurns frame request turn events transcript out → Prop
  | done (frame : Frame) (request : Request) (turn : Nat) :
      PairMutableAdmission (PositionalMutableTurns.done frame request turn)
  | foreignLog {frame : Frame} {request : Request} {turn : Nat}
      {log : Log} {events : List (Log ⊕ Exec.LocatedFrame)} {tail : Transcript} {out : TurnsResult}
      (mutable : externalStatic frame request = false)
      (rest : PositionalMutableTurns
        {frame with current := {frame.current with logs := frame.current.logs ++
          [.foreign {invocation := frame.context.invocation, site := request.site, turn := turn}
            log.address log.topics log.data]}}
        request (turn + 1) events tail out)
      (admittedRest : PairMutableAdmission rest) :
      PairMutableAdmission (PositionalMutableTurns.foreignLog mutable rest)
  | invoke {frame : Frame} {request : Request} {turn : Nat}
      {located : Exec.LocatedFrame} {entry : Entry}
      {events : List (Log ⊕ Exec.LocatedFrame)} {nested tail : Transcript}
      {child : RunResult} {out : TurnsResult}
      (selected : PositionalConsumes (Exec.Frame.rootDeriv located.frame)
        (Exec.Frame.rootDeriv located.frame) 0
        (startTyped frame.current
          (childContext frame request turn located.frame.sevm.caller
            located.frame.sevm.value located.frame.sevm.isStatic) entry) nested child)
      (output : child.status = .success
        (Execution.committedPost located.frame.out located.frame.committed).output)
      (rest : PositionalMutableTurns {frame with current := child.frame.current}
        request (turn + 1) events tail out)
      (admittedChild : PairSourceAdmission selected)
      (admittedRest : PairMutableAdmission rest) :
      PairMutableAdmission (PositionalMutableTurns.invoke selected output rest)
end

/-- The stronger endpoint retains admission on the same rooted consumption proof. -/
def PairAdmittedConsumes (root : Exec.Deriv) (segment : SegmentResult)
    (transcript : Transcript) (out : RunResult) : Prop :=
  ∃ selected : PositionalConsumes root root 0 segment transcript out,
    PairSourceAdmission selected

/-- The actual output belongs to the same admitted child result. -/
def PairAdmittedChildConsumes (root : Exec.Deriv) (segment : SegmentResult)
    (transcript : Transcript) (out : RunResult) : Prop :=
  PairAdmittedConsumes root segment transcript out ∧
    ∀ committed : Execution.commits root.exn = true,
      out.status = .success (Execution.committedPost root.exn committed).output

/-- The fold carries one positional turn proof and admission on that same proof. -/
def PairAdmittedMutableTurns (frame : Frame) (request : Request) (turn : Nat)
    (events : List (Log ⊕ Exec.LocatedFrame)) (transcript : Transcript) (out : TurnsResult) : Prop :=
  ∃ selected : PositionalMutableTurns frame request turn events transcript out,
    PairMutableAdmission selected

theorem PairAdmittedConsumes.positional {root : Exec.Deriv} {segment : SegmentResult}
    {transcript : Transcript} {out : RunResult}
    (admitted : PairAdmittedConsumes root segment transcript out) :
    PairRootedConsumes root segment transcript out := admitted.choose

theorem admittedMutableTurnRules :
    MutableTurnRules PairAdmittedChildConsumes PairAdmittedMutableTurns := by
  refine ⟨?_, ?_⟩
  · intro frame request turn log events tail out mutable rest
    obtain ⟨selected, admitted⟩ := rest
    exact ⟨.foreignLog mutable selected, .foreignLog mutable selected admitted⟩
  · intro frame request turn located entry events nested tail child out selected rest
    obtain ⟨⟨source, admittedSource⟩, output⟩ := selected
    obtain ⟨tailProof, admittedTail⟩ := rest
    exact ⟨.invoke source (output located.frame.committed) tailProof,
      .invoke source (output located.frame.committed) tailProof admittedSource admittedTail⟩

theorem admittedMutableTurns_done (frame : Frame) (request : Request) (turn : Nat) :
    PairAdmittedMutableTurns frame request turn [] .done
      {complete := true, frame := frame, childReturns := []} :=
  ⟨.done frame request turn, .done frame request turn⟩

end Blanc.Lift.UniswapV2Pair
