import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.Lift.UniswapV2Pair.MutableTurns

namespace Blanc.Lift.UniswapV2Pair

open Jaune

mutual
/-- Entry admission follows this same positional source derivation. Mutable
queues retain the exact located-entry transcript and recursively selected children. -/
inductive SourceAdmission (Auth : Exec.Deriv → Entry → Transcript → Prop) :
    {root start : Exec.Deriv} → {index : Nat} →
    {segment : SegmentResult} → {transcript : Transcript} → {out : RunResult} →
    PositionalConsumes root start index segment transcript out → Prop
  | finished {root start : Exec.Deriv} {index : Nat} (frame : Frame) (bytes : Bytes)
      (free : ∀ node, Exec.Deriv.ParentPrefix start node →
        ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
      SourceAdmission Auth (PositionalConsumes.finished (root := root) (index := index)
        frame bytes free)
  | failed {root start : Exec.Deriv} {index : Nat} (frame : Frame) (failure : Failure)
      (genuine : failure ≠ .incompleteTranscript)
      (free : ∀ node, Exec.Deriv.ParentPrefix start node →
        ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
      SourceAdmission Auth (PositionalConsumes.failed (root := root) (index := index)
        frame failure genuine free)
  | nextCall {root start : Exec.Deriv} {index : Nat}
      {frame : Frame} {request : Request} {continuation : Continuation}
      {reply : ExternalResult} {turns tail : Transcript} {executed : TurnsResult} {out : RunResult}
      (observed : SourceCallAt root frame request reply index)
      (gap : Exec.Deriv.ExecFreeUntil start observed.call.occurrence.node)
      (staticExternal : externalStatic frame request = true)
      (present : (request.requiresCode && !reply.codeExists) = false)
      (noCodeTurns : reply.codeExists = false → turns = .done)
      (during : PositionalTurns frame request observed.paths turns executed)
      (rest : PositionalConsumes root observed.call.returned (index + 1)
        (resumeSegment
          (if reply.success then executed.frame else {executed.frame with current := frame.current})
          request continuation reply) tail out)
      (admittedRest : SourceAdmission Auth rest) :
      SourceAdmission Auth (PositionalConsumes.nextCall observed gap present noCodeTurns during rest)
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
        Auth (Exec.Frame.rootDeriv located.frame) entry nested)
      (admittedDuring : MutableAdmission Auth during)
      (admittedRest : SourceAdmission Auth rest) :
      SourceAdmission Auth (PositionalConsumes.nextMutableCall observed gap queue present
        noCodeTurns during rest)

/-- Every invoked child's admission is indexed by the original fold's same
selected positional proof, at the exact incoming checkpoint and child context. -/
inductive MutableAdmission (Auth : Exec.Deriv → Entry → Transcript → Prop) :
    {frame : Frame} → {request : Request} → {turn : Nat} →
    {events : List (Log ⊕ Exec.LocatedFrame)} → {transcript : Transcript} → {out : TurnsResult} →
    PositionalMutableTurns frame request turn events transcript out → Prop
  | done (frame : Frame) (request : Request) (turn : Nat) :
      MutableAdmission Auth (PositionalMutableTurns.done frame request turn)
  | foreignLog {frame : Frame} {request : Request} {turn : Nat}
      {log : Log} {events : List (Log ⊕ Exec.LocatedFrame)} {tail : Transcript} {out : TurnsResult}
      (mutable : externalStatic frame request = false)
      (rest : PositionalMutableTurns
        {frame with current := {frame.current with logs := frame.current.logs ++
          [.foreign {invocation := frame.context.invocation, site := request.site, turn := turn}
            log.address log.topics log.data]}}
        request (turn + 1) events tail out)
      (admittedRest : MutableAdmission Auth rest) :
      MutableAdmission Auth (PositionalMutableTurns.foreignLog mutable rest)
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
      (admittedChild : SourceAdmission Auth selected)
      (admittedRest : MutableAdmission Auth rest) :
      MutableAdmission Auth (PositionalMutableTurns.invoke selected output rest)
end

/-- Admission retains one positional proof at all original source indices. -/
def AdmittedSourceConsumes (Auth : Exec.Deriv → Entry → Transcript → Prop)
    (root start : Exec.Deriv) (index : Nat) (segment : SegmentResult)
    (transcript : Transcript) (out : RunResult) : Prop :=
  ∃ selected : PositionalConsumes root start index segment transcript out,
    SourceAdmission Auth selected

theorem AdmittedSourceConsumes.positional {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {root start : Exec.Deriv} {index : Nat} {segment : SegmentResult}
    {transcript : Transcript} {out : RunResult}
    (admitted : AdmittedSourceConsumes Auth root start index segment transcript out) :
    PositionalConsumes root start index segment transcript out := admitted.choose

theorem AdmittedSourceConsumes.finished {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {root start : Exec.Deriv} {index : Nat} (frame : Frame) (bytes : Bytes)
    (free : ∀ node, Exec.Deriv.ParentPrefix start node →
      ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
    AdmittedSourceConsumes Auth root start index (.finished frame bytes) .done
      {status := .success bytes, frame := frame, remaining := .done, childReturns := []} :=
  ⟨.finished frame bytes free, .finished frame bytes free⟩

theorem AdmittedSourceConsumes.failed {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {root start : Exec.Deriv} {index : Nat} (frame : Frame) (failure : Failure)
    (genuine : failure ≠ .incompleteTranscript)
    (free : ∀ node, Exec.Deriv.ParentPrefix start node →
      ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
    AdmittedSourceConsumes Auth root start index (.failed frame failure) .done
      {status := .failed failure, frame := frame, remaining := .done, childReturns := []} :=
  ⟨.failed frame failure genuine free, .failed frame failure genuine free⟩

theorem AdmittedSourceConsumes.nextCall {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {root start : Exec.Deriv} {index : Nat}
    {frame : Frame} {request : Request} {continuation : Continuation}
    {reply : ExternalResult} {turns tail : Transcript} {executed : TurnsResult} {out : RunResult}
    (observed : SourceCallAt root frame request reply index)
    (gap : Exec.Deriv.ExecFreeUntil start observed.call.occurrence.node)
    (staticExternal : externalStatic frame request = true)
    (present : (request.requiresCode && !reply.codeExists) = false)
    (noCodeTurns : reply.codeExists = false → turns = .done)
    (during : PositionalTurns frame request observed.paths turns executed)
    (rest : AdmittedSourceConsumes Auth root observed.call.returned (index + 1)
      (resumeSegment
        (if reply.success then executed.frame else {executed.frame with current := frame.current})
        request continuation reply) tail out) :
    AdmittedSourceConsumes Auth root start index (.suspended frame request continuation)
      (.next reply turns tail) {out with childReturns := executed.childReturns ++ out.childReturns} := by
  obtain ⟨selected, admitted⟩ := rest
  exact ⟨.nextCall observed gap present noCodeTurns during selected,
    .nextCall observed gap staticExternal present noCodeTurns during selected admitted⟩

/-- A completed existing source witness needs only the same actual no-call suffix. -/
theorem AdmittedSourceConsumes.of_done {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {root start : Exec.Deriv} {index : Nat} {segment : SegmentResult} {out : RunResult}
    (consumed : ExactConsumes segment .done out)
    (free : ∀ node, Exec.Deriv.ParentPrefix start node →
      ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
    AdmittedSourceConsumes Auth root start index segment .done out := by
  cases consumed with
  | finished frame bytes => exact .finished frame bytes free
  | failed frame failure genuine => exact .failed frame failure genuine free

end Blanc.Lift.UniswapV2Pair
