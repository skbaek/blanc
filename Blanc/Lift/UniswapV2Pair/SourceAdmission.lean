import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.Lift.UniswapV2Pair.MutableTurns
import Blanc.ExecutionFrameTime

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

/-- A frame selected into a mutable call's event queue runs at the calling root's block statics:
it is a raw frame root of the entered child (`Exec.retainedTargetFramesFromAt_rawFrameRoot`), which
inherits the caller's statics (`Exec.frameAdmitted_benvStat`, `Evm.step_spawn_child_benvStat`). -/
theorem SourceSlotEvents.located_benvStat {root : Exec.Deriv} {x : Xinst}
    {call : CallOccurrenceStep root x} {pair : Adr} {index : Nat}
    {events : List (Log ⊕ Exec.LocatedFrame)} (observed : SourceSlotEvents call pair index events)
    {located : Exec.LocatedFrame} (member : Sum.inr located ∈ events) :
    located.frame.sevm.benvStat = root.sevm.benvStat := by
  rcases observed with ⟨-, rfl⟩ |
    ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed, -, -, rfl⟩
  · cases member
  by_cases settles : Jaune.Frame.settlementCommits callee raw = true
  · rw [dite_eq_left_of_eq_true (eq_true settles)] at member
    have selected : located ∈ (Exec.targetLogEventsFrom pair [index] 0 child
        (Jaune.Frame.raw_commits_of_settlementCommits settles)).filterMap Sum.getRight? :=
      List.mem_filterMap.mpr ⟨_, member, rfl⟩
    rw [Exec.targetLogEventsFrom_frames] at selected
    obtain ⟨rawRoot, target⟩ := Exec.retainedTargetFramesFromAt_rawFrameRoot pair child _ selected
    rw [← Blanc.Exec.Deriv.ParentPrefix.sevm_eq call.sameFrame]
    exact (Exec.frameAdmitted_benvStat child pair _ rawRoot target).trans
      (Evm.step_spawn_child_benvStat spawn enter)
  · rw [dite_eq_right_of_eq_false (eq_false settles)] at member
    cases member

mutual
/-- Admission under `Auth` is admission under `Auth'` when `Auth` implies `Auth'` at every frame
whose block statics satisfy `P` and the root's statics satisfy `P`: every frame admitted below the
root runs at the root's statics (`SourceSlotEvents.located_benvStat`). -/
theorem SourceAdmission.mono_benvStat {Auth Auth' : Exec.Deriv → Entry → Transcript → Prop}
    {P : BenvStat → Prop}
    (weaken : ∀ D entry nested, P D.sevm.benvStat → Auth D entry nested → Auth' D entry nested)
    {root start : Exec.Deriv} {index : Nat} {segment : SegmentResult} {transcript : Transcript}
    {out : RunResult} {selected : PositionalConsumes root start index segment transcript out}
    (admits : P root.sevm.benvStat) :
    SourceAdmission Auth selected → SourceAdmission Auth' selected
  | .finished frame bytes free => .finished frame bytes free
  | .failed frame failure genuine free => .failed frame failure genuine free
  | .nextCall observed gap staticExternal present noCodeTurns during rest admittedRest =>
      .nextCall observed gap staticExternal present noCodeTurns during rest
        (SourceAdmission.mono_benvStat weaken admits admittedRest)
  | .nextMutableCall (events := events) observed gap queue present noCodeTurns during rest
      selectedTurns mapped transcriptEq authentic admittedDuring admittedRest =>
      have inherited : ∀ located, Sum.inr located ∈ events → P located.frame.sevm.benvStat :=
        fun located member => (queue.located_benvStat member).symm ▸ admits
      .nextMutableCall observed gap queue present noCodeTurns during rest selectedTurns mapped
        transcriptEq
        (fun located entry nested member => weaken _ entry nested
          (inherited located (by rw [← mapped]; exact List.mem_map_of_mem (f := MutableTurn.event) member))
          (authentic located entry nested member))
        (MutableAdmission.mono_benvStat weaken inherited admittedDuring)
        (SourceAdmission.mono_benvStat weaken admits admittedRest)

/-- `SourceAdmission.mono_benvStat` for a mutable turn queue whose selected frames run at block
statics satisfying `P`. -/
theorem MutableAdmission.mono_benvStat {Auth Auth' : Exec.Deriv → Entry → Transcript → Prop}
    {P : BenvStat → Prop}
    (weaken : ∀ D entry nested, P D.sevm.benvStat → Auth D entry nested → Auth' D entry nested)
    {frame : Frame} {request : Request} {turn : Nat} {events : List (Log ⊕ Exec.LocatedFrame)}
    {transcript : Transcript} {out : TurnsResult}
    {selected : PositionalMutableTurns frame request turn events transcript out}
    (inherited : ∀ located, Sum.inr located ∈ events → P located.frame.sevm.benvStat) :
    MutableAdmission Auth selected → MutableAdmission Auth' selected
  | .done frame request turn => .done frame request turn
  | .foreignLog mutable rest admittedRest =>
      .foreignLog mutable rest (MutableAdmission.mono_benvStat weaken
        (fun other member => inherited other (List.mem_cons_of_mem _ member)) admittedRest)
  | .invoke (located := located) selected output rest admittedChild admittedRest =>
      .invoke selected output rest
        (SourceAdmission.mono_benvStat weaken (inherited located List.mem_cons_self) admittedChild)
        (MutableAdmission.mono_benvStat weaken
          (fun other member => inherited other (List.mem_cons_of_mem _ member)) admittedRest)
end

end Blanc.Lift.UniswapV2Pair
