import Blanc.Lift.CursorOccurrence
import Blanc.Lift.UniswapV2Pair.StaticViewTurns

/-! Source transitions annotated by the actual external occurrence they consume. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The byte response and recovery-memory response have different observation seams. -/
inductive SourceReplyAt (request : Request) (reply : ExternalResult)
    (child : Devm) (returned : Exec.Deriv) (outputOffset : Nat) : Prop
  | bytes
      (ordinary : ∀ digest v r s, request.operation ≠ .recover digest v r s)
      (success : reply.success = !child.error.isSome)
      (returndata : reply.returndata = child.output) :
      SourceReplyAt request reply child returned outputOffset
  | recovery {digest : B256} {v : UInt8} {r s : B256}
      (operation : request.operation = .recover digest v r s)
      (success : reply.success = !child.error.isSome)
      (returndata : reply.returndata = child.output)
      (copied : reply.recoveryOutput =
        Bytes.toB256 (returned.devm.memory.read outputOffset 32).1) :
      SourceReplyAt request reply child returned outputOffset

/-- The complete selected target-frame queue belongs to this occurrence's exact slot. -/
def SourceSlotQueue {root : Exec.Deriv} {x : Xinst}
    (call : CallOccurrenceStep root x) (pair : Adr) (index : Nat)
    (paths : List Exec.LocatedFrame) : Prop :=
  (call.occurrence.slot = .none ∧ paths = []) ∨
    ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
      (resume : Resume) (pc' : Nat)
      (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (next : Exec pc' call.occurrence.node.sevm call.returned.devm call.occurrence.node.exn)
      (spawn : Evm.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm,
        call.occurrence.node.devm⟩ = .spawn callee resume pc')
      (enter : callee.enter = .run childEvm)
      (resumed : resume.run (callee.settle raw) = .ok call.returned.devm),
      call.occurrence.slot = .some ⟨childEvm, raw⟩ ∧
      call.occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
      paths = (if Jaune.Frame.settlementCommits callee raw = true then
        (Exec.retainedTargetTurnsAt pair [index] childRun).filterMap Sum.getRight?
      else [])

/-- Complete chronological events belong to the original slot and settlement.
The parent index counts every spawn, and every retained child keeps its full path. -/
def SourceSlotEvents {root : Exec.Deriv} {x : Xinst}
    (call : CallOccurrenceStep root x) (pair : Adr) (index : Nat)
    (events : List (Log ⊕ Exec.LocatedFrame)) : Prop :=
  (call.occurrence.slot = .none ∧ events = []) ∨
    ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
      (resume : Resume) (pc' : Nat)
      (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (next : Exec pc' call.occurrence.node.sevm call.returned.devm call.occurrence.node.exn)
      (spawn : Evm.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm,
        call.occurrence.node.devm⟩ = .spawn callee resume pc')
      (enter : callee.enter = .run childEvm)
      (resumed : resume.run (callee.settle raw) = .ok call.returned.devm),
      call.occurrence.slot = .some ⟨childEvm, raw⟩ ∧
      call.occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
      events = (if settles : Jaune.Frame.settlementCommits callee raw = true then
        Exec.targetLogEventsFrom pair [index] 0 childRun
          (Jaune.Frame.raw_commits_of_settlementCommits settles)
      else [])

/-- The full event queue projects to exactly the original selected-frame queue. -/
theorem SourceSlotEvents.queue {root : Exec.Deriv} {x : Xinst}
    {call : CallOccurrenceStep root x} {pair : Adr} {index : Nat}
    {events : List (Log ⊕ Exec.LocatedFrame)}
    (observed : SourceSlotEvents call pair index events) :
    SourceSlotQueue call pair index (events.filterMap Sum.getRight?) := by
  rcases observed with ⟨none, empty⟩ |
    ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed, slot, run, eventsEq⟩
  · exact Or.inl ⟨none, by rw [empty]; rfl⟩
  · refine Or.inr ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed,
      slot, run, ?_⟩
    rw [eventsEq]
    by_cases settles : Jaune.Frame.settlementCommits callee raw = true
    · rw [dite_eq_left settles, ite_eq_left settles,
        Exec.targetLogEventsFrom_frames,
        Exec.retainedTargetTurnsAt_filterMap_eq _ _ _
          (Jaune.Frame.raw_commits_of_settlementCommits settles)]
    · rw [dite_eq_right settles, ite_eq_right settles]
      rfl

/-- A suspended source request and reply observed one actual external instruction. -/
structure SourceCallAt (root : Exec.Deriv) (frame : Frame) (request : Request)
    (reply : ExternalResult) (index : Nat) where
  call : CallOccurrenceStep root (match request.kind with | .call => .call | .staticCall => .staticcall)
  message : Msg
  resume : Resume
  nextPc : Nat
  child : Devm
  outputOffset : Nat
  outputSize : Nat
  parent : Devm
  spawned : Evm.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm,
    call.occurrence.node.devm⟩ = .spawn (Jaune.Frame.ofCall message) resume nextPc
  target : message.target = some request.target
  caller : message.caller = frame.context.pair
  value : message.value = request.value
  calldata : message.data = request.calldata
  static : message.isStatic = externalStatic frame request
  response : ProcessMessage message call.occurrence.slot (.ok child)
  resumeEq : resume = Resume.call parent outputOffset outputSize
  resumed : resume.run (.ok child) = .ok call.returned.devm
  replyAt : SourceReplyAt request reply child call.returned outputOffset
  guarded : request.requiresCode = true →
    (reply.codeExists = true ↔
      (call.occurrence.node.devm.getCode request.target).size.toB256 ≠ 0)
  unguardedEntry : request.requiresCode = false →
    reply.codeExists = call.occurrence.slot.isSome
  paths : List Exec.LocatedFrame
  queue : SourceSlotQueue call frame.context.pair index paths
  childFrames : List Exec.LocatedFrame
  partition : Exec.descendantFramePaths [] index call.occurrence.node.exc =
    childFrames ++ Exec.descendantFramePaths [] (index + 1) call.returned.exc

/-- Static source invocations are read start the complete actual-slot queue, with
the same getter, context and actual return bytes observed each full entering path. -/
inductive PositionalTurns (frame : Frame) (request : Request)
    (paths : List Exec.LocatedFrame) : Transcript → TurnsResult → Prop
  | staticViews (views : List StaticViewTurn)
      (mapped : views.map Prod.fst = paths)
      (authentic : ∀ picked ∈ views, picked.Authentic frame)
      {out : TurnsResult}
      (consumed : ExactTurns frame request 0 (staticViewTranscript views .done) out) :
      PositionalTurns frame request paths (staticViewTranscript views .done) out

/-- Annotation erasure preserves the exact same source turn queue and result. -/
theorem PositionalTurns.forget {frame : Frame} {request : Request}
    {paths : List Exec.LocatedFrame} {turns : Transcript} {out : TurnsResult}
    (annotated : PositionalTurns frame request paths turns out) :
    ExactTurns frame request 0 turns out := by
  cases annotated with
  | staticViews views mapped authentic consumed => exact consumed

mutual
/-- Source consumption advances along the actual returned parent node and the
source continuation's carried state. Terminal cases exclude further calls. -/
inductive PositionalConsumes :
    Exec.Deriv → Exec.Deriv → Nat → SegmentResult → Transcript → RunResult → Prop
  | finished {root start : Exec.Deriv} {index : Nat} (frame : Frame) (bytes : Bytes)
      (free : ∀ node, Exec.Deriv.ParentPrefix start node →
        ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
      PositionalConsumes root start index (.finished frame bytes) .done
        {status := .success bytes, frame := frame, remaining := .done, childReturns := []}
  | failed {root start : Exec.Deriv} {index : Nat} (frame : Frame) (failure : Failure)
      (genuine : failure ≠ .incompleteTranscript)
      (free : ∀ node, Exec.Deriv.ParentPrefix start node →
        ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
      PositionalConsumes root start index (.failed frame failure) .done
        {status := .failed failure, frame := frame, remaining := .done, childReturns := []}
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
          request continuation reply) tail out) :
      PositionalConsumes root start index (.suspended frame request continuation)
        (.next reply turns tail) {out with childReturns := executed.childReturns ++ out.childReturns}

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
          request continuation reply) tail out) :
      PositionalConsumes root start index (.suspended frame request continuation)
        (.next reply turns tail) {out with childReturns := executed.childReturns ++ out.childReturns}

/-- Mutable invocations consume the actual located child at the current checkpoint.
The same child result carries the actual output and advances the following turn. -/
inductive PositionalMutableTurns :
    Frame → Request → Nat → List (Log ⊕ Exec.LocatedFrame) → Transcript → TurnsResult → Prop
  | done (frame : Frame) (request : Request) (turn : Nat) :
      PositionalMutableTurns frame request turn [] .done
        {complete := true, frame := frame, childReturns := []}
  | foreignLog {frame : Frame} {request : Request} {turn : Nat}
      {log : Log} {events : List (Log ⊕ Exec.LocatedFrame)} {tail : Transcript} {out : TurnsResult}
      (mutable : externalStatic frame request = false)
      (rest : PositionalMutableTurns
        {frame with current :=
          {frame.current with logs := frame.current.logs ++
            [.foreign {invocation := frame.context.invocation, site := request.site, turn := turn}
              log.address log.topics log.data]}}
        request (turn + 1) events tail out) :
      PositionalMutableTurns frame request turn (.inl log :: events)
        (.foreignLog log.address log.topics log.data tail) out
  | invoke {frame : Frame} {request : Request} {turn : Nat}
      {located : Exec.LocatedFrame} {entry : Entry}
      {events : List (Log ⊕ Exec.LocatedFrame)} {transcript tail : Transcript}
      {child : RunResult} {out : TurnsResult}
      (selected : PositionalConsumes (Exec.Frame.rootDeriv located.frame)
        (Exec.Frame.rootDeriv located.frame) 0
        (startTyped frame.current
          (childContext frame request turn located.frame.sevm.caller
            located.frame.sevm.value located.frame.sevm.isStatic) entry) transcript child)
      (output : child.status = .success
        (Execution.committedPost located.frame.out located.frame.committed).output)
      (rest : PositionalMutableTurns {frame with current := child.frame.current}
        request (turn + 1) events tail out) :
      PositionalMutableTurns frame request turn (.inr located :: events)
        (.invoke located.frame.sevm.caller located.frame.sevm.value located.frame.sevm.isStatic
          entry transcript tail)
        {out with childReturns := child.childReturns ++
          [{context := childContext frame request turn located.frame.sevm.caller
              located.frame.sevm.value located.frame.sevm.isStatic,
            entry := entry, status := child.status}] ++ out.childReturns}
end

/-- Erasure keeps the identical source segment, transcript and result. -/
theorem PositionalConsumes.forget {root start : Exec.Deriv} {index : Nat}
    {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (annotated : PositionalConsumes root start index segment transcript out) :
    ExactConsumes segment transcript out := by
  refine PositionalConsumes.rec
    (motive_1 := fun _ _ _ segment transcript out _ => ExactConsumes segment transcript out)
    (motive_2 := fun frame request turn _ transcript out _ =>
      ExactTurns frame request turn transcript out) ?_ ?_ ?_ ?_ ?_ ?_ ?_ annotated
  · intro root start index frame bytes free
    exact .finished frame bytes
  · intro root start index frame failure genuine free
    exact .failed frame failure genuine
  · intro root start index frame request continuation reply turns tail executed out
      observed gap present noCodeTurns during rest ih
    exact .nextCall present noCodeTurns during.forget ih
  · intro root start index frame request continuation reply turns tail executed out events
      observed gap queue present noCodeTurns during rest ihDuring ihRest
    exact .nextCall present noCodeTurns ihDuring ihRest
  · intro frame request turn
    exact .done frame request turn
  · intro frame request turn log events tail out mutable rest ih
    exact .foreignLog mutable ih
  · intro frame request turn located entry events transcript tail child out
      selected output rest ihSelected ihRest
    exact .invoke ihSelected ihRest

/-- Erasure keeps the identical mutable turn queue and recursively selected results. -/
theorem PositionalMutableTurns.forget {frame : Frame} {request : Request} {turn : Nat}
    {events : List (Log ⊕ Exec.LocatedFrame)} {transcript : Transcript} {out : TurnsResult}
    (annotated : PositionalMutableTurns frame request turn events transcript out) :
    ExactTurns frame request turn transcript out := by
  refine PositionalMutableTurns.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun frame request turn _ transcript out _ =>
      ExactTurns frame request turn transcript out) ?_ ?_ ?_ ?_ ?_ ?_ ?_ annotated
  · intro root start index frame bytes free
    exact True.intro
  · intro root start index frame failure genuine free
    exact True.intro
  · intro root start index frame request continuation reply turns tail executed out
      observed gap present noCodeTurns during rest ih
    exact True.intro
  · intro root start index frame request continuation reply turns tail executed out events
      observed gap queue present noCodeTurns during rest ihDuring ihRest
    exact True.intro
  · intro frame request turn
    exact .done frame request turn
  · intro frame request turn log events tail out mutable rest ih
    exact .foreignLog mutable ih
  · intro frame request turn located entry events transcript tail child out
      selected output rest ihSelected ihRest
    exact .invoke selected.forget ihRest

end Blanc.Lift.UniswapV2Pair
