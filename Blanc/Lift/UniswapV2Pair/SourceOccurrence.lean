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

/-- Source consumption advances along the actual returned parent node and the
source continuation's carried state. Terminal cases exclude further calls. -/
inductive PositionalConsumes (root : Exec.Deriv) :
    Exec.Deriv → Nat → SegmentResult → Transcript → RunResult → Prop
  | finished {start : Exec.Deriv} {index : Nat} (frame : Frame) (bytes : Bytes)
      (free : ∀ node, Exec.Deriv.ParentPrefix start node →
        ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
      PositionalConsumes root start index (.finished frame bytes) .done
        {status := .success bytes, frame := frame, remaining := .done, childReturns := []}
  | failed {start : Exec.Deriv} {index : Nat} (frame : Frame) (failure : Failure)
      (genuine : failure ≠ .incompleteTranscript)
      (free : ∀ node, Exec.Deriv.ParentPrefix start node →
        ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
      PositionalConsumes root start index (.failed frame failure) .done
        {status := .failed failure, frame := frame, remaining := .done, childReturns := []}
  | nextCall {start : Exec.Deriv} {index : Nat}
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

/-- Annotation erasure recovers the existing exact consumption, without
reselecting a model state, request, transcript or successful result. -/
theorem PositionalConsumes.forget {root start : Exec.Deriv} {index : Nat}
    {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (annotated : PositionalConsumes root start index segment transcript out) :
    ExactConsumes segment transcript out := by
  induction annotated with
  | finished frame bytes free => exact .finished frame bytes
  | failed frame failure genuine free => exact .failed frame failure genuine
  | nextCall observed gap present noCodeTurns during rest ih =>
      exact .nextCall present noCodeTurns during.forget ih

end Blanc.Lift.UniswapV2Pair
