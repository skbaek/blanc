import Blanc.Lift.ConsolidationRequest.Queue

/-!
# Exact delivery at the EIP-7251 contract, over a given sequence of frames

The input is a list of frames at the consolidation contract, each with what its frame law gives: a submission or a
fee read by a non-system caller (`Submitted`, `RequestFee.PlainUserPath.FeeRead`, which `exec_user_frame` produces
for every successful fresh user frame), or the request phase's checked system call (empty calldata), all under a
covered fork. `Frame.toStep` packages each with its queue law (C5 for a submission, C4 for a system call), and the
shared `RequestQueue.Chain` says each frame ran on the storage the one before it left.

* `delivered_append_queue`: over any list of frames, the records the system calls deliver, in order, followed by
  the records still queued, are the starting queue followed by the submitted records, in order.
* `delivered`: on a chain from storage representing a queue, storage at the end represents the model's queue, the
  queue is exactly the submissions not yet delivered, and the concatenated system-call output is exactly the
  delivered records' bytes, in order.
* `delivery_from_empty`: the same from empty storage (`empty_represents`), with fewer than `2 ^ 253` submissions.
* `system_delivers`: each system call's output is the oldest `min(2, length)` records submitted before it and not
  yet delivered; a record submitted later cannot appear.

The list is an input: "committed" means "in the given sequence". That a chain's retained frames form such a list
(no other frame touched the storage, no frame with the system caller ran inside a user transaction) is a message,
transaction and history statement this module does not make.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open RequestSystem
open BuilderRequest (QueueState queueBase queueSlot Represents)
open RequestQueue (Effect push drainedBy Step Holds)
open RequestFee (PlainUserPath)
open SystemExecution.ConsolidationRequest.Amsterdam (sysShape)

/-- One frame at the consolidation contract, with what its frame law gives, under a covered fork. -/
inductive Frame where
  /-- A submission by a non-system caller. -/
  | submission (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256)
      (fork : CoveredFork sevm.benvStat.fork)
      (at_contract : sevm.currentTarget = consolidationRequestPredeployAddress)
      (caller : sevm.caller ≠ systemAddress) (law : Submitted sevm pre post iterations finalOutput)
  /-- A fee read by a non-system caller. -/
  | feeRead (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256)
      (fork : CoveredFork sevm.benvStat.fork)
      (at_contract : sevm.currentTarget = consolidationRequestPredeployAddress)
      (caller : sevm.caller ≠ systemAddress) (law : PlainUserPath.FeeRead sevm pre post iterations finalOutput)
  /-- The request phase's call: the checked system transaction on empty calldata. -/
  | system (benv : Benv) (post : State) (out : MsgCallOutput) (fork : CoveredFork benv.stat.fork)
      (installed : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
      (run : processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] = .ok (post, out))

namespace Frame

/-- The contract's storage when the frame starts. -/
def before : Frame → Stor
  | .submission _ pre .. => pre.getStor consolidationRequestPredeployAddress
  | .feeRead _ pre .. => pre.getStor consolidationRequestPredeployAddress
  | .system benv .. => benv.state.getStor consolidationRequestPredeployAddress

/-- The contract's storage when the frame ends. -/
def after : Frame → Stor
  | .submission _ _ post .. => post.getStor consolidationRequestPredeployAddress
  | .feeRead _ _ post .. => post.getStor consolidationRequestPredeployAddress
  | .system _ post .. => post.getStor consolidationRequestPredeployAddress

/-- What the frame does to the queue: a submission pushes its caller and calldata, a fee read keeps the
queue, a system call drains it, storing the runtime's excess. -/
def effect : Frame → Effect Record
  | .submission sevm _ _ _ _ _ _ _ law => .push (recordOf sevm law.length)
  | .feeRead .. => .keep
  | .system .. => .drain sysExcess

/-- What the frame adds to the block's requests: a system call's return data, otherwise nothing. -/
def output : Frame → Bytes
  | .system _ _ out .. => out.returnData
  | _ => []

/-- The record a submission frame enqueues. -/
def record? : Frame → Option Record
  | .submission sevm _ _ _ _ _ _ _ law => some (recordOf sevm law.length)
  | _ => none

/-- **Each frame's queue law.** A submission is C5 (`submission_represents`), a fee read changes no storage,
and a system call is C4 at frame level (`system_call_fifo`). -/
def toStep (f : Frame) : Step queue where
  before := f.before
  after := f.after
  effect := f.effect
  output := f.output
  holds := fun {st} rep slots count => by
    cases f with
    | submission sevm pre post i o fork at_contract caller law =>
      have hs : queueBase 4 st.tail + 4 ≤ 2 ^ 256 := by
        have : queueBase 4 (st.tail + 1) ≤ 2 ^ 256 := slots
        rwa [RequestQueue.queueBase_succ] at this
      have h := submission_represents law (by rw [at_contract]; exact rep) hs count
      rw [at_contract] at h
      exact h
    | feeRead sevm pre post i o fork at_contract caller law =>
      show Holds queue (post.getStor _) _
      rw [law.storage]
      exact rep
    | system benv post out fork installed run =>
      obtain ⟨post', out', run', hpost, -, -, -, hrep⟩ := system_call_fifo fork installed rep
      have e : (post, out) = (post', out') := Except.ok.inj (run.symm.trans run')
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      exact hrep
  output_eq := fun rep => by
    cases f with
    | submission => rfl
    | feeRead => rfl
    | system benv post out fork installed run =>
      obtain ⟨post', out', run', -, -, -, hret, -⟩ := system_call_fifo fork installed rep
      have e : (post, out) = (post', out') := Except.ok.inj (run.symm.trans run')
      obtain ⟨-, rfl⟩ := Prod.mk.inj e
      exact hret

end Frame

/-- **Every successful fresh user frame is a frame of the sequence.** A `UserFrame` (`exec_user_frame`) at the
contract, from a non-system caller under a covered fork, is a submission or fee-read `Frame` on the same storage. -/
theorem Frame.exists_of_userFrame {sevm : Sevm} {pre post : Devm} (fork : CoveredFork sevm.benvStat.fork)
    (at_contract : sevm.currentTarget = consolidationRequestPredeployAddress)
    (caller : sevm.caller ≠ systemAddress) (user : UserFrame sevm pre post) :
    ∃ f : Frame, f.before = pre.getStor consolidationRequestPredeployAddress ∧
      f.after = post.getStor consolidationRequestPredeployAddress ∧ f.output = [] := by
  cases user with
  | submission i o law => exact ⟨.submission sevm pre post i o fork at_contract caller law, rfl, rfl, rfl⟩
  | feeRead i o _ law => exact ⟨.feeRead sevm pre post i o fork at_contract caller law, rfl, rfl, rfl⟩

/-- The records a list of frames submits, in order: each submission frame's caller and calldata. -/
def submissions (frames : List Frame) : List Record := frames.filterMap Frame.record?

theorem submissions_eq (frames : List Frame) :
    RequestQueue.submissions (frames.map Frame.toStep) = submissions frames := by
  induction frames with
  | nil => rfl
  | cons f frames ih =>
    cases f with
    | submission => exact congrArg (_ :: ·) ih
    | feeRead => exact ih
    | system => exact ih

/-- The queue model after a list of frames. -/
def queueAfter (st : QueueState Record) (frames : List Frame) : QueueState Record :=
  RequestQueue.run 2 st (frames.map Frame.effect)

/-- The records each frame delivers, in order: a system call the oldest `min(2, length)`, others nothing. -/
def deliveries (st : QueueState Record) (frames : List Frame) : List (List Record) :=
  RequestQueue.deliveries 2 st (frames.map Frame.effect)

/-- **The EIP-7251 FIFO over a list of frames.** The records the frames' system calls deliver, in order,
followed by the records still queued, are the starting queue followed by the records the frames submit, in
order: nothing is dropped, duplicated or reordered. -/
theorem delivered_append_queue (st : QueueState Record) (frames : List Frame) :
    (deliveries st frames).flatten ++ (queueAfter st frames).queue = st.queue ++ submissions frames := by
  show (RequestQueue.deliveries 2 st (frames.map Frame.effect)).flatten ++
    (RequestQueue.run 2 st (frames.map Frame.effect)).queue = _
  rw [RequestQueue.fifo 2 st (frames.map Frame.effect), ← submissions_eq]
  simp only [RequestQueue.submissions, RequestQueue.effects, List.map_map]
  rfl

/-- **The EIP-7251 sequence delivers exactly.** On a chain of frames from storage representing a queue, with the
record slots and the count the submissions reach in word range, storage at the end represents the model's
queue, the queue holds exactly the submissions not yet delivered, and the concatenated system-call output is
exactly the delivered records, `caller ++ calldata` each, in order. -/
theorem delivered {s t : Stor} {frames : List Frame} (chain : RequestQueue.Chain s (frames.map Frame.toStep) t)
    {st : QueueState Record} (rep : Holds queue s st)
    (slots : queueBase 4 (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256) :
    RequestQueue.Delivered st (frames.map Frame.toStep) t := by
  rw [← submissions_eq] at slots count
  exact chain.delivered rep slots count

/-- `delivered` with the stride-4 bound: the tail after every submission stays below `2 ^ 253`. -/
theorem delivered_of_lt {s t : Stor} {frames : List Frame}
    (chain : RequestQueue.Chain s (frames.map Frame.toStep) t) {st : QueueState Record} (rep : Holds queue s st)
    (tail_lt : st.tail + (submissions frames).length < 2 ^ 253)
    (count : st.count + (submissions frames).length < 2 ^ 256) :
    RequestQueue.Delivered st (frames.map Frame.toStep) t :=
  delivered chain rep (by unfold queueBase; omega) count

/-- **A system call delivers the next records and no others.** On a chain from storage representing a queue, a
system call's output is the oldest `min(2, length)` of the records submitted before it and not yet delivered. -/
theorem system_delivers {s t : Stor} {xs ys : List Frame} {benv : Benv} {post : State} {out : MsgCallOutput}
    {fork : CoveredFork benv.stat.fork}
    {installed : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode}
    {run : processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] = .ok (post, out)}
    (chain : RequestQueue.Chain s ((xs ++ Frame.system benv post out fork installed run :: ys).map Frame.toStep) t)
    {st : QueueState Record} (rep : Holds queue s st)
    (slots : queueBase 4 (st.tail + (submissions xs).length) ≤ 2 ^ 256)
    (count : st.count + (submissions xs).length < 2 ^ 256) :
    out.returnData = (((st.queue ++ submissions xs).drop
      (RequestQueue.deliveredRecords st (xs.map Frame.toStep))).take 2).flatMap Record.out := by
  rw [List.map_append, List.map_cons] at chain
  rw [← submissions_eq] at slots count ⊢
  exact chain.drain_delivers (next := sysExcess) rep slots count rfl

/-- The empty queue: every counter 0, no record. -/
def emptyQueue : QueueState Record := ⟨0, 0, 0, 0, []⟩

/-- Empty storage represents the empty queue, so the represented-start premise is met. -/
theorem empty_represents : Holds queue Stor.empty emptyQueue where
  coherent := rfl
  excess_lt := by decide
  count_lt := by decide
  head_lt := by decide
  tail_lt := by decide
  live_lt := fun i hi => absurd hi (Nat.not_lt_zero _)
  excess := rfl
  count := rfl
  head := rfl
  tail := rfl
  live := fun i hi => absurd hi (Nat.not_lt_zero _)

/-- **Exact delivery from empty storage.** Over any chain of frames from empty storage, with fewer than
`2 ^ 253` submissions: storage at the end represents the model's queue, which holds exactly the submissions not yet
delivered, in order, and the system calls' concatenated output is exactly the delivered submissions'
`caller ++ calldata`, in order. -/
theorem delivery_from_empty {frames : List Frame} {t : Stor}
    (chain : RequestQueue.Chain Stor.empty (frames.map Frame.toStep) t)
    (range : (submissions frames).length < 2 ^ 253) :
    Holds queue t (RequestQueue.queueAfter emptyQueue (frames.map Frame.toStep)) ∧
      (RequestQueue.queueAfter emptyQueue (frames.map Frame.toStep)).queue =
        (submissions frames).drop (RequestQueue.deliveredRecords emptyQueue (frames.map Frame.toStep)) ∧
      RequestQueue.output (frames.map Frame.toStep) =
        ((submissions frames).take
          (RequestQueue.deliveredRecords emptyQueue (frames.map Frame.toStep))).flatMap Record.out := by
  have h := delivered_of_lt chain empty_represents (by show 0 + _ < _; omega) (by show 0 + _ < _; omega)
  rw [← submissions_eq] at range ⊢
  exact ⟨h.represents, h.queue, h.output⟩

end Blanc.Lift.ConsolidationRequest
