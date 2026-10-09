import Blanc.Lift.UniswapV2Pair.SwapSourceOccurrenceTransfer
import Blanc.Lift.AccountAccessState

/-! The guarded callback observes the same physical CALL and complete slot queue. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- A guarded callback keeps its own successful reply and actual code guard;
its entered slot bit is not substituted for the guarded request's code bit. -/
theorem SwapCallbackOccurrence.sourceCall {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {q toWord a0 a1 len dataStart : B256} {K : List SFunc}
    (r : SwapCallbackOccurrence root start b L M q toWord a0 a1 len dataStart K)
    (frame : Frame) (index : Nat)
    (staticContext : frame.context.isStatic = start.sevm.isStatic)
    (pair : frame.context.pair = start.sevm.currentTarget)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ observed : SourceCallAt root frame
        (requestFor .swapCallback toWord.toAdr (.callback start.sevm.caller a0 a1
          (start.sevm.data.sliceD dataStart.toNat len.toNat 0)))
        (swapCallbackReply r.step.returned.devm.returnData) index,
      observed.call = r.step := by
  let request := requestFor .swapCallback toWord.toAdr (.callback start.sevm.caller a0 a1
    (start.sevm.data.sliceD dataStart.toNat len.toNat 0))
  let unguarded : Request := {request with requiresCode := false}
  have target : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord =
      toWord.toAdr.toB256 := ff20_and_word toWord
  have operands : (r.gas.toB256 :: toWord.toAdr.toB256 :: 0 :: q ::
      (swapCallbackEnd q len - q) :: q :: 0 :: []) <<+ r.step.occurrence.node.devm.stack := by
    rw [r.input]
    simp only [St.stack, target]
    exact pref_append _ _
  have data : (r.step.occurrence.node.devm.memory.read q.toNat
      (swapCallbackEnd q len - q).toNat).1 = unguarded.calldata := by
    rw [r.input]
    simp only [St.memory]
    exact r.calldata
  have flag : [1] <<+ r.step.returned.devm.stack := by
    rw [r.stack]; exact pref_append _ _
  obtain ⟨paths, queue⟩ := CallOccurrenceStep.sourceSlotQueue r.step frame.context.pair index
  obtain ⟨raw, same, _⟩ := transfer_source_call_at (request := unguarded)
    (reply := swapObservedTransferReply r.step.returned.devm.returnData r.step.occurrence.slot.isSome)
    r.step rfl rfl
    (by intro digest v rr ss impossible; cases impossible)
    (by rw [r.sevmEq]; exact staticContext) (by rw [r.sevmEq]; exact pair)
    operands data flag rfl rfl rfl (by rw [r.sevmEq]; exact fork) queue
  have present : (raw.call.occurrence.node.devm.getCode request.target).size.toB256 ≠ 0 := by
    rw [same, r.input]
    simp only [St, Devm.getCode_setMach, Blanc.Lift.temporalAccountAccessBase_getCode]
    have guarded := r.codePresent
    rw [target, toAdr_toB256] at guarded
    exact guarded
  have replyAt : SourceReplyAt request (swapCallbackReply r.step.returned.devm.returnData)
      raw.child raw.call.returned raw.outputOffset := by
    cases raw.replyAt with
    | bytes ordinary success bytes => exact .bytes ordinary success bytes
    | recovery operation success bytes copied => cases operation
  refine ⟨{
    call := raw.call
    message := raw.message
    resume := raw.resume
    nextPc := raw.nextPc
    child := raw.child
    outputOffset := raw.outputOffset
    outputSize := raw.outputSize
    parent := raw.parent
    spawned := raw.spawned
    target := raw.target
    caller := raw.caller
    value := raw.value
    calldata := raw.calldata
    static := raw.static
    response := raw.response
    resumeEq := raw.resumeEq
    resumed := raw.resumed
    replyAt := replyAt
    guarded := by intro _; exact ⟨fun _ => present, fun _ => rfl⟩
    unguardedEntry := by intro impossible; cases impossible
    paths := raw.paths
    queue := raw.queue
    childFrames := raw.childFrames
    partition := raw.partition
  }, same⟩

end Blanc.Lift.UniswapV2Pair
