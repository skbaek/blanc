import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.ExecutionPathLocator

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- An ordinary code-guarded source request is bound to the supplied original
STATICCALL, its exact slot, full physical reply and per-spawn partition. -/
theorem static_source_call_at {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} {g ii is oi os : B256} {S : List B256}
    {paths : List Exec.LocatedFrame}
    (call : CallOccurrenceStep root
      (match request.kind with | .call => .call | .staticCall => .staticcall))
    (kind : request.kind = .staticCall) (requires : request.requiresCode = true)
    (ordinary : ∀ digest v r s, request.operation ≠ .recover digest v r s)
    (value : request.value = 0) (pair : frame.context.pair = call.occurrence.node.sevm.currentTarget)
    (operands : (g :: request.target.toB256 :: ii :: is :: oi :: os :: S) <<+
      call.occurrence.node.devm.stack)
    (calldata : (call.occurrence.node.devm.memory.read ii.toNat is.toNat).1 = request.calldata)
    (flag : [1] <<+ call.returned.devm.stack)
    (success : reply.success = true) (bytes : reply.returndata = call.returned.devm.returnData)
    (codeBit : reply.codeExists = true)
    (guard : (call.occurrence.node.devm.getCode request.target).size.toB256 ≠ 0)
    (fork : CoveredFork call.occurrence.node.sevm.benvStat.fork)
    (queue : SourceSlotQueue call frame.context.pair index paths) :
    ∃ observed : SourceCallAt root frame request reply index,
      observed.call = call ∧ observed.paths = paths := by
  have instruction : call.occurrence.instruction = Ninst.staticcall := by
    simpa only [kind] using call.instruction
  have primitive : Ninst.StepRun call.occurrence.node.pc call.occurrence.node.sevm
      call.occurrence.node.devm Ninst.staticcall call.occurrence.slot (.ok call.returned.devm) := by
    simpa only [instruction, call.result] using call.occurrence.stepRun
  rcases of_step_staticcall_val_with_depth_frame_cause operands call.occurrence.filled primitive fork
    with failed | entered
  · have impossible : (0 : B256) = 1 := pref_head_unique failed.1 flag
    exact False.elim ((by decide : (0 : B256) ≠ 1) impossible)
  · obtain ⟨parent, child, dp, na, childCode, avail, depth, childStack, parentState,
      parentMemory, parentLogs, parentOutput, authentication, filled, process, clean,
      resumed, returnedState, returnedData, returnedMemory, returnedStack, spawned⟩ := entered
    let msg := callMsg call.occurrence.node.sevm parent (min g.toNat (except64th avail)) 0
      call.occurrence.node.sevm.currentTarget request.target na true true request.calldata childCode dp
    have actualMsg : callMsg call.occurrence.node.sevm parent (min g.toNat (except64th avail)) 0
        call.occurrence.node.sevm.currentTarget request.target.toB256.toAdr na true true
        (call.occurrence.node.devm.memory.read ii.toNat is.toNat).1 childCode dp = msg := by
      rw [toAdr_toB256, calldata]
    rw [actualMsg] at process spawned
    have decoded : Ninst.At call.occurrence.node.sevm.code call.occurrence.node.pc Ninst.staticcall := by
      rw [← instruction]
      exact call.occurrence.decoded
    have driver : Evm.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm,
        call.occurrence.node.devm⟩ = .spawn (Jaune.Frame.ofCall msg)
        (Resume.call parent oi.toNat os.toNat) (call.occurrence.node.pc + 1) := by
      rw [Evm.step_next decoded]
      exact spawned
    obtain ⟨childFrames, partition⟩ :=
      Blanc.Exec.Deriv.ParentStep.descendantFramePaths_spawn_suffix call.edge driver [] index
    refine ⟨{
      call := call
      message := msg
      resume := Resume.call parent oi.toNat os.toNat
      nextPc := call.occurrence.node.pc + 1
      child := child
      outputOffset := oi.toNat
      outputSize := os.toNat
      parent := parent
      spawned := driver
      target := rfl
      caller := pair.symm
      value := value.symm
      calldata := rfl
      static := by simp only [msg, callMsg, externalStatic, kind, BEq.rfl, Bool.or_true, Bool.true_or]
      response := process
      resumeEq := rfl
      resumed := resumed
      replyAt := .bytes ordinary (by rw [success, clean]; rfl) (bytes.trans returnedData)
      guarded := by intro _; exact ⟨fun _ => guard, fun _ => codeBit⟩
      unguardedEntry := by intro absent; rw [requires] at absent; cases absent
      paths := paths
      queue := queue
      childFrames := childFrames
      partition := partition
    }, rfl, rfl⟩

end Blanc.Lift.UniswapV2Pair
