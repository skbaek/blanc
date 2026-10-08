import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.ExecutionPathLocator
import Blanc.LadderBase

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- An ordinary unguarded source request is bound to the supplied original
CALL, its exact slot, full physical reply and per-spawn partition. -/
theorem transfer_source_call_at {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} {g ii is oi os : B256} {S : List B256}
    {paths : List Exec.LocatedFrame}
    (call : CallOccurrenceStep root
      (match request.kind with | .call => .call | .staticCall => .staticcall))
    (kind : request.kind = .call) (requires : request.requiresCode = false)
    (ordinary : ∀ digest v r s, request.operation ≠ .recover digest v r s)
    (staticContext : frame.context.isStatic = call.occurrence.node.sevm.isStatic)
    (pair : frame.context.pair = call.occurrence.node.sevm.currentTarget)
    (operands : (g :: request.target.toB256 :: request.value :: ii :: is :: oi :: os :: S) <<+
      call.occurrence.node.devm.stack)
    (calldata : (call.occurrence.node.devm.memory.read ii.toNat is.toNat).1 = request.calldata)
    (flag : [1] <<+ call.returned.devm.stack)
    (success : reply.success = true) (bytes : reply.returndata = call.returned.devm.returnData)
    (codeBit : reply.codeExists = call.occurrence.slot.isSome)
    (fork : CoveredFork call.occurrence.node.sevm.benvStat.fork)
    (queue : SourceSlotQueue call frame.context.pair index paths) :
    ∃ observed : SourceCallAt root frame request reply index,
      observed.call = call ∧ observed.paths = paths := by
  have instruction : call.occurrence.instruction = Ninst.call := by
    simpa only [kind] using call.instruction
  have primitive : Ninst.StepRun call.occurrence.node.pc call.occurrence.node.sevm
      call.occurrence.node.devm Ninst.call call.occurrence.slot (.ok call.returned.devm) := by
    simpa only [instruction, call.result] using call.occurrence.stepRun
  rcases of_step_call_val_with_depth_frame operands call.occurrence.filled primitive fork
    with failed | entered
  · have impossible : (0 : B256) = 1 := pref_head_unique failed.1 flag
    exact False.elim ((by decide : (0 : B256) ≠ 1) impossible)
  · obtain ⟨parent, child, dp, na, childCode, avail, depth, childStack, parentState,
      parentMemory, parentLogs, parentOutput, authentication, filled, process, clean,
      resumed, returnedState, returnedData, returnedMemory, returnedStack, spawned⟩ := entered
    let msg := callMsg call.occurrence.node.sevm parent
      (min g.toNat (except64th avail) + (if request.value.toNat = 0 then 0 else gCallStipend)) request.value
      call.occurrence.node.sevm.currentTarget request.target na true false request.calldata childCode dp
    have actualMsg : callMsg call.occurrence.node.sevm parent
      (min g.toNat (except64th avail) + (if request.value.toNat = 0 then 0 else gCallStipend)) request.value
        call.occurrence.node.sevm.currentTarget request.target.toB256.toAdr na true false
        (call.occurrence.node.devm.memory.read ii.toNat is.toNat).1 childCode dp = msg := by
      rw [toAdr_toB256, calldata]
    rw [actualMsg] at process spawned
    have decoded : Ninst.At call.occurrence.node.sevm.code call.occurrence.node.pc Ninst.call := by
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
      value := rfl
      calldata := rfl
      static := by
        dsimp only [msg, callMsg, externalStatic]
        simp only [kind, show (CallKind.call == CallKind.staticCall) = false from rfl]
        rw [staticContext]
        cases call.occurrence.node.sevm.isStatic <;> rfl
      response := process
      resumeEq := rfl
      resumed := resumed
      replyAt := .bytes ordinary (by rw [success, clean]; rfl) (bytes.trans returnedData)
      guarded := by intro present; rw [requires] at present; cases present
      unguardedEntry := by intro _; exact codeBit
      paths := paths
      queue := queue
      childFrames := childFrames
      partition := partition
    }, rfl, rfl⟩

end Blanc.Lift.UniswapV2Pair
