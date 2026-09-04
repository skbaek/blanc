import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetInterface
import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute
import Blanc.ForwardCall

/-!
# Exact `isPaused()` runtime semantics

This unit follows one successful compiled runtime execution from its empty
entry stack through the exact `isPaused()` selector route.  After the shared
nonpayable wrapper is peeled, the selected source body is walked instruction
by instruction through `SLOAD`, `TIMESTAMP`, `LT`, `MSTORE`, and `RETURN`.
The result is an exact storage projection and output theorem; there is no
evaluator witness or assumed body walk.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

/-- A successful exact `isPaused()` runtime call reads the entry
`resumeSinceSlot` word without changing it and returns the canonical ABI word
for `block.timestamp < resumeSince`.

The zero callvalue fact is a consequence of reaching the body through the
runtime's `nonpayable` wrapper, rather than an extra premise.  `Mem.Wf` is the
ordinary message-entry memory invariant needed to identify the complete word
written and read by the return fragment. -/
theorem isPaused_exact_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiledTo sevm pre (runtime dp) (.ok post))
    (entryStack : pre.stack = [])
    (calldata : sevm.data = isPausedCalldata)
    (memoryWf : Mem.Wf pre.memory) :
    sevm.value = 0 ∧
      post.getStorVal sevm.currentTarget resumeSinceSlot =
        pre.getStorVal sevm.currentTarget resumeSinceSlot ∧
      post.output =
        (if sevm.benvStat.time <
            pre.getStorVal sevm.currentTarget resumeSinceSlot then
          (1 : B256)
        else 0).toBytes := by
  have guard :
      B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0 := by
    rw [calldata, isPausedCalldata_length]
    change B256.ltCheck (4 : B256) 4 = 0
    rw [B256.ltCheck, if_neg (lt_irrefl _)]
  have selected : Sevm.selector sevm = selIsPaused := by
    apply selector_eq_of_data_eq_abiSelectorBytes_append
        (selected := selIsPaused) (tail := [])
    · rfl
    · simpa [isPausedCalldata] using calldata
  have member : (selIsPaused, isPaused) ∈ sharedNonpayableFuncs := by
    simp [sharedNonpayableFuncs]
  have notTrigger : selIsPaused ≠ selTriggerFullWithdrawals := by decide
  have valueZero := runtime_value_zero_of_prog_run_ok_of_nontrigger
    run entryStack guard selected notTrigger
  obtain ⟨bodyPre, bodyCompiled, _bodyStack, dispatchFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame run entryStack valueZero guard
      selected notTrigger member
  have queryRun :
      Func.Run ((runtime dp).main :: (runtime dp).aux) sevm bodyPre
        isPaused post :=
    Func.Run.of_runCompiled
      (Func.RunCompiled.of_runCompiledTo_ok bodyCompiled)

  have routeStorage : Devm.getStor pre = Devm.getStor bodyPre := by
    funext owner
    unfold Devm.getStor Devm.getAcct
    rw [dispatchFrame.state]
  have routeMemory : pre.memory = bodyPre.memory := dispatchFrame.memory

  unfold isPaused at queryRun
  rcases of_run_prepend
      [Ninst.pushB256 resumeSinceSlot, Ninst.sload,
        Ninst.timestamp, Ninst.lt]
      returnWord queryRun with
    ⟨beforeReturn, queryLineRun, returnRun⟩
  have queryStorage : Devm.getStor bodyPre = Devm.getStor beforeReturn :=
    Line.of_inv Devm.getStor (by line_inv) queryLineRun
  have returnRunFull := returnRun
  have returnStorage : Devm.getStor beforeReturn = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold returnWord
      func_inv) returnRunFull

  rcases Line.of_run_cons queryLineRun with
    ⟨afterKey, keyRun, queryLineRun⟩
  rcases Line.of_run_cons queryLineRun with
    ⟨afterLoad, loadRun, queryLineRun⟩
  rcases Line.of_run_cons queryLineRun with
    ⟨afterTime, timeRun, queryLineRun⟩
  rcases Line.of_run_cons queryLineRun with
    ⟨_afterLt, ltRun, queryLineNil⟩
  cases queryLineNil

  have keyPrefix : resumeSinceSlot :: [] <<+ afterKey.stack :=
    prefix_of_push (of_run_pushB256 keyRun) nil_pref
  rcases prefix_of_sload loadRun keyPrefix with
    ⟨resumeSince, resumePrefix, resumeRead⟩
  have timePush :
      Devm.PushBurn [sevm.benvStat.time] afterLoad afterTime := by
    change Ninst.Run sevm afterLoad (.reg .timestamp) afterTime at timeRun
    rcases of_run_reg timeRun with ⟨_, instructionRun⟩
    simp only [Rinst.run, Rinst.runCore] at instructionRun
    exact Devm.pushBurn_of_pushItem instructionRun
  have queryMemory : bodyPre.memory = beforeReturn.memory :=
    (of_run_pushB256 keyRun).memory.trans
      ((Ninst.Hinv.inv (f := Devm.memory) loadRun).trans
        (timePush.memory.trans
          (Ninst.Hinv.inv (f := Devm.memory) ltRun)))
  have timePrefix : sevm.benvStat.time :: resumeSince :: [] <<+
      afterTime.stack :=
    prefix_of_push timePush resumePrefix
  have pausedPrefix : (sevm.benvStat.time <? resumeSince) :: [] <<+
      beforeReturn.stack :=
    prefix_of_lt ltRun timePrefix

  have keyStorage : Devm.getStor bodyPre = Devm.getStor afterKey :=
    Ninst.Hinv.inv (f := Devm.getStor) keyRun
  have resumeReadAtEntry :
      resumeSince = pre.getStorVal sevm.currentTarget resumeSinceSlot := by
    rw [resumeRead]
    change
      (Devm.getStor afterKey sevm.currentTarget).get resumeSinceSlot =
        (Devm.getStor pre sevm.currentTarget).get resumeSinceSlot
    rw [← congrFun keyStorage sevm.currentTarget,
      ← congrFun routeStorage sevm.currentTarget]
  rw [resumeReadAtEntry] at pausedPrefix

  have projection :
      post.getStorVal sevm.currentTarget resumeSinceSlot =
        pre.getStorVal sevm.currentTarget resumeSinceSlot := by
    have storage : Devm.getStor pre = Devm.getStor post :=
      routeStorage.trans (queryStorage.trans returnStorage)
    change
      (Devm.getStor post sevm.currentTarget).get resumeSinceSlot =
        (Devm.getStor pre sevm.currentTarget).get resumeSinceSlot
    rw [← congrFun storage sevm.currentTarget]

  have beforeReturnWf : Mem.Wf beforeReturn.memory := by
    rw [← queryMemory, ← routeMemory]
    exact memoryWf
  have beforeReturnReads :
      Mem.Reads beforeReturn.memory beforeReturn.memory.data.toList := by
    intro index
    simp

  unfold returnWord returnMemoryRange at returnRun
  rcases of_run_prepend (mstoreAt 0) _ returnRun with
    ⟨afterStore, storeRun, returnRun⟩
  rcases of_run_mstoreAt_val storeRun pausedPrefix with
    ⟨stackAfterStore, memoryAfterStore⟩
  have storedReads : Mem.Reads afterStore.memory
      (Bytes.writeAt beforeReturn.memory.data.toList 0
        (sevm.benvStat.time <?
          pre.getStorVal sevm.currentTarget resumeSinceSlot).toBytes) := by
    rw [memoryAfterStore]
    exact Mem.Reads.write beforeReturnWf beforeReturnReads 0 _

  rcases of_run_prepend (pushList [32, 0]) _ returnRun with
    ⟨beforeRet, rangeRun, returnRun⟩
  have rangeRunFull := rangeRun
  rcases Line.of_run_cons rangeRun with
    ⟨afterSize, sizeRun, rangeRun⟩
  rcases Line.of_run_cons rangeRun with
    ⟨_afterOffset, offsetRun, rangeNil⟩
  cases rangeNil
  have sizePrefix : (32 : B256) :: [] <<+ afterSize.stack :=
    prefix_of_push (of_run_pushB256 sizeRun) stackAfterStore
  have offsetPrefix : (0 : B256) :: (32 : B256) :: [] <<+
      beforeRet.stack :=
    prefix_of_push (of_run_pushB256 offsetRun) sizePrefix
  have rangeMemory : afterStore.memory = beforeRet.memory :=
    Line.of_inv Devm.memory (by line_inv) rangeRunFull
  have outputWord :
      post.output =
        (sevm.benvStat.time <?
          pre.getStorVal sevm.currentTarget resumeSinceSlot).toBytes := by
    rw [(of_run_return_val offsetPrefix returnRun).1,
      show (0 : B256).toNat = 0 from rfl,
      show (32 : B256).toNat = 32 from rfl,
      Mem.Reads.read (rangeMemory ▸ storedReads) 0 32,
      show (32 : Nat) =
          (sevm.benvStat.time <?
            pre.getStorVal sevm.currentTarget resumeSinceSlot).toBytes.length
        from (B256.length_toBytes _).symm,
      Bytes.sliceD_writeAt]

  refine ⟨valueZero, projection, ?_⟩
  simpa only [B256.ltCheck] using outputWord

end LidoTriggerableWithdrawalsGateway
end Blanc
