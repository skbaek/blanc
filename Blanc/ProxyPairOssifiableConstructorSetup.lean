import Blanc.ProxyPairOssifiableConstructorInitialize
import Blanc.ProxyPairOssifiableConstructorEffects

/-!
# OssifiableProxy constructor setup child settlement

This module opens the constructor's nonempty setup helper through its exact
compiled `DELEGATECALL`, retains the actual delegated child, and classifies the
three source outcomes: resume into the post-setup phase, inherited empty-error
fallback, or byte-for-byte nonempty bubbling.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Exact setup-call boundary -/

/-- The post-call constructor tail.  A clean child enters auxiliary slot 5;
a failed child tests the complete returned length, then bubbles nonempty bytes
or enters the inherited empty-error body at slot 3. -/
def ossifiableConstructorDelegateTail : Func :=
  (.call 5) <?>
    (retdatasize :::
      (Func.revReturnData <?> (.call 3)))

theorem ossifiableConstructorDelegateSetup_split_shape :
    ossifiableConstructorDelegateSetup =
      pushB256 0 :::
      pushB256 0 :::
      [pushB256 128, mload] +++
      pushB256 0x100 :::
      [pushB256 0, mload] +++
      gas ::: delcall ::: ossifiableConstructorDelegateTail := by
  rfl

/-- Execution-derived constructor setup-call cut.  The six exact operands and
actual compiled child step are retained; no child status is assumed. -/
inductive OssifiableConstructorDelegateBoundary
    (fs : List Func) (sevm : Sevm) (pre : Devm) (tail : Stack)
    (decodedImage : Bytes) (implementation : B256)
    (setupData : Bytes) (out : Execution) : Prop where
  | intro (gasWord : B256) (callPre callPost : Devm)
      (callRun : Ninst.RunCompiled sevm callPre (.exec .delcall) callPost)
      (tailRun : Func.RunCompiledTo fs sevm callPost
        ossifiableConstructorDelegateTail out)
      (stack :
        gasWord :: implementation :: 0x100 ::
          Nat.toB256 setupData.length :: 0 :: 0 :: tail <<+
            callPre.stack)
      (memoryWf : Mem.Wf callPre.memory)
      (memoryReads : Mem.Reads callPre.memory decodedImage)
      (state : pre.state = callPre.state)
      (logs : pre.logs = callPre.logs)

/-- Open the constructor setup helper through its actual compiled
`DELEGATECALL`.  Both loaded words are derived from the proof-carrying decoder
image rather than accepted as call operands. -/
theorem ossifiableConstructorDelegateSetup_boundary
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {image : Bytes} {implementation : B256} {setupData : Bytes}
    {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (himplementation :
      Bytes.toB256 (image.sliceD 0 32 0) = implementation)
    (hlength :
      Bytes.toB256 (image.sliceD 128 32 0) =
        Nat.toB256 setupData.length)
    (run : Func.RunCompiledTo fs sevm pre
      ossifiableConstructorDelegateSetup out) :
    OssifiableConstructorDelegateBoundary fs sevm pre tail image
      implementation setupData out := by
  rw [ossifiableConstructorDelegateSetup_split_shape] at run
  obtain ⟨zeroOutputOffsetPost, qOutputOffset, run⟩ :=
    runCompiledTo_next_inv run
  obtain ⟨zeroOutputSizePost, qOutputSize, run⟩ :=
    runCompiledTo_next_inv run
  have outputOffsetPush :=
    of_run_pushB256 (Ninst.Run.of_runCompiled qOutputOffset)
  have outputSizePush :=
    of_run_pushB256 (Ninst.Run.of_runCompiled qOutputSize)
  have pOutputOffset : (0 : B256) :: tail <<+
      zeroOutputOffsetPost.stack :=
    prefix_of_push outputOffsetPush hp
  have pOutputSize : (0 : B256) :: 0 :: tail <<+
      zeroOutputSizePost.stack :=
    prefix_of_push outputSizePush pOutputOffset
  obtain ⟨lengthPost, loadLengthRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pLength, wfLength, readsLength, stateLength⟩ :=
    of_run_loadWordAt_image (word := 4)
      (value := Nat.toB256 setupData.length) pOutputSize
      (by
        rw [← outputSizePush.memory, ← outputOffsetPush.memory]
        exact hwf)
      (by
        rw [← outputSizePush.memory, ← outputOffsetPush.memory]
        exact hreads)
      (by
        rw [show ((4 : B256) * 32).toNat = 128 from by decide]
        exact hlength)
      loadLengthRun
  have logsLength := of_run_loadWordAt_logs (word := 4) loadLengthRun
  obtain ⟨inputOffsetPost, qInputOffset, run⟩ :=
    runCompiledTo_next_inv run
  have inputOffsetPush :=
    of_run_pushB256 (Ninst.Run.of_runCompiled qInputOffset)
  have pInputOffset :
      (0x100 : B256) :: Nat.toB256 setupData.length :: 0 :: 0 :: tail <<+
        inputOffsetPost.stack :=
    prefix_of_push inputOffsetPush pLength
  obtain ⟨implementationPost, loadImplementationRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pImplementation, wfImplementation, readsImplementation,
      stateImplementation⟩ :=
    of_run_loadWordAt_image (word := 0) (value := implementation)
      pInputOffset
      (by rw [← inputOffsetPush.memory]; exact wfLength)
      (by rw [← inputOffsetPush.memory]; exact readsLength)
      (by
        rw [show ((0 : B256) * 32).toNat = 0 from rfl]
        exact himplementation)
      loadImplementationRun
  have logsImplementation :=
    of_run_loadWordAt_logs (word := 0) loadImplementationRun
  obtain ⟨callPre, qGas, run⟩ := runCompiledTo_next_inv run
  have rGas := Ninst.Run.of_runCompiled qGas
  obtain ⟨gasWord, gasPush⟩ := of_run_gas rGas
  have pGas :
      gasWord :: implementation :: 0x100 ::
        Nat.toB256 setupData.length :: 0 :: 0 :: tail <<+
          callPre.stack :=
    prefix_of_push gasPush pImplementation
  obtain ⟨callPost, callRun, tailRun⟩ := runCompiledTo_next_inv run
  refine .intro gasWord callPre callPost callRun tailRun pGas ?_ ?_ ?_ ?_
  · rw [← gasPush.memory]
    exact wfImplementation
  · rw [← gasPush.memory]
    exact readsImplementation
  · exact outputOffsetPush.state.trans
      (outputSizePush.state.trans
        (stateLength.trans
          (inputOffsetPush.state.trans
            (stateImplementation.trans gasPush.state))))
  · exact outputOffsetPush.logs.trans
      (outputSizePush.logs.trans
        (logsLength.trans
          (inputOffsetPush.logs.trans
            (logsImplementation.trans gasPush.logs))))

/-- Expose the exact call states and retain whichever child actually settled
the compiled setup step. -/
theorem OssifiableConstructorDelegateBoundary.settled_child
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {decodedImage : Bytes} {implementation : B256}
    {setupData : Bytes} {out : Execution}
    (boundary : OssifiableConstructorDelegateBoundary fs sevm pre tail
      decodedImage implementation setupData out) :
    ∃ callPre callPost,
      Ninst.RunCompiled sevm callPre (.exec .delcall) callPost ∧
      Func.RunCompiledTo fs sevm callPost
        ossifiableConstructorDelegateTail out ∧
      ∀ spawn : DelegatecallSpawnDescriptor sevm callPre,
        spawn.parent.stack.length < 1024 →
          ∃ child, DelegatecallSettledBoundary spawn child callPost := by
  rcases boundary with
    ⟨_, callPre, callPost, callRun, tailRun, _, _, _, _, _⟩
  exact ⟨callPre, callPost, callRun, tailRun,
    fun spawn room => spawn.settled_of_runCompiled callRun room⟩

/-- Operand- and data-exact strengthening of `settled_child`.  Any descriptor
for the retained call state must carry the six words read by the compiled
step; its child input is consequently the decoded setup bytes, and its zero
output window preserves the decoder memory image after resumption. -/
theorem OssifiableConstructorDelegateBoundary.settled_child_exact
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {decodedImage : Bytes} {implementation : B256}
    {setupData : Bytes} {out : Execution}
    (boundary : OssifiableConstructorDelegateBoundary fs sevm pre tail
      decodedImage implementation setupData out)
    (setupLengthBound : setupData.length < 2 ^ 256)
    (setupImage :
      decodedImage.sliceD 0x100 setupData.length 0 = setupData) :
    ∃ gasWord callPre callPost,
      Ninst.RunCompiled sevm callPre (.exec .delcall) callPost ∧
      Func.RunCompiledTo fs sevm callPost
        ossifiableConstructorDelegateTail out ∧
      ∀ spawn : DelegatecallSpawnDescriptor sevm callPre,
        spawn.parent.stack.length < 1024 →
          spawn.gasWord = gasWord ∧
          spawn.codeWord = implementation ∧
          spawn.inputOffsetWord = 0x100 ∧
          spawn.inputSizeWord = Nat.toB256 setupData.length ∧
          spawn.outputOffsetWord = 0 ∧
          spawn.outputSizeWord = 0 ∧
          spawn.child.data = setupData ∧
          ∃ child,
            DelegatecallSettledBoundary spawn child callPost ∧
            Mem.Wf callPost.memory ∧
            Mem.Reads callPost.memory decodedImage := by
  rcases boundary with
    ⟨gasWord, callPre, callPost, callRun, tailRun, pCall,
      wfCall, readsCall, _, _⟩
  refine ⟨gasWord, callPre, callPost, callRun, tailRun, ?_⟩
  intro spawn room
  have knownPref :
      ([gasWord, implementation, 0x100, Nat.toB256 setupData.length,
          0, 0] : List B256) <<+ callPre.stack := by
    exact pref_trans
      (pref_append
        [gasWord, implementation, 0x100, Nat.toB256 setupData.length, 0, 0]
        tail)
      (by simpa using pCall)
  have spawnPref :
      ([spawn.gasWord, spawn.codeWord, spawn.inputOffsetWord,
          spawn.inputSizeWord, spawn.outputOffsetWord,
          spawn.outputSizeWord] : List B256) <<+ callPre.stack := by
    rw [spawn.stackEq]
    exact ⟨spawn.stackTail, rfl⟩
  have operands := List.pref_unique (by simp) knownPref spawnPref
  simp only [List.cons.injEq, and_true] at operands
  rcases operands with
    ⟨gasEq, codeEq, inputOffsetEq, inputSizeEq, outputOffsetEq,
      outputSizeEq⟩
  have parentReads : Mem.Reads spawn.parent.memory decodedImage := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_memory,
      spawn.afterAccess_memory]
    exact Mem.Reads.extends _ readsCall
  have childData : spawn.child.data = setupData := by
    rw [spawn.child_data, ← inputOffsetEq, ← inputSizeEq,
      show ((0x100 : B256)).toNat = 0x100 from by decide,
      B256.toNat_toB256_of_lt setupLengthBound,
      Mem.Reads.read parentReads, setupImage]
  obtain ⟨child, settled⟩ := spawn.settled_of_runCompiled callRun room
  obtain ⟨postWf, postReads⟩ :=
    settled.memory_image_of_outputSize_zero outputSizeEq.symm
      wfCall readsCall
  exact ⟨gasEq.symm, codeEq.symm, inputOffsetEq.symm,
    inputSizeEq.symm, outputOffsetEq.symm, outputSizeEq.symm,
    childData, child, settled, postWf, postReads⟩

/-- The nonempty setup-selection arm opens table slot 6 and reaches the exact
constructor setup-call boundary.  The returned storage/log equations connect
the implementation-commit state to the delegate helper entry without claiming
that the helper or child preserves either ERC-1967 slot. -/
theorem OssifiableConstructorSetupSelectionRoute.delegate_boundary
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack} {image : Bytes} {length implementation : B256}
    {setupData : Bytes}
    (selection : OssifiableConstructorSetupSelectionRoute fs sevm pre out
      tail image length)
    (lengthNonzero : length ≠ 0)
    (hDelegate : fs[6]? = some ossifiableConstructorDelegateSetup)
    (himplementation :
      Bytes.toB256 (image.sliceD 0 32 0) = implementation)
    (hlength :
      Bytes.toB256 (image.sliceD 128 32 0) =
        Nat.toB256 setupData.length) :
    ∃ bodyPre,
      Devm.getStor pre = Devm.getStor bodyPre ∧
      pre.logs = bodyPre.logs ∧
      OssifiableConstructorDelegateBoundary fs sevm bodyPre tail image
        implementation setupData out := by
  rcases selection with
    ⟨afterPre, lengthZero, _, _, _, _, _, _⟩ |
      ⟨delegatePre, _, delegateRun, pDelegate, wfDelegate, readsDelegate,
        storDelegate, logsDelegate⟩
  · exact (lengthNonzero lengthZero).elim
  · obtain ⟨bodyPre, burn, bodyRun⟩ :=
      runCompiledTo_call_inv hDelegate delegateRun
    have pBody : tail <<+ bodyPre.stack := by
      rw [← burn.stack]
      exact pDelegate
    have wfBody : Mem.Wf bodyPre.memory := by
      rw [← burn.memory]
      exact wfDelegate
    have readsBody : Mem.Reads bodyPre.memory image := by
      rw [← burn.memory]
      exact readsDelegate
    refine ⟨bodyPre, ?_, ?_,
      ossifiableConstructorDelegateSetup_boundary pBody wfBody readsBody
        himplementation hlength bodyRun⟩
    · exact storDelegate.trans
        (funext (getStor_eq_of_state_eq burn.state))
    · exact logsDelegate.trans burn.logs

/-- The zero-length setup arm skips `DELEGATECALL` and enters `_changeAdmin`
directly.  This is the constructor's canonical empty-data path, stated before
specializing the already-committed implementation write and `Upgraded` log. -/
theorem OssifiableConstructorSetupSelectionRoute.empty_afterSetup_success
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {pre post : Devm} {tail : Stack}
    {image runtimeBytes : Bytes} {length : B256}
    {requestedAdmin : Adr}
    (selection : OssifiableConstructorSetupSelectionRoute
      (ossifiableConstructorFunctions runtimeOffset runtimeLength)
      sevm pre (.ok post) tail image length)
    (lengthZero : length = 0)
    (hrequested :
      Bytes.toB256 (image.sliceD 32 32 0) = requestedAdmin.toB256)
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256) :
    requestedAdmin ≠ 0 ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set adminSlotLit
          (addressSlotWriteWord
            (pre.getStorVal sevm.currentTarget adminSlotLit)
            requestedAdmin.toB256) ∧
      post.logs = pre.logs ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          (pre.getStorVal sevm.currentTarget adminSlotLit)
          requestedAdmin] ∧
      post.output = runtimeBytes := by
  rcases selection with
    ⟨afterPre, _, afterRun, pAfter, wfAfter, readsAfter,
      storageAfter, logsAfter⟩ |
    ⟨_, lengthNonzero, _, _, _, _, _, _⟩
  · obtain ⟨bodyPre, burn, bodyRun⟩ := runCompiledTo_call_inv
      (ossifiableConstructorFunctions_afterSetup runtimeOffset runtimeLength)
      afterRun
    have pBody : tail <<+ bodyPre.stack := by
      rw [← burn.stack]
      exact pAfter
    have wfBody : Mem.Wf bodyPre.memory := by
      rw [← burn.memory]
      exact wfAfter
    have readsBody : Mem.Reads bodyPre.memory image := by
      rw [← burn.memory]
      exact readsAfter
    have preToBodyStor : Devm.getStor pre = Devm.getStor bodyPre :=
      storageAfter.trans (funext (getStor_eq_of_state_eq burn.state))
    have bodyToPreStor : Devm.getStor bodyPre = Devm.getStor pre :=
      preToBodyStor.symm
    have bodyAdmin :
        bodyPre.getStorVal sevm.currentTarget adminSlotLit =
          pre.getStorVal sevm.currentTarget adminSlotLit := by
      exact congrArg (fun stor => stor.get adminSlotLit)
        (congrFun bodyToPreStor sevm.currentTarget)
    have bodyLogs : bodyPre.logs = pre.logs :=
      burn.logs.symm.trans logsAfter.symm
    rcases ossifiableConstructorAfterSetup_success
        (ossifiableConstructorFunctions_zeroAdmin runtimeOffset runtimeLength)
        wfBody readsBody hrequested hruntime hruntimeLength hruntimeNonempty
        hoffsetBound hlengthBound pBody bodyRun with
      ⟨adminNonzero, postStorage, postLogs, postOutput⟩
    refine ⟨adminNonzero, ?_, ?_, postOutput⟩
    · rw [postStorage, congrFun bodyToPreStor sevm.currentTarget, bodyAdmin]
    · rw [postLogs, bodyLogs, bodyAdmin]
  · exact (lengthNonzero lengthZero).elim

/-- Compose the empty setup selection with the already-proved implementation
commit.  The result states the exact two writes and the source log chronology
without assuming an initially empty admin slot. -/
theorem OssifiableConstructorPreparedRoute.empty_afterSetup_success
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {pre post : Devm} {tail : Stack}
    {image runtimeBytes : Bytes} {implementation length : B256}
    {requestedAdmin : Adr}
    (route : OssifiableConstructorPreparedRoute
      (ossifiableConstructorFunctions runtimeOffset runtimeLength)
      sevm pre (.ok post) tail image implementation length)
    (lengthZero : length = 0)
    (hrequested :
      Bytes.toB256 (image.sliceD 32 32 0) = requestedAdmin.toB256)
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256) :
    requestedAdmin ≠ 0 ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set implementationSlotLit
          (addressSlotUpdateRaw pre sevm.currentTarget
            implementationSlotLit implementation)).set adminSlotLit
          (addressSlotWriteWord
            (((Devm.getStor pre sevm.currentTarget).set implementationSlotLit
              (addressSlotUpdateRaw pre sevm.currentTarget
                implementationSlotLit implementation)).get adminSlotLit)
            requestedAdmin.toB256) ∧
      post.logs =
        pre.logs ++ [rawUpgradedLog sevm.currentTarget implementation] ++
          [ossifiableConstructorAdminChangedLog sevm.currentTarget
            (((Devm.getStor pre sevm.currentTarget).set
              implementationSlotLit
              (addressSlotUpdateRaw pre sevm.currentTarget
                implementationSlotLit implementation)).get adminSlotLit)
            requestedAdmin] ∧
      post.output = runtimeBytes := by
  rcases route with
    noCode |
    ⟨next, _, nextStorage, nextLogs, selection⟩
  · rcases noCode with
      ⟨_, _, _, _, _, _, _, _, noCodeOutcome⟩
    rcases noCodeOutcome with
      ⟨_, impossible, _, _, _⟩ | ⟨_, impossible, _, _, _, _⟩ <;>
        cases impossible
  · rcases selection.empty_afterSetup_success lengthZero hrequested hruntime
        hruntimeLength hruntimeNonempty hoffsetBound hlengthBound with
      ⟨adminNonzero, postStorage, postLogs, postOutput⟩
    have nextAdmin :
        next.getStorVal sevm.currentTarget adminSlotLit =
          (((Devm.getStor pre sevm.currentTarget).set implementationSlotLit
            (addressSlotUpdateRaw pre sevm.currentTarget
              implementationSlotLit implementation)).get adminSlotLit) := by
      exact congrArg (fun stor => stor.get adminSlotLit) nextStorage
    refine ⟨adminNonzero, ?_, ?_, postOutput⟩
    · rw [postStorage, nextStorage, nextAdmin]
    · rw [postLogs, nextLogs, nextAdmin, List.append_assoc]

/-! ## Accepted decoder into the prepared constructor route -/

/-- Proof-carrying successful decoder/implementation preparation.  This
packages the exact decoded setup bytes and their memory projections alongside
the actual setup selection; malformed-input, allocation-panic, and no-code
walks cannot inhabit it at an `.ok` constructor result. -/
structure OssifiableConstructorPreparedSuccess
    (runtimeOffset runtimeLength argsOffset : Nat)
    (sevm : Sevm) (entry post : Devm) (tail : Stack)
    (image : Bytes) (implementation requestedAdmin : B256)
    (setupData : Bytes) (bodyPre : Devm) : Prop where
  implementationClean : addressMask &&& implementation = 0
  requestedAdminClean : addressMask &&& requestedAdmin = 0
  setupLengthBound : setupData.length < 2 ^ 256
  implementationImage :
    Bytes.toB256
      ((ossifiableConstructorDecodedImage image sevm.code.toList
        argsOffset).sliceD 0 32 0) = implementation
  requestedAdminImage :
    Bytes.toB256
      ((ossifiableConstructorDecodedImage image sevm.code.toList
        argsOffset).sliceD 32 32 0) = requestedAdmin
  setupLengthImage :
    Bytes.toB256
      ((ossifiableConstructorDecodedImage image sevm.code.toList
        argsOffset).sliceD 128 32 0) = Nat.toB256 setupData.length
  setupImage :
    (ossifiableConstructorDecodedImage image sevm.code.toList
      argsOffset).sliceD 0x100 setupData.length 0 = setupData
  spec :
    ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
      .accepted implementation requestedAdmin setupData
  entryState : entry.state = bodyPre.state
  entryLogs : entry.logs = bodyPre.logs
  prepared : OssifiableConstructorPreparedRoute
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)
    sevm bodyPre (.ok post) tail
      (ossifiableConstructorDecodedImage image sevm.code.toList argsOffset)
      implementation (Nat.toB256 setupData.length)

/-- A successful complete decoder walk necessarily reaches the accepted body,
commits the implementation, and selects the empty or nonempty setup route.
All decoded-memory facts are derived here once for both downstream arms. -/
theorem OssifiableConstructorDecodeRoute.prepare_of_ok
    {runtimeOffset runtimeLength argsOffset : Nat}
    {sevm : Sevm} {entry post : Devm} {tail : Stack} {image : Bytes}
    (route : OssifiableConstructorDecodeRoute
      (ossifiableConstructorFunctions runtimeOffset runtimeLength)
      sevm entry ossifiableConstructorInitializeImplementation argsOffset
      tail image (.ok post)) :
    ∃ implementation requestedAdmin setupData bodyPre,
      OssifiableConstructorPreparedSuccess runtimeOffset runtimeLength
        argsOffset sevm entry post tail image implementation requestedAdmin
        setupData bodyPre := by
  rcases route with
    ⟨implementation, requestedAdmin, setupData, implementationWord,
      requestedAdminWord, implementationClean, requestedAdminClean, _,
      setupDataShape, setupDataLength, spec, boundary⟩ |
    ⟨_, _, _, emptyRun, _, _, _, _, _⟩ |
    ⟨_, _, _, panicRun, _, _, _, _, _⟩
  · have setupLengthBound : setupData.length < 2 ^ 256 := by
      rw [setupDataLength]
      exact B256.toNat_lt _
    have implementationImage :
        Bytes.toB256
          ((ossifiableConstructorDecodedImage image sevm.code.toList
            argsOffset).sliceD 0 32 0) = implementation :=
      (ossifiableConstructorDecodedImage_implementationWord _ _ _).trans
        implementationWord
    have requestedAdminImage :
        Bytes.toB256
          ((ossifiableConstructorDecodedImage image sevm.code.toList
            argsOffset).sliceD 32 32 0) = requestedAdmin :=
      (ossifiableConstructorDecodedImage_adminWord _ _ _).trans
        requestedAdminWord
    have setupLengthImage :
        Bytes.toB256
          ((ossifiableConstructorDecodedImage image sevm.code.toList
            argsOffset).sliceD 128 32 0) =
          Nat.toB256 setupData.length := by
      rw [ossifiableConstructorDecodedImage_lengthWord, setupDataLength,
        toB256_toNat]
    have setupImage :
        (ossifiableConstructorDecodedImage image sevm.code.toList
          argsOffset).sliceD 0x100 setupData.length 0 = setupData := by
      rw [setupDataLength, ossifiableConstructorDecodedImage_setupData]
      simpa only [ossifiableConstructorDataStart] using setupDataShape.symm
    rcases boundary.initializeImplementation
        (ossifiableConstructorFunctions_noCode runtimeOffset runtimeLength) with
      ⟨bodyPre, entryState, entryLogs, checked⟩
    have prepared := checked.commit.selectSetup setupLengthImage
    rw [implementationWord] at prepared
    exact ⟨implementation, requestedAdmin, setupData, bodyPre,
      ⟨implementationClean, requestedAdminClean, setupLengthBound,
        implementationImage, requestedAdminImage, setupLengthImage, setupImage,
        spec, entryState, entryLogs, prepared⟩⟩
  · exact (Func.RunCompiledTo.not_ok_call_rev
      (ossifiableConstructorFunctions_emptyRevert runtimeOffset runtimeLength)
      emptyRun).elim
  · exact (Func.RunCompiledTo.not_ok_call_revData
      (ossifiableConstructorFunctions_allocationPanic runtimeOffset
        runtimeLength) panicRun).elim

/-- Specialize a prepared successful decoder to empty setup bytes.  The clean
ABI address guard supplies the exact `B256 → Adr → B256` round trip required
by the post-setup proof. -/
theorem OssifiableConstructorPreparedSuccess.empty_afterSetup_success
    {runtimeOffset runtimeLength argsOffset : Nat}
    {sevm : Sevm} {entry post : Devm} {tail : Stack}
    {image runtimeBytes setupData : Bytes}
    {implementation requestedAdmin : B256} {bodyPre : Devm}
    (success : OssifiableConstructorPreparedSuccess runtimeOffset
      runtimeLength argsOffset sevm entry post tail image implementation
      requestedAdmin setupData bodyPre)
    (setupDataEmpty : setupData = [])
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256) :
    requestedAdmin.toAdr ≠ 0 ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor bodyPre sevm.currentTarget).set
          implementationSlotLit
          (addressSlotUpdateRaw bodyPre sevm.currentTarget
            implementationSlotLit implementation)).set adminSlotLit
          (addressSlotWriteWord
            (((Devm.getStor bodyPre sevm.currentTarget).set
              implementationSlotLit
              (addressSlotUpdateRaw bodyPre sevm.currentTarget
                implementationSlotLit implementation)).get
                  adminSlotLit)
            requestedAdmin.toAdr.toB256) ∧
      post.logs = bodyPre.logs ++
        [rawUpgradedLog sevm.currentTarget implementation] ++
          [ossifiableConstructorAdminChangedLog sevm.currentTarget
            (((Devm.getStor bodyPre sevm.currentTarget).set
              implementationSlotLit
              (addressSlotUpdateRaw bodyPre sevm.currentTarget
                implementationSlotLit implementation)).get
                  adminSlotLit)
            requestedAdmin.toAdr] ∧
      post.output = runtimeBytes := by
  have lengthZero : Nat.toB256 setupData.length = (0 : B256) := by
    rw [setupDataEmpty]
    decide
  have requestedCanonical :
      requestedAdmin.toAdr.toB256 = requestedAdmin :=
    toB256_toAdr (validAdr_iff.mpr success.requestedAdminClean)
  have requestedImage :
      Bytes.toB256
        ((ossifiableConstructorDecodedImage image sevm.code.toList
          argsOffset).sliceD 32 32 0) =
        requestedAdmin.toAdr.toB256 :=
    success.requestedAdminImage.trans requestedCanonical.symm
  exact success.prepared.empty_afterSetup_success lengthZero requestedImage
    hruntime hruntimeLength hruntimeNonempty hoffsetBound hlengthBound

/-! ## Settled child outcome -/

/-- Exact source outcomes after the constructor's setup child returns.  The
clean arm retains the actual call to the post-setup phase.  Failed-child arms
retain the rolled-back suspended-parent observations before choosing the
inherited empty error or byte-for-byte bubble. -/
inductive OssifiableConstructorDelegateOutcome
    {sevm : Sevm} {callPre callPost : Devm}
    (fs : List Func) (spawn : DelegatecallSpawnDescriptor sevm callPre)
    (child : Devm) (image : Bytes) (out : Execution) : Prop where
  | success (afterPre : Devm)
      (certificate : Nonempty
        (DelegatedChildCertificate spawn.child (.ok child)))
      (childClean : child.error.isSome = false)
      (returnData : callPost.returnData = child.output)
      (run : Func.RunCompiledTo fs sevm afterPre (.call 5) out)
      (stack : spawn.parent.stack <<+ afterPre.stack)
      (memoryWf : Mem.Wf afterPre.memory)
      (memoryReads : Mem.Reads afterPre.memory image)
      (state : afterPre.state = child.state)
      (transientStorage :
        afterPre.transientStorage = child.transientStorage)
      (logs : afterPre.logs = spawn.parent.logs ++ child.logs)
  | emptyFailure (errorPre : Devm)
      (certificate : Nonempty
        (DelegatedChildCertificate spawn.child (.ok child)))
      (childFailed : child.error.isSome = true)
      (outputEmpty : child.output = [])
      (returnData : callPost.returnData = child.output)
      (callState : callPost.state = spawn.parent.state)
      (callTransientStorage :
        callPost.transientStorage = spawn.parent.transientStorage)
      (callLogs : callPost.logs = spawn.parent.logs)
      (errorEntryState : errorPre.state = callPost.state)
      (outcome : ControlErrorOutcome errorPre
        emptyDelegatecallErrorData out)
  | bubbledFailure (bubblePre : Devm)
      (certificate : Nonempty
        (DelegatedChildCertificate spawn.child (.ok child)))
      (childFailed : child.error.isSome = true)
      (outputNonempty : child.output ≠ [])
      (returnData : callPost.returnData = child.output)
      (callState : callPost.state = spawn.parent.state)
      (callTransientStorage :
        callPost.transientStorage = spawn.parent.transientStorage)
      (callLogs : callPost.logs = spawn.parent.logs)
      (bubbleEntryState : bubblePre.state = callPost.state)
      (outcome :
        (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
          (∃ post, out = .error (.revert, post) ∧
            post.output = child.output))

/-- Classify the actual constructor setup tail from a retained settled child.
The output-length bound is the exact round-trip premise used by the nonempty
`RETURNDATACOPY`/`REVERT` bubble. -/
theorem ossifiableConstructorDelegateTail_outcome
    {fs : List Func} {sevm : Sevm} {callPre callPost child : Devm}
    {image : Bytes} {out : Execution}
    (hEmpty : fs[3]? = some (Func.revData emptyDelegatecallErrorData))
    (spawn : DelegatecallSpawnDescriptor sevm callPre)
    (settled : DelegatecallSettledBoundary spawn child callPost)
    (outputLength : child.output.length < 2 ^ 256)
    (memoryWf : Mem.Wf callPost.memory)
    (memoryReads : Mem.Reads callPost.memory image)
    (run : Func.RunCompiledTo fs sevm callPost
      ossifiableConstructorDelegateTail out) :
    OssifiableConstructorDelegateOutcome (callPost := callPost)
      fs spawn child image out := by
  rcases settled with
    ⟨certificate, resume, returnData, stack, callState, callTransient,
      callLogs⟩
  obtain ⟨childCertificate⟩ := certificate
  unfold ossifiableConstructorDelegateTail at run
  cases status : child.error.isSome with
  | false =>
      have pOne : (1 : B256) :: spawn.parent.stack <<+ callPost.stack :=
        ⟨[], by simpa [Split, status] using stack⟩
      obtain ⟨afterPre, _, _, branchPop, afterRun, pAfter⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pOne run
      exact .success afterPre ⟨childCertificate⟩ status returnData afterRun
        pAfter (by rw [← branchPop.memory]; exact memoryWf)
        (by rw [← branchPop.memory]; exact memoryReads)
        (branchPop.state.symm.trans callState)
        (branchPop.transientStorage.symm.trans callTransient)
        (branchPop.logs.symm.trans (by simpa [status] using callLogs))
  | true =>
      have pZero : (0 : B256) :: spawn.parent.stack <<+ callPost.stack :=
        ⟨[], by simpa [Split, status] using stack⟩
      obtain ⟨failedPre, failedPop, failedRun, _⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pZero run
      obtain ⟨sizePost, sizeRun, payloadBranch⟩ :=
        runCompiledTo_next_inv failedRun
      have sizePush := of_run_retdatasize_val
        (Ninst.Run.of_runCompiled sizeRun)
      have failedReturnData : failedPre.returnData = child.output :=
        failedPop.returnData.symm.trans returnData
      have childRollback := childCertificate.rollback_of_error status
      have rolledState : callPost.state = spawn.parent.state :=
        callState.trans (childRollback.1.trans rfl)
      have rolledTransient :
          callPost.transientStorage = spawn.parent.transientStorage :=
        callTransient.trans (childRollback.2.trans rfl)
      have rolledLogs : callPost.logs = spawn.parent.logs := by
        simpa [status] using callLogs
      by_cases outputEmpty : child.output = []
      · have pLengthZero : (0 : B256) :: failedPre.stack <<+
            sizePost.stack :=
          ⟨[], by
            simpa [Split, Stack.Push, failedReturnData, outputEmpty,
              show Nat.toB256 0 = (0 : B256) by decide]
              using sizePush.stack⟩
        obtain ⟨errorPre, errorPop, errorRun, _⟩ :=
          Func.RunCompiledTo.zero_branch_of_prefix pLengthZero payloadBranch
        have errorMemory : errorPre.memory = callPost.memory :=
          errorPop.memory.symm.trans
            (sizePush.memory.symm.trans failedPop.memory.symm)
        have errorState : errorPre.state = callPost.state :=
          errorPop.state.symm.trans
            (sizePush.state.symm.trans failedPop.state.symm)
        have errorWf : Mem.Wf errorPre.memory := by
          rw [errorMemory]
          exact memoryWf
        have errorReads : Mem.Reads errorPre.memory image := by
          rw [errorMemory]
          exact memoryReads
        exact .emptyFailure errorPre ⟨childCertificate⟩ status outputEmpty
          returnData rolledState rolledTransient rolledLogs errorState
          (by
            simpa only [ControlErrorOutcome] using
              runCompiledTo_call_revData_frame_inv hEmpty errorWf errorReads
                (by decide +kernel) (by decide +kernel) errorRun)
      · have lengthWordNonzero :
            Nat.toB256 child.output.length ≠ 0 := by
          intro hzero
          have hnat := congrArg B256.toNat hzero
          rw [B256.toNat_toB256_of_lt outputLength,
            B256.toNat_zero] at hnat
          exact outputEmpty (List.length_eq_zero_iff.mp hnat)
        have pLength : Nat.toB256 child.output.length :: failedPre.stack <<+
            sizePost.stack :=
          ⟨[], by
            simpa [Split, Stack.Push, failedReturnData] using sizePush.stack⟩
        obtain ⟨bubblePre, _, _, bubblePop, bubbleRun, _⟩ :=
          Func.RunCompiledTo.succ_branch_of_prefix
            lengthWordNonzero pLength payloadBranch
        have bubbleReturnData : bubblePre.returnData = child.output :=
          bubblePop.returnData.symm.trans
            (sizePush.returnData.symm.trans failedReturnData)
        have bubbleState : bubblePre.state = callPost.state :=
          bubblePop.state.symm.trans
            (sizePush.state.symm.trans failedPop.state.symm)
        rcases Func.runCompiledTo_revReturnData_inv bubbleRun with
          outOfGas | ⟨post, postOutcome, postOutput⟩
        · exact .bubbledFailure bubblePre ⟨childCertificate⟩ status
            outputEmpty returnData rolledState rolledTransient rolledLogs
            bubbleState (Or.inl outOfGas)
        · have exactOutput : post.output = child.output := by
            rw [postOutput, bubbleReturnData,
              B256.toNat_toB256_of_lt outputLength, List.take_length]
          exact .bubbledFailure bubblePre ⟨childCertificate⟩ status
            outputEmpty returnData rolledState rolledTransient rolledLogs
            bubbleState (Or.inr ⟨post, postOutcome, exactOutput⟩)

/-! ## Successful child into the post-setup constructor phase -/

/-- A clean setup child feeds its actual storage and logs into `_changeAdmin`.
In particular, neither ERC-1967 slot is reset to its pre-child value: the
requested admin overwrites only the packed admin word after the event names
the child's post-setup admin as `previousAdmin`; the implementation slot stays
exactly as the child left it. -/
theorem OssifiableConstructorDelegateOutcome.afterSetup_success
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {callPre callPost child post : Devm}
    {spawn : DelegatecallSpawnDescriptor sevm callPre}
    {image runtimeBytes : Bytes} {requestedAdmin : Adr}
    (outcome : OssifiableConstructorDelegateOutcome
      (callPost := callPost)
      (ossifiableConstructorFunctions runtimeOffset runtimeLength)
      spawn child image (.ok post))
    (hrequested :
      Bytes.toB256 (image.sliceD 32 32 0) = requestedAdmin.toB256)
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256) :
    requestedAdmin ≠ 0 ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor child sevm.currentTarget).set adminSlotLit
          (addressSlotWriteWord
            (child.getStorVal sevm.currentTarget adminSlotLit)
            requestedAdmin.toB256) ∧
      post.logs = spawn.parent.logs ++ child.logs ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          (child.getStorVal sevm.currentTarget adminSlotLit)
          requestedAdmin] ∧
      post.output = runtimeBytes := by
  rcases outcome with
    ⟨afterPre, _, _, _, afterRun, pAfter, wfAfter, readsAfter,
      stateAfter, _, logsAfter⟩ |
    ⟨_, _, _, _, _, _, _, _, _, errorOutcome⟩ |
    ⟨_, _, _, _, _, _, _, _, _, bubbleOutcome⟩
  · obtain ⟨bodyPre, burn, bodyRun⟩ := runCompiledTo_call_inv
      (ossifiableConstructorFunctions_afterSetup runtimeOffset runtimeLength)
      afterRun
    have pBody : spawn.parent.stack <<+ bodyPre.stack := by
      rw [← burn.stack]
      exact pAfter
    have wfBody : Mem.Wf bodyPre.memory := by
      rw [← burn.memory]
      exact wfAfter
    have readsBody : Mem.Reads bodyPre.memory image := by
      rw [← burn.memory]
      exact readsAfter
    have bodyToChildState : bodyPre.state = child.state :=
      burn.state.symm.trans stateAfter
    have bodyToChildStor : Devm.getStor bodyPre = Devm.getStor child :=
      funext (getStor_eq_of_state_eq bodyToChildState)
    have bodyAdmin :
        bodyPre.getStorVal sevm.currentTarget adminSlotLit =
          child.getStorVal sevm.currentTarget adminSlotLit := by
      exact congrArg (fun stor => stor.get adminSlotLit)
        (congrFun bodyToChildStor sevm.currentTarget)
    have bodyLogs : bodyPre.logs = spawn.parent.logs ++ child.logs :=
      burn.logs.symm.trans logsAfter
    rcases ossifiableConstructorAfterSetup_success
        (ossifiableConstructorFunctions_zeroAdmin runtimeOffset runtimeLength)
        wfBody readsBody hrequested hruntime hruntimeLength hruntimeNonempty
        hoffsetBound hlengthBound pBody bodyRun with
      ⟨adminNonzero, postStorage, postLogs, postOutput⟩
    refine ⟨adminNonzero, ?_, ?_, postOutput⟩
    · rw [postStorage, congrFun bodyToChildStor sevm.currentTarget,
        bodyAdmin]
    · rw [postLogs, bodyLogs, bodyAdmin, List.append_assoc]
  · rcases errorOutcome with
      ⟨_, impossible, _, _, _⟩ | ⟨_, impossible, _, _, _, _⟩ <;>
        cases impossible
  · rcases bubbleOutcome with
      ⟨_, impossible⟩ | ⟨_, impossible, _⟩ <;> cases impossible

/-- Slot-level projection of `afterSetup_success`.  It makes the constructor's
two mutation guarantees explicit: every clean child rewrite of the
implementation slot survives, while the final admin write uses the child's
post-setup admin word as its packed-word base. -/
theorem OssifiableConstructorDelegateOutcome.afterSetup_success_slots
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {callPre callPost child post : Devm}
    {spawn : DelegatecallSpawnDescriptor sevm callPre}
    {image runtimeBytes : Bytes} {requestedAdmin : Adr}
    (outcome : OssifiableConstructorDelegateOutcome
      (callPost := callPost)
      (ossifiableConstructorFunctions runtimeOffset runtimeLength)
      spawn child image (.ok post))
    (hrequested :
      Bytes.toB256 (image.sliceD 32 32 0) = requestedAdmin.toB256)
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256) :
    requestedAdmin ≠ 0 ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        child.getStorVal sevm.currentTarget implementationSlotLit ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        addressSlotWriteWord
          (child.getStorVal sevm.currentTarget adminSlotLit)
          requestedAdmin.toB256 ∧
      post.logs = spawn.parent.logs ++ child.logs ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          (child.getStorVal sevm.currentTarget adminSlotLit)
          requestedAdmin] ∧
      post.output = runtimeBytes := by
  rcases outcome.afterSetup_success hrequested hruntime hruntimeLength
      hruntimeNonempty hoffsetBound hlengthBound with
    ⟨adminNonzero, storage, logs, output⟩
  refine ⟨adminNonzero, ?_, ?_, logs, output⟩
  · change
      (Devm.getStor post sevm.currentTarget).get implementationSlotLit = _
    rw [storage, Stor.get_set_ne _
      (show adminSlotLit ≠ implementationSlotLit by decide)]
    rfl
  · change (Devm.getStor post sevm.currentTarget).get adminSlotLit = _
    rw [storage, Stor.get_set_self]

end Blanc.ProxyPair
