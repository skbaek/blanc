import Blanc.ProxyPairOssifiableConstructorExecution

/-!
# OssifiableProxy nonempty constructor setup

This module composes the execution-derived constructor decoder, implementation
commit, exact delegated setup boundary, retained child settlement, and the
post-setup admin/runtime tail.  It does not evaluate the whole CREATE message:
the child is the exact message spawned by the compiled `DELEGATECALL`, and its
storage and logs remain visible in the result.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

private theorem DelegatecallSpawnDescriptor.parent_state_eq_callPre
    {sevm : Sevm} {callPre : Devm}
    (spawn : DelegatecallSpawnDescriptor sevm callPre) :
    spawn.parent.state = callPre.state := by
  have delegationState := congrArg
    (fun result : Bool × Adr × ByteArray × Nat × Devm =>
      result.2.2.2.2.state)
    spawn.delegationEq
  change spawn.afterAccess.state = callPre.state
  rw [← delegationState]
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress
      ((addAccessedAddress
        (callPre.setMach
          ⟨spawn.stackTail, callPre.memory, callPre.gasLeft⟩)
        spawn.codeWord.toAdr).state.getCode spawn.codeWord.toAdr) <;> rfl

private theorem DelegatecallSpawnDescriptor.parent_logs_eq_callPre
    {sevm : Sevm} {callPre : Devm}
    (spawn : DelegatecallSpawnDescriptor sevm callPre) :
    spawn.parent.logs = callPre.logs := by
  have delegationLogs := congrArg
    (fun result : Bool × Adr × ByteArray × Nat × Devm =>
      result.2.2.2.2.logs)
    spawn.delegationEq
  change spawn.afterAccess.logs = callPre.logs
  rw [← delegationLogs]
  dsimp only [accessDelegation]
  cases getDelegatedCodeAddress
      ((addAccessedAddress
        (callPre.setMach
          ⟨spawn.stackTail, callPre.memory, callPre.gasLeft⟩)
        spawn.codeWord.toAdr).state.getCode spawn.codeWord.toAdr) <;> rfl

/-- A setup tail that finishes successfully can only have resumed a clean
child.  The failed-child side always reaches either the inherited empty error
or `revReturnData`; the proof does not need a mathematical bound on the
returndata list length because it branches on its actual `B256` length word. -/
theorem OssifiableConstructorDelegateOutcome.success_of_ok
    {fs : List Func} {sevm : Sevm} {callPre callPost child post : Devm}
    {spawn : DelegatecallSpawnDescriptor sevm callPre} {image : Bytes}
    (hEmpty : fs[3]? = some (Func.revData emptyDelegatecallErrorData))
    (settled : DelegatecallSettledBoundary spawn child callPost)
    (memoryWf : Mem.Wf callPost.memory)
    (memoryReads : Mem.Reads callPost.memory image)
    (run : Func.RunCompiledTo fs sevm callPost
      ossifiableConstructorDelegateTail (.ok post)) :
    child.error.isSome = false ∧
      OssifiableConstructorDelegateOutcome (callPost := callPost)
        fs spawn child image (.ok post) := by
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
      refine ⟨rfl, .success afterPre ⟨childCertificate⟩ status
        returnData afterRun pAfter ?_ ?_ ?_ ?_ ?_⟩
      · rw [← branchPop.memory]
        exact memoryWf
      · rw [← branchPop.memory]
        exact memoryReads
      · exact branchPop.state.symm.trans callState
      · exact branchPop.transientStorage.symm.trans callTransient
      · exact branchPop.logs.symm.trans (by simpa [status] using callLogs)
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
      by_cases lengthWordZero : Nat.toB256 child.output.length = 0
      · have pLengthZero : (0 : B256) :: failedPre.stack <<+
            sizePost.stack :=
          ⟨[], by
            simpa [Split, Stack.Push, failedReturnData, lengthWordZero]
              using sizePush.stack⟩
        obtain ⟨_, _, errorRun, _⟩ :=
          Func.RunCompiledTo.zero_branch_of_prefix pLengthZero payloadBranch
        exact (Func.RunCompiledTo.not_ok_call_revData hEmpty errorRun).elim
      · have pLength : Nat.toB256 child.output.length :: failedPre.stack <<+
            sizePost.stack :=
          ⟨[], by
            simpa [Split, Stack.Push, failedReturnData] using sizePush.stack⟩
        obtain ⟨_, _, _, _, bubbleRun, _⟩ :=
          Func.RunCompiledTo.succ_branch_of_prefix
            lengthWordZero pLength payloadBranch
        rcases Func.runCompiledTo_revReturnData_inv bubbleRun with
          outOfGas | ⟨revertPost, revertOutcome, _⟩
        · rcases outOfGas with ⟨_, impossible⟩
          cases impossible
        · cases revertOutcome

/-- Open an actual successful setup boundary for any descriptor of its retained
compiled call.  The conclusion fixes every call operand and the child input,
then exposes the exact child-written slots, child logs, post-setup admin event,
runtime output, and requested-admin write. -/
theorem OssifiableConstructorDelegateBoundary.success_child_slots
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {pre post : Devm} {tail : Stack}
    {decodedImage runtimeBytes setupData : Bytes}
    {implementation : B256} {requestedAdmin : Adr}
    (boundary : OssifiableConstructorDelegateBoundary
      (ossifiableConstructorFunctions runtimeOffset runtimeLength)
      sevm pre tail decodedImage implementation setupData (.ok post))
    (setupLengthBound : setupData.length < 2 ^ 256)
    (setupImage :
      decodedImage.sliceD 0x100 setupData.length 0 = setupData)
    (hrequested :
      Bytes.toB256 (decodedImage.sliceD 32 32 0) =
        requestedAdmin.toB256)
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256) :
    ∃ gasWord callPre callPost,
      Ninst.RunCompiled sevm callPre (.exec .delcall) callPost ∧
      ∀ spawn : DelegatecallSpawnDescriptor sevm callPre,
        spawn.parent.stack.length < 1024 →
          spawn.gasWord = gasWord ∧
          spawn.codeWord = implementation ∧
          spawn.inputOffsetWord = 0x100 ∧
          spawn.inputSizeWord = Nat.toB256 setupData.length ∧
          spawn.outputOffsetWord = 0 ∧
          spawn.outputSizeWord = 0 ∧
          spawn.parent.state = pre.state ∧
          spawn.parent.logs = pre.logs ∧
          requestedAdmin ≠ 0 ∧
          ∃ child : Devm,
            spawn.child.data = setupData ∧
            child.error.isSome = false ∧
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
  rcases boundary.settled_child_exact setupLengthBound setupImage with
    ⟨gasWord, callPre, callPost, callRun, tailRun, preState, preLogs,
      retained⟩
  refine ⟨gasWord, callPre, callPost, callRun, ?_⟩
  intro spawn room
  rcases retained spawn room with
    ⟨gasEq, codeEq, inputOffsetEq, inputSizeEq, outputOffsetEq,
      outputSizeEq, childData, child, settled, postWf, postReads⟩
  obtain ⟨childClean, outcome⟩ :=
    OssifiableConstructorDelegateOutcome.success_of_ok
      (ossifiableConstructorFunctions_emptyDelegatecall runtimeOffset
        runtimeLength)
      settled postWf postReads tailRun
  rcases outcome.afterSetup_success_slots hrequested hruntime hruntimeLength
      hruntimeNonempty hoffsetBound hlengthBound with
    ⟨adminNonzero, implementationSlot, adminSlot, logs, output⟩
  exact ⟨gasEq, codeEq, inputOffsetEq, inputSizeEq, outputOffsetEq,
    outputSizeEq,
    (DelegatecallSpawnDescriptor.parent_state_eq_callPre spawn).trans
      preState.symm,
    (DelegatecallSpawnDescriptor.parent_logs_eq_callPre spawn).trans
      preLogs.symm,
    adminNonzero, child, childData, childClean, implementationSlot,
    adminSlot, logs, output⟩

/-- A successful accepted decoder carrying nonempty setup bytes necessarily
passes through the implementation commit and the actual delegated setup
boundary.  This is the missing composition seam between the whole-constructor
carrier and `success_child_slots`; it retains the `Upgraded` chronology and
does not assume either slot survives the child. -/
theorem OssifiableConstructorPreparedSuccess.nonempty_delegate_boundary
    {runtimeOffset runtimeLength argsOffset : Nat}
    {sevm : Sevm} {entry post : Devm} {tail : Stack}
    {image setupData : Bytes} {implementation requestedAdmin : B256}
    {bodyPre : Devm}
    (success : OssifiableConstructorPreparedSuccess runtimeOffset
      runtimeLength argsOffset sevm entry post tail image implementation
      requestedAdmin setupData bodyPre)
    (setupDataNonempty : setupData ≠ []) :
    ∃ next delegatePre,
      Devm.getStor next sevm.currentTarget =
        (Devm.getStor bodyPre sevm.currentTarget).set
          implementationSlotLit
          (addressSlotUpdateRaw bodyPre sevm.currentTarget
            implementationSlotLit implementation) ∧
      next.logs = bodyPre.logs ++
        [rawUpgradedLog sevm.currentTarget implementation] ∧
      Devm.getStor next = Devm.getStor delegatePre ∧
      next.logs = delegatePre.logs ∧
      OssifiableConstructorDelegateBoundary
        (ossifiableConstructorFunctions runtimeOffset runtimeLength)
        sevm delegatePre tail
        (ossifiableConstructorDecodedImage image sevm.code.toList argsOffset)
        implementation setupData (.ok post) := by
  have setupLengthNonzero : Nat.toB256 setupData.length ≠ 0 := by
    intro hzero
    have hnat := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt success.setupLengthBound,
      B256.toNat_zero] at hnat
    exact setupDataNonempty (List.length_eq_zero_iff.mp hnat)
  rcases success.prepared with noCode | ⟨next, _, nextStorage, nextLogs,
      selection⟩
  · rcases noCode with ⟨_, _, _, _, _, _, _, _, noCodeOutcome⟩
    rcases noCodeOutcome with
      ⟨_, impossible, _, _, _⟩ | ⟨_, impossible, _, _, _, _⟩ <;>
        cases impossible
  · rcases selection.delegate_boundary setupLengthNonzero
        (ossifiableConstructorFunctions_delegateSetup runtimeOffset
          runtimeLength)
        success.implementationImage success.setupLengthImage with
      ⟨delegatePre, storage, logs, boundary⟩
    exact ⟨next, delegatePre, nextStorage, nextLogs, storage, logs,
      boundary⟩

/-! ## Whole-program nonempty success -/

/-- Source-order certificate for a successful complete constructor carrying
nonempty setup data.  The implementation write and `Upgraded` log precede
the exact compiled child call.  For every descriptor of that retained call,
the actual clean child supplies both post-setup slot words and its logs; the
requested-admin write and `AdminChanged` event are then derived from those
child observations rather than from the pre-setup state. -/
structure OssifiableConstructorNonemptySuccessResult
    (runtimeOffset runtimeLength : Nat)
    (sevm : Sevm) (entry post : Devm) (tail : Stack)
    (image runtimeBytes setupData : Bytes)
    (implementation requestedAdmin : B256) : Prop where
  accepted :
    ossifiableConstructorDecodeSpec sevm.code.toList
      (runtimeOffset + runtimeLength) =
        .accepted implementation requestedAdmin setupData
  setupDataNonempty : setupData ≠ []
  requestedAdminCanonical : requestedAdmin.toAdr.toB256 = requestedAdmin
  witnesses : ∃ bodyPre next delegatePre gasWord callPre callPost,
    entry.state = bodyPre.state ∧
    entry.logs = bodyPre.logs ∧
    Devm.getStor next sevm.currentTarget =
      (Devm.getStor bodyPre sevm.currentTarget).set
        implementationSlotLit
        (addressSlotUpdateRaw bodyPre sevm.currentTarget
          implementationSlotLit implementation) ∧
    next.logs = bodyPre.logs ++
      [rawUpgradedLog sevm.currentTarget implementation] ∧
    Devm.getStor next = Devm.getStor delegatePre ∧
    next.logs = delegatePre.logs ∧
    Ninst.RunCompiled sevm callPre (.exec .delcall) callPost ∧
    ∀ spawn : DelegatecallSpawnDescriptor sevm callPre,
      spawn.parent.stack.length < 1024 →
        spawn.gasWord = gasWord ∧
        spawn.codeWord = implementation ∧
        spawn.inputOffsetWord = 0x100 ∧
        spawn.inputSizeWord = Nat.toB256 setupData.length ∧
        spawn.outputOffsetWord = 0 ∧
        spawn.outputSizeWord = 0 ∧
        spawn.parent.state = delegatePre.state ∧
        spawn.parent.logs = delegatePre.logs ∧
        requestedAdmin.toAdr ≠ 0 ∧
        ∃ child : Devm,
          spawn.child.data = setupData ∧
          child.error.isSome = false ∧
          post.getStorVal sevm.currentTarget implementationSlotLit =
            child.getStorVal sevm.currentTarget implementationSlotLit ∧
          post.getStorVal sevm.currentTarget adminSlotLit =
            addressSlotWriteWord
              (child.getStorVal sevm.currentTarget adminSlotLit)
              requestedAdmin ∧
          post.logs = entry.logs ++
            [rawUpgradedLog sevm.currentTarget implementation] ++
            child.logs ++
            [ossifiableConstructorAdminChangedLog sevm.currentTarget
              (child.getStorVal sevm.currentTarget adminSlotLit)
              requestedAdmin.toAdr] ∧
          post.output = runtimeBytes

/-- Lift the complete compiled creation program into the nonempty source-order
certificate.  The decoder equality identifies the caller-named ABI values;
all call operands, the child calldata, post-setup slot observations, log
chronology, and returned runtime then come from the actual program walk. -/
theorem ossifiableConstructorProgram_nonempty_success
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {entry post : Devm} {tail : Stack}
    {image runtimeBytes setupData : Bytes}
    {implementation requestedAdmin : B256}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : runtimeOffset + runtimeLength + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hspec :
      ossifiableConstructorDecodeSpec sevm.code.toList
        (runtimeOffset + runtimeLength) =
          .accepted implementation requestedAdmin setupData)
    (setupDataNonempty : setupData ≠ [])
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256)
    (run : Prog.RunCompiledTo sevm entry
      (ossifiableConstructorProgram runtimeOffset
        (runtimeOffset + runtimeLength) runtimeLength) (.ok post)) :
    OssifiableConstructorNonemptySuccessResult runtimeOffset runtimeLength
      sevm entry post tail image runtimeBytes setupData implementation
      requestedAdmin := by
  rcases ossifiableConstructorProgram_prepare_of_ok hp hwf hreads
      hcoordinate hcodeSize run with
    ⟨decodePre, actualImplementation, actualRequestedAdmin, actualSetupData,
      bodyPre, entryDecodeState, entryDecodeLogs, _, success⟩
  have acceptedEq :
      OssifiableConstructorDecodeResult.accepted actualImplementation
          actualRequestedAdmin actualSetupData =
        .accepted implementation requestedAdmin setupData :=
    success.spec.symm.trans hspec
  injection acceptedEq with implementationEq requestedAdminEq setupDataEq
  subst actualImplementation
  subst actualRequestedAdmin
  subst actualSetupData
  have requestedAdminCanonical :
      requestedAdmin.toAdr.toB256 = requestedAdmin :=
    toB256_toAdr (validAdr_iff.mpr success.requestedAdminClean)
  rcases success.nonempty_delegate_boundary setupDataNonempty with
    ⟨next, delegatePre, implementationStorage, upgradedLogs,
      delegateStorage, delegateLogs, boundary⟩
  rcases boundary.success_child_slots success.setupLengthBound
      success.setupImage
      (success.requestedAdminImage.trans requestedAdminCanonical.symm)
      hruntime hruntimeLength hruntimeNonempty hoffsetBound hlengthBound with
    ⟨gasWord, callPre, callPost, callRun, settled⟩
  refine ⟨hspec, setupDataNonempty, requestedAdminCanonical, bodyPre, next,
    delegatePre, gasWord, callPre, callPost,
    entryDecodeState.trans success.entryState,
    entryDecodeLogs.trans success.entryLogs, implementationStorage,
    upgradedLogs, delegateStorage, delegateLogs, callRun, ?_⟩
  intro spawn room
  rcases settled spawn room with
    ⟨gasEq, codeEq, inputOffsetEq, inputSizeEq, outputOffsetEq,
      outputSizeEq, parentState, parentLogs, adminNonzero, child,
      childData, childClean, implementationSlot, adminSlot, logs, output⟩
  refine ⟨gasEq, codeEq, inputOffsetEq, inputSizeEq, outputOffsetEq,
    outputSizeEq, parentState, parentLogs, adminNonzero, child, childData,
    childClean, implementationSlot, ?_, ?_, output⟩
  · simpa only [requestedAdminCanonical] using adminSlot
  · rw [logs, parentLogs, ← delegateLogs, upgradedLogs,
      ← (entryDecodeLogs.trans success.entryLogs), List.append_assoc]

end Blanc.ProxyPair
