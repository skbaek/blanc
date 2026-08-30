import Blanc.ProxyPairOssifiableConstructorDecode
import Blanc.ProxyPairOssifiableControlEffects

/-!
# OssifiableProxy constructor implementation check

This module opens the first protected constructor phase after strict ABI
decoding.  It reads the decoded implementation word, performs the word-exact
`EXTCODESIZE` test, and retains either the inherited no-code error call or the
exact implementation-commit continuation.  Address warming is deliberately
not erased; the boundary preserves only storage, logs, and the proof-carrying
memory image across the check.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst
open scoped LogOutputHinv

private def ossifiableConstructorAfterImplementationCommit : Func :=
  [pushB256 128, mload] +++ ((.call 6) <?> (.call 5))

private theorem ossifiableConstructorInitialize_split_shape :
    ossifiableConstructorInitializeImplementation =
      [pushB256 0, mload] +++
        dup 0 ::: extcodesize ::: iszero :::
          ((.call 2) <?>
            upgradeImplementationCommit
              ossifiableConstructorAfterImplementationCommit) := by
  rfl

/-- Exact inherited no-code error route at auxiliary slot 2. -/
inductive OssifiableConstructorNoCodeRoute
    (fs : List Func) (sevm : Sevm) (pre : Devm) (out : Execution)
    (tail : Stack) (image : Bytes) (implementation : B256) : Prop where
  | intro (callPre : Devm)
      (codeSizeWordZero :
        (pre.getCode implementation.toAdr).size.toB256 = 0)
      (run : Func.RunCompiledTo fs sevm callPre (.call 2) out)
      (stack : implementation :: tail <<+ callPre.stack)
      (memoryWf : Mem.Wf callPre.memory)
      (memoryReads : Mem.Reads callPre.memory image)
      (storage : Devm.getStor pre = Devm.getStor callPre)
      (logs : pre.logs = callPre.logs)
      (outcome : ControlErrorOutcome callPre noCodeImplementationErrorData out)

/-- Exact alternatives at the constructor's implementation-code guard.  The
accepted arm has not yet performed the packed implementation write or emitted
`Upgraded`; it retains the actual commit continuation with the decoded word on
top of the stack. -/
inductive OssifiableConstructorImplementationCheckRoute
    (fs : List Func) (sevm : Sevm) (pre : Devm) (out : Execution)
    (tail : Stack) (image : Bytes) (implementation : B256) : Prop where
  | noCode
      (route : OssifiableConstructorNoCodeRoute fs sevm pre out tail image
        implementation)
  | accepted (commitPre : Devm)
      (codeSizeWordNonzero :
        (pre.getCode implementation.toAdr).size.toB256 ≠ 0)
      (run : Func.RunCompiledTo fs sevm commitPre
        (upgradeImplementationCommit
          ossifiableConstructorAfterImplementationCommit) out)
      (stack : implementation :: tail <<+ commitPre.stack)
      (memoryWf : Mem.Wf commitPre.memory)
      (memoryReads : Mem.Reads commitPre.memory image)
      (storage : Devm.getStor pre = Devm.getStor commitPre)
      (logs : pre.logs = commitPre.logs)

/-- The actual constructor implementation check is exhaustive and word-exact.
The no-code arm reaches auxiliary slot 2 with its inherited error payload; the
code-present arm reaches the shared packed-write/`Upgraded` commit fragment.
-/
theorem ossifiableConstructorInitializeImplementation_route
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack} {image : Bytes} {implementation : B256}
    (hNoCode : fs[2]? = some (Func.revData noCodeImplementationErrorData))
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (himplementation :
      Bytes.toB256 (image.sliceD 0 32 0) = implementation)
    (run : Func.RunCompiledTo fs sevm pre
      ossifiableConstructorInitializeImplementation out) :
    OssifiableConstructorImplementationCheckRoute fs sevm pre out tail image
      implementation := by
  rw [ossifiableConstructorInitialize_split_shape] at run
  obtain ⟨loadPost, loadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pImplementation, wfLoad, readsLoad, stateLoad⟩ :=
    of_run_loadWordAt_image (word := 0) (value := implementation)
      hp hwf hreads himplementation loadRun
  have logsLoad := of_run_loadWordAt_logs (word := 0) loadRun
  obtain ⟨dupPost, qdup, run⟩ := runCompiledTo_next_inv run
  obtain ⟨codePost, qcode, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have dupRun := Ninst.Run.of_runCompiled qdup
  have codeRun := Ninst.Run.of_runCompiled qcode
  have zeroRun := Ninst.Run.of_runCompiled qzero
  have pDup := prefix_of_dup_val dupRun (Stack.Nth.head _ _) pImplementation
  have pCodeRaw := prefix_of_extcodesize_val pDup codeRun
  have preToDupState : pre.state = dupPost.state :=
    stateLoad.trans (Ninst.Hinv.inv (f := Devm.state) dupRun)
  have codeAtDup : dupPost.getCode implementation.toAdr =
      pre.getCode implementation.toAdr := by
    unfold Devm.getCode Devm.getAcct
    rw [← preToDupState]
  have pCode :
      (pre.getCode implementation.toAdr).size.toB256 ::
        implementation :: tail <<+ codePost.stack := by
    rw [← codeAtDup]
    exact pCodeRaw.1
  have pTest := prefix_of_iszero zeroRun pCode
  have wfTest : Mem.Wf testPre.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) zeroRun,
      ← pCodeRaw.2,
      ← Ninst.Hinv.inv (f := Devm.memory) dupRun]
    exact wfLoad
  have readsTest : Mem.Reads testPre.memory image := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) zeroRun,
      ← pCodeRaw.2,
      ← Ninst.Hinv.inv (f := Devm.memory) dupRun]
    exact readsLoad
  have prefixStor : Devm.getStor pre = Devm.getStor testPre :=
    (funext (getStor_eq_of_state_eq stateLoad)).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) dupRun).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) codeRun).trans
          (Ninst.Hinv.inv (f := Devm.getStor) zeroRun)))
  have prefixLogs : pre.logs = testPre.logs :=
    logsLoad.trans
      ((Ninst.Hinv.inv (f := Devm.logs) dupRun).trans
        ((Ninst.Hinv.inv (f := Devm.logs) codeRun).trans
          (Ninst.Hinv.inv (f := Devm.logs) zeroRun)))
  by_cases hzero :
      (pre.getCode implementation.toAdr).size.toB256 = 0
  · have pOne : (1 : B256) :: implementation :: tail <<+
        testPre.stack := by
      simpa [hzero, B256.eqCheck] using pTest
    obtain ⟨callPre, _, _, branchPop, callRun, pCall⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) pOne branchRun
    have callWf : Mem.Wf callPre.memory := by
      rw [← branchPop.memory]
      exact wfTest
    have callReads : Mem.Reads callPre.memory image := by
      rw [← branchPop.memory]
      exact readsTest
    have callStor : Devm.getStor pre = Devm.getStor callPre :=
      prefixStor.trans (funext (getStor_eq_of_state_eq branchPop.state))
    have callLogs : pre.logs = callPre.logs :=
      prefixLogs.trans branchPop.logs
    have outcome :
        ControlErrorOutcome callPre noCodeImplementationErrorData out := by
      simpa only [ControlErrorOutcome] using
        runCompiledTo_call_revData_frame_inv hNoCode callWf callReads
          (by decide +kernel) (by decide +kernel) callRun
    exact .noCode ⟨callPre, hzero, callRun, pCall, callWf, callReads,
      callStor, callLogs, outcome⟩
  · have pZero : (0 : B256) :: implementation :: tail <<+
        testPre.stack := by
      simpa [hzero, B256.eqCheck] using pTest
    obtain ⟨commitPre, branchPop, commitRun, pCommit⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
    exact .accepted commitPre hzero commitRun pCommit
      (by rw [← branchPop.memory]; exact wfTest)
      (by rw [← branchPop.memory]; exact readsTest)
      (prefixStor.trans (funext (getStor_eq_of_state_eq branchPop.state)))
      (prefixLogs.trans branchPop.logs)

/-- Initialization either retains the exact no-code outcome or completes the
packed implementation write and `Upgraded` append, stopping immediately before
the decoded setup-length load. -/
inductive OssifiableConstructorImplementationRoute
    (fs : List Func) (sevm : Sevm) (pre : Devm) (out : Execution)
    (tail : Stack) (image : Bytes) (implementation : B256) : Prop where
  | noCode
      (route : OssifiableConstructorNoCodeRoute fs sevm pre out tail image
        implementation)
  | initialized (next : Devm)
      (codeSizeWordNonzero :
        (pre.getCode implementation.toAdr).size.toB256 ≠ 0)
      (run : Func.RunCompiledTo fs sevm next
        ossifiableConstructorAfterImplementationCommit out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory image)
      (storage : Devm.getStor next sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set implementationSlotLit
          (addressSlotUpdateRaw pre sevm.currentTarget
            implementationSlotLit implementation))
      (logs : next.logs = pre.logs ++
        [rawUpgradedLog sevm.currentTarget implementation])

theorem OssifiableConstructorImplementationCheckRoute.commit
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack} {image : Bytes} {implementation : B256}
    (route : OssifiableConstructorImplementationCheckRoute fs sevm pre out
      tail image implementation) :
    OssifiableConstructorImplementationRoute fs sevm pre out tail image
      implementation := by
  rcases route with noCode | ⟨commitPre, hcode, commitRun, pCommit,
      wfCommit, readsCommit, preToCommitStor, preToCommitLogs⟩
  · exact .noCode noCode
  · rcases upgradeImplementationWordCommit_boundary pCommit commitRun with
      ⟨next, nextRun, pNext, nextStor, nextLogs, nextMemory⟩
    refine .initialized next hcode nextRun pNext ?_ ?_ ?_ ?_
    · rw [nextMemory]
      exact wfCommit
    · rw [nextMemory]
      exact readsCommit
    · rw [nextStor]
      change
        (Devm.getStor commitPre sevm.currentTarget).set implementationSlotLit
            ((addressMask &&&
                (Devm.getStor commitPre sevm.currentTarget).get
                  implementationSlotLit) ||| implementation) =
          (Devm.getStor pre sevm.currentTarget).set implementationSlotLit
            ((addressMask &&&
                (Devm.getStor pre sevm.currentTarget).get
                  implementationSlotLit) ||| implementation)
      rw [← congrFun preToCommitStor sevm.currentTarget]
    · rw [nextLogs, ← preToCommitLogs]

/-! ## Empty/nonempty setup selection -/

inductive OssifiableConstructorSetupSelectionRoute
    (fs : List Func) (sevm : Sevm) (pre : Devm) (out : Execution)
    (tail : Stack) (image : Bytes) (length : B256) : Prop where
  | empty (afterPre : Devm)
      (lengthZero : length = 0)
      (run : Func.RunCompiledTo fs sevm afterPre (.call 5) out)
      (stack : tail <<+ afterPre.stack)
      (memoryWf : Mem.Wf afterPre.memory)
      (memoryReads : Mem.Reads afterPre.memory image)
      (storage : Devm.getStor pre = Devm.getStor afterPre)
      (logs : pre.logs = afterPre.logs)
  | nonempty (delegatePre : Devm)
      (lengthNonzero : length ≠ 0)
      (run : Func.RunCompiledTo fs sevm delegatePre (.call 6) out)
      (stack : tail <<+ delegatePre.stack)
      (memoryWf : Mem.Wf delegatePre.memory)
      (memoryReads : Mem.Reads delegatePre.memory image)
      (storage : Devm.getStor pre = Devm.getStor delegatePre)
      (logs : pre.logs = delegatePre.logs)

theorem ossifiableConstructorSetupSelection_route
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack} {image : Bytes} {length : B256}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hlength : Bytes.toB256 (image.sliceD 128 32 0) = length)
    (run : Func.RunCompiledTo fs sevm pre
      ossifiableConstructorAfterImplementationCommit out) :
    OssifiableConstructorSetupSelectionRoute fs sevm pre out tail image
      length := by
  unfold ossifiableConstructorAfterImplementationCommit at run
  obtain ⟨lengthPost, lengthRun, branchRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pLength, wfLength, readsLength, stateLength⟩ :=
    of_run_loadWordAt_image (word := 4) (value := length)
      hp hwf hreads hlength lengthRun
  have logsLength := of_run_loadWordAt_logs (word := 4) lengthRun
  by_cases hzero : length = 0
  · have pZero : (0 : B256) :: tail <<+ lengthPost.stack := by
      simpa [hzero] using pLength
    obtain ⟨afterPre, branchPop, afterRun, pAfter⟩ :=
      ossifiableConstructorEmptySetup_selectsAfterSetup pZero branchRun
    exact .empty afterPre hzero afterRun pAfter
      (by rw [← branchPop.memory]; exact wfLength)
      (by rw [← branchPop.memory]; exact readsLength)
      ((funext (getStor_eq_of_state_eq stateLength)).trans
        (funext (getStor_eq_of_state_eq branchPop.state)))
      (logsLength.trans branchPop.logs)
  · obtain ⟨delegatePre, _, _, branchPop, delegateRun, pDelegate⟩ :=
      ossifiableConstructorNonemptySetup_selectsDelegateSetup
        hzero pLength branchRun
    exact .nonempty delegatePre hzero delegateRun pDelegate
      (by rw [← branchPop.memory]; exact wfLength)
      (by rw [← branchPop.memory]; exact readsLength)
      ((funext (getStor_eq_of_state_eq stateLength)).trans
        (funext (getStor_eq_of_state_eq branchPop.state)))
      (logsLength.trans branchPop.logs)

/-- Apply the implementation-code route directly at an accepted decoder body
boundary, with the implementation fixed to the actual decoded head word. -/
theorem OssifiableConstructorDecodeBoundary.initializeImplementation
    {fs : List Func} {sevm : Sevm} {entry : Devm}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (decode : OssifiableConstructorDecodeBoundary fs sevm entry
      ossifiableConstructorInitializeImplementation argsOffset tail image out)
    (hNoCode : fs[2]? = some (Func.revData noCodeImplementationErrorData)) :
    ∃ bodyPre,
      entry.state = bodyPre.state ∧
      entry.logs = bodyPre.logs ∧
      OssifiableConstructorImplementationCheckRoute fs sevm bodyPre out tail
        (ossifiableConstructorDecodedImage image sevm.code.toList argsOffset)
        (ossifiableConstructorCodeWord sevm.code.toList argsOffset) := by
  rcases decode with
    ⟨bodyPre, bodyRun, pBody, wfBody, readsBody, stateBody, logsBody⟩
  refine ⟨bodyPre, stateBody, logsBody, ?_⟩
  exact ossifiableConstructorInitializeImplementation_route hNoCode pBody
    wfBody readsBody
    (ossifiableConstructorDecodedImage_implementationWord _ _ _) bodyRun

/-- Combined boundary after implementation checking/commit and setup-length
selection.  The setup arm retains the implementation effect separately from
the branch walk so later child settlement can use the actual warmed state. -/
inductive OssifiableConstructorPreparedRoute
    (fs : List Func) (sevm : Sevm) (pre : Devm) (out : Execution)
    (tail : Stack) (image : Bytes) (implementation length : B256) : Prop where
  | noCode
      (route : OssifiableConstructorNoCodeRoute fs sevm pre out tail image
        implementation)
  | setup (next : Devm)
      (codeSizeWordNonzero :
        (pre.getCode implementation.toAdr).size.toB256 ≠ 0)
      (storage : Devm.getStor next sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set implementationSlotLit
          (addressSlotUpdateRaw pre sevm.currentTarget
            implementationSlotLit implementation))
      (logs : next.logs = pre.logs ++
        [rawUpgradedLog sevm.currentTarget implementation])
      (selection : OssifiableConstructorSetupSelectionRoute fs sevm next out
        tail image length)

theorem OssifiableConstructorImplementationRoute.selectSetup
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack} {image : Bytes} {implementation length : B256}
    (route : OssifiableConstructorImplementationRoute fs sevm pre out tail
      image implementation)
    (hlength : Bytes.toB256 (image.sliceD 128 32 0) = length) :
    OssifiableConstructorPreparedRoute fs sevm pre out tail image
      implementation length := by
  rcases route with noCode | ⟨next, hcode, nextRun, pNext, wfNext,
      readsNext, nextStor, nextLogs⟩
  · exact .noCode noCode
  · exact .setup next hcode nextStor nextLogs
      (ossifiableConstructorSetupSelection_route pNext wfNext readsNext
        hlength nextRun)

end Blanc.ProxyPair
