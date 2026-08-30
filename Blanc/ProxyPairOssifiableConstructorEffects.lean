import Blanc.ProxyPairOssifiableConstructor
import Blanc.ProxyPairOssifiableControlEffects

/-!
# OssifiableProxy constructor phase effects

This module opens the executable constructor after optional setup.  Its main
success theorem starts from the actual compiled `afterSetup` function, reads
the admin slot at that point (not before the child), emits the source-ordered
event, validates the requested admin, performs the packed slot write, copies
the appended runtime, and returns exactly that runtime window.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst
open scoped LogOutputHinv

private def ossifiableConstructorCommitAndReturn
    (runtimeOffset runtimeLength : Nat) : Func :=
  [pushB256 32, mload] +++
    storeAddressWordAt adminSlotLit +++
    ossifiablePushCreationCoordinate runtimeLength :::
      ossifiablePushCreationCoordinate runtimeOffset :::
      pushB256 0 ::: codecopy :::
    ossifiablePushCreationCoordinate runtimeLength :::
      pushB256 0 ::: Func.ret

private def ossifiableConstructorAfterSetupBranch
    (runtimeOffset runtimeLength : Nat) : Func :=
  (.call 4) <?>
    ossifiableConstructorCommitAndReturn runtimeOffset runtimeLength

private def ossifiableConstructorEventImage
    (image : Bytes) (oldRaw requested : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt image 160 (addressSlotReadWord oldRaw).toBytes)
    192 requested.toBytes

private def OssifiableConstructorAfterSetupCheckpoint
    (fs : List Func) (sevm : Sevm) (pre : Devm) (out : Execution)
    (tail : Stack) (image : Bytes) (requestedAdmin : Adr)
    (runtimeOffset runtimeLength : Nat) : Prop :=
  ∃ checkpoint : Devm,
    (requestedAdmin.toB256 =? 0) :: tail <<+ checkpoint.stack ∧
    Mem.Wf checkpoint.memory ∧
    Mem.Reads checkpoint.memory
      (ossifiableConstructorEventImage image
        (pre.getStorVal sevm.currentTarget adminSlotLit)
        requestedAdmin.toB256) ∧
    Devm.getStor pre = Devm.getStor checkpoint ∧
    checkpoint.logs = pre.logs ++
      [ossifiableConstructorAdminChangedLog sevm.currentTarget
        (pre.getStorVal sevm.currentTarget adminSlotLit)
        requestedAdmin] ∧
    Func.RunCompiledTo fs sevm checkpoint
      (ossifiableConstructorAfterSetupBranch runtimeOffset runtimeLength)
      out

private theorem ossifiableConstructorAfterSetup_semantic_shape
    (runtimeOffset runtimeLength : Nat) :
    ossifiableConstructorAfterSetup runtimeOffset runtimeLength =
      loadAddressWordAt adminSlotLit +++
        mstoreAt 5 +++
        [pushB256 32, mload] +++
        mstoreAt 6 +++
        pushB256 adminChangedEventTopic ::: logWith 0 5 2 +++
        [pushB256 32, mload] +++ iszero :::
        ossifiableConstructorAfterSetupBranch runtimeOffset runtimeLength := by
  rfl

private theorem ossifiableConstructorAfterSetup_checkpoint
    {runtimeOffset runtimeLength : Nat}
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack} {image : Bytes} {requestedAdmin : Adr}
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hrequested :
      Bytes.toB256 (image.sliceD 32 32 0) = requestedAdmin.toB256)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (ossifiableConstructorAfterSetup runtimeOffset runtimeLength)
      out) :
    OssifiableConstructorAfterSetupCheckpoint fs sevm pre out tail image
      requestedAdmin runtimeOffset runtimeLength := by
  rw [ossifiableConstructorAfterSetup_semantic_shape] at run
  obtain ⟨readPost, readRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pPrevious, readMemory, readLogs, readStor⟩ :=
    of_loadAddressWordAt_val hp readRun
  have pPrevious' :
      addressSlotReadWord
          (pre.getStorVal sevm.currentTarget adminSlotLit) :: tail <<+
        readPost.stack := pPrevious
  have readWf : Mem.Wf readPost.memory := by
    rw [readMemory]
    exact hwf
  have readReads : Mem.Reads readPost.memory image := by
    rw [readMemory]
    exact hreads
  obtain ⟨oldPost, oldStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pOld, oldWf, oldReads, oldState⟩ :=
    of_run_mstoreAt_image pPrevious' readWf readReads oldStoreRun
  let oldImage := Bytes.writeAt image 160
    (addressSlotReadWord
      (pre.getStorVal sevm.currentTarget adminSlotLit)).toBytes
  have oldReads' : Mem.Reads oldPost.memory oldImage := by
    simpa only [oldImage, show ((5 : B256) * 32).toNat = 160 by decide]
      using oldReads
  have requestedInOldImage :
      Bytes.toB256 (oldImage.sliceD 32 32 0) = requestedAdmin.toB256 := by
    unfold oldImage
    rw [Bytes.readWord_writeAt_of_disjoint image 32 160 _ (by omega),
      hrequested]
  obtain ⟨requestedPost, requestedLoadRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pRequested, requestedWf, requestedReads, requestedState⟩ :=
    of_run_loadWordAt_image (word := 1)
      (value := requestedAdmin.toB256) pOld oldWf oldReads'
      requestedInOldImage requestedLoadRun
  obtain ⟨newPost, newStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pNew, newWf, newReads, newState⟩ :=
    of_run_mstoreAt_image pRequested requestedWf requestedReads
      newStoreRun
  let eventImage := ossifiableConstructorEventImage image
    (pre.getStorVal sevm.currentTarget adminSlotLit) requestedAdmin.toB256
  have newReads' : Mem.Reads newPost.memory eventImage := by
    simpa only [eventImage, ossifiableConstructorEventImage, oldImage,
      show ((6 : B256) * 32).toNat = 192 by decide]
      using newReads
  obtain ⟨topicPost, qtopic, run⟩ := runCompiledTo_next_inv run
  have topicPush := of_run_pushB256 (Ninst.Run.of_runCompiled qtopic)
  have pTopic := prefix_of_push topicPush pNew
  have topicWf : Mem.Wf topicPost.memory := by
    rw [← topicPush.memory]
    exact newWf
  have topicReads : Mem.Reads topicPost.memory eventImage := by
    rw [← topicPush.memory]
    exact newReads'
  obtain ⟨logPost, logRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pLogged, logsRaw⟩ :=
    of_logWith_val (k := 0) (x := 5) (y := 2)
      (topics := [adminChangedEventTopic]) (by simp)
      (by simpa using pTopic) logRun
  obtain ⟨logWf, logReads⟩ :=
    of_logWith_image topicWf topicReads logRun
  have logData :
      (topicPost.memory.read 160 64).1 =
        (addressSlotReadWord
          (pre.getStorVal sevm.currentTarget adminSlotLit)).toBytes ++
          requestedAdmin.toB256.toBytes := by
    rw [Mem.Reads.read topicReads]
    simpa only [eventImage, ossifiableConstructorEventImage] using
      Bytes.read_two_word_writes_at image 160
        (addressSlotReadWord
          (pre.getStorVal sevm.currentTarget adminSlotLit))
        requestedAdmin.toB256
  have preToTopicLogs : pre.logs = topicPost.logs :=
    readLogs.symm.trans
      ((Line.of_inv Devm.logs (by line_inv) oldStoreRun).trans
        ((of_run_loadWordAt_logs (word := 1) requestedLoadRun).trans
          ((Line.of_inv Devm.logs (by line_inv) newStoreRun).trans
            topicPush.logs)))
  have logged : logPost.logs = pre.logs ++
      [ossifiableConstructorAdminChangedLog sevm.currentTarget
        (pre.getStorVal sevm.currentTarget adminSlotLit)
        requestedAdmin] := by
    rw [logsRaw,
      show ((5 : B256) * 32).toNat = 160 by decide,
      show ((2 : B256) * 32).toNat = 64 by decide,
      logData, ← preToTopicLogs]
    rfl
  have requestedInEventImage :
      Bytes.toB256 (eventImage.sliceD 32 32 0) =
        requestedAdmin.toB256 := by
    unfold eventImage ossifiableConstructorEventImage
    rw [Bytes.readWord_writeAt_of_disjoint _ 32 192 _ (by omega),
      Bytes.readWord_writeAt_of_disjoint image 32 160 _ (by omega),
      hrequested]
  obtain ⟨testLoadPost, testLoadRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pTestValue, testWf, testReads, testState⟩ :=
    of_run_loadWordAt_image (word := 1)
      (value := requestedAdmin.toB256) pLogged logWf logReads
      requestedInEventImage testLoadRun
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have zeroRun := Ninst.Run.of_runCompiled qzero
  have pTest := prefix_of_iszero zeroRun pTestValue
  have zeroMemory : testLoadPost.memory = testPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) zeroRun
  have checkpointWf : Mem.Wf testPre.memory := by
    rw [← zeroMemory]
    exact testWf
  have checkpointReads : Mem.Reads testPre.memory eventImage := by
    rw [← zeroMemory]
    exact testReads
  have preToTestStor : Devm.getStor pre = Devm.getStor testPre :=
    readStor.symm.trans
      ((funext (getStor_eq_of_state_eq oldState)).trans
        ((funext (getStor_eq_of_state_eq requestedState)).trans
          ((funext (getStor_eq_of_state_eq newState)).trans
            ((funext (getStor_eq_of_state_eq topicPush.state)).trans
              ((Line.of_inv Devm.getStor (by line_inv) logRun).trans
                ((funext (getStor_eq_of_state_eq testState)).trans
                  (Ninst.Hinv.inv (f := Devm.getStor) zeroRun)))))))
  have zeroLogs : testLoadPost.logs = testPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) zeroRun
  have checkpointLogs : testPre.logs = pre.logs ++
      [ossifiableConstructorAdminChangedLog sevm.currentTarget
        (pre.getStorVal sevm.currentTarget adminSlotLit)
        requestedAdmin] :=
    (zeroLogs.symm.trans
      (of_run_loadWordAt_logs (word := 1) testLoadRun).symm).trans logged
  refine ⟨testPre, pTest, checkpointWf, ?_, preToTestStor,
    checkpointLogs, branchRun⟩
  simpa only [eventImage] using checkpointReads

private theorem ossifiableConstructorAfterSetup_success_of_checkpoint
    {runtimeOffset runtimeLength : Nat}
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {tail : Stack} {image runtimeBytes : Bytes}
    {requestedAdmin : Adr}
    (hZeroAdmin : fs[4]? = some (Func.revData zeroAdminErrorData))
    (hrequested :
      Bytes.toB256 (image.sliceD 32 32 0) = requestedAdmin.toB256)
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256)
    (checkpoint : OssifiableConstructorAfterSetupCheckpoint fs sevm pre
      (.ok post)
      tail image requestedAdmin runtimeOffset runtimeLength) :
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
  unfold OssifiableConstructorAfterSetupCheckpoint at checkpoint
  rcases checkpoint with
    ⟨testPre, pTest, testWf, testReads, preToTestStor, testLogs, branchRun⟩
  unfold ossifiableConstructorAfterSetupBranch at branchRun
  let eventImage := ossifiableConstructorEventImage image
    (pre.getStorVal sevm.currentTarget adminSlotLit) requestedAdmin.toB256
  have testReads' : Mem.Reads testPre.memory eventImage := by
    simpa only [eventImage] using testReads
  have requestedInEventImage :
      Bytes.toB256 (eventImage.sliceD 32 32 0) =
        requestedAdmin.toB256 := by
    unfold eventImage ossifiableConstructorEventImage
    rw [Bytes.readWord_writeAt_of_disjoint _ 32 192 _ (by omega),
      Bytes.readWord_writeAt_of_disjoint image 32 160 _ (by omega),
      hrequested]
  by_cases requestedWordZero : requestedAdmin.toB256 = 0
  · have pOne : (1 : B256) :: tail <<+ testPre.stack := by
      simpa [requestedWordZero, B256.eqCheck] using pTest
    obtain ⟨callPre, _, _, _, callRun, _⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) pOne branchRun
    exact (Func.RunCompiledTo.not_ok_call_revData hZeroAdmin callRun).elim
  · have requestedNonzero : requestedAdmin ≠ 0 := by
      intro requestedZero
      subst requestedAdmin
      exact requestedWordZero (by decide)
    have pZero : (0 : B256) :: tail <<+ testPre.stack := by
      simpa [requestedWordZero, B256.eqCheck] using pTest
    obtain ⟨writePre, branchPop, writeRun, pWrite⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
    unfold ossifiableConstructorCommitAndReturn at writeRun
    have writeWf : Mem.Wf writePre.memory := by
      rw [← branchPop.memory]
      exact testWf
    have writeReads : Mem.Reads writePre.memory eventImage := by
      rw [← branchPop.memory]
      exact testReads'
    obtain ⟨writeLoadPost, writeLoadRun, writeRun⟩ :=
      runCompiledTo_prepend_inv writeRun
    obtain ⟨pWriteValue, _, _, writeLoadState⟩ :=
      of_run_loadWordAt_image (word := 1)
        (value := requestedAdmin.toB256) pWrite writeWf writeReads
        requestedInEventImage writeLoadRun
    obtain ⟨storedPost, storeRun, writeRun⟩ :=
      runCompiledTo_prepend_inv writeRun
    obtain ⟨pStored, storedStor, _, storedLogs⟩ :=
      of_storeAddressWordAt_val pWriteValue storeRun
    obtain ⟨lengthPost, qlength, writeRun⟩ :=
      runCompiledTo_next_inv writeRun
    have lengthPush := of_run_push
      (Ninst.Run.of_runCompiled qlength)
    have pLength : Nat.toB256 runtimeLength :: tail <<+
        lengthPost.stack := by
      simpa [ossifiablePushCreationCoordinate, B256.toB256_toBytes] using
        prefix_of_push lengthPush pStored
    obtain ⟨offsetPost, qoffset, writeRun⟩ :=
      runCompiledTo_next_inv writeRun
    have offsetPush := of_run_push
      (Ninst.Run.of_runCompiled qoffset)
    have pOffset : Nat.toB256 runtimeOffset ::
        Nat.toB256 runtimeLength :: tail <<+ offsetPost.stack := by
      simpa [ossifiablePushCreationCoordinate, B256.toB256_toBytes] using
        prefix_of_push offsetPush pLength
    obtain ⟨zeroPost, qcopyZero, writeRun⟩ :=
      runCompiledTo_next_inv writeRun
    have copyZeroPush := of_run_pushB256
      (Ninst.Run.of_runCompiled qcopyZero)
    have pCopy : (0 : B256) :: Nat.toB256 runtimeOffset ::
        Nat.toB256 runtimeLength :: tail <<+ zeroPost.stack :=
      prefix_of_push copyZeroPush pOffset
    obtain ⟨copyPost, qcopy, writeRun⟩ :=
      runCompiledTo_next_inv writeRun
    have copyRun := Ninst.Run.of_runCompiled qcopy
    obtain ⟨pCopied, copyMemory⟩ := prefix_of_codecopy_val copyRun pCopy
    obtain ⟨returnLengthPost, qreturnLength, writeRun⟩ :=
      runCompiledTo_next_inv writeRun
    have returnLengthPush := of_run_push
      (Ninst.Run.of_runCompiled qreturnLength)
    have pReturnLength : Nat.toB256 runtimeLength :: tail <<+
        returnLengthPost.stack := by
      simpa [ossifiablePushCreationCoordinate, B256.toB256_toBytes] using
        prefix_of_push returnLengthPush pCopied
    obtain ⟨returnPre, qreturnZero, returnRun⟩ :=
      runCompiledTo_next_inv writeRun
    have returnZeroPush := of_run_pushB256
      (Ninst.Run.of_runCompiled qreturnZero)
    have pReturn : (0 : B256) :: Nat.toB256 runtimeLength :: tail <<+
        returnPre.stack := prefix_of_push returnZeroPush pReturnLength
    have returnRunOk : Func.Run fs sevm returnPre Func.ret post :=
      Func.Run.of_runCompiled
        (Func.RunCompiled.of_runCompiledTo_ok returnRun)
    have outputRaw := (of_run_ret_val pReturn returnRunOk).1
    have outputExact : post.output = runtimeBytes := by
      rw [outputRaw, show (0 : B256).toNat = 0 by rfl,
        B256.toNat_toB256_of_lt hlengthBound,
        ← returnZeroPush.memory, ← returnLengthPush.memory, copyMemory,
        B256.toNat_toB256_of_lt hoffsetBound,
        B256.toNat_toB256_of_lt hlengthBound, hruntime,
        ← hruntimeLength]
      exact Mem.read_write_zero zeroPost.memory hruntimeNonempty
    have preToWriteStor : Devm.getStor pre = Devm.getStor writeLoadPost :=
      preToTestStor.trans
        ((funext (getStor_eq_of_state_eq branchPop.state)).trans
          (funext (getStor_eq_of_state_eq writeLoadState)))
    have storedToPostStor :
        Devm.getStor storedPost = Devm.getStor post :=
      (funext (getStor_eq_of_state_eq lengthPush.state)).trans
        ((funext (getStor_eq_of_state_eq offsetPush.state)).trans
          ((funext (getStor_eq_of_state_eq copyZeroPush.state)).trans
            ((Ninst.Hinv.inv (f := Devm.getStor) copyRun).trans
              ((funext (getStor_eq_of_state_eq
                  returnLengthPush.state)).trans
                ((funext (getStor_eq_of_state_eq
                    returnZeroPush.state)).trans
                  (Func.of_inv Devm.getStor Devm.getStor
                    (by func_inv) returnRunOk))))))
    have testToWriteLogs : testPre.logs = writeLoadPost.logs :=
      branchPop.logs.trans
        (of_run_loadWordAt_logs (word := 1) writeLoadRun)
    have storedToPostLogs : storedPost.logs = post.logs :=
      lengthPush.logs.trans
        (offsetPush.logs.trans
          (copyZeroPush.logs.trans
            ((of_run_codecopy_logs copyRun).trans
              (returnLengthPush.logs.trans
                (returnZeroPush.logs.trans
                  (Func.of_inv Devm.logs Devm.logs
                    (by func_inv) returnRunOk))))))
    refine ⟨requestedNonzero, ?_, ?_, outputExact⟩
    · rw [← congrFun storedToPostStor sevm.currentTarget, storedStor]
      change
        (Devm.getStor writeLoadPost sevm.currentTarget).set adminSlotLit
            (addressSlotWriteWord
              ((Devm.getStor writeLoadPost sevm.currentTarget).get
                adminSlotLit) requestedAdmin.toB256) = _
      rw [← congrFun preToWriteStor sevm.currentTarget]
      rfl
    · rw [← storedToPostLogs, storedLogs, ← testToWriteLogs, testLogs]

/-- A requested zero admin reaches the actual constructor error-table entry
after the post-setup `AdminChanged` append.  The exact error outcome is stated
at that reached call frame.  Enclosing CREATE settlement restores world state
and transient storage; transaction-observable failed-CREATE logs are filtered
at the outer call boundary rather than by `Devm.rollback`. -/
theorem ossifiableConstructorAfterSetup_zeroAdmin_exact
    {runtimeOffset runtimeLength : Nat}
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {tail : Stack} {image : Bytes} {out : Execution}
    (hZeroAdmin : fs[4]? = some (Func.revData zeroAdminErrorData))
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      (0 : Adr).toB256)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (ossifiableConstructorAfterSetup runtimeOffset runtimeLength) out) :
    ∃ callPre,
      Devm.getStor callPre = Devm.getStor pre ∧
      callPre.logs = pre.logs ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          (pre.getStorVal sevm.currentTarget adminSlotLit) 0] ∧
      ControlErrorOutcome callPre zeroAdminErrorData out := by
  have checkpoint := ossifiableConstructorAfterSetup_checkpoint
    (requestedAdmin := (0 : Adr)) hwf hreads hrequested hp run
  unfold OssifiableConstructorAfterSetupCheckpoint at checkpoint
  rcases checkpoint with
    ⟨testPre, pTest, testWf, testReads, preToTestStor, testLogs, branchRun⟩
  unfold ossifiableConstructorAfterSetupBranch at branchRun
  have zeroWord : (0 : Adr).toB256 = (0 : B256) := by decide
  have pOne : (1 : B256) :: tail <<+ testPre.stack := by
    simpa [zeroWord, B256.eqCheck] using pTest
  obtain ⟨callPre, _, _, branchPop, callRun, _⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) pOne branchRun
  have callWf : Mem.Wf callPre.memory := by
    rw [← branchPop.memory]
    exact testWf
  have callReads : Mem.Reads callPre.memory
      (ossifiableConstructorEventImage image
        (pre.getStorVal sevm.currentTarget adminSlotLit) (0 : Adr).toB256) := by
    rw [← branchPop.memory]
    exact testReads
  have callStor : Devm.getStor callPre = Devm.getStor pre :=
    (funext (getStor_eq_of_state_eq branchPop.state)).symm.trans
      preToTestStor.symm
  have callLogs : callPre.logs = pre.logs ++
      [ossifiableConstructorAdminChangedLog sevm.currentTarget
        (pre.getStorVal sevm.currentTarget adminSlotLit) 0] :=
    branchPop.logs.symm.trans testLogs
  refine ⟨callPre, callStor, callLogs, ?_⟩
  simpa only [ControlErrorOutcome] using
    runCompiledTo_call_revData_frame_inv hZeroAdmin callWf callReads
      (by decide +kernel) (by decide +kernel) callRun

/-- The complete creation program rejects value before decoding or any
constructor phase.  This is the raw compiled-frame result; the enclosing
CREATE message theorem supplies persistent-world rollback. -/
theorem ossifiableConstructorProgram_value_rejected
    {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {pre : Devm} {tail : Stack} {out : Execution}
    (valueNonzero : sevm.value ≠ 0)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo
      (ossifiableConstructorFunctions runtimeOffset runtimeLength)
      sevm pre
      (ossifiableConstructorProgram runtimeOffset
        (runtimeOffset + runtimeLength) runtimeLength).main out) :
    ∃ post,
      out = .error (.revert, post) ∧ post.output = [] := by
  rw [ossifiableConstructorProgram_main_shape] at run
  obtain ⟨valuePost, qvalue, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have pValue := prefix_of_push
    (of_run_callvalue (Ninst.Run.of_runCompiled qvalue)) hp
  have pTest := prefix_of_iszero
    (Ninst.Run.of_runCompiled qzero) pValue
  have pZero : (0 : B256) :: tail <<+ testPre.stack := by
    simpa [B256.eqCheck, valueNonzero] using pTest
  obtain ⟨callPre, _, callRun, _⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  obtain ⟨revertPre, _, revertRun⟩ := runCompiledTo_call_inv
    (ossifiableConstructorFunctions_emptyRevert runtimeOffset runtimeLength)
    callRun
  exact runCompiledTo_rev_inv revertRun

/-- Successful post-setup constructor execution reads the post-child admin
word, appends `AdminChanged`, performs the packed admin-slot write, and returns
the exact appended runtime window.  No premise constrains what setup did to
either ERC-1967 slot. -/
theorem ossifiableConstructorAfterSetup_success
    {runtimeOffset runtimeLength : Nat}
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {tail : Stack} {image runtimeBytes : Bytes}
    {requestedAdmin : Adr}
    (hZeroAdmin : fs[4]? = some (Func.revData zeroAdminErrorData))
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hrequested :
      Bytes.toB256 (image.sliceD 32 32 0) = requestedAdmin.toB256)
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (ossifiableConstructorAfterSetup runtimeOffset runtimeLength)
      (.ok post)) :
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
  apply ossifiableConstructorAfterSetup_success_of_checkpoint hZeroAdmin
    hrequested hruntime hruntimeLength hruntimeNonempty hoffsetBound
    hlengthBound
  exact ossifiableConstructorAfterSetup_checkpoint hwf hreads hrequested hp run

end Blanc.ProxyPair
