import Blanc.ProxyPairOssifiableControl
import Blanc.AddressSlotProofs

/-!
# Exact effects of the OssifiableProxy control plane

This module executes the concrete mutation bodies opened by
`ProxyPairOssifiableControl`.  Its success predicates describe raw compiled
frame effects: packed slot words and source-ordered logs.  Revert-payload
theorems remain tied to an actual auxiliary call walk.  Message settlement and
its state rollback are intentionally not folded into these raw effects.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Blanc.Ninst
open scoped LogOutputHinv

namespace ProxyPair

def addressSlotUpdateRaw
    (pre : Devm) (owner : Adr) (slot newAddress : B256) : B256 :=
  (addressMask &&& pre.getStorVal owner slot) ||| newAddress

def rawAdminChangedLog
    (proxy : Adr) (previousAdmin newAdmin : B256) : Log :=
  ⟨proxy, [adminChangedEventTopic],
    previousAdmin.toBytes ++ newAdmin.toBytes⟩

def rawUpgradedLog (proxy : Adr) (implementation : B256) : Log :=
  ⟨proxy, [upgradedEventTopic, implementation], []⟩

private theorem complement_and_masked_or_zero_eq_zero
    (mask value : B256) :
    (~~~ mask) &&& ((mask &&& value) ||| 0) = 0 := by
  have hcomponent (m v : UInt64) :
      (~~~ m) &&& ((m &&& v) ||| 0) = 0 := by
    rw [UInt64.or_zero, ← UInt64.and_assoc, UInt64.not_and_self,
      UInt64.zero_and]
  rcases mask with ⟨⟨mh0, mh1⟩, ⟨ml0, ml1⟩⟩
  rcases value with ⟨⟨vh0, vh1⟩, ⟨vl0, vl1⟩⟩
  change
    (⟨⟨~~~ mh0 &&& ((mh0 &&& vh0) ||| 0),
        ~~~ mh1 &&& ((mh1 &&& vh1) ||| 0)⟩,
      ⟨~~~ ml0 &&& ((ml0 &&& vl0) ||| 0),
        ~~~ ml1 &&& ((ml1 &&& vl1) ||| 0)⟩⟩ : B256) =
      (⟨⟨0, 0⟩, ⟨0, 0⟩⟩ : B256)
  simp only [hcomponent]

/-- Exact raw-frame outcomes of a constant-data error call.  The exceptional
arm is the reverter's final memory-window charge; the normal error arm fixes
every payload byte. -/
def ControlErrorOutcome (pre : Devm) (blob : Bytes)
    (out : Execution) : Prop :=
  (∃ d,
    out = .error (.halt (.outOfGas .none), d) ∧
    Devm.getStor d = Devm.getStor pre ∧
    d.transientStorage = pre.transientStorage ∧
    d.logs = pre.logs) ∨
  (∃ post,
    out = .error (.revert, post) ∧
    post.output = blob ∧
    Devm.getStor post = Devm.getStor pre ∧
    post.transientStorage = pre.transientStorage ∧
    post.logs = pre.logs)

private theorem controlErrorCall_exact
    {sevm : Sevm} {pre : Devm} {slot : Nat} {blob image : Bytes}
    {out : Execution}
    (hget :
      (runtimeBaseline.main :: runtimeBaseline.aux)[slot]? =
        some (Func.revData blob))
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hblob : blob.length < 2 ^ 256)
    (hwords : 32 * (bytesWords blob).length < 2 ^ 256)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm pre (.call slot) out) :
    ControlErrorOutcome pre blob out := by
  simpa only [ControlErrorOutcome] using
    runCompiledTo_call_revData_frame_inv hget hwf hreads hblob hwords run

theorem notAdmin_call_exact
    {sevm : Sevm} {pre : Devm} {image : Bytes} {out : Execution}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm pre (.call notAdminErrorSlot) out) :
    ControlErrorOutcome pre notAdminErrorData out := by
  apply controlErrorCall_exact
      (slot := notAdminErrorSlot) (blob := notAdminErrorData)
      (image := image) (out := out)
  · simp [runtimeBaseline, runtimeBaselineAux, notAdminErrorSlot,
      notAdminError]
  · exact hwf
  · exact hreads
  · decide +kernel
  · decide +kernel
  · exact run

theorem proxyIsOssified_call_exact
    {sevm : Sevm} {pre : Devm} {image : Bytes} {out : Execution}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm pre (.call proxyIsOssifiedErrorSlot) out) :
    ControlErrorOutcome pre proxyIsOssifiedErrorData out := by
  apply controlErrorCall_exact
      (slot := proxyIsOssifiedErrorSlot) (blob := proxyIsOssifiedErrorData)
      (image := image) (out := out)
  · simp [runtimeBaseline, runtimeBaselineAux, proxyIsOssifiedErrorSlot,
      proxyIsOssifiedError]
  · exact hwf
  · exact hreads
  · decide +kernel
  · decide +kernel
  · exact run

theorem zeroAdmin_call_exact
    {sevm : Sevm} {pre : Devm} {image : Bytes} {out : Execution}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm pre (.call zeroAdminErrorSlot) out) :
    ControlErrorOutcome pre zeroAdminErrorData out := by
  apply controlErrorCall_exact
      (slot := zeroAdminErrorSlot) (blob := zeroAdminErrorData)
      (image := image) (out := out)
  · simp [runtimeBaseline, runtimeBaselineAux, zeroAdminErrorSlot,
      zeroAdminError]
  · exact hwf
  · exact hreads
  · decide +kernel
  · decide +kernel
  · exact run

theorem noCodeImplementation_call_exact
    {sevm : Sevm} {pre : Devm} {image : Bytes} {out : Execution}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm pre (.call noCodeImplementationErrorSlot) out) :
    ControlErrorOutcome pre noCodeImplementationErrorData out := by
  apply controlErrorCall_exact
      (slot := noCodeImplementationErrorSlot)
      (blob := noCodeImplementationErrorData)
      (image := image) (out := out)
  · simp [runtimeBaseline, runtimeBaselineAux,
      noCodeImplementationErrorSlot, noCodeImplementationError]
  · exact hwf
  · exact hreads
  · decide +kernel
  · decide +kernel
  · exact run

/-! ## Upgrade code check and commit -/

def upgradeImplementationCommit (continuation : Func) : Func :=
  dup 0 ::: storeAddressWordAt implementationSlotLit +++
    pushB256 upgradedEventTopic ::: logWith 1 0 0 +++ continuation

theorem upgradeImplementationControl_split_shape (continuation : Func) :
    upgradeImplementationControl continuation =
      arg 0 +++ dup 0 ::: extcodesize ::: iszero :::
        ((.call noCodeImplementationErrorSlot) <?>
          upgradeImplementationCommit continuation) := by
  rfl

/-- Exact split at the `EXTCODESIZE` guard.  In the code-present arm there is
no old/new comparison: the packed write and event commit remain ahead. -/
theorem upgradeImplementationControl_route
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {continuation : Func} {out : Execution}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeImplementationControl continuation) out) :
    (((pre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 = 0) ∧
      ∃ callPre,
        Func.RunCompiledTo fs sevm callPre
          (.call noCodeImplementationErrorSlot) out ∧
        Sevm.argWord sevm 0 :: tail <<+ callPre.stack ∧
        Devm.getStor pre = Devm.getStor callPre ∧
        pre.logs = callPre.logs ∧
        pre.memory = callPre.memory) ∨
    (((pre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 ≠ 0) ∧
      ∃ commitPre,
        Func.RunCompiledTo fs sevm commitPre
          (upgradeImplementationCommit continuation) out ∧
        Sevm.argWord sevm 0 :: tail <<+ commitPre.stack ∧
        Devm.getStor pre = Devm.getStor commitPre ∧
        pre.logs = commitPre.logs ∧
        pre.memory = commitPre.memory) := by
  rw [upgradeImplementationControl_split_shape] at run
  obtain ⟨argPost, argRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨dupPost, qdup, run⟩ := runCompiledTo_next_inv run
  obtain ⟨codePost, qcode, run⟩ := runCompiledTo_next_inv run
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have pArg := prefix_of_arg hp argRun
  have pDup := prefix_of_dup_val
    (Ninst.Run.of_runCompiled qdup) (Stack.Nth.head _ _) pArg
  have pCode0 := prefix_of_extcodesize_val pDup
    (Ninst.Run.of_runCompiled qcode)
  have hstate : pre.state = dupPost.state :=
    (Line.of_inv Devm.state (by line_inv) argRun).trans
      (Ninst.Hinv.inv (f := Devm.state)
        (Ninst.Run.of_runCompiled qdup))
  have hcode : dupPost.getCode (Sevm.argWord sevm 0).toAdr =
      pre.getCode (Sevm.argWord sevm 0).toAdr := by
    unfold Devm.getCode Devm.getAcct
    rw [← hstate]
  have pCode :
      (pre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 ::
        Sevm.argWord sevm 0 :: tail <<+ codePost.stack := by
    rw [← hcode]
    exact pCode0.1
  have pTest := prefix_of_iszero (Ninst.Run.of_runCompiled qzero) pCode
  have prefixStor : Devm.getStor pre = Devm.getStor testPre :=
    (Line.of_inv Devm.getStor (by line_inv) argRun).trans
      ((Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled qdup)).trans
        ((Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled qcode)).trans
          (Ninst.Hinv.inv (f := Devm.getStor)
            (Ninst.Run.of_runCompiled qzero))))
  have prefixLogs : pre.logs = testPre.logs :=
    (Line.of_inv Devm.logs (by line_inv) argRun).trans
      ((Ninst.Hinv.inv (f := Devm.logs)
        (Ninst.Run.of_runCompiled qdup)).trans
        ((Ninst.Hinv.inv (f := Devm.logs)
          (Ninst.Run.of_runCompiled qcode)).trans
          (Ninst.Hinv.inv (f := Devm.logs)
            (Ninst.Run.of_runCompiled qzero))))
  have prefixMemory : pre.memory = testPre.memory :=
    (Line.of_inv Devm.memory (by line_inv) argRun).trans
      ((Ninst.Hinv.inv (f := Devm.memory)
        (Ninst.Run.of_runCompiled qdup)).trans
        (pCode0.2.trans
          (Ninst.Hinv.inv (f := Devm.memory)
            (Ninst.Run.of_runCompiled qzero))))
  by_cases hzero :
      (pre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 = 0
  · have pOne : (1 : B256) :: Sevm.argWord sevm 0 :: tail <<+
        testPre.stack := by
      simpa [hzero, B256.eqCheck] using pTest
    obtain ⟨callPre, _, _, hpop, callRun, pCall⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) pOne branchRun
    exact Or.inl ⟨hzero, callPre, callRun, pCall,
      prefixStor.trans (funext (getStor_eq_of_state_eq hpop.state)),
      prefixLogs.trans hpop.logs, prefixMemory.trans hpop.memory⟩
  · have pZero : (0 : B256) :: Sevm.argWord sevm 0 :: tail <<+
        testPre.stack := by
      simpa [hzero, B256.eqCheck] using pTest
    obtain ⟨commitPre, hpop, commitRun, pCommit⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
    exact Or.inr ⟨hzero, commitPre, commitRun, pCommit,
      prefixStor.trans (funext (getStor_eq_of_state_eq hpop.state)),
      prefixLogs.trans hpop.logs, prefixMemory.trans hpop.memory⟩

/-- The no-code arm reaches the concrete error call and, under the standard
memory invariant, that reached call has the exact inherited error payload (or
the reverter's final out-of-gas leg). -/
theorem upgradeImplementationControl_noCode_exact
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {image : Bytes} {out : Execution}
    (hNoCode : fs[noCodeImplementationErrorSlot]? =
      some (Func.revData noCodeImplementationErrorData))
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hp : tail <<+ pre.stack)
    (codeZero :
      (pre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 = 0)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeImplementationControl Func.stop) out) :
    ∃ callPre,
      Func.RunCompiledTo fs sevm callPre
        (.call noCodeImplementationErrorSlot) out ∧
      ControlErrorOutcome callPre noCodeImplementationErrorData out := by
  rcases upgradeImplementationControl_route hp run with
    ⟨_, callPre, callRun, _, _, _, memoryEq⟩ |
      ⟨codeNonzero, _, _, _, _, _, _⟩
  · refine ⟨callPre, callRun, ?_⟩
    have hwfCall : Mem.Wf callPre.memory := by
      rw [← memoryEq]
      exact hwf
    have hreadsCall : Mem.Reads callPre.memory image := by
      rw [← memoryEq]
      exact hreads
    simpa only [ControlErrorOutcome] using
      runCompiledTo_call_revData_frame_inv hNoCode hwfCall hreadsCall
        (by decide +kernel) (by decide +kernel) callRun
  · exact (codeNonzero codeZero).elim

/-- A successful code-present commit performs the packed implementation write
and emits exactly one source-shaped `Upgraded` log. -/
theorem upgradeImplementationControl_success
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {tail : Stack}
    (hNoCode : fs[noCodeImplementationErrorSlot]? =
      some (Func.revData noCodeImplementationErrorData))
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeImplementationControl Func.stop) (.ok post)) :
    (pre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 ≠ 0 ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set implementationSlotLit
          (addressSlotUpdateRaw pre sevm.currentTarget
            implementationSlotLit (Sevm.argWord sevm 0)) ∧
      post.logs = pre.logs ++
        [rawUpgradedLog sevm.currentTarget (Sevm.argWord sevm 0)] := by
  rcases upgradeImplementationControl_route hp run with
    ⟨_, callPre, callRun, _, _, _, _⟩ |
      ⟨hcode, commitPre, commitRun, pCommit, commitStor, commitLogs, _⟩
  · exact (Func.RunCompiledTo.not_ok_call_revData hNoCode callRun).elim
  · unfold upgradeImplementationCommit at commitRun
    obtain ⟨dupPost, qdup, commitRun⟩ := runCompiledTo_next_inv commitRun
    obtain ⟨storePost, storeRun, commitRun⟩ :=
      runCompiledTo_prepend_inv commitRun
    obtain ⟨topicPost, qtopic, commitRun⟩ :=
      runCompiledTo_next_inv commitRun
    obtain ⟨logPost, logRun, stopRun⟩ :=
      runCompiledTo_prepend_inv commitRun
    have pDup := prefix_of_dup_val
      (Ninst.Run.of_runCompiled qdup) (Stack.Nth.head _ _) pCommit
    obtain ⟨pStore, hstore, _, hstoreLogs⟩ :=
      of_storeAddressWordAt_val pDup storeRun
    have pTopic := prefix_of_push
      (of_run_pushB256 (Ninst.Run.of_runCompiled qtopic)) pStore
    obtain ⟨_, hlog⟩ := of_logWith_val (k := 1) (x := 0) (y := 0)
      (topics := [upgradedEventTopic, Sevm.argWord sevm 0])
      (by simp) (by simpa using pTopic) logRun
    have postEq : post = logPost := Func.RunCompiledTo.stop_eq stopRun
    have commitToStore : Devm.getStor commitPre = Devm.getStor dupPost :=
      Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled qdup)
    have storeToLog : Devm.getStor storePost = Devm.getStor logPost :=
      (Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled qtopic)).trans
        (Line.of_inv Devm.getStor (by line_inv) logRun)
    have preToStore : Devm.getStor pre = Devm.getStor dupPost :=
      commitStor.trans commitToStore
    have preToTopicLogs : pre.logs = topicPost.logs :=
      commitLogs.trans
        ((Ninst.Hinv.inv (f := Devm.logs)
          (Ninst.Run.of_runCompiled qdup)).trans
          (hstoreLogs.symm.trans
            (of_run_pushB256
              (Ninst.Run.of_runCompiled qtopic)).logs))
    constructor
    · exact hcode
    constructor
    · rw [postEq, ← congrFun storeToLog sevm.currentTarget,
        hstore]
      change
        (Devm.getStor dupPost sevm.currentTarget).set
            implementationSlotLit
            ((addressMask &&&
                (Devm.getStor dupPost sevm.currentTarget).get
                  implementationSlotLit) ||| Sevm.argWord sevm 0) =
          (Devm.getStor pre sevm.currentTarget).set
            implementationSlotLit
            ((addressMask &&&
                (Devm.getStor pre sevm.currentTarget).get
                  implementationSlotLit) ||| Sevm.argWord sevm 0)
      rw [← congrFun preToStore sevm.currentTarget]
    · rw [postEq, hlog, ← preToTopicLogs]
      have hzero : ((0 : B256) * 32).toNat = 0 := by rfl
      have hempty : (topicPost.memory.read 0 0).1 = [] := by rfl
      simp [rawUpgradedLog, hzero, hempty]

theorem upgradeImplementationControl_same_value_logs
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {tail : Stack}
    (hNoCode : fs[noCodeImplementationErrorSlot]? =
      some (Func.revData noCodeImplementationErrorData))
    (hp : tail <<+ pre.stack)
    (sameValue : Sevm.argWord sevm 0 =
      storedImplementationWord pre sevm.currentTarget)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeImplementationControl Func.stop) (.ok post)) :
    post.logs = pre.logs ++
      [rawUpgradedLog sevm.currentTarget
        (storedImplementationWord pre sevm.currentTarget)] := by
  have effect := upgradeImplementationControl_success hNoCode hp run
  simpa [sameValue] using effect.2.2

/-! ## changeAdmin mutation -/

/-- A successful change-admin mutation rejects the zero word, performs the
packed address-slot update, and emits the `AdminChanged` log even when old and
new canonical values are equal. -/
theorem changeAdminMutation_success
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {tail : Stack} {image : Bytes}
    (hZeroAdmin : fs[zeroAdminErrorSlot]? =
      some (Func.revData zeroAdminErrorData))
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre changeAdminMutation (.ok post)) :
    Sevm.argWord sevm 0 ≠ 0 ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set adminSlotLit
          (addressSlotUpdateRaw pre sevm.currentTarget adminSlotLit
            (Sevm.argWord sevm 0)) ∧
      post.logs = pre.logs ++
        [rawAdminChangedLog sevm.currentTarget
          (storedAdminWord pre sevm.currentTarget)
          (Sevm.argWord sevm 0)] := by
  unfold changeAdminMutation at run
  obtain ⟨readPost, readRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pPrevious, hreadMemory, hreadLogs, hreadStor⟩ :=
    of_loadAddressWordAt_val hp readRun
  have pPrevious' : storedAdminWord pre sevm.currentTarget :: tail <<+
      readPost.stack := by
    simpa [storedAdminWord, canonicalAddressWord] using pPrevious
  obtain ⟨oldPost, oldStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pOld, hmemoryOld⟩ :=
    of_run_mstoreAt_val oldStoreRun pPrevious'
  obtain ⟨argPost, argRun, run⟩ := runCompiledTo_prepend_inv run
  have pNew := prefix_of_arg pOld argRun
  obtain ⟨newPost, newStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pNewStored, hmemoryNew⟩ :=
    of_run_mstoreAt_val newStoreRun pNew
  obtain ⟨topicPost, qtopic, run⟩ := runCompiledTo_next_inv run
  have topicPush := of_run_pushB256 (Ninst.Run.of_runCompiled qtopic)
  have pTopic := prefix_of_push topicPush pNewStored
  obtain ⟨logPost, logRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pLogged, hlogsRaw⟩ :=
    of_logWith_val (k := 0) (x := 0) (y := 2)
      (topics := [adminChangedEventTopic]) (by simp)
      (by simpa using pTopic) logRun
  have argMemory : oldPost.memory = argPost.memory :=
    Line.of_inv Devm.memory (by line_inv) argRun
  have hlogData :
      (topicPost.memory.read ((0 : B256) * 32).toNat
          ((2 : B256) * 32).toNat).1 =
        (storedAdminWord pre sevm.currentTarget).toBytes ++
          (Sevm.argWord sevm 0).toBytes := by
    change (topicPost.memory.read 0 64).1 =
      (storedAdminWord pre sevm.currentTarget).toBytes ++
        (Sevm.argWord sevm 0).toBytes
    rw [← topicPush.memory, hmemoryNew, ← argMemory, hmemoryOld,
      hreadMemory]
    exact Mem.read_two_word_writes hwf hreads _ _
  have preToTopicLogs : pre.logs = topicPost.logs :=
    hreadLogs.symm.trans
      ((Line.of_inv Devm.logs (by line_inv) oldStoreRun).trans
        ((Line.of_inv Devm.logs (by line_inv) argRun).trans
          ((Line.of_inv Devm.logs (by line_inv) newStoreRun).trans
            topicPush.logs)))
  have hlogs : logPost.logs = pre.logs ++
      [rawAdminChangedLog sevm.currentTarget
        (storedAdminWord pre sevm.currentTarget)
        (Sevm.argWord sevm 0)] := by
    rw [hlogsRaw, hlogData, ← preToTopicLogs]
    rfl
  obtain ⟨testArgPost, testArgRun, run⟩ :=
    runCompiledTo_prepend_inv run
  have pTestArg := prefix_of_arg pLogged testArgRun
  obtain ⟨testPre, qzero, branchRun⟩ := runCompiledTo_next_inv run
  have pTest := prefix_of_iszero
    (Ninst.Run.of_runCompiled qzero) pTestArg
  by_cases hnewZero : Sevm.argWord sevm 0 = 0
  · have pOne : (1 : B256) :: tail <<+ testPre.stack := by
      simpa [hnewZero, B256.eqCheck] using pTest
    obtain ⟨callPre, _, _, _, callRun, _⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) pOne branchRun
    exact (Func.RunCompiledTo.not_ok_call_revData hZeroAdmin callRun).elim
  · have pZero : (0 : B256) :: tail <<+ testPre.stack := by
      simpa [hnewZero, B256.eqCheck] using pTest
    obtain ⟨writePre, hpop, writeRun, pWrite⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
    obtain ⟨writeArgPost, writeArgRun, writeRun⟩ :=
      runCompiledTo_prepend_inv writeRun
    have pWriteArg := prefix_of_arg pWrite writeArgRun
    obtain ⟨stopPre, storeRun, stopRun⟩ :=
      runCompiledTo_prepend_inv writeRun
    obtain ⟨_, hstore, _, hstoreLogs⟩ :=
      of_storeAddressWordAt_val pWriteArg storeRun
    have postEq : post = stopPre := Func.RunCompiledTo.stop_eq stopRun
    have preToLogStor : Devm.getStor pre = Devm.getStor logPost :=
      hreadStor.symm.trans
        ((Line.of_inv Devm.getStor (by line_inv) oldStoreRun).trans
          ((Line.of_inv Devm.getStor (by line_inv) argRun).trans
            ((Line.of_inv Devm.getStor (by line_inv) newStoreRun).trans
              ((Ninst.Hinv.inv (f := Devm.getStor)
                (Ninst.Run.of_runCompiled qtopic)).trans
                (Line.of_inv Devm.getStor (by line_inv) logRun)))))
    have logToStoreStor : Devm.getStor logPost =
        Devm.getStor writeArgPost :=
      (Line.of_inv Devm.getStor (by line_inv) testArgRun).trans
        ((Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled qzero)).trans
          ((funext (getStor_eq_of_state_eq hpop.state)).trans
            (Line.of_inv Devm.getStor (by line_inv) writeArgRun)))
    have preToStoreStor : Devm.getStor pre =
        Devm.getStor writeArgPost :=
      preToLogStor.trans logToStoreStor
    have logToStoreLogs : logPost.logs = writeArgPost.logs :=
      (Line.of_inv Devm.logs (by line_inv) testArgRun).trans
        ((Ninst.Hinv.inv (f := Devm.logs)
          (Ninst.Run.of_runCompiled qzero)).trans
          (hpop.logs.trans
            (Line.of_inv Devm.logs (by line_inv) writeArgRun)))
    refine ⟨hnewZero, ?_, ?_⟩
    · rw [postEq, hstore]
      change
        (Devm.getStor writeArgPost sevm.currentTarget).set adminSlotLit
            ((addressMask &&&
                (Devm.getStor writeArgPost sevm.currentTarget).get
                  adminSlotLit) ||| Sevm.argWord sevm 0) =
          (Devm.getStor pre sevm.currentTarget).set adminSlotLit
            ((addressMask &&&
                (Devm.getStor pre sevm.currentTarget).get adminSlotLit) |||
              Sevm.argWord sevm 0)
      rw [← congrFun preToStoreStor sevm.currentTarget]
    · rw [postEq, hstoreLogs, ← logToStoreLogs, hlogs]

theorem changeAdminMutation_same_value_logs
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {tail : Stack} {image : Bytes}
    (hZeroAdmin : fs[zeroAdminErrorSlot]? =
      some (Func.revData zeroAdminErrorData))
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hp : tail <<+ pre.stack)
    (sameValue : Sevm.argWord sevm 0 =
      storedAdminWord pre sevm.currentTarget)
    (run : Func.RunCompiledTo fs sevm pre changeAdminMutation (.ok post)) :
    post.logs = pre.logs ++
      [rawAdminChangedLog sevm.currentTarget
        (storedAdminWord pre sevm.currentTarget)
        (storedAdminWord pre sevm.currentTarget)] := by
  have effect := changeAdminMutation_success hZeroAdmin hwf hreads hp run
  simpa [sameValue] using effect.2.2

/-! ## ossify mutation and irreversible control precedence -/

theorem ossifyMutation_split_shape :
    ossifyMutation =
      loadAddressWordAt adminSlotLit +++
        (mstoreAt 0 +++
          pushB256 0 ::: storeAddressWordAt adminSlotLit +++
          pushB256 0 ::: mstoreAt 1 +++
          pushB256 adminChangedEventTopic ::: logWith 0 0 2 +++
          pushB256 proxyOssifiedEventTopic ::: logWith 0 0 0 +++
          Func.stop) := by
  rfl

/-- Successful ossification preserves the raw upper ninety-six admin-slot
bits, zeros the address field, and emits the two source-ordered logs. -/
theorem ossifyMutation_success
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {tail : Stack} {image : Bytes}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre ossifyMutation (.ok post)) :
    Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set adminSlotLit
          (addressSlotUpdateRaw pre sevm.currentTarget adminSlotLit 0) ∧
      post.logs = pre.logs ++
        [rawAdminChangedLog sevm.currentTarget
          (storedAdminWord pre sevm.currentTarget) 0,
         proxyOssifiedLog sevm.currentTarget] := by
  rw [ossifyMutation_split_shape] at run
  obtain ⟨readPost, readRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pPrevious, hreadMemory, hreadLogs, hreadStor⟩ :=
    of_loadAddressWordAt_val hp readRun
  have pPrevious' : storedAdminWord pre sevm.currentTarget :: tail <<+
      readPost.stack := by
    simpa [storedAdminWord, canonicalAddressWord] using pPrevious
  obtain ⟨oldPost, oldStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pOld, hmemoryOld⟩ :=
    of_run_mstoreAt_val oldStoreRun pPrevious'
  obtain ⟨zeroStorePre, qzeroStore, run⟩ :=
    runCompiledTo_next_inv run
  have zeroStorePush :=
    of_run_pushB256 (Ninst.Run.of_runCompiled qzeroStore)
  have pZeroStore := prefix_of_push zeroStorePush pOld
  obtain ⟨storePost, addressStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pStored, hstore, hstoreMemory, hstoreLogs⟩ :=
    of_storeAddressWordAt_val pZeroStore addressStoreRun
  obtain ⟨zeroDataPre, qzeroData, run⟩ := runCompiledTo_next_inv run
  have zeroDataPush := of_run_pushB256 (Ninst.Run.of_runCompiled qzeroData)
  have pZeroData := prefix_of_push zeroDataPush pStored
  obtain ⟨eventMemoryPost, newStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pEventMemory, hmemoryNew⟩ :=
    of_run_mstoreAt_val newStoreRun pZeroData
  obtain ⟨adminTopicPost, qadminTopic, run⟩ :=
    runCompiledTo_next_inv run
  have adminTopicPush :=
    of_run_pushB256 (Ninst.Run.of_runCompiled qadminTopic)
  have pAdminTopic := prefix_of_push adminTopicPush pEventMemory
  obtain ⟨adminLogPost, adminLogRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pAdminLogged, hadminLogsRaw⟩ :=
    of_logWith_val (k := 0) (x := 0) (y := 2)
      (topics := [adminChangedEventTopic]) (by simp)
      (by simpa using pAdminTopic) adminLogRun
  have hadminData :
      (adminTopicPost.memory.read ((0 : B256) * 32).toNat
          ((2 : B256) * 32).toNat).1 =
        (storedAdminWord pre sevm.currentTarget).toBytes ++
          (0 : B256).toBytes := by
    change (adminTopicPost.memory.read 0 64).1 =
      (storedAdminWord pre sevm.currentTarget).toBytes ++
        (0 : B256).toBytes
    rw [← adminTopicPush.memory, hmemoryNew, ← zeroDataPush.memory,
      hstoreMemory, ← zeroStorePush.memory, hmemoryOld, hreadMemory]
    exact Mem.read_two_word_writes hwf hreads _ _
  have preToAdminTopicLogs : pre.logs = adminTopicPost.logs :=
    hreadLogs.symm.trans
      ((Line.of_inv Devm.logs (by line_inv) oldStoreRun).trans
        (zeroStorePush.logs.trans
          (hstoreLogs.symm.trans
            (zeroDataPush.logs.trans
              ((Line.of_inv Devm.logs (by line_inv) newStoreRun).trans
                adminTopicPush.logs)))))
  have hadminLogs : adminLogPost.logs = pre.logs ++
      [rawAdminChangedLog sevm.currentTarget
        (storedAdminWord pre sevm.currentTarget) 0] := by
    rw [hadminLogsRaw, hadminData, ← preToAdminTopicLogs]
    rfl
  obtain ⟨ossifiedTopicPost, qossifiedTopic, run⟩ :=
    runCompiledTo_next_inv run
  have ossifiedTopicPush :=
    of_run_pushB256 (Ninst.Run.of_runCompiled qossifiedTopic)
  have pOssifiedTopic := prefix_of_push ossifiedTopicPush pAdminLogged
  obtain ⟨ossifiedLogPost, ossifiedLogRun, stopRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨_, hossifiedLogsRaw⟩ :=
    of_logWith_val (k := 0) (x := 0) (y := 0)
      (topics := [proxyOssifiedEventTopic]) (by simp)
      (by simpa using pOssifiedTopic) ossifiedLogRun
  have postEq : post = ossifiedLogPost :=
    Func.RunCompiledTo.stop_eq stopRun
  have preToStorePre : Devm.getStor pre = Devm.getStor zeroStorePre :=
    hreadStor.symm.trans
      ((Line.of_inv Devm.getStor (by line_inv) oldStoreRun).trans
        (Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled qzeroStore)))
  have storeToFinal : Devm.getStor storePost =
      Devm.getStor ossifiedLogPost :=
    (Ninst.Hinv.inv (f := Devm.getStor)
      (Ninst.Run.of_runCompiled qzeroData)).trans
      ((Line.of_inv Devm.getStor (by line_inv) newStoreRun).trans
        ((Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled qadminTopic)).trans
          ((Line.of_inv Devm.getStor (by line_inv) adminLogRun).trans
            ((Ninst.Hinv.inv (f := Devm.getStor)
              (Ninst.Run.of_runCompiled qossifiedTopic)).trans
              (Line.of_inv Devm.getStor (by line_inv) ossifiedLogRun)))))
  constructor
  · rw [postEq, ← congrFun storeToFinal sevm.currentTarget,
      hstore]
    change
      (Devm.getStor zeroStorePre sevm.currentTarget).set adminSlotLit
          ((addressMask &&&
              (Devm.getStor zeroStorePre sevm.currentTarget).get
                adminSlotLit) ||| 0) =
        (Devm.getStor pre sevm.currentTarget).set adminSlotLit
          ((addressMask &&&
              (Devm.getStor pre sevm.currentTarget).get adminSlotLit) ||| 0)
    rw [← congrFun preToStorePre sevm.currentTarget]
  · rw [postEq, hossifiedLogsRaw, ← ossifiedTopicPush.logs, hadminLogs]
    have hzero : ((0 : B256) * 32).toNat = 0 := by rfl
    have hempty : (ossifiedTopicPost.memory.read 0 0).1 = [] := by rfl
    simp [proxyOssifiedLog, hzero, hempty, List.append_assoc]

/-- The exact packed zero write makes the public address view of the admin
slot zero, irrespective of arbitrary raw high bits. -/
theorem storedAdminWord_zero_of_ossifyMutation_success
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {tail : Stack} {image : Bytes}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre ossifyMutation (.ok post)) :
    storedAdminWord post sevm.currentTarget = 0 := by
  have effect := ossifyMutation_success hwf hreads hp run
  unfold storedAdminWord canonicalAddressWord
  change (~~~ addressMask) &&&
      (Devm.getStor post sevm.currentTarget).get adminSlotLit = 0
  rw [effect.1, Stor.get_set_self]
  simpa only [addressSlotUpdateRaw] using
    complement_and_masked_or_zero_eq_zero addressMask
      (pre.getStorVal sevm.currentTarget adminSlotLit)

/-- All three state-changing control entries are permanently captured by the
ossified check when a later fresh frame shares the locked storage world.  Each
conclusion retains the reached `ProxyIsOssified` call walk and does not depend
on a caller-mismatch premise. -/
def OssifiedControlEntries (locked : Devm) (owner : Adr) : Prop :=
  (∀ {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr},
    sevm.currentTarget = owner →
    Devm.getStor locked = Devm.getStor entry →
    entry.stack = [] → sevm.value = 0 →
    sevm.data = proxyChangeAdminCalldata newAdmin →
    Prog.RunCompiledTo sevm entry runtimeBaseline out →
    ∃ callPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call proxyIsOssifiedErrorSlot) out) ∧
  (∀ {sevm : Sevm} {entry : Devm} {out : Execution}
      {newImplementation : Adr},
    sevm.currentTarget = owner →
    Devm.getStor locked = Devm.getStor entry →
    entry.stack = [] → sevm.value = 0 →
    sevm.data = proxyUpgradeToCalldata newImplementation →
    Prog.RunCompiledTo sevm entry runtimeBaseline out →
    ∃ callPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call proxyIsOssifiedErrorSlot) out) ∧
  (∀ {sevm : Sevm} {entry : Devm} {out : Execution},
    sevm.currentTarget = owner →
    Devm.getStor locked = Devm.getStor entry →
    entry.stack = [] → sevm.value = 0 →
    sevm.data = proxyOssifyCalldata →
    Prog.RunCompiledTo sevm entry runtimeBaseline out →
    ∃ callPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call proxyIsOssifiedErrorSlot) out)

theorem ossifiedControlEntries_of_admin_zero
    {locked : Devm} {owner : Adr}
    (adminZero : storedAdminWord locked owner = 0) :
    OssifiedControlEntries locked owner := by
  constructor
  · intro sevm entry out newAdmin htarget hstor hstack hvalue hdata hprog
    apply changeAdmin_ossified_precedence hprog hstack hvalue hdata
    have hword := storedAdminWord_eq_of_getStor_eq hstor (owner := owner)
    rw [htarget, ← hword]
    exact adminZero
  constructor
  · intro sevm entry out newImplementation htarget hstor hstack hvalue
      hdata hprog
    apply upgradeTo_ossified_precedence hprog hstack hvalue hdata
    have hword := storedAdminWord_eq_of_getStor_eq hstor (owner := owner)
    rw [htarget, ← hword]
    exact adminZero
  · intro sevm entry out htarget hstor hstack hvalue hdata hprog
    apply ossify_ossified_precedence hprog hstack hvalue hdata
    have hword := storedAdminWord_eq_of_getStor_eq hstor (owner := owner)
    rw [htarget, ← hword]
    exact adminZero

theorem ossifyMutation_success_irreversible
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {tail : Stack} {image : Bytes}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre ossifyMutation (.ok post)) :
    OssifiedControlEntries post sevm.currentTarget :=
  ossifiedControlEntries_of_admin_zero
    (storedAdminWord_zero_of_ossifyMutation_success hwf hreads hp run)

/-! ## Program-level reached error calls -/

/-- Unauthorized `changeAdmin` reaches the concrete NotAdmin call.  Exact
payload classification is supplied from that same reached call under its
standard memory-image invariant. -/
theorem changeAdmin_unauthorized_exact_call
    {sevm : Sevm} {entry : Devm} {out : Execution} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline out)
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminNeCaller : storedAdminWord entry sevm.currentTarget ≠
      sevm.caller.toB256) :
    ∃ callPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm callPre (.call notAdminErrorSlot) out ∧
      ∀ image : Bytes, Mem.Wf callPre.memory →
        Mem.Reads callPre.memory image →
        ControlErrorOutcome callPre notAdminErrorData out := by
  obtain ⟨callPre, callRun⟩ := changeAdmin_unauthorized_route
    hprog hentryStack hvalue hdata adminNonzero adminNeCaller
  refine ⟨callPre, callRun, ?_⟩
  intro image hwf hreads
  exact notAdmin_call_exact hwf hreads callRun

/-! ## Compiled-program consumers of the exact bodies -/

theorem changeAdmin_authorized_success_opened_of_program
    {sevm : Sevm} {entry post : Devm} {newAdmin : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyChangeAdminCalldata newAdmin)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256) :
    ∃ mutationPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm mutationPre changeAdminMutation (.ok post) ∧
      ∀ image : Bytes, Mem.Wf mutationPre.memory →
        Mem.Reads mutationPre.memory image →
        newAdmin.toB256 ≠ 0 ∧
        Devm.getStor post sevm.currentTarget =
          (Devm.getStor mutationPre sevm.currentTarget).set adminSlotLit
            (addressSlotUpdateRaw mutationPre sevm.currentTarget adminSlotLit
              newAdmin.toB256) ∧
        post.logs = mutationPre.logs ++
          [rawAdminChangedLog sevm.currentTarget
            (storedAdminWord mutationPre sevm.currentTarget)
            newAdmin.toB256] := by
  obtain ⟨mutationPre, mutationRun, pMutation⟩ :=
    changeAdmin_authorized_reaches_mutation hprog hentryStack hvalue hdata
      adminNonzero adminEqCaller
  refine ⟨mutationPre, mutationRun, ?_⟩
  intro image hwf hreads
  have effect := changeAdminMutation_success
    (fs := runtimeBaseline.main :: runtimeBaseline.aux)
    (by simp [runtimeBaseline, runtimeBaselineAux, zeroAdminErrorSlot,
      zeroAdminError])
    hwf hreads pMutation mutationRun
  rw [proxyChangeAdminCalldata_arg0 hdata] at effect
  exact effect

theorem upgradeTo_authorized_success_opened_of_program
    {sevm : Sevm} {entry post : Devm} {newImplementation : Adr}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyUpgradeToCalldata newImplementation)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256) :
    ∃ checkPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm checkPre (upgradeImplementationControl Func.stop) (.ok post) ∧
      (checkPre.getCode newImplementation).size.toB256 ≠ 0 ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor checkPre sevm.currentTarget).set
          implementationSlotLit
          (addressSlotUpdateRaw checkPre sevm.currentTarget
            implementationSlotLit newImplementation.toB256) ∧
      post.logs = checkPre.logs ++
        [rawUpgradedLog sevm.currentTarget newImplementation.toB256] := by
  obtain ⟨checkPre, checkRun, pCheck⟩ :=
    upgradeTo_authorized_reaches_code_check hprog hentryStack hvalue hdata
      adminNonzero adminEqCaller
  refine ⟨checkPre, checkRun, ?_⟩
  have effect := upgradeImplementationControl_success
    (fs := runtimeBaseline.main :: runtimeBaseline.aux)
    (by simp [runtimeBaseline, runtimeBaselineAux,
      noCodeImplementationErrorSlot, noCodeImplementationError]) pCheck checkRun
  rw [proxyUpgradeToCalldata_arg0 hdata] at effect
  rw [toAdr_toB256] at effect
  exact effect

theorem ossify_authorized_success_opened_of_program
    {sevm : Sevm} {entry post : Devm}
    (hprog : Prog.RunCompiledTo sevm entry runtimeBaseline (.ok post))
    (hentryStack : entry.stack = []) (hvalue : sevm.value = 0)
    (hdata : sevm.data = proxyOssifyCalldata)
    (adminNonzero : storedAdminWord entry sevm.currentTarget ≠ 0)
    (adminEqCaller : storedAdminWord entry sevm.currentTarget =
      sevm.caller.toB256) :
    ∃ mutationPre,
      Func.RunCompiledTo
        (runtimeBaseline.main :: runtimeBaseline.aux)
        sevm mutationPre ossifyMutation (.ok post) ∧
      ∀ image : Bytes, Mem.Wf mutationPre.memory →
        Mem.Reads mutationPre.memory image →
        Devm.getStor post sevm.currentTarget =
          (Devm.getStor mutationPre sevm.currentTarget).set adminSlotLit
            (addressSlotUpdateRaw mutationPre sevm.currentTarget
              adminSlotLit 0) ∧
        post.logs = mutationPre.logs ++
          [rawAdminChangedLog sevm.currentTarget
            (storedAdminWord mutationPre sevm.currentTarget) 0,
           proxyOssifiedLog sevm.currentTarget] ∧
        OssifiedControlEntries post sevm.currentTarget := by
  obtain ⟨mutationPre, mutationRun, pMutation⟩ :=
    ossify_authorized_reaches_mutation hprog hentryStack hvalue hdata
      adminNonzero adminEqCaller
  refine ⟨mutationPre, mutationRun, ?_⟩
  intro image hwf hreads
  have effect := ossifyMutation_success hwf hreads pMutation mutationRun
  exact ⟨effect.1, effect.2,
    ossifyMutation_success_irreversible hwf hreads pMutation mutationRun⟩

end ProxyPair
end Blanc
