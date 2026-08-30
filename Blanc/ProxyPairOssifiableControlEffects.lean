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
  addressSlotWriteWord (pre.getStorVal owner slot) newAddress

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

theorem emptyDelegatecallError_call_exact
    {sevm : Sevm} {pre : Devm} {image : Bytes} {out : Execution}
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (run : Func.RunCompiledTo
      (runtimeBaseline.main :: runtimeBaseline.aux)
      sevm pre (.call emptyDelegatecallErrorSlot) out) :
    ControlErrorOutcome pre emptyDelegatecallErrorData out := by
  apply controlErrorCall_exact
      (slot := emptyDelegatecallErrorSlot)
      (blob := emptyDelegatecallErrorData)
      (image := image) (out := out)
  · simp [runtimeBaseline, runtimeBaselineAux,
      emptyDelegatecallErrorSlot, emptyDelegatecallError]
  · exact hwf
  · exact hreads
  · decide +kernel
  · decide +kernel
  · exact run

/-! ## `upgradeToAndCall` decoder boundary -/

/- The source decoder is one nested guard chain.  These suffix names keep each
proof step small while `upgradeToAndCallDecoder_split_shape` definitionally
locks their composition to the executable body. -/

private def upgradeToAndCallDecoderAfterCopy (body : Func) : Func :=
  arg 2 +++ dup 0 ::: iszero ::: iszero ::: eq :::
    ((arg 2 +++ mstoreAt upgradeToAndCallForceWord +++ body) <?>
      (.call emptyRevertSlot))

private def upgradeToAndCallDecoderAfterPayloadBound (body : Func) : Func :=
  loadUpgradeToAndCallWord upgradeToAndCallSetupLengthWord +++
    loadUpgradeToAndCallWord upgradeToAndCallOffsetWord +++
      pushB256 36 ::: add :::
        pushB256 upgradeToAndCallSetupMemoryBase ::: calldatacopy :::
          upgradeToAndCallDecoderAfterCopy body

private def upgradeToAndCallDecoderAfterLengthBound (body : Func) : Func :=
  loadUpgradeToAndCallWord upgradeToAndCallOffsetWord +++
    pushB256 36 ::: add :::
      loadUpgradeToAndCallWord upgradeToAndCallSetupLengthWord +++ add :::
        calldatasize ::: lt :::
          ((.call emptyRevertSlot) <?>
            upgradeToAndCallDecoderAfterPayloadBound body)

private def upgradeToAndCallDecoderAfterHeader (body : Func) : Func :=
  loadUpgradeToAndCallWord upgradeToAndCallOffsetWord +++
    pushB256 4 ::: add ::: calldataload :::
      mstoreAt upgradeToAndCallSetupLengthWord +++
        pushB256 upgradeToAndCallAbiMaxUint64 :::
          loadUpgradeToAndCallWord upgradeToAndCallSetupLengthWord +++ gt :::
            ((.call allocationPanicSlot) <?>
              upgradeToAndCallDecoderAfterLengthBound body)

private def upgradeToAndCallDecoderAfterOffset (body : Func) : Func :=
  arg 1 +++ mstoreAt upgradeToAndCallOffsetWord +++
    loadUpgradeToAndCallWord upgradeToAndCallOffsetWord +++
      pushB256 36 ::: add ::: calldatasize ::: lt :::
        ((.call emptyRevertSlot) <?>
          upgradeToAndCallDecoderAfterHeader body)

private def upgradeToAndCallDecoderAfterAddress (body : Func) : Func :=
  arg 0 +++ mstoreAt upgradeToAndCallImplementationWord +++
    pushB256 upgradeToAndCallAbiMaxUint64 ::: arg 1 +++ gt :::
      ((.call emptyRevertSlot) <?>
        upgradeToAndCallDecoderAfterOffset body)

private def upgradeToAndCallDecoderAfterSize (body : Func) : Func :=
  arg 0 +++ checkNonAddress +++
    ((.call emptyRevertSlot) <?>
      upgradeToAndCallDecoderAfterAddress body)

private theorem upgradeToAndCallDecoder_split_shape (body : Func) :
    decodeUpgradeToAndCallControl body =
      pushB256 100 ::: calldatasize ::: lt :::
        ((.call emptyRevertSlot) <?>
          upgradeToAndCallDecoderAfterSize body) := by
  rfl

/-- The exact proof image left by the canonical decoder: four scratch words
and the unpadded setup bytes, in executable write order. -/
def upgradeToAndCallDecodedImage (image : Bytes)
    (newImplementation : Adr) (setupCalldata : Bytes)
    (forceCall : Bool) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt image 0 newImplementation.toB256.toBytes)
          96 (96 : B256).toBytes)
        32 (Nat.toB256 setupCalldata.length).toBytes)
      128 setupCalldata)
    64 (if forceCall then (1 : B256) else 0).toBytes

/-- Execution-derived boundary at the protected body of the canonical
`(address,bytes,bool)` decoder. -/
inductive UpgradeToAndCallDecodeBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (tail : Stack) (image : Bytes) (newImplementation : Adr)
    (setupCalldata : Bytes) (forceCall : Bool) (out : Execution) : Prop
  | intro (bodyPre : Devm)
      (bodyRun : Func.RunCompiledTo fs sevm bodyPre body out)
      (stack : tail <<+ bodyPre.stack)
      (memoryWf : Mem.Wf bodyPre.memory)
      (memoryReads : Mem.Reads bodyPre.memory
        (upgradeToAndCallDecodedImage image newImplementation setupCalldata
          forceCall))
      (state : entry.state = bodyPre.state)

private theorem upgradeToAndCallDecoder_step_size
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {out : Execution}
    (hp : tail <<+ pre.stack)
    (hsize : (Nat.toB256 sevm.data.length <? (100 : B256)) = 0)
    (run : Func.RunCompiledTo fs sevm pre
      (decodeUpgradeToAndCallControl body) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next
        (upgradeToAndCallDecoderAfterSize body) out ∧
      tail <<+ next.stack ∧
      pre.state = next.state ∧
      pre.memory = next.memory := by
  rw [upgradeToAndCallDecoder_split_shape] at run
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s3, q3, branchRun⟩ := runCompiledTo_next_inv run
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have p1 := prefix_of_push (of_run_pushB256 r1) hp
  have p2 := prefix_of_push (of_run_calldatasize r2) p1
  have p3 := prefix_of_lt r3 p2
  have pZero : (0 : B256) :: tail <<+ s3.stack := by
    simpa [hsize] using p3
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  exact ⟨next, nextRun, pNext,
    (Ninst.Hinv.inv (f := Devm.state) r1).trans
      ((Ninst.Hinv.inv (f := Devm.state) r2).trans
        ((Ninst.Hinv.inv (f := Devm.state) r3).trans hpop.state)),
    (Ninst.Hinv.inv (f := Devm.memory) r1).trans
      ((Ninst.Hinv.inv (f := Devm.memory) r2).trans
        ((Ninst.Hinv.inv (f := Devm.memory) r3).trans hpop.memory))⟩

private theorem upgradeToAndCallDecoder_step_address
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {out : Execution}
    (hp : tail <<+ pre.stack)
    (hvalid : ValidAdr (Sevm.argWord sevm 0))
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeToAndCallDecoderAfterSize body) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next
        (upgradeToAndCallDecoderAfterAddress body) out ∧
      tail <<+ next.stack ∧
      pre.state = next.state ∧
      pre.memory = next.memory := by
  unfold upgradeToAndCallDecoderAfterSize at run
  obtain ⟨argPost, argRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨testPre, checkRun, branchRun⟩ :=
    runCompiledTo_prepend_inv run
  have pArg := prefix_of_arg hp argRun
  obtain ⟨dirty, pDirty, hdirty⟩ :=
    of_check_non_address pArg checkRun
  have hdirtyZero : dirty = 0 := hdirty.mpr hvalid
  have pZero : (0 : B256) :: tail <<+ testPre.stack := by
    simpa [hdirtyZero] using pDirty
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  exact ⟨next, nextRun, pNext,
    (Line.of_inv Devm.state (by line_inv) argRun).trans
      ((Line.of_inv Devm.state (by line_inv) checkRun).trans hpop.state),
    (Line.of_inv Devm.memory (by line_inv) argRun).trans
      ((Line.of_inv Devm.memory (by line_inv) checkRun).trans hpop.memory)⟩

private theorem upgradeToAndCallDecoder_step_implementation
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {image : Bytes} {newImplementation : Adr}
    {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (harg0 : Sevm.argWord sevm 0 = newImplementation.toB256)
    (harg1 : Sevm.argWord sevm 1 = 96)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeToAndCallDecoderAfterAddress body) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next
        (upgradeToAndCallDecoderAfterOffset body) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory
        (Bytes.writeAt image 0 newImplementation.toB256.toBytes) ∧
      pre.state = next.state := by
  unfold upgradeToAndCallDecoderAfterAddress at run
  obtain ⟨s1, arg0Run, run⟩ := runCompiledTo_prepend_inv run
  have p1 : newImplementation.toB256 :: tail <<+ s1.stack := by
    rw [← harg0]
    exact prefix_of_arg hp arg0Run
  have wf1 : Mem.Wf s1.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg0Run]
    exact hwf
  have reads1 : Mem.Reads s1.memory image := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg0Run]
    exact hreads
  obtain ⟨s2, storeRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_mstoreAt_image p1 wf1 reads1 storeRun
  rw [show ((upgradeToAndCallImplementationWord * 32 : B256)).toNat = 0
    from by decide] at reads2
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  have r3 := Ninst.Run.of_runCompiled q3
  have p3 := prefix_of_push (of_run_pushB256 r3) p2
  obtain ⟨s4, arg1Run, run⟩ := runCompiledTo_prepend_inv run
  have p4 : (96 : B256) :: upgradeToAndCallAbiMaxUint64 :: tail <<+
      s4.stack := by
    rw [← harg1]
    exact prefix_of_arg p3 arg1Run
  obtain ⟨s5, q5, branchRun⟩ := runCompiledTo_next_inv run
  have r5 := Ninst.Run.of_runCompiled q5
  have p5 := prefix_of_gt r5 p4
  have pZero : (0 : B256) :: tail <<+ s5.stack := by
    simpa [show ((96 : B256) >? upgradeToAndCallAbiMaxUint64) = 0
      from by decide] using p5
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← Line.of_inv Devm.memory (by line_inv) arg1Run,
      ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact wf2
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← Line.of_inv Devm.memory (by line_inv) arg1Run,
      ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact reads2
  · exact (Line.of_inv Devm.state (by line_inv) arg0Run).trans
      (state2.trans ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        ((Line.of_inv Devm.state (by line_inv) arg1Run).trans
          ((Ninst.Hinv.inv (f := Devm.state) r5).trans hpop.state))))

private theorem upgradeToAndCallDecoder_step_offset
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {image : Bytes} {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (harg1 : Sevm.argWord sevm 1 = 96)
    (hheader : (Nat.toB256 sevm.data.length <? (132 : B256)) = 0)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeToAndCallDecoderAfterOffset body) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next
        (upgradeToAndCallDecoderAfterHeader body) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory
        (Bytes.writeAt image 96 (96 : B256).toBytes) ∧
      pre.state = next.state := by
  unfold upgradeToAndCallDecoderAfterOffset at run
  obtain ⟨s1, arg1Run, run⟩ := runCompiledTo_prepend_inv run
  have p1 : (96 : B256) :: tail <<+ s1.stack := by
    rw [← harg1]
    exact prefix_of_arg hp arg1Run
  have wf1 : Mem.Wf s1.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg1Run]
    exact hwf
  have reads1 : Mem.Reads s1.memory image := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg1Run]
    exact hreads
  obtain ⟨s2, storeRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_mstoreAt_image p1 wf1 reads1 storeRun
  rw [show ((upgradeToAndCallOffsetWord * 32 : B256)).toNat = 96
    from by decide] at reads2
  obtain ⟨s3, loadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p3, wf3, reads3, state3⟩ :=
    of_run_loadWordAt_image (value := (96 : B256)) p2 wf2 reads2
      (by
        rw [show ((upgradeToAndCallOffsetWord * 32 : B256)).toNat = 96
          from by decide]
        exact Bytes.readWord_writeAt_self _ 96 96)
      loadRun
  obtain ⟨s4, q4, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s5, q5, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s6, q6, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s7, q7, branchRun⟩ := runCompiledTo_next_inv run
  have r4 := Ninst.Run.of_runCompiled q4
  have r5 := Ninst.Run.of_runCompiled q5
  have r6 := Ninst.Run.of_runCompiled q6
  have r7 := Ninst.Run.of_runCompiled q7
  have p4 := prefix_of_push (of_run_pushB256 r4) p3
  have p5 : (132 : B256) :: tail <<+ s5.stack := by
    simpa [show ((36 : B256) + 96) = 132 from by decide]
      using prefix_of_add r5 p4
  have p6 := prefix_of_push (of_run_calldatasize r6) p5
  have p7 := prefix_of_lt r7 p6
  have pZero : (0 : B256) :: tail <<+ s7.stack := by
    simpa [hheader] using p7
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r7,
      ← Ninst.Hinv.inv (f := Devm.memory) r6,
      ← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← Ninst.Hinv.inv (f := Devm.memory) r4]
    exact wf3
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r7,
      ← Ninst.Hinv.inv (f := Devm.memory) r6,
      ← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← Ninst.Hinv.inv (f := Devm.memory) r4]
    exact reads3
  · exact (Line.of_inv Devm.state (by line_inv) arg1Run).trans
      (state2.trans (state3.trans
        ((Ninst.Hinv.inv (f := Devm.state) r4).trans
          ((Ninst.Hinv.inv (f := Devm.state) r5).trans
            ((Ninst.Hinv.inv (f := Devm.state) r6).trans
              ((Ninst.Hinv.inv (f := Devm.state) r7).trans hpop.state))))))

private theorem upgradeToAndCallDecoder_step_header
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {image : Bytes} {setupCalldata : Bytes}
    {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hoffset : Bytes.toB256 (image.sliceD 96 32 0) = 96)
    (hsetupLength : Sevm.dataWord sevm 100 =
      Nat.toB256 setupCalldata.length)
    (hlengthGuard :
      (Nat.toB256 setupCalldata.length >?
        upgradeToAndCallAbiMaxUint64) = 0)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeToAndCallDecoderAfterHeader body) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next
        (upgradeToAndCallDecoderAfterLengthBound body) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory
        (Bytes.writeAt image 32
          (Nat.toB256 setupCalldata.length).toBytes) ∧
      pre.state = next.state := by
  unfold upgradeToAndCallDecoderAfterHeader at run
  obtain ⟨s1, loadOffsetRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image (value := (96 : B256)) hp hwf hreads
      (by
        rw [show ((upgradeToAndCallOffsetWord * 32 : B256)).toNat = 96
          from by decide]
        exact hoffset)
      loadOffsetRun
  obtain ⟨s2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s4, q4, run⟩ := runCompiledTo_next_inv run
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have p2 := prefix_of_push (of_run_pushB256 r2) p1
  have p3 : (100 : B256) :: tail <<+ s3.stack := by
    simpa [show ((4 : B256) + 96) = 100 from by decide]
      using prefix_of_add r3 p2
  have p4 : Nat.toB256 setupCalldata.length :: tail <<+ s4.stack := by
    rw [← hsetupLength]
    exact prefix_of_calldataload_val r4 p3
  have wf4 : Mem.Wf s4.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r4,
      ← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← Ninst.Hinv.inv (f := Devm.memory) r2]
    exact wf1
  have reads4 : Mem.Reads s4.memory image := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r4,
      ← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← Ninst.Hinv.inv (f := Devm.memory) r2]
    exact reads1
  obtain ⟨s5, storeLengthRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p5, wf5, reads5, state5⟩ :=
    of_run_mstoreAt_image p4 wf4 reads4 storeLengthRun
  rw [show ((upgradeToAndCallSetupLengthWord * 32 : B256)).toNat = 32
    from by decide] at reads5
  obtain ⟨s6, q6, run⟩ := runCompiledTo_next_inv run
  have r6 := Ninst.Run.of_runCompiled q6
  have p6 := prefix_of_push (of_run_pushB256 r6) p5
  obtain ⟨s7, loadLengthRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p7, wf7, reads7, state7⟩ :=
    of_run_loadWordAt_image
      (value := Nat.toB256 setupCalldata.length) p6
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r6]; exact wf5)
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r6]; exact reads5)
      (by
        rw [show ((upgradeToAndCallSetupLengthWord * 32 : B256)).toNat = 32
          from by decide]
        exact Bytes.readWord_writeAt_self _ 32
          (Nat.toB256 setupCalldata.length))
      loadLengthRun
  obtain ⟨s8, q8, branchRun⟩ := runCompiledTo_next_inv run
  have r8 := Ninst.Run.of_runCompiled q8
  have p8 := prefix_of_gt r8 p7
  have pZero : (0 : B256) :: tail <<+ s8.stack := by
    simpa [hlengthGuard] using p8
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r8]
    exact wf7
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r8]
    exact reads7
  · exact state1.trans
      ((Ninst.Hinv.inv (f := Devm.state) r2).trans
        ((Ninst.Hinv.inv (f := Devm.state) r3).trans
          ((Ninst.Hinv.inv (f := Devm.state) r4).trans
            (state5.trans ((Ninst.Hinv.inv (f := Devm.state) r6).trans
              (state7.trans
                ((Ninst.Hinv.inv (f := Devm.state) r8).trans
                  hpop.state)))))))

private theorem upgradeToAndCallDecoder_step_payload_bound
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {image : Bytes} {setupCalldata : Bytes}
    {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hoffset : Bytes.toB256 (image.sliceD 96 32 0) = 96)
    (hlength : Bytes.toB256 (image.sliceD 32 32 0) =
      Nat.toB256 setupCalldata.length)
    (hpayloadGuard :
      (Nat.toB256 sevm.data.length <?
        (Nat.toB256 setupCalldata.length + 132)) = 0)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeToAndCallDecoderAfterLengthBound body) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next
        (upgradeToAndCallDecoderAfterPayloadBound body) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory image ∧
      pre.state = next.state := by
  unfold upgradeToAndCallDecoderAfterLengthBound at run
  obtain ⟨s1, loadOffsetRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image (value := (96 : B256)) hp hwf hreads
      (by
        rw [show ((upgradeToAndCallOffsetWord * 32 : B256)).toNat = 96
          from by decide]
        exact hoffset)
      loadOffsetRun
  obtain ⟨s2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have p2 := prefix_of_push (of_run_pushB256 r2) p1
  have p3 : (132 : B256) :: tail <<+ s3.stack := by
    simpa [show ((36 : B256) + 96) = 132 from by decide]
      using prefix_of_add r3 p2
  have wf3 : Mem.Wf s3.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← Ninst.Hinv.inv (f := Devm.memory) r2]
    exact wf1
  have reads3 : Mem.Reads s3.memory image := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← Ninst.Hinv.inv (f := Devm.memory) r2]
    exact reads1
  obtain ⟨s4, loadLengthRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p4, wf4, reads4, state4⟩ :=
    of_run_loadWordAt_image
      (value := Nat.toB256 setupCalldata.length) p3 wf3 reads3
      (by
        rw [show ((upgradeToAndCallSetupLengthWord * 32 : B256)).toNat = 32
          from by decide]
        exact hlength)
      loadLengthRun
  obtain ⟨s5, q5, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s6, q6, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s7, q7, branchRun⟩ := runCompiledTo_next_inv run
  have r5 := Ninst.Run.of_runCompiled q5
  have r6 := Ninst.Run.of_runCompiled q6
  have r7 := Ninst.Run.of_runCompiled q7
  have p5 := prefix_of_add r5 p4
  have p6 := prefix_of_push (of_run_calldatasize r6) p5
  have p7 := prefix_of_lt r7 p6
  have pZero : (0 : B256) :: tail <<+ s7.stack := by
    simpa [hpayloadGuard] using p7
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r7,
      ← Ninst.Hinv.inv (f := Devm.memory) r6,
      ← Ninst.Hinv.inv (f := Devm.memory) r5]
    exact wf4
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r7,
      ← Ninst.Hinv.inv (f := Devm.memory) r6,
      ← Ninst.Hinv.inv (f := Devm.memory) r5]
    exact reads4
  · exact state1.trans
      ((Ninst.Hinv.inv (f := Devm.state) r2).trans
        ((Ninst.Hinv.inv (f := Devm.state) r3).trans
          (state4.trans ((Ninst.Hinv.inv (f := Devm.state) r5).trans
            ((Ninst.Hinv.inv (f := Devm.state) r6).trans
              ((Ninst.Hinv.inv (f := Devm.state) r7).trans
                hpop.state))))))

private theorem upgradeToAndCallDecoder_step_copy
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {tail : Stack} {image : Bytes} {setupCalldata : Bytes}
    {forceCall : Bool} {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hoffset : Bytes.toB256 (image.sliceD 96 32 0) = 96)
    (hlength : Bytes.toB256 (image.sliceD 32 32 0) =
      Nat.toB256 setupCalldata.length)
    (hlengthBound : setupCalldata.length < 2 ^ 256)
    (hsetupSlice :
      sevm.data.sliceD 132 setupCalldata.length 0 = setupCalldata)
    (harg2 : Sevm.argWord sevm 2 =
      if forceCall then 1 else 0)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeToAndCallDecoderAfterPayloadBound body) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next body out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory
        (Bytes.writeAt (Bytes.writeAt image 128 setupCalldata) 64
          (if forceCall then (1 : B256) else 0).toBytes) ∧
      pre.state = next.state := by
  unfold upgradeToAndCallDecoderAfterPayloadBound at run
  obtain ⟨s1, loadLengthRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image
      (value := Nat.toB256 setupCalldata.length) hp hwf hreads
      (by
        rw [show ((upgradeToAndCallSetupLengthWord * 32 : B256)).toNat = 32
          from by decide]
        exact hlength)
      loadLengthRun
  obtain ⟨s2, loadOffsetRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_loadWordAt_image (value := (96 : B256)) p1 wf1 reads1
      (by
        rw [show ((upgradeToAndCallOffsetWord * 32 : B256)).toNat = 96
          from by decide]
        exact hoffset)
      loadOffsetRun
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s4, q4, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s5, q5, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s6, q6, run⟩ := runCompiledTo_next_inv run
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have r5 := Ninst.Run.of_runCompiled q5
  have r6 := Ninst.Run.of_runCompiled q6
  have p3 := prefix_of_push (of_run_pushB256 r3) p2
  have p4 : (132 : B256) :: Nat.toB256 setupCalldata.length :: tail <<+
      s4.stack := by
    simpa [show ((36 : B256) + 96) = 132 from by decide]
      using prefix_of_add r4 p3
  have p5 := prefix_of_push (of_run_pushB256 r5) p4
  obtain ⟨p6, memory6⟩ := prefix_of_calldatacopy_val r6 p5
  have wf5 : Mem.Wf s5.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← Ninst.Hinv.inv (f := Devm.memory) r4,
      ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact wf2
  have reads5 : Mem.Reads s5.memory image := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← Ninst.Hinv.inv (f := Devm.memory) r4,
      ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact reads2
  have wf6 : Mem.Wf s6.memory := by
    rw [memory6, show ((upgradeToAndCallSetupMemoryBase : B256)).toNat = 128
      from by decide,
      show ((132 : B256)).toNat = 132 from by decide,
      B256.toNat_toB256_of_lt hlengthBound, hsetupSlice]
    exact wf5.write _ _
  have reads6 : Mem.Reads s6.memory
      (Bytes.writeAt image 128 setupCalldata) := by
    rw [memory6, show ((upgradeToAndCallSetupMemoryBase : B256)).toNat = 128
      from by decide,
      show ((132 : B256)).toNat = 132 from by decide,
      B256.toNat_toB256_of_lt hlengthBound, hsetupSlice]
    exact Mem.Reads.write wf5 reads5 _ _
  unfold upgradeToAndCallDecoderAfterCopy at run
  obtain ⟨s7, arg2Run, run⟩ := runCompiledTo_prepend_inv run
  have p7 : (if forceCall then (1 : B256) else 0) :: tail <<+
      s7.stack := by
    rw [← harg2]
    exact prefix_of_arg p6 arg2Run
  obtain ⟨s8, q8, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s9, q9, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s10, q10, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s11, q11, branchRun⟩ := runCompiledTo_next_inv run
  have r8 := Ninst.Run.of_runCompiled q8
  have r9 := Ninst.Run.of_runCompiled q9
  have r10 := Ninst.Run.of_runCompiled q10
  have r11 := Ninst.Run.of_runCompiled q11
  have p8 := prefix_of_dup_val r8 (Stack.Nth.head _ _) p7
  have p9 := prefix_of_iszero r9 p8
  have p10 := prefix_of_iszero r10 p9
  have p11 := prefix_of_eq r11 p10
  have pOne : (1 : B256) :: tail <<+ s11.stack := by
    cases forceCall <;> simpa [B256.eqCheck] using p11
  obtain ⟨storePathPre, _, _, hpop, storePathRun, pStorePath⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) pOne branchRun
  obtain ⟨s12, arg2Run', storePathRun⟩ :=
    runCompiledTo_prepend_inv storePathRun
  have p12 : (if forceCall then (1 : B256) else 0) :: tail <<+
      s12.stack := by
    rw [← harg2]
    exact prefix_of_arg pStorePath arg2Run'
  have wf12 : Mem.Wf s12.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg2Run',
      ← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r11,
      ← Ninst.Hinv.inv (f := Devm.memory) r10,
      ← Ninst.Hinv.inv (f := Devm.memory) r9,
      ← Ninst.Hinv.inv (f := Devm.memory) r8,
      ← Line.of_inv Devm.memory (by line_inv) arg2Run]
    exact wf6
  have reads12 : Mem.Reads s12.memory
      (Bytes.writeAt image 128 setupCalldata) := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg2Run',
      ← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r11,
      ← Ninst.Hinv.inv (f := Devm.memory) r10,
      ← Ninst.Hinv.inv (f := Devm.memory) r9,
      ← Ninst.Hinv.inv (f := Devm.memory) r8,
      ← Line.of_inv Devm.memory (by line_inv) arg2Run]
    exact reads6
  obtain ⟨next, storeForceRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv storePathRun
  obtain ⟨pNext, wfNext, readsNext, stateNext⟩ :=
    of_run_mstoreAt_image p12 wf12 reads12 storeForceRun
  rw [show ((upgradeToAndCallForceWord * 32 : B256)).toNat = 64
    from by decide] at readsNext
  refine ⟨next, bodyRun, pNext, wfNext, readsNext, ?_⟩
  exact state1.trans (state2.trans
    ((Ninst.Hinv.inv (f := Devm.state) r3).trans
      ((Ninst.Hinv.inv (f := Devm.state) r4).trans
        ((Ninst.Hinv.inv (f := Devm.state) r5).trans
          ((Ninst.Hinv.inv (f := Devm.state) r6).trans
            ((Line.of_inv Devm.state (by line_inv) arg2Run).trans
              ((Ninst.Hinv.inv (f := Devm.state) r8).trans
                ((Ninst.Hinv.inv (f := Devm.state) r9).trans
                  ((Ninst.Hinv.inv (f := Devm.state) r10).trans
                    ((Ninst.Hinv.inv (f := Devm.state) r11).trans
                      (hpop.state.trans
                        ((Line.of_inv Devm.state (by line_inv) arg2Run').trans
                          stateNext))))))))))))

/-- Canonical ABI words plus the decoder's explicit arithmetic guards produce
the protected-body boundary.  The following public corollary discharges these
guard equations from the canonical encoder's numeric bounds. -/
theorem decodeUpgradeToAndCallControl_boundary_of_guards
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {tail : Stack} {image : Bytes} {newImplementation : Adr}
    {setupCalldata : Bytes} {forceCall : Bool} {out : Execution}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (hsizeGuard :
      (Nat.toB256 sevm.data.length <? (100 : B256)) = 0)
    (hheaderGuard :
      (Nat.toB256 sevm.data.length <? (132 : B256)) = 0)
    (hlengthGuard :
      (Nat.toB256 setupCalldata.length >?
        upgradeToAndCallAbiMaxUint64) = 0)
    (hpayloadGuard :
      (Nat.toB256 sevm.data.length <?
        (Nat.toB256 setupCalldata.length + 132)) = 0)
    (hlengthBound : setupCalldata.length < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm entry
      (decodeUpgradeToAndCallControl body) out) :
    UpgradeToAndCallDecodeBoundary fs sevm entry body tail image
      newImplementation setupCalldata forceCall out := by
  have harg0 := proxyUpgradeToAndCallCalldata_arg0 hdata
  have harg1 := proxyUpgradeToAndCallCalldata_arg1 hdata
  have harg2 := proxyUpgradeToAndCallCalldata_arg2 hdata
  have hsetupLength := proxyUpgradeToAndCallCalldata_setupLength hdata
  have hsetupSlice := proxyUpgradeToAndCallCalldata_setupSlice hdata
  obtain ⟨n1, run1, p1, state1, memory1⟩ :=
    upgradeToAndCallDecoder_step_size hp hsizeGuard run
  have wf1 : Mem.Wf n1.memory := by rw [← memory1]; exact hwf
  have reads1 : Mem.Reads n1.memory image := by
    rw [← memory1]
    exact hreads
  have hvalid : ValidAdr (Sevm.argWord sevm 0) := by
    rw [harg0]
    exact ⟨newImplementation, rfl⟩
  obtain ⟨n2, run2, p2, state2, memory2⟩ :=
    upgradeToAndCallDecoder_step_address p1 hvalid run1
  have wf2 : Mem.Wf n2.memory := by rw [← memory2]; exact wf1
  have reads2 : Mem.Reads n2.memory image := by
    rw [← memory2]
    exact reads1
  obtain ⟨n3, run3, p3, wf3, reads3, state3⟩ :=
    upgradeToAndCallDecoder_step_implementation p2 wf2 reads2 harg0 harg1
      run2
  obtain ⟨n4, run4, p4, wf4, reads4, state4⟩ :=
    upgradeToAndCallDecoder_step_offset p3 wf3 reads3 harg1 hheaderGuard
      run3
  have hoffset4 : Bytes.toB256
      ((Bytes.writeAt
        (Bytes.writeAt image 0 newImplementation.toB256.toBytes)
        96 (96 : B256).toBytes).sliceD 96 32 0) = 96 :=
    Bytes.readWord_writeAt_self _ 96 96
  obtain ⟨n5, run5, p5, wf5, reads5, state5⟩ :=
    upgradeToAndCallDecoder_step_header p4 wf4 reads4 hoffset4 hsetupLength
      hlengthGuard run4
  have hoffset5 : Bytes.toB256
      ((Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt image 0 newImplementation.toB256.toBytes)
          96 (96 : B256).toBytes)
        32 (Nat.toB256 setupCalldata.length).toBytes).sliceD 96 32 0) =
      96 := by
    rw [Bytes.readWord_writeAt_of_disjoint _ 96 32
        (Nat.toB256 setupCalldata.length) (Or.inr (by omega))]
    exact Bytes.readWord_writeAt_self _ 96 96
  have hlength5 : Bytes.toB256
      ((Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt image 0 newImplementation.toB256.toBytes)
          96 (96 : B256).toBytes)
        32 (Nat.toB256 setupCalldata.length).toBytes).sliceD 32 32 0) =
      Nat.toB256 setupCalldata.length :=
    Bytes.readWord_writeAt_self _ 32 (Nat.toB256 setupCalldata.length)
  obtain ⟨n6, run6, p6, wf6, reads6, state6⟩ :=
    upgradeToAndCallDecoder_step_payload_bound p5 wf5 reads5
      hoffset5 hlength5 hpayloadGuard run5
  obtain ⟨n7, run7, p7, wf7, reads7, state7⟩ :=
    upgradeToAndCallDecoder_step_copy p6 wf6 reads6 hoffset5 hlength5
      hlengthBound hsetupSlice harg2 run6
  refine ⟨n7, run7, p7, wf7, ?_, ?_⟩
  · simpa [upgradeToAndCallDecodedImage] using reads7
  · exact state1.trans (state2.trans (state3.trans (state4.trans
      (state5.trans (state6.trans state7)))))

/-- The canonical encoder clears every decoder guard under the Solidity
decoder's `uint64` length bound and the ordinary 256-bit calldata-size bound. -/
theorem decodeUpgradeToAndCallControl_boundary
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {tail : Stack} {image : Bytes} {newImplementation : Adr}
    {setupCalldata : Bytes} {forceCall : Bool} {out : Execution}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hdata : sevm.data = proxyUpgradeToAndCallCalldata
      newImplementation setupCalldata forceCall)
    (hlength64 : setupCalldata.length < 2 ^ 64)
    (hdataLength : 132 + ceil32 setupCalldata.length < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm entry
      (decodeUpgradeToAndCallControl body) out) :
    UpgradeToAndCallDecodeBoundary fs sevm entry body tail image
      newImplementation setupCalldata forceCall out := by
  have hlen : sevm.data.length = 132 + ceil32 setupCalldata.length := by
    rw [hdata]
    exact proxyUpgradeToAndCallCalldata_length _ _ _
  have hlength256 : setupCalldata.length < 2 ^ 256 := by omega
  have hsizeGuard :
      (Nat.toB256 sevm.data.length <? (100 : B256)) = 0 := by
    unfold B256.ltCheck
    rw [if_neg (by
      rw [B256.lt_iff_toNat_lt_toNat,
        B256.toNat_toB256_of_lt (by omega),
        show ((100 : B256)).toNat = 100 from by decide]
      have hceil := Nat.le_ceil32 setupCalldata.length
      omega)]
  have hheaderGuard :
      (Nat.toB256 sevm.data.length <? (132 : B256)) = 0 := by
    unfold B256.ltCheck
    rw [if_neg (by
      rw [B256.lt_iff_toNat_lt_toNat,
        B256.toNat_toB256_of_lt (by omega),
        show ((132 : B256)).toNat = 132 from by decide]
      have hceil := Nat.le_ceil32 setupCalldata.length
      omega)]
  have hlengthGuard :
      (Nat.toB256 setupCalldata.length >?
        upgradeToAndCallAbiMaxUint64) = 0 := by
    unfold B256.gtCheck
    rw [if_neg (by
      apply not_lt_of_ge
      rw [B256.le_iff_toNat_le_toNat,
        B256.toNat_toB256_of_lt hlength256,
        show upgradeToAndCallAbiMaxUint64.toNat = 2 ^ 64 - 1
          from by decide]
      omega)]
  have hpayloadGuard :
      (Nat.toB256 sevm.data.length <?
        (Nat.toB256 setupCalldata.length + 132)) = 0 := by
    unfold B256.ltCheck
    rw [if_neg (by
      rw [B256.lt_iff_toNat_lt_toNat,
        B256.toNat_toB256_of_lt (by omega), B256.toNat_add,
        B256.toNat_toB256_of_lt hlength256,
        show ((132 : B256)).toNat = 132 from by decide,
        Nat.lo_eq_of_lt (by omega)]
      have hceil := Nat.le_ceil32 setupCalldata.length
      omega)]
  exact decodeUpgradeToAndCallControl_boundary_of_guards hp hwf hreads hdata
    hsizeGuard hheaderGuard hlengthGuard hpayloadGuard hlength256 run

/-! ## The three decoded setup routes -/

/-- Exhaustive execution-derived routes through the setup-length/force tail. -/
inductive UpgradeToAndCallSetupRoute
    (fs : List Func) (sevm : Sevm) (pre : Devm) (tail : Stack)
    (decodedImage : Bytes) (setupCalldata : Bytes) (forceCall : Bool)
    (out : Execution) : Prop
  | nonempty (setupNonempty : setupCalldata ≠ [])
      (delegatePre : Devm)
      (delegateRun : Func.RunCompiledTo fs sevm delegatePre
        upgradeToAndCallDelegateSetup out)
      (stack : tail <<+ delegatePre.stack)
      (memoryWf : Mem.Wf delegatePre.memory)
      (memoryReads : Mem.Reads delegatePre.memory decodedImage)
      (state : pre.state = delegatePre.state)
  | forced (setupEmpty : setupCalldata = [])
      (forceTrue : forceCall = true)
      (delegatePre : Devm)
      (delegateRun : Func.RunCompiledTo fs sevm delegatePre
        upgradeToAndCallDelegateSetup out)
      (stack : tail <<+ delegatePre.stack)
      (memoryWf : Mem.Wf delegatePre.memory)
      (memoryReads : Mem.Reads delegatePre.memory decodedImage)
      (state : pre.state = delegatePre.state)
  | skipped (setupEmpty : setupCalldata = [])
      (forceFalse : forceCall = false)
      (stopPre : Devm)
      (stopRun : Func.RunCompiledTo fs sevm stopPre Func.stop out)
      (stack : tail <<+ stopPre.stack)
      (memoryWf : Mem.Wf stopPre.memory)
      (memoryReads : Mem.Reads stopPre.memory decodedImage)
      (state : pre.state = stopPre.state)

theorem upgradeToAndCallAfter_route
    {fs : List Func} {sevm : Sevm} {pre : Devm} {tail : Stack}
    {image : Bytes} {newImplementation : Adr} {setupCalldata : Bytes}
    {forceCall : Bool} {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall))
    (hlengthBound : setupCalldata.length < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm pre upgradeToAndCallAfter out) :
    UpgradeToAndCallSetupRoute fs sevm pre tail
      (upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall)
      setupCalldata forceCall out := by
  have hlengthImage : Bytes.toB256
      ((upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall).sliceD 32 32 0) =
      Nat.toB256 setupCalldata.length := by
    unfold upgradeToAndCallDecodedImage
    rw [Bytes.sliceD_writeAt_before _ _ 32 32 64 (by omega),
      Bytes.sliceD_writeAt_before _ _ 32 32 128 (by omega)]
    exact Bytes.readWord_writeAt_self _ 32
      (Nat.toB256 setupCalldata.length)
  have hforceImage : Bytes.toB256
      ((upgradeToAndCallDecodedImage image newImplementation setupCalldata
        forceCall).sliceD 64 32 0) =
      (if forceCall then (1 : B256) else 0) := by
    unfold upgradeToAndCallDecodedImage
    exact Bytes.readWord_writeAt_self _ 64
      (if forceCall then (1 : B256) else 0)
  unfold upgradeToAndCallAfter at run
  obtain ⟨lengthPost, loadLengthRun, branchRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨pLength, wfLength, readsLength, stateLength⟩ :=
    of_run_loadWordAt_image
      (value := Nat.toB256 setupCalldata.length) hp hwf hreads
      (by
        rw [show ((upgradeToAndCallSetupLengthWord * 32 : B256)).toNat = 32
          from by decide]
        exact hlengthImage)
      loadLengthRun
  by_cases hzero : setupCalldata.length = 0
  · have hwordZero : Nat.toB256 setupCalldata.length = (0 : B256) := by
      rw [hzero]
      decide
    have pZero : (0 : B256) :: tail <<+ lengthPost.stack := by
      rw [← hwordZero]
      exact pLength
    obtain ⟨forcePre, hlengthPop, forceRun, pForcePre⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
    obtain ⟨forcePost, loadForceRun, forceBranch⟩ :=
      runCompiledTo_prepend_inv forceRun
    obtain ⟨pForce, wfForce, readsForce, stateForce⟩ :=
      of_run_loadWordAt_image
        (value := if forceCall then (1 : B256) else 0) pForcePre
        (by rw [← hlengthPop.memory]; exact wfLength)
        (by rw [← hlengthPop.memory]; exact readsLength)
        (by
          rw [show ((upgradeToAndCallForceWord * 32 : B256)).toNat = 64
            from by decide]
          exact hforceImage)
        loadForceRun
    have setupEmpty : setupCalldata = [] := List.length_eq_zero_iff.mp hzero
    cases forceCall with
    | false =>
      have pForceZero : (0 : B256) :: tail <<+ forcePost.stack := by
        simpa using pForce
      obtain ⟨stopPre, hforcePop, stopRun, pStop⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pForceZero forceBranch
      exact .skipped setupEmpty rfl stopPre stopRun pStop
        (by rw [← hforcePop.memory]; exact wfForce)
        (by rw [← hforcePop.memory]; exact readsForce)
        (stateLength.trans (hlengthPop.state.trans
          (stateForce.trans hforcePop.state)))
    | true =>
      have pForceOne : (1 : B256) :: tail <<+ forcePost.stack := by
        simpa using pForce
      obtain ⟨delegatePre, _, _, hforcePop, delegateRun, pDelegate⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pForceOne forceBranch
      exact .forced setupEmpty rfl delegatePre delegateRun pDelegate
        (by rw [← hforcePop.memory]; exact wfForce)
        (by rw [← hforcePop.memory]; exact readsForce)
        (stateLength.trans (hlengthPop.state.trans
          (stateForce.trans hforcePop.state)))
  · have hwordNonzero : Nat.toB256 setupCalldata.length ≠ 0 := by
      intro hword
      have hnat := congrArg B256.toNat hword
      rw [B256.toNat_toB256_of_lt hlengthBound,
        show ((0 : B256)).toNat = 0 from rfl] at hnat
      exact hzero hnat
    obtain ⟨delegatePre, _, _, hlengthPop, delegateRun, pDelegate⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix hwordNonzero pLength branchRun
    exact .nonempty (by intro hnil; apply hzero; simp [hnil])
      delegatePre delegateRun pDelegate
      (by rw [← hlengthPop.memory]; exact wfLength)
      (by rw [← hlengthPop.memory]; exact readsLength)
      (stateLength.trans hlengthPop.state)

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
    {continuation : Func} {image : Bytes} {out : Execution}
    (hNoCode : fs[noCodeImplementationErrorSlot]? =
      some (Func.revData noCodeImplementationErrorData))
    (hwf : Mem.Wf pre.memory) (hreads : Mem.Reads pre.memory image)
    (hp : tail <<+ pre.stack)
    (codeZero :
      (pre.getCode (Sevm.argWord sevm 0).toAdr).size.toB256 = 0)
    (run : Func.RunCompiledTo fs sevm pre
      (upgradeImplementationControl continuation) out) :
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
    simpa only [storedAdminWord, canonicalAddressWord,
      addressSlotReadWord] using pPrevious
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
    simpa only [storedAdminWord, canonicalAddressWord,
      addressSlotReadWord] using pPrevious
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
  simpa only [addressSlotUpdateRaw, addressSlotWriteWord] using
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
