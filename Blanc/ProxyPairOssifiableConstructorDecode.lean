import Blanc.ProxyPairOssifiableConstructor

/-!
# OssifiableProxy executable constructor decoder

This module opens the actual nested `CODECOPY` constructor decoder.  Its
boundaries retain a proof-carrying memory image, persistent state, and log
chronology.  The pure `ossifiableConstructorDecodeSpec` remains the result
index; this owner supplies the execution-derived route to that specification.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst
open scoped LogOutputHinv

private def constructorDecodeLoadWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

private def constructorDecodeAfterPayloadBound (body : Func) : Func :=
  constructorDecodeLoadWord 4 +++
    constructorDecodeLoadWord 3 +++ pushB256 32 ::: add :::
      pushB256 0x100 ::: codecopy ::: body

private def constructorDecodeAfterLengthBound (body : Func) : Func :=
  constructorDecodeLoadWord 3 +++ pushB256 32 ::: add :::
    constructorDecodeLoadWord 4 +++ add ::: codesize ::: lt :::
      ((.call 1) <?> constructorDecodeAfterPayloadBound body)

private def constructorDecodeAfterLengthCopy (body : Func) : Func :=
  pushB256 ossifiableConstructorAbiMaxUint64 :::
    constructorDecodeLoadWord 4 +++ gt :::
      ((.call 7) <?> constructorDecodeAfterLengthBound body)

private def constructorDecodeAfterLengthComplete (body : Func) : Func :=
  pushB256 32 ::: constructorDecodeLoadWord 3 +++
    pushB256 128 ::: codecopy ::: constructorDecodeAfterLengthCopy body

private def constructorDecodeAfterPointer (body : Func) : Func :=
  constructorDecodeLoadWord 3 +++ pushB256 32 ::: add :::
    codesize ::: lt :::
      ((.call 1) <?> constructorDecodeAfterLengthComplete body)

private def constructorDecodeAfterOffsetBound
    (argsOffset : Nat) (body : Func) : Func :=
  constructorDecodeLoadWord 2 +++
    ossifiablePushCreationCoordinate argsOffset ::: add :::
      mstoreAt 3 +++ constructorDecodeAfterPointer body

private def constructorDecodeAfterAdmin (argsOffset : Nat) (body : Func) : Func :=
  pushB256 ossifiableConstructorAbiMaxUint64 :::
    constructorDecodeLoadWord 2 +++ gt :::
      ((.call 1) <?> constructorDecodeAfterOffsetBound argsOffset body)

private def constructorDecodeAfterImplementation
    (argsOffset : Nat) (body : Func) : Func :=
  constructorDecodeLoadWord 1 +++ checkNonAddress +++
    ((.call 1) <?> constructorDecodeAfterAdmin argsOffset body)

private def constructorDecodeAfterHeadCopy
    (argsOffset : Nat) (body : Func) : Func :=
  constructorDecodeLoadWord 0 +++ checkNonAddress +++
    ((.call 1) <?> constructorDecodeAfterImplementation argsOffset body)

private theorem constructorDecodeAfterHeadCopy_shape
    (argsOffset : Nat) (body : Func) :
    constructorDecodeAfterHeadCopy argsOffset body =
      constructorDecodeLoadWord 0 +++ checkNonAddress +++
        ((.call 1) <?>
          constructorDecodeAfterImplementation argsOffset body) := by
  rfl

private theorem constructorDecodeAfterImplementation_shape
    (argsOffset : Nat) (body : Func) :
    constructorDecodeAfterImplementation argsOffset body =
      constructorDecodeLoadWord 1 +++ checkNonAddress +++
        ((.call 1) <?> constructorDecodeAfterAdmin argsOffset body) := by
  rfl

private def constructorDecodeAfterHead
    (argsOffset : Nat) (body : Func) : Func :=
  pushB256 96 ::: ossifiablePushCreationCoordinate argsOffset :::
    pushB256 0 ::: codecopy :::
      constructorDecodeAfterHeadCopy argsOffset body

private theorem constructorDecode_split_shape (argsOffset : Nat) (body : Func) :
    ossifiableConstructorDecode argsOffset body =
      ossifiablePushCreationCoordinate (argsOffset + 96) :::
        codesize ::: lt :::
          ((.call 1) <?> constructorDecodeAfterHead argsOffset body) := by
  rfl

/-- Proof image immediately after the decoder copies the complete three-word
ABI head into scratch memory at zero. -/
def ossifiableConstructorHeadImage
    (image code : Bytes) (argsOffset : Nat) : Bytes :=
  Bytes.writeAt image 0 (code.sliceD argsOffset 96 0)

/-- Accepted first-guard boundary, before either address word is classified. -/
inductive OssifiableConstructorHeadBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterHeadCopy argsOffset body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorHeadImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

private theorem constructorDecode_step_head
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {out : Execution}
    (hp : tail <<+ entry.stack)
    (hguard :
      (sevm.code.size.toB256 <? Nat.toB256 (argsOffset + 96)) = 0)
    (run : Func.RunCompiledTo fs sevm entry
      (ossifiableConstructorDecode argsOffset body) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterHead argsOffset body) out ∧
      tail <<+ next.stack ∧
      entry.state = next.state ∧
      entry.logs = next.logs ∧
      entry.memory = next.memory := by
  rw [constructorDecode_split_shape] at run
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s3, q3, branchRun⟩ := runCompiledTo_next_inv run
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have pushHead := of_run_push r1
  have p1 : Nat.toB256 (argsOffset + 96) :: tail <<+ s1.stack := by
    simpa [ossifiablePushCreationCoordinate, B256.toB256_toBytes] using
      prefix_of_push pushHead hp
  have codeSize := of_run_codesize r2
  have p2 := prefix_of_push codeSize p1
  have p3 := prefix_of_lt r3 p2
  have pZero : (0 : B256) :: tail <<+ s3.stack := by
    simpa [hguard] using p3
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  exact ⟨next, nextRun, pNext,
    pushHead.state.trans (codeSize.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) r3).trans hpop.state)),
    pushHead.logs.trans (codeSize.logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) r3).trans hpop.logs)),
    pushHead.memory.trans (codeSize.memory.trans
      ((Ninst.Hinv.inv (f := Devm.memory) r3).trans hpop.memory))⟩

/-- A successful natural-size head guard reaches the exact proof-carrying
three-word scratch image.  The coordinate bound is the only premise needed to
identify the fixed-width EVM word with the natural creation-code offset. -/
theorem ossifiableConstructorDecode_headBoundary
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes}
    {out : Execution}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : argsOffset + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hcomplete : argsOffset + 96 ≤ sevm.code.size)
    (run : Func.RunCompiledTo fs sevm entry
      (ossifiableConstructorDecode argsOffset body) out) :
    OssifiableConstructorHeadBoundary fs sevm entry body argsOffset tail image
      out := by
  have hguard :
      (sevm.code.size.toB256 <? Nat.toB256 (argsOffset + 96)) = 0 := by
    unfold B256.ltCheck
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hcodeSize,
      B256.toNat_toB256_of_lt hcoordinate]
    omega
  obtain ⟨copyPre, copyRun, pCopy, stateCopy, logsCopy, memoryCopy⟩ :=
    constructorDecode_step_head hp hguard run
  unfold constructorDecodeAfterHead at copyRun
  obtain ⟨s1, q1, copyRun⟩ := runCompiledTo_next_inv copyRun
  obtain ⟨s2, q2, copyRun⟩ := runCompiledTo_next_inv copyRun
  obtain ⟨s3, q3, copyRun⟩ := runCompiledTo_next_inv copyRun
  obtain ⟨next, q4, nextRun⟩ := runCompiledTo_next_inv copyRun
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have pushSize := of_run_pushB256 r1
  have p1 := prefix_of_push pushSize pCopy
  have pushOffset := of_run_push r2
  have p2 : Nat.toB256 argsOffset :: (96 : B256) :: tail <<+ s2.stack := by
    simpa [ossifiablePushCreationCoordinate, B256.toB256_toBytes] using
      prefix_of_push pushOffset p1
  have pushZero := of_run_pushB256 r3
  have p3 := prefix_of_push pushZero p2
  have wf3 : Mem.Wf s3.memory := by
    rw [← pushZero.memory, ← pushOffset.memory, ← pushSize.memory,
      ← memoryCopy]
    exact hwf
  have reads3 : Mem.Reads s3.memory image := by
    rw [← pushZero.memory, ← pushOffset.memory, ← pushSize.memory,
      ← memoryCopy]
    exact hreads
  obtain ⟨pNext, wfNext, readsNext, stateNext, logsNext⟩ :=
    of_run_codecopy_image p3 wf3 reads3 r4
  refine ⟨next, nextRun, pNext, wfNext, ?_, ?_, ?_⟩
  · simpa [ossifiableConstructorHeadImage, ByteArray.sliceD_eq,
      B256.toNat_toB256_of_lt (by omega : argsOffset < 2 ^ 256),
      show ((0 : B256)).toNat = 0 from by decide,
      show ((96 : B256)).toNat = 96 from by decide,
      show Linst.toUInt8 .stop = 0 from by decide] using readsNext
  · exact stateCopy.trans
      (pushSize.state.trans (pushOffset.state.trans
        (pushZero.state.trans stateNext)))
  · exact logsCopy.trans
      (pushSize.logs.trans (pushOffset.logs.trans
        (pushZero.logs.trans logsNext)))

/-! ## Strict address-head guards -/

private theorem constructorDecode_step_cleanAddress
    {fs : List Func} {sevm : Sevm} {pre : Devm} {suffix : Func}
    {word value : B256} {tail : Stack} {image : Bytes}
    {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hword : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (hclean : addressMask &&& value = 0)
    (run : Func.RunCompiledTo fs sevm pre
      (constructorDecodeLoadWord word +++ checkNonAddress +++
        ((.call 1) <?> suffix)) out) :
    ∃ next,
      Func.RunCompiledTo fs sevm next suffix out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory image ∧
      pre.state = next.state ∧
      pre.logs = next.logs := by
  obtain ⟨loaded, loadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pLoaded, wfLoaded, readsLoaded, stateLoaded⟩ :=
    of_run_loadWordAt_image (word := word) (value := value)
      hp hwf hreads hword loadRun
  have logsLoaded := of_run_loadWordAt_logs loadRun
  obtain ⟨tested, checkRun, branchRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨dirty, pDirty, dirtyZero⟩ :=
    of_check_non_address pLoaded checkRun
  have valid : ValidAdr value := validAdr_iff.mpr hclean
  have pZero : (0 : B256) :: tail <<+ tested.stack := by
    simpa [dirtyZero.mpr valid] using pDirty
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_, ?_⟩
  · rw [← hpop.memory,
      ← Line.of_inv Devm.memory (by line_inv) checkRun]
    exact wfLoaded
  · rw [← hpop.memory,
      ← Line.of_inv Devm.memory (by line_inv) checkRun]
    exact readsLoaded
  · exact stateLoaded.trans
      ((Line.of_inv Devm.state (by line_inv) checkRun).trans hpop.state)
  · exact logsLoaded.trans
      ((Line.of_inv Devm.logs (by line_inv) checkRun).trans hpop.logs)

private theorem ossifiableConstructorHeadImage_implementationWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorHeadImage image code argsOffset).sliceD 0 32 0) =
      ossifiableConstructorCodeWord code argsOffset := by
  have hheadLength : (code.sliceD argsOffset 96 0).length = 96 := by
    unfold List.sliceD
    exact List.takeD_length _ _ _
  unfold ossifiableConstructorHeadImage ossifiableConstructorCodeWord
  rw [Bytes.sliceD_writeAt_inside _ _ 0 0 32 (by omega)
      (by rw [hheadLength]; omega),
    Bytes.sliceD_sliceD_of_le _ argsOffset 96 0 32 (by omega)]
  simp only [Nat.add_zero]

private theorem ossifiableConstructorHeadImage_adminWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorHeadImage image code argsOffset).sliceD 32 32 0) =
      ossifiableConstructorCodeWord code (argsOffset + 32) := by
  have hheadLength : (code.sliceD argsOffset 96 0).length = 96 := by
    unfold List.sliceD
    exact List.takeD_length _ _ _
  unfold ossifiableConstructorHeadImage ossifiableConstructorCodeWord
  rw [Bytes.sliceD_writeAt_inside _ _ 0 32 32 (by omega)
      (by rw [hheadLength]; omega),
    Bytes.sliceD_sliceD_of_le _ argsOffset 96 32 32 (by omega)]

private theorem ossifiableConstructorHeadImage_offsetWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorHeadImage image code argsOffset).sliceD 64 32 0) =
      ossifiableConstructorCodeWord code (argsOffset + 64) := by
  have hheadLength : (code.sliceD argsOffset 96 0).length = 96 := by
    unfold List.sliceD
    exact List.takeD_length _ _ _
  unfold ossifiableConstructorHeadImage ossifiableConstructorCodeWord
  rw [Bytes.sliceD_writeAt_inside _ _ 0 64 32 (by omega)
      (by rw [hheadLength]),
    Bytes.sliceD_sliceD_of_le _ argsOffset 96 64 32 (by omega)]

/-- Boundary after the implementation head has passed the strict address
check, before the requested-admin word is tested. -/
inductive OssifiableConstructorImplementationBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterImplementation argsOffset body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorHeadImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

theorem OssifiableConstructorHeadBoundary.implementationClean
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (head : OssifiableConstructorHeadBoundary fs sevm entry body argsOffset
      tail image out)
    (hclean : addressMask &&&
      ossifiableConstructorCodeWord sevm.code.toList argsOffset = 0) :
    OssifiableConstructorImplementationBoundary fs sevm entry body argsOffset
      tail image out := by
  rcases head with
    ⟨headPre, headRun, pHead, wfHead, readsHead, stateHead, logsHead⟩
  change Func.RunCompiledTo fs sevm headPre
    (constructorDecodeLoadWord 0 +++ checkNonAddress +++
      ((.call 1) <?>
        constructorDecodeAfterImplementation argsOffset body)) out at headRun
  obtain ⟨next, nextRun, pNext, wfNext, readsNext, stateNext, logsNext⟩ :=
    constructorDecode_step_cleanAddress
      (suffix := constructorDecodeAfterImplementation argsOffset body)
      (word := 0)
      (value := ossifiableConstructorCodeWord sevm.code.toList argsOffset)
      pHead wfHead readsHead
      (ossifiableConstructorHeadImage_implementationWord _ _ _)
      hclean headRun
  exact ⟨next, nextRun, pNext, wfNext, readsNext,
    stateHead.trans stateNext, logsHead.trans logsNext⟩

/-- Boundary after both strict Solidity address words have been accepted. -/
inductive OssifiableConstructorAddressBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterAdmin argsOffset body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorHeadImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

theorem OssifiableConstructorImplementationBoundary.adminClean
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (implementation : OssifiableConstructorImplementationBoundary fs sevm
      entry body argsOffset tail image out)
    (hclean : addressMask &&&
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32) = 0) :
    OssifiableConstructorAddressBoundary fs sevm entry body argsOffset tail
      image out := by
  rcases implementation with
    ⟨adminPre, adminRun, pAdmin, wfAdmin, readsAdmin,
      stateAdmin, logsAdmin⟩
  change Func.RunCompiledTo fs sevm adminPre
    (constructorDecodeLoadWord 1 +++ checkNonAddress +++
      ((.call 1) <?> constructorDecodeAfterAdmin argsOffset body)) out at adminRun
  obtain ⟨next, nextRun, pNext, wfNext, readsNext, stateNext, logsNext⟩ :=
    constructorDecode_step_cleanAddress
      (suffix := constructorDecodeAfterAdmin argsOffset body)
      (word := 1)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (argsOffset + 32))
      pAdmin wfAdmin readsAdmin
      (ossifiableConstructorHeadImage_adminWord _ _ _) hclean adminRun
  exact ⟨next, nextRun, pNext, wfNext, readsNext,
    stateAdmin.trans stateNext, logsAdmin.trans logsNext⟩

/-! ## Dynamic-offset guard and pointer store -/

/-- Boundary after the relative dynamic offset has passed the decoder's
`uint64.max` guard. -/
inductive OssifiableConstructorOffsetBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterOffsetBound argsOffset body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorHeadImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

theorem OssifiableConstructorAddressBoundary.offsetBound
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (address : OssifiableConstructorAddressBoundary fs sevm entry body
      argsOffset tail image out)
    (hbound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) :
    OssifiableConstructorOffsetBoundary fs sevm entry body argsOffset tail
      image out := by
  rcases address with
    ⟨offsetPre, offsetRun, pOffset, wfOffset, readsOffset,
      stateOffset, logsOffset⟩
  change Func.RunCompiledTo fs sevm offsetPre
    (pushB256 ossifiableConstructorAbiMaxUint64 :::
      constructorDecodeLoadWord 2 +++ gt :::
        ((.call 1) <?> constructorDecodeAfterOffsetBound argsOffset body)) out at offsetRun
  obtain ⟨s1, q1, offsetRun⟩ := runCompiledTo_next_inv offsetRun
  have r1 := Ninst.Run.of_runCompiled q1
  have pushMax := of_run_pushB256 r1
  have p1 := prefix_of_push pushMax pOffset
  have wf1 : Mem.Wf s1.memory := by rw [← pushMax.memory]; exact wfOffset
  have reads1 : Mem.Reads s1.memory
      (ossifiableConstructorHeadImage image sevm.code.toList argsOffset) := by
    rw [← pushMax.memory]
    exact readsOffset
  obtain ⟨s2, loadRun, offsetRun⟩ := runCompiledTo_prepend_inv offsetRun
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_loadWordAt_image (word := 2)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (argsOffset + 64))
      p1 wf1 reads1
      (ossifiableConstructorHeadImage_offsetWord _ _ _) loadRun
  have logs2 := of_run_loadWordAt_logs loadRun
  obtain ⟨s3, q3, branchRun⟩ := runCompiledTo_next_inv offsetRun
  have r3 := Ninst.Run.of_runCompiled q3
  have p3 := prefix_of_gt r3 p2
  have hguard :
      (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64) >?
        ossifiableConstructorAbiMaxUint64) = 0 := by
    unfold B256.gtCheck
    rw [if_neg hbound]
  have pZero : (0 : B256) :: tail <<+ s3.stack := by
    simpa [hguard] using p3
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact wf2
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact reads2
  · exact stateOffset.trans (pushMax.state.trans
      (state2.trans ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        hpop.state)))
  · exact logsOffset.trans (pushMax.logs.trans
      (logs2.trans ((Ninst.Hinv.inv (f := Devm.logs) r3).trans
        hpop.logs)))

/-- Proof image after storing the wrapped dynamic-data pointer at scratch word
3.  The EVM-word addition remains visible exactly as in the pure decoder. -/
def ossifiableConstructorPointerImage
    (image code : Bytes) (argsOffset : Nat) : Bytes :=
  Bytes.writeAt (ossifiableConstructorHeadImage image code argsOffset) 96
    (ossifiableConstructorDataPointer argsOffset
      (ossifiableConstructorCodeWord code (argsOffset + 64))).toBytes

/-- Boundary after the relative offset has been added to the argument base and
the exact wrapped pointer stored at scratch word 3. -/
inductive OssifiableConstructorPointerBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterPointer body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorPointerImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

theorem OssifiableConstructorOffsetBoundary.storePointer
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (offset : OssifiableConstructorOffsetBoundary fs sevm entry body
      argsOffset tail image out) :
    OssifiableConstructorPointerBoundary fs sevm entry body argsOffset tail
      image out := by
  rcases offset with
    ⟨pointerPre, pointerRun, pPointer, wfPointer, readsPointer,
      statePointer, logsPointer⟩
  change Func.RunCompiledTo fs sevm pointerPre
    (constructorDecodeLoadWord 2 +++
      ossifiablePushCreationCoordinate argsOffset ::: add :::
        mstoreAt 3 +++ constructorDecodeAfterPointer body) out at pointerRun
  obtain ⟨s1, loadRun, pointerRun⟩ := runCompiledTo_prepend_inv pointerRun
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image (word := 2)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (argsOffset + 64))
      pPointer wfPointer readsPointer
      (ossifiableConstructorHeadImage_offsetWord _ _ _) loadRun
  have logs1 := of_run_loadWordAt_logs loadRun
  obtain ⟨s2, q2, pointerRun⟩ := runCompiledTo_next_inv pointerRun
  have r2 := Ninst.Run.of_runCompiled q2
  have pushBase := of_run_push r2
  have p2 : Nat.toB256 argsOffset ::
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64) ::
      tail <<+ s2.stack := by
    simpa [ossifiablePushCreationCoordinate, B256.toB256_toBytes] using
      prefix_of_push pushBase p1
  obtain ⟨s3, q3, pointerRun⟩ := runCompiledTo_next_inv pointerRun
  have r3 := Ninst.Run.of_runCompiled q3
  have p3 : ossifiableConstructorDataPointer argsOffset
      (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) ::
      tail <<+ s3.stack := by
    have pointerEq :
        Nat.toB256 argsOffset +
          ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64) =
        ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64)) := by
      unfold ossifiableConstructorDataPointer
      exact B256.add_comm
    rw [← pointerEq]
    exact prefix_of_add r3 p2
  have wf3 : Mem.Wf s3.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3, ← pushBase.memory]
    exact wf1
  have reads3 : Mem.Reads s3.memory
      (ossifiableConstructorHeadImage image sevm.code.toList argsOffset) := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3, ← pushBase.memory]
    exact reads1
  obtain ⟨next, storeRun, nextRun⟩ :=
    runCompiledTo_prepend_inv pointerRun
  obtain ⟨pNext, wfNext, readsNext, stateNext⟩ :=
    of_run_mstoreAt_image p3 wf3 reads3 storeRun
  rw [show ((3 : B256) * 32).toNat = 96 from by decide] at readsNext
  refine ⟨next, nextRun, pNext, wfNext, ?_, ?_, ?_⟩
  · simpa [ossifiableConstructorPointerImage] using readsNext
  · exact statePointer.trans (state1.trans (pushBase.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) r3).trans stateNext)))
  · exact logsPointer.trans (logs1.trans (pushBase.logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) r3).trans
        (Line.of_inv Devm.logs (by line_inv) storeRun))))

/-! ## Dynamic length word -/

private theorem ossifiableConstructorPointerImage_pointerWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorPointerImage image code argsOffset).sliceD
        96 32 0) =
      ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64)) := by
  unfold ossifiableConstructorPointerImage
  exact Bytes.readWord_writeAt_self _ 96 _

/-- Boundary after proving that the dynamic length word is fully contained in
the creation-code image. -/
inductive OssifiableConstructorLengthCompleteBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterLengthComplete body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorPointerImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

theorem OssifiableConstructorPointerBoundary.lengthComplete
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (pointer : OssifiableConstructorPointerBoundary fs sevm entry body
      argsOffset tail image out)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hcomplete :
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) +
          32).toNat ≤ sevm.code.size) :
    OssifiableConstructorLengthCompleteBoundary fs sevm entry body argsOffset
      tail image out := by
  rcases pointer with
    ⟨lengthPre, lengthRun, pLength, wfLength, readsLength,
      stateLength, logsLength⟩
  change Func.RunCompiledTo fs sevm lengthPre
    (constructorDecodeLoadWord 3 +++ pushB256 32 ::: add :::
      codesize ::: lt :::
        ((.call 1) <?> constructorDecodeAfterLengthComplete body)) out at lengthRun
  obtain ⟨s1, loadRun, lengthRun⟩ := runCompiledTo_prepend_inv lengthRun
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image (word := 3)
      (value := ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)))
      pLength wfLength readsLength
      (ossifiableConstructorPointerImage_pointerWord _ _ _) loadRun
  have logs1 := of_run_loadWordAt_logs loadRun
  obtain ⟨s2, q2, lengthRun⟩ := runCompiledTo_next_inv lengthRun
  obtain ⟨s3, q3, lengthRun⟩ := runCompiledTo_next_inv lengthRun
  obtain ⟨s4, q4, lengthRun⟩ := runCompiledTo_next_inv lengthRun
  obtain ⟨s5, q5, branchRun⟩ := runCompiledTo_next_inv lengthRun
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have r5 := Ninst.Run.of_runCompiled q5
  have push32 := of_run_pushB256 r2
  have p2 := prefix_of_push push32 p1
  have p3 :
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) +
          32) :: tail <<+ s3.stack := by
    have startEq :
        (32 : B256) +
          ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) =
        ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) + 32 :=
      B256.add_comm
    rw [← startEq]
    exact prefix_of_add r3 p2
  have codeSize := of_run_codesize r4
  have p4 := prefix_of_push codeSize p3
  have p5 := prefix_of_lt r5 p4
  have hguard :
      (sevm.code.size.toB256 <?
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) +
            32)) = 0 := by
    unfold B256.ltCheck
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hcodeSize]
    omega
  have pZero : (0 : B256) :: tail <<+ s5.stack := by
    simpa [hguard] using p5
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← codeSize.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← push32.memory]
    exact wf1
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← codeSize.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← push32.memory]
    exact reads1
  · exact stateLength.trans (state1.trans (push32.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        (codeSize.state.trans
          ((Ninst.Hinv.inv (f := Devm.state) r5).trans hpop.state)))))
  · exact logsLength.trans (logs1.trans (push32.logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) r3).trans
        (codeSize.logs.trans
          ((Ninst.Hinv.inv (f := Devm.logs) r5).trans hpop.logs)))))

/-- Proof image after copying the exact dynamic length word to scratch word 4. -/
def ossifiableConstructorLengthImage
    (image code : Bytes) (argsOffset : Nat) : Bytes :=
  Bytes.writeAt (ossifiableConstructorPointerImage image code argsOffset) 128
    (code.sliceD
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat
      32 0)

private theorem ossifiableConstructorLengthImage_lengthWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorLengthImage image code argsOffset).sliceD
        128 32 0) =
      ossifiableConstructorCodeWord code
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat := by
  let pointer := ossifiableConstructorDataPointer argsOffset
    (ossifiableConstructorCodeWord code (argsOffset + 64))
  let payload := code.sliceD pointer.toNat 32 0
  have hlength : payload.length = 32 := by
    dsimp only [payload]
    unfold List.sliceD
    exact List.takeD_length _ _ _
  change Bytes.toB256
      ((Bytes.writeAt (ossifiableConstructorPointerImage image code argsOffset)
        128 payload).sliceD 128 32 0) = Bytes.toB256 payload
  have hslice :
      (Bytes.writeAt (ossifiableConstructorPointerImage image code argsOffset)
        128 payload).sliceD 128 32 0 = payload := by
    rw [← hlength]
    exact Bytes.sliceD_writeAt _ _ _
  exact congrArg Bytes.toB256 hslice

/-- Boundary after the actual length-word `CODECOPY`. -/
inductive OssifiableConstructorLengthBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterLengthCopy body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorLengthImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

theorem OssifiableConstructorLengthCompleteBoundary.copyLength
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (complete : OssifiableConstructorLengthCompleteBoundary fs sevm entry body
      argsOffset tail image out) :
    OssifiableConstructorLengthBoundary fs sevm entry body argsOffset tail
      image out := by
  rcases complete with
    ⟨copyPre, copyRun, pCopy, wfCopy, readsCopy, stateCopy, logsCopy⟩
  change Func.RunCompiledTo fs sevm copyPre
    (pushB256 32 ::: constructorDecodeLoadWord 3 +++
      pushB256 128 ::: codecopy ::: constructorDecodeAfterLengthCopy body) out at copyRun
  obtain ⟨s1, q1, copyRun⟩ := runCompiledTo_next_inv copyRun
  have r1 := Ninst.Run.of_runCompiled q1
  have pushSize := of_run_pushB256 r1
  have p1 := prefix_of_push pushSize pCopy
  have wf1 : Mem.Wf s1.memory := by rw [← pushSize.memory]; exact wfCopy
  have reads1 : Mem.Reads s1.memory
      (ossifiableConstructorPointerImage image sevm.code.toList argsOffset) := by
    rw [← pushSize.memory]
    exact readsCopy
  obtain ⟨s2, loadRun, copyRun⟩ := runCompiledTo_prepend_inv copyRun
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_loadWordAt_image (word := 3)
      (value := ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)))
      p1 wf1 reads1
      (ossifiableConstructorPointerImage_pointerWord _ _ _) loadRun
  have logs2 := of_run_loadWordAt_logs loadRun
  obtain ⟨s3, q3, copyRun⟩ := runCompiledTo_next_inv copyRun
  obtain ⟨next, q4, nextRun⟩ := runCompiledTo_next_inv copyRun
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have pushDest := of_run_pushB256 r3
  have p3 := prefix_of_push pushDest p2
  have wf3 : Mem.Wf s3.memory := by rw [← pushDest.memory]; exact wf2
  have reads3 : Mem.Reads s3.memory
      (ossifiableConstructorPointerImage image sevm.code.toList argsOffset) := by
    rw [← pushDest.memory]
    exact reads2
  obtain ⟨pNext, wfNext, readsNext, stateNext, logsNext⟩ :=
    of_run_codecopy_image p3 wf3 reads3 r4
  refine ⟨next, nextRun, pNext, wfNext, ?_, ?_, ?_⟩
  · simpa [ossifiableConstructorLengthImage, ByteArray.sliceD_eq,
      show ((128 : B256)).toNat = 128 from by decide,
      show ((32 : B256)).toNat = 32 from by decide,
      show Linst.toUInt8 .stop = 0 from by decide] using readsNext
  · exact stateCopy.trans (pushSize.state.trans (state2.trans
      (pushDest.state.trans stateNext)))
  · exact logsCopy.trans (pushSize.logs.trans (logs2.trans
      (pushDest.logs.trans logsNext)))

/-! ## Length guard and payload extent -/

/-- Boundary after the copied dynamic length has passed the `uint64.max`
allocation guard. -/
inductive OssifiableConstructorLengthBoundBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterLengthBound body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorLengthImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

theorem OssifiableConstructorLengthBoundary.lengthBound
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (length : OssifiableConstructorLengthBoundary fs sevm entry body
      argsOffset tail image out)
    (hbound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat) :
    OssifiableConstructorLengthBoundBoundary fs sevm entry body argsOffset
      tail image out := by
  rcases length with
    ⟨boundPre, boundRun, pBound, wfBound, readsBound,
      stateBound, logsBound⟩
  change Func.RunCompiledTo fs sevm boundPre
    (pushB256 ossifiableConstructorAbiMaxUint64 :::
      constructorDecodeLoadWord 4 +++ gt :::
        ((.call 7) <?> constructorDecodeAfterLengthBound body)) out at boundRun
  obtain ⟨s1, q1, boundRun⟩ := runCompiledTo_next_inv boundRun
  have r1 := Ninst.Run.of_runCompiled q1
  have pushMax := of_run_pushB256 r1
  have p1 := prefix_of_push pushMax pBound
  have wf1 : Mem.Wf s1.memory := by rw [← pushMax.memory]; exact wfBound
  have reads1 : Mem.Reads s1.memory
      (ossifiableConstructorLengthImage image sevm.code.toList argsOffset) := by
    rw [← pushMax.memory]
    exact readsBound
  obtain ⟨s2, loadRun, boundRun⟩ := runCompiledTo_prepend_inv boundRun
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_loadWordAt_image (word := 4)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat)
      p1 wf1 reads1
      (ossifiableConstructorLengthImage_lengthWord _ _ _) loadRun
  have logs2 := of_run_loadWordAt_logs loadRun
  obtain ⟨s3, q3, branchRun⟩ := runCompiledTo_next_inv boundRun
  have r3 := Ninst.Run.of_runCompiled q3
  have p3 := prefix_of_gt r3 p2
  have hguard :
      (ossifiableConstructorCodeWord sevm.code.toList
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat >?
        ossifiableConstructorAbiMaxUint64) = 0 := by
    unfold B256.gtCheck
    rw [if_neg hbound]
  have pZero : (0 : B256) :: tail <<+ s3.stack := by
    simpa [hguard] using p3
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact wf2
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact reads2
  · exact stateBound.trans (pushMax.state.trans
      (state2.trans ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        hpop.state)))
  · exact logsBound.trans (pushMax.logs.trans
      (logs2.trans ((Ninst.Hinv.inv (f := Devm.logs) r3).trans
        hpop.logs)))

/-- Boundary after proving the declared setup payload is fully contained in
the creation-code image. -/
inductive OssifiableConstructorPayloadCompleteBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (next : Devm)
      (run : Func.RunCompiledTo fs sevm next
        (constructorDecodeAfterPayloadBound body) out)
      (stack : tail <<+ next.stack)
      (memoryWf : Mem.Wf next.memory)
      (memoryReads : Mem.Reads next.memory
        (ossifiableConstructorLengthImage image sevm.code.toList argsOffset))
      (state : entry.state = next.state)
      (logs : entry.logs = next.logs)

private theorem ossifiableConstructorLengthImage_pointerWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorLengthImage image code argsOffset).sliceD
        96 32 0) =
      ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64)) := by
  unfold ossifiableConstructorLengthImage
  rw [Bytes.sliceD_writeAt_before _ _ 96 32 128 (by omega)]
  exact ossifiableConstructorPointerImage_pointerWord _ _ _

theorem OssifiableConstructorLengthBoundBoundary.payloadComplete
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (length : OssifiableConstructorLengthBoundBoundary fs sevm entry body
      argsOffset tail image out)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hcomplete :
      (ossifiableConstructorDataEnd argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
        (ossifiableConstructorCodeWord sevm.code.toList
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat)).toNat ≤ sevm.code.size) :
    OssifiableConstructorPayloadCompleteBoundary fs sevm entry body argsOffset
      tail image out := by
  rcases length with
    ⟨payloadPre, payloadRun, pPayload, wfPayload, readsPayload,
      statePayload, logsPayload⟩
  change Func.RunCompiledTo fs sevm payloadPre
    (constructorDecodeLoadWord 3 +++ pushB256 32 ::: add :::
      constructorDecodeLoadWord 4 +++ add ::: codesize ::: lt :::
        ((.call 1) <?> constructorDecodeAfterPayloadBound body)) out at payloadRun
  obtain ⟨s1, loadPointerRun, payloadRun⟩ :=
    runCompiledTo_prepend_inv payloadRun
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image (word := 3)
      (value := ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)))
      pPayload wfPayload readsPayload
      (ossifiableConstructorLengthImage_pointerWord _ _ _) loadPointerRun
  have logs1 := of_run_loadWordAt_logs loadPointerRun
  obtain ⟨s2, q2, payloadRun⟩ := runCompiledTo_next_inv payloadRun
  obtain ⟨s3, q3, payloadRun⟩ := runCompiledTo_next_inv payloadRun
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have push32 := of_run_pushB256 r2
  have p2 := prefix_of_push push32 p1
  have p3 : ossifiableConstructorDataStart argsOffset
      (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) ::
      tail <<+ s3.stack := by
    have startEq :
        (32 : B256) +
          ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) =
        ossifiableConstructorDataStart argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64)) := by
      unfold ossifiableConstructorDataStart
      exact B256.add_comm
    rw [← startEq]
    exact prefix_of_add r3 p2
  have wf3 : Mem.Wf s3.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3, ← push32.memory]
    exact wf1
  have reads3 : Mem.Reads s3.memory
      (ossifiableConstructorLengthImage image sevm.code.toList argsOffset) := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3, ← push32.memory]
    exact reads1
  obtain ⟨s4, loadLengthRun, payloadRun⟩ :=
    runCompiledTo_prepend_inv payloadRun
  obtain ⟨p4, wf4, reads4, state4⟩ :=
    of_run_loadWordAt_image (word := 4)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat)
      p3 wf3 reads3
      (ossifiableConstructorLengthImage_lengthWord _ _ _) loadLengthRun
  have logs4 := of_run_loadWordAt_logs loadLengthRun
  obtain ⟨s5, q5, payloadRun⟩ := runCompiledTo_next_inv payloadRun
  obtain ⟨s6, q6, payloadRun⟩ := runCompiledTo_next_inv payloadRun
  obtain ⟨s7, q7, branchRun⟩ := runCompiledTo_next_inv payloadRun
  have r5 := Ninst.Run.of_runCompiled q5
  have r6 := Ninst.Run.of_runCompiled q6
  have r7 := Ninst.Run.of_runCompiled q7
  have p5 : ossifiableConstructorDataEnd argsOffset
      (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
      (ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat) :: tail <<+ s5.stack := by
    have endEq :
        ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat +
          ossifiableConstructorDataStart argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) =
        ossifiableConstructorDataEnd argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
          (ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat) := by
      unfold ossifiableConstructorDataEnd
      exact B256.add_comm
    rw [← endEq]
    exact prefix_of_add r5 p4
  have codeSize := of_run_codesize r6
  have p6 := prefix_of_push codeSize p5
  have p7 := prefix_of_lt r7 p6
  have hguard :
      (sevm.code.size.toB256 <?
        ossifiableConstructorDataEnd argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
          (ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat)) = 0 := by
    unfold B256.ltCheck
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hcodeSize]
    omega
  have pZero : (0 : B256) :: tail <<+ s7.stack := by
    simpa [hguard] using p7
  obtain ⟨next, hpop, nextRun, pNext⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pZero branchRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r7,
      ← codeSize.memory, ← Ninst.Hinv.inv (f := Devm.memory) r5]
    exact wf4
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r7,
      ← codeSize.memory, ← Ninst.Hinv.inv (f := Devm.memory) r5]
    exact reads4
  · exact statePayload.trans (state1.trans (push32.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        (state4.trans ((Ninst.Hinv.inv (f := Devm.state) r5).trans
          (codeSize.state.trans
            ((Ninst.Hinv.inv (f := Devm.state) r7).trans hpop.state)))))))
  · exact logsPayload.trans (logs1.trans (push32.logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) r3).trans
        (logs4.trans ((Ninst.Hinv.inv (f := Devm.logs) r5).trans
          (codeSize.logs.trans
            ((Ninst.Hinv.inv (f := Devm.logs) r7).trans hpop.logs)))))))

/-! ## Accepted decoder body boundary -/

def ossifiableConstructorDecodedImage
    (image code : Bytes) (argsOffset : Nat) : Bytes :=
  let offset := ossifiableConstructorCodeWord code (argsOffset + 64)
  let pointer := ossifiableConstructorDataPointer argsOffset offset
  let length := ossifiableConstructorCodeWord code pointer.toNat
  Bytes.writeAt (ossifiableConstructorLengthImage image code argsOffset) 0x100
    (code.sliceD (pointer + 32).toNat length.toNat 0)

@[simp] theorem ossifiableConstructorDecodedImage_implementationWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorDecodedImage image code argsOffset).sliceD
        0 32 0) =
      ossifiableConstructorCodeWord code argsOffset := by
  unfold ossifiableConstructorDecodedImage ossifiableConstructorLengthImage
    ossifiableConstructorPointerImage
  rw [Bytes.sliceD_writeAt_before _ _ 0 32 0x100 (by omega),
    Bytes.sliceD_writeAt_before _ _ 0 32 128 (by omega),
    Bytes.sliceD_writeAt_before _ _ 0 32 96 (by omega)]
  exact ossifiableConstructorHeadImage_implementationWord _ _ _

@[simp] theorem ossifiableConstructorDecodedImage_adminWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorDecodedImage image code argsOffset).sliceD
        32 32 0) =
      ossifiableConstructorCodeWord code (argsOffset + 32) := by
  unfold ossifiableConstructorDecodedImage ossifiableConstructorLengthImage
    ossifiableConstructorPointerImage
  rw [Bytes.sliceD_writeAt_before _ _ 32 32 0x100 (by omega),
    Bytes.sliceD_writeAt_before _ _ 32 32 128 (by omega),
    Bytes.sliceD_writeAt_before _ _ 32 32 96 (by omega)]
  exact ossifiableConstructorHeadImage_adminWord _ _ _

@[simp] theorem ossifiableConstructorDecodedImage_lengthWord
    (image code : Bytes) (argsOffset : Nat) :
    Bytes.toB256
      ((ossifiableConstructorDecodedImage image code argsOffset).sliceD
        128 32 0) =
      ossifiableConstructorCodeWord code
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat := by
  unfold ossifiableConstructorDecodedImage
  rw [Bytes.sliceD_writeAt_before _ _ 128 32 0x100 (by omega)]
  exact ossifiableConstructorLengthImage_lengthWord _ _ _

@[simp] theorem ossifiableConstructorDecodedImage_setupData
    (image code : Bytes) (argsOffset : Nat) :
    let offset := ossifiableConstructorCodeWord code (argsOffset + 64)
    let pointer := ossifiableConstructorDataPointer argsOffset offset
    let length := ossifiableConstructorCodeWord code pointer.toNat
    (ossifiableConstructorDecodedImage image code argsOffset).sliceD
        0x100 length.toNat 0 =
      code.sliceD (pointer + 32).toNat length.toNat 0 := by
  dsimp only
  let offset := ossifiableConstructorCodeWord code (argsOffset + 64)
  let pointer := ossifiableConstructorDataPointer argsOffset offset
  let length := ossifiableConstructorCodeWord code pointer.toNat
  let payload := code.sliceD (pointer + 32).toNat length.toNat 0
  have hpayloadLength : payload.length = length.toNat := by
    dsimp only [payload]
    unfold List.sliceD
    exact List.takeD_length _ _ _
  change
    (Bytes.writeAt (ossifiableConstructorLengthImage image code argsOffset)
      0x100 payload).sliceD 0x100 length.toNat 0 = payload
  rw [← hpayloadLength]
  exact Bytes.sliceD_writeAt _ _ _

/-- Execution-derived boundary at the protected constructor body for an
accepted strict decoder route. -/
inductive OssifiableConstructorDecodeBoundary
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | intro (bodyPre : Devm)
      (bodyRun : Func.RunCompiledTo fs sevm bodyPre body out)
      (stack : tail <<+ bodyPre.stack)
      (memoryWf : Mem.Wf bodyPre.memory)
      (memoryReads : Mem.Reads bodyPre.memory
        (ossifiableConstructorDecodedImage image sevm.code.toList argsOffset))
      (state : entry.state = bodyPre.state)
      (logs : entry.logs = bodyPre.logs)

theorem OssifiableConstructorPayloadCompleteBoundary.copyPayload
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (payload : OssifiableConstructorPayloadCompleteBoundary fs sevm entry body
      argsOffset tail image out) :
    OssifiableConstructorDecodeBoundary fs sevm entry body argsOffset tail
      image out := by
  rcases payload with
    ⟨copyPre, copyRun, pCopy, wfCopy, readsCopy, stateCopy, logsCopy⟩
  change Func.RunCompiledTo fs sevm copyPre
    (constructorDecodeLoadWord 4 +++ constructorDecodeLoadWord 3 +++
      pushB256 32 ::: add ::: pushB256 0x100 ::: codecopy ::: body) out at copyRun
  obtain ⟨s1, loadLengthRun, copyRun⟩ :=
    runCompiledTo_prepend_inv copyRun
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image (word := 4)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat)
      pCopy wfCopy readsCopy
      (ossifiableConstructorLengthImage_lengthWord _ _ _) loadLengthRun
  have logs1 := of_run_loadWordAt_logs loadLengthRun
  obtain ⟨s2, loadPointerRun, copyRun⟩ :=
    runCompiledTo_prepend_inv copyRun
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_loadWordAt_image (word := 3)
      (value := ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)))
      p1 wf1 reads1
      (ossifiableConstructorLengthImage_pointerWord _ _ _) loadPointerRun
  have logs2 := of_run_loadWordAt_logs loadPointerRun
  obtain ⟨s3, q3, copyRun⟩ := runCompiledTo_next_inv copyRun
  obtain ⟨s4, q4, copyRun⟩ := runCompiledTo_next_inv copyRun
  obtain ⟨s5, q5, copyRun⟩ := runCompiledTo_next_inv copyRun
  obtain ⟨bodyPre, q6, bodyRun⟩ := runCompiledTo_next_inv copyRun
  have r3 := Ninst.Run.of_runCompiled q3
  have r4 := Ninst.Run.of_runCompiled q4
  have r5 := Ninst.Run.of_runCompiled q5
  have r6 := Ninst.Run.of_runCompiled q6
  have push32 := of_run_pushB256 r3
  have p3 := prefix_of_push push32 p2
  have p4 : ossifiableConstructorDataStart argsOffset
      (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) ::
      ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat :: tail <<+ s4.stack := by
    have startEq :
        (32 : B256) +
          ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) =
        ossifiableConstructorDataStart argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64)) := by
      unfold ossifiableConstructorDataStart
      exact B256.add_comm
    rw [← startEq]
    exact prefix_of_add r4 p3
  have pushDest := of_run_pushB256 r5
  have p5 := prefix_of_push pushDest p4
  have wf5 : Mem.Wf s5.memory := by
    rw [← pushDest.memory, ← Ninst.Hinv.inv (f := Devm.memory) r4,
      ← push32.memory]
    exact wf2
  have reads5 : Mem.Reads s5.memory
      (ossifiableConstructorLengthImage image sevm.code.toList argsOffset) := by
    rw [← pushDest.memory, ← Ninst.Hinv.inv (f := Devm.memory) r4,
      ← push32.memory]
    exact reads2
  obtain ⟨pBody, wfBody, readsBody, state6, logs6⟩ :=
    of_run_codecopy_image p5 wf5 reads5 r6
  refine ⟨bodyPre, bodyRun, pBody, wfBody, ?_, ?_, ?_⟩
  · simpa [ossifiableConstructorDecodedImage,
      ossifiableConstructorDataStart, ByteArray.sliceD_eq,
      show ((0x100 : B256)).toNat = 0x100 from by decide,
      show Linst.toUInt8 .stop = 0 from by decide] using readsBody
  · exact stateCopy.trans (state1.trans (state2.trans
      (push32.state.trans ((Ninst.Hinv.inv (f := Devm.state) r4).trans
        (pushDest.state.trans state6)))))
  · exact logsCopy.trans (logs1.trans (logs2.trans
      (push32.logs.trans ((Ninst.Hinv.inv (f := Devm.logs) r4).trans
        (pushDest.logs.trans logs6)))))

/-! ## Accepted-route composition -/

theorem ossifiableConstructorDecode_pointerBoundary_of_guards
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : argsOffset + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hheadComplete : argsOffset + 96 ≤ sevm.code.size)
    (himplementationClean : addressMask &&&
      ossifiableConstructorCodeWord sevm.code.toList argsOffset = 0)
    (hadminClean : addressMask &&&
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32) = 0)
    (hoffsetBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
    (run : Func.RunCompiledTo fs sevm entry
      (ossifiableConstructorDecode argsOffset body) out) :
    OssifiableConstructorPointerBoundary fs sevm entry body argsOffset tail
      image out := by
  have head := ossifiableConstructorDecode_headBoundary hp hwf hreads
    hcoordinate hcodeSize hheadComplete run
  have implementation := head.implementationClean himplementationClean
  have address := implementation.adminClean hadminClean
  exact (address.offsetBound hoffsetBound).storePointer

theorem OssifiableConstructorPointerBoundary.accepted
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (pointer : OssifiableConstructorPointerBoundary fs sevm entry body
      argsOffset tail image out)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hlengthComplete :
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) +
          32).toNat ≤ sevm.code.size)
    (hlengthBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat)
    (hpayloadComplete :
      (ossifiableConstructorDataEnd argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
        (ossifiableConstructorCodeWord sevm.code.toList
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat)).toNat ≤ sevm.code.size) :
    OssifiableConstructorDecodeBoundary fs sevm entry body argsOffset tail
      image out := by
  have complete := pointer.lengthComplete hcodeSize hlengthComplete
  have length := complete.copyLength
  have bounded := length.lengthBound hlengthBound
  exact (bounded.payloadComplete hcodeSize hpayloadComplete).copyPayload

/-- Seven successful natural decoder guards produce both the actual protected
body boundary and the matching total pure-spec result. -/
theorem ossifiableConstructorDecode_accepted_of_guards
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : argsOffset + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hheadComplete : argsOffset + 96 ≤ sevm.code.size)
    (himplementationClean : addressMask &&&
      ossifiableConstructorCodeWord sevm.code.toList argsOffset = 0)
    (hadminClean : addressMask &&&
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32) = 0)
    (hoffsetBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
    (hlengthComplete :
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) +
          32).toNat ≤ sevm.code.size)
    (hlengthBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat)
    (hpayloadComplete :
      (ossifiableConstructorDataEnd argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
        (ossifiableConstructorCodeWord sevm.code.toList
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat)).toNat ≤ sevm.code.size)
    (run : Func.RunCompiledTo fs sevm entry
      (ossifiableConstructorDecode argsOffset body) out) :
    OssifiableConstructorDecodeBoundary fs sevm entry body argsOffset tail
        image out ∧
      ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
        .accepted
          (ossifiableConstructorCodeWord sevm.code.toList argsOffset)
          (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32))
          (sevm.code.toList.sliceD
            (ossifiableConstructorDataStart argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat
            (ossifiableConstructorCodeWord sevm.code.toList
              (ossifiableConstructorDataPointer argsOffset
                (ossifiableConstructorCodeWord sevm.code.toList
                  (argsOffset + 64))).toNat).toNat
            0) := by
  have pointer := ossifiableConstructorDecode_pointerBoundary_of_guards
    hp hwf hreads hcoordinate hcodeSize hheadComplete himplementationClean
      hadminClean hoffsetBound run
  constructor
  · exact pointer.accepted hcodeSize hlengthComplete hlengthBound
      hpayloadComplete
  · apply ossifiableConstructorDecodeSpec_accepted
    · simpa only [← ByteArray.size_eq_length_toList] using hheadComplete
    · exact himplementationClean
    · exact hadminClean
    · exact hoffsetBound
    · simpa only [← ByteArray.size_eq_length_toList] using hlengthComplete
    · exact hlengthBound
    · simpa only [← ByteArray.size_eq_length_toList] using hpayloadComplete

/-! ## Total result-indexed routes -/

/-- Exhaustive executable exits of the strict constructor decoder.  Error
routes retain the actual auxiliary-call walk and the exact pure-spec result;
the accepted route retains the protected-body boundary. -/
inductive OssifiableConstructorDecodeRoute
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | accepted (implementation requestedAdmin : B256) (setupData : Bytes)
      (implementationClean : addressMask &&& implementation = 0)
      (requestedAdminClean : addressMask &&& requestedAdmin = 0)
      (setupLengthBound : ¬ ossifiableConstructorAbiMaxUint64 <
        ossifiableConstructorCodeWord sevm.code.toList
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat)
      (setupDataShape : setupData =
        sevm.code.toList.sliceD
          (ossifiableConstructorDataStart argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat
          (ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat).toNat
          0)
      (setupDataLength : setupData.length =
        (ossifiableConstructorCodeWord sevm.code.toList
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat).toNat)
      (spec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
        .accepted implementation requestedAdmin setupData)
      (boundary : OssifiableConstructorDecodeBoundary fs sevm entry body
        argsOffset tail image out)
  | emptyRevert (callPre : Devm) (callImage : Bytes)
      (spec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
        .emptyRevert)
      (run : Func.RunCompiledTo fs sevm callPre (.call 1) out)
      (stack : tail <<+ callPre.stack)
      (memoryWf : Mem.Wf callPre.memory)
      (memoryReads : Mem.Reads callPre.memory callImage)
      (state : entry.state = callPre.state)
      (logs : entry.logs = callPre.logs)
  | allocationPanic (callPre : Devm) (callImage : Bytes)
      (spec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
        .allocationPanic)
      (run : Func.RunCompiledTo fs sevm callPre (.call 7) out)
      (stack : tail <<+ callPre.stack)
      (memoryWf : Mem.Wf callPre.memory)
      (memoryReads : Mem.Reads callPre.memory callImage)
      (state : entry.state = callPre.state)
      (logs : entry.logs = callPre.logs)

theorem ossifiableConstructorDecode_shortHead_route
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : argsOffset + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hshort : sevm.code.size < argsOffset + 96)
    (run : Func.RunCompiledTo fs sevm entry
      (ossifiableConstructorDecode argsOffset body) out) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  rw [constructorDecode_split_shape] at run
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s3, q3, branchRun⟩ := runCompiledTo_next_inv run
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have pushHead := of_run_push r1
  have p1 : Nat.toB256 (argsOffset + 96) :: tail <<+ s1.stack := by
    simpa [ossifiablePushCreationCoordinate, B256.toB256_toBytes] using
      prefix_of_push pushHead hp
  have codeSize := of_run_codesize r2
  have p2 := prefix_of_push codeSize p1
  have p3 := prefix_of_lt r3 p2
  have hlt : sevm.code.size.toB256 < Nat.toB256 (argsOffset + 96) := by
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hcodeSize,
      B256.toNat_toB256_of_lt hcoordinate]
    exact hshort
  have hguard :
      (sevm.code.size.toB256 <? Nat.toB256 (argsOffset + 96)) = 1 := by
    unfold B256.ltCheck
    rw [if_pos hlt]
  have pOne : (1 : B256) :: tail <<+ s3.stack := by
    simpa [hguard] using p3
  obtain ⟨callPre, _, _, hpop, callRun, pCall⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) pOne branchRun
  have callWf : Mem.Wf callPre.memory := by
    rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← codeSize.memory, ← pushHead.memory]
    exact hwf
  have callReads : Mem.Reads callPre.memory image := by
    rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← codeSize.memory, ← pushHead.memory]
    exact hreads
  apply OssifiableConstructorDecodeRoute.emptyRevert callPre image
  · apply ossifiableConstructorDecodeSpec_shortHead
    simpa only [← ByteArray.size_eq_length_toList] using hshort
  · exact callRun
  · exact pCall
  · exact callWf
  · exact callReads
  · exact pushHead.state.trans (codeSize.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) r3).trans hpop.state))
  · exact pushHead.logs.trans (codeSize.logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) r3).trans hpop.logs))

private theorem constructorDecode_step_dirtyAddress
    {fs : List Func} {sevm : Sevm} {pre : Devm} {suffix : Func}
    {word value : B256} {tail : Stack} {image : Bytes}
    {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hword : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (hdirty : addressMask &&& value ≠ 0)
    (run : Func.RunCompiledTo fs sevm pre
      (constructorDecodeLoadWord word +++ checkNonAddress +++
        ((.call 1) <?> suffix)) out) :
    ∃ callPre,
      Func.RunCompiledTo fs sevm callPre (.call 1) out ∧
      tail <<+ callPre.stack ∧
      Mem.Wf callPre.memory ∧
      Mem.Reads callPre.memory image ∧
      pre.state = callPre.state ∧
      pre.logs = callPre.logs := by
  obtain ⟨loaded, loadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨pLoaded, wfLoaded, readsLoaded, stateLoaded⟩ :=
    of_run_loadWordAt_image (word := word) (value := value)
      hp hwf hreads hword loadRun
  have logsLoaded := of_run_loadWordAt_logs loadRun
  obtain ⟨tested, checkRun, branchRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨dirty, pDirty, dirtyZero⟩ :=
    of_check_non_address pLoaded checkRun
  have invalid : ¬ ValidAdr value := by
    intro valid
    exact hdirty (validAdr_iff.mp valid)
  have dirtyNe : dirty ≠ 0 := by
    intro zero
    exact invalid (dirtyZero.mp zero)
  obtain ⟨callPre, _, _, hpop, callRun, pCall⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix dirtyNe pDirty branchRun
  refine ⟨callPre, callRun, pCall, ?_, ?_, ?_, ?_⟩
  · rw [← hpop.memory,
      ← Line.of_inv Devm.memory (by line_inv) checkRun]
    exact wfLoaded
  · rw [← hpop.memory,
      ← Line.of_inv Devm.memory (by line_inv) checkRun]
    exact readsLoaded
  · exact stateLoaded.trans
      ((Line.of_inv Devm.state (by line_inv) checkRun).trans hpop.state)
  · exact logsLoaded.trans
      ((Line.of_inv Devm.logs (by line_inv) checkRun).trans hpop.logs)

theorem OssifiableConstructorHeadBoundary.dirtyImplementation_route
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (head : OssifiableConstructorHeadBoundary fs sevm entry body argsOffset
      tail image out)
    (hdirty : addressMask &&&
      ossifiableConstructorCodeWord sevm.code.toList argsOffset ≠ 0)
    (hspec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
      .emptyRevert) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  rcases head with
    ⟨guardPre, guardRun, pGuard, wfGuard, readsGuard,
      stateGuard, logsGuard⟩
  change Func.RunCompiledTo fs sevm guardPre
    (constructorDecodeLoadWord 0 +++ checkNonAddress +++
      ((.call 1) <?>
        constructorDecodeAfterImplementation argsOffset body)) out at guardRun
  obtain ⟨callPre, callRun, pCall, wfCall, readsCall,
      stateCall, logsCall⟩ :=
    constructorDecode_step_dirtyAddress
      (suffix := constructorDecodeAfterImplementation argsOffset body)
      (word := 0)
      (value := ossifiableConstructorCodeWord sevm.code.toList argsOffset)
      pGuard wfGuard readsGuard
      (ossifiableConstructorHeadImage_implementationWord _ _ _)
      hdirty guardRun
  exact .emptyRevert callPre
    (ossifiableConstructorHeadImage image sevm.code.toList argsOffset)
    hspec callRun pCall wfCall readsCall
    (stateGuard.trans stateCall) (logsGuard.trans logsCall)

theorem OssifiableConstructorImplementationBoundary.dirtyAdmin_route
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (implementation : OssifiableConstructorImplementationBoundary fs sevm
      entry body argsOffset tail image out)
    (hdirty : addressMask &&&
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32) ≠ 0)
    (hspec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
      .emptyRevert) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  rcases implementation with
    ⟨guardPre, guardRun, pGuard, wfGuard, readsGuard,
      stateGuard, logsGuard⟩
  change Func.RunCompiledTo fs sevm guardPre
    (constructorDecodeLoadWord 1 +++ checkNonAddress +++
      ((.call 1) <?> constructorDecodeAfterAdmin argsOffset body)) out at guardRun
  obtain ⟨callPre, callRun, pCall, wfCall, readsCall,
      stateCall, logsCall⟩ :=
    constructorDecode_step_dirtyAddress
      (suffix := constructorDecodeAfterAdmin argsOffset body)
      (word := 1)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (argsOffset + 32))
      pGuard wfGuard readsGuard
      (ossifiableConstructorHeadImage_adminWord _ _ _)
      hdirty guardRun
  exact .emptyRevert callPre
    (ossifiableConstructorHeadImage image sevm.code.toList argsOffset)
    hspec callRun pCall wfCall readsCall
    (stateGuard.trans stateCall) (logsGuard.trans logsCall)

private theorem constructorDecode_step_largeWord
    {fs : List Func} {sevm : Sevm} {pre : Devm} {suffix : Func}
    {slot : Nat} {word value : B256} {tail : Stack} {image : Bytes}
    {out : Execution}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hword : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (hlarge : ossifiableConstructorAbiMaxUint64 < value)
    (run : Func.RunCompiledTo fs sevm pre
      (pushB256 ossifiableConstructorAbiMaxUint64 :::
        constructorDecodeLoadWord word +++ gt :::
          ((.call slot) <?> suffix)) out) :
    ∃ callPre,
      Func.RunCompiledTo fs sevm callPre (.call slot) out ∧
      tail <<+ callPre.stack ∧
      Mem.Wf callPre.memory ∧
      Mem.Reads callPre.memory image ∧
      pre.state = callPre.state ∧
      pre.logs = callPre.logs := by
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  have r1 := Ninst.Run.of_runCompiled q1
  have pushMax := of_run_pushB256 r1
  have p1 := prefix_of_push pushMax hp
  have wf1 : Mem.Wf s1.memory := by rw [← pushMax.memory]; exact hwf
  have reads1 : Mem.Reads s1.memory image := by
    rw [← pushMax.memory]
    exact hreads
  obtain ⟨s2, loadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_loadWordAt_image (word := word) (value := value)
      p1 wf1 reads1 hword loadRun
  have logs2 := of_run_loadWordAt_logs loadRun
  obtain ⟨s3, q3, branchRun⟩ := runCompiledTo_next_inv run
  have r3 := Ninst.Run.of_runCompiled q3
  have p3 := prefix_of_gt r3 p2
  have hguard : (value >? ossifiableConstructorAbiMaxUint64) = 1 := by
    unfold B256.gtCheck
    rw [if_pos hlarge]
  have pOne : (1 : B256) :: tail <<+ s3.stack := by
    simpa [hguard] using p3
  obtain ⟨callPre, _, _, hpop, callRun, pCall⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) pOne branchRun
  refine ⟨callPre, callRun, pCall, ?_, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact wf2
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r3]
    exact reads2
  · exact pushMax.state.trans
      (state2.trans ((Ninst.Hinv.inv (f := Devm.state) r3).trans hpop.state))
  · exact pushMax.logs.trans
      (logs2.trans ((Ninst.Hinv.inv (f := Devm.logs) r3).trans hpop.logs))

theorem OssifiableConstructorAddressBoundary.largeOffset_route
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (address : OssifiableConstructorAddressBoundary fs sevm entry body
      argsOffset tail image out)
    (hlarge : ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
    (hspec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
      .emptyRevert) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  rcases address with
    ⟨guardPre, guardRun, pGuard, wfGuard, readsGuard,
      stateGuard, logsGuard⟩
  change Func.RunCompiledTo fs sevm guardPre
    (pushB256 ossifiableConstructorAbiMaxUint64 :::
      constructorDecodeLoadWord 2 +++ gt :::
        ((.call 1) <?> constructorDecodeAfterOffsetBound argsOffset body)) out at guardRun
  obtain ⟨callPre, callRun, pCall, wfCall, readsCall,
      stateCall, logsCall⟩ :=
    constructorDecode_step_largeWord
      (slot := 1) (word := 2)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (argsOffset + 64))
      pGuard wfGuard readsGuard
      (ossifiableConstructorHeadImage_offsetWord _ _ _) hlarge guardRun
  exact .emptyRevert callPre
    (ossifiableConstructorHeadImage image sevm.code.toList argsOffset)
    hspec callRun pCall wfCall readsCall
    (stateGuard.trans stateCall) (logsGuard.trans logsCall)

theorem OssifiableConstructorLengthBoundary.largeLength_route
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (length : OssifiableConstructorLengthBoundary fs sevm entry body
      argsOffset tail image out)
    (hlarge : ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat)
    (hspec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
      .allocationPanic) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  rcases length with
    ⟨guardPre, guardRun, pGuard, wfGuard, readsGuard,
      stateGuard, logsGuard⟩
  change Func.RunCompiledTo fs sevm guardPre
    (pushB256 ossifiableConstructorAbiMaxUint64 :::
      constructorDecodeLoadWord 4 +++ gt :::
        ((.call 7) <?> constructorDecodeAfterLengthBound body)) out at guardRun
  obtain ⟨callPre, callRun, pCall, wfCall, readsCall,
      stateCall, logsCall⟩ :=
    constructorDecode_step_largeWord
      (slot := 7) (word := 4)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat)
      pGuard wfGuard readsGuard
      (ossifiableConstructorLengthImage_lengthWord _ _ _) hlarge guardRun
  exact .allocationPanic callPre
    (ossifiableConstructorLengthImage image sevm.code.toList argsOffset)
    hspec callRun pCall wfCall readsCall
    (stateGuard.trans stateCall) (logsGuard.trans logsCall)

private theorem constructorDecode_step_codeSizeShort
    {fs : List Func} {sevm : Sevm} {pre : Devm} {suffix : Func}
    {slot : Nat} {bound : B256} {tail : Stack} {image : Bytes}
    {out : Execution}
    (hp : bound :: tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hshort : sevm.code.size < bound.toNat)
    (run : Func.RunCompiledTo fs sevm pre
      (codesize ::: lt ::: ((.call slot) <?> suffix)) out) :
    ∃ callPre,
      Func.RunCompiledTo fs sevm callPre (.call slot) out ∧
      tail <<+ callPre.stack ∧
      Mem.Wf callPre.memory ∧
      Mem.Reads callPre.memory image ∧
      pre.state = callPre.state ∧
      pre.logs = callPre.logs := by
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s2, q2, branchRun⟩ := runCompiledTo_next_inv run
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have codeSize := of_run_codesize r1
  have p1 := prefix_of_push codeSize hp
  have p2 := prefix_of_lt r2 p1
  have hlt : sevm.code.size.toB256 < bound := by
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hcodeSize]
    exact hshort
  have hguard : (sevm.code.size.toB256 <? bound) = 1 := by
    unfold B256.ltCheck
    rw [if_pos hlt]
  have pOne : (1 : B256) :: tail <<+ s2.stack := by
    simpa [hguard] using p2
  obtain ⟨callPre, _, _, hpop, callRun, pCall⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by decide : (1 : B256) ≠ 0) pOne branchRun
  refine ⟨callPre, callRun, pCall, ?_, ?_, ?_, ?_⟩
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r2,
      ← codeSize.memory]
    exact hwf
  · rw [← hpop.memory, ← Ninst.Hinv.inv (f := Devm.memory) r2,
      ← codeSize.memory]
    exact hreads
  · exact codeSize.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) r2).trans hpop.state)
  · exact codeSize.logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) r2).trans hpop.logs)

theorem OssifiableConstructorPointerBoundary.incompleteLength_route
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (pointer : OssifiableConstructorPointerBoundary fs sevm entry body
      argsOffset tail image out)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hshort : sevm.code.size <
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) +
          32).toNat)
    (hspec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
      .emptyRevert) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  rcases pointer with
    ⟨guardPre, guardRun, pGuard, wfGuard, readsGuard,
      stateGuard, logsGuard⟩
  change Func.RunCompiledTo fs sevm guardPre
    (constructorDecodeLoadWord 3 +++ pushB256 32 ::: add ::: codesize ::: lt :::
      ((.call 1) <?> constructorDecodeAfterLengthComplete body)) out at guardRun
  obtain ⟨s1, loadRun, guardRun⟩ := runCompiledTo_prepend_inv guardRun
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image (word := 3)
      (value := ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)))
      pGuard wfGuard readsGuard
      (ossifiableConstructorPointerImage_pointerWord _ _ _) loadRun
  have logs1 := of_run_loadWordAt_logs loadRun
  obtain ⟨s2, q2, guardRun⟩ := runCompiledTo_next_inv guardRun
  obtain ⟨testPre, q3, testRun⟩ := runCompiledTo_next_inv guardRun
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have push32 := of_run_pushB256 r2
  have p2 := prefix_of_push push32 p1
  have pTest :
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) +
          32) :: tail <<+ testPre.stack := by
    have startEq :
        (32 : B256) +
          ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) =
        ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) + 32 := B256.add_comm
    rw [← startEq]
    exact prefix_of_add r3 p2
  have wfTest : Mem.Wf testPre.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3, ← push32.memory]
    exact wf1
  have readsTest : Mem.Reads testPre.memory
      (ossifiableConstructorPointerImage image sevm.code.toList argsOffset) := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3, ← push32.memory]
    exact reads1
  obtain ⟨callPre, callRun, pCall, wfCall, readsCall,
      stateCall, logsCall⟩ :=
    constructorDecode_step_codeSizeShort pTest wfTest readsTest hcodeSize
      hshort testRun
  exact .emptyRevert callPre
    (ossifiableConstructorPointerImage image sevm.code.toList argsOffset)
    hspec callRun pCall wfCall readsCall
    (stateGuard.trans (state1.trans (push32.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) r3).trans stateCall))))
    (logsGuard.trans (logs1.trans (push32.logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) r3).trans logsCall))))

theorem OssifiableConstructorLengthBoundBoundary.payloadOutOfBounds_route
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (length : OssifiableConstructorLengthBoundBoundary fs sevm entry body
      argsOffset tail image out)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hshort : sevm.code.size <
      (ossifiableConstructorDataEnd argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
        (ossifiableConstructorCodeWord sevm.code.toList
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat)).toNat)
    (hspec : ossifiableConstructorDecodeSpec sevm.code.toList argsOffset =
      .emptyRevert) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  rcases length with
    ⟨guardPre, guardRun, pGuard, wfGuard, readsGuard,
      stateGuard, logsGuard⟩
  change Func.RunCompiledTo fs sevm guardPre
    (constructorDecodeLoadWord 3 +++ pushB256 32 ::: add :::
      constructorDecodeLoadWord 4 +++ add ::: codesize ::: lt :::
        ((.call 1) <?> constructorDecodeAfterPayloadBound body)) out at guardRun
  obtain ⟨s1, loadPointerRun, guardRun⟩ :=
    runCompiledTo_prepend_inv guardRun
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image (word := 3)
      (value := ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)))
      pGuard wfGuard readsGuard
      (ossifiableConstructorLengthImage_pointerWord _ _ _) loadPointerRun
  have logs1 := of_run_loadWordAt_logs loadPointerRun
  obtain ⟨s2, q2, guardRun⟩ := runCompiledTo_next_inv guardRun
  obtain ⟨s3, q3, guardRun⟩ := runCompiledTo_next_inv guardRun
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have push32 := of_run_pushB256 r2
  have p2 := prefix_of_push push32 p1
  have p3 : ossifiableConstructorDataStart argsOffset
      (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)) ::
      tail <<+ s3.stack := by
    have startEq :
        (32 : B256) +
          ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) =
        ossifiableConstructorDataStart argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64)) := by
      unfold ossifiableConstructorDataStart
      exact B256.add_comm
    rw [← startEq]
    exact prefix_of_add r3 p2
  have wf3 : Mem.Wf s3.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3, ← push32.memory]
    exact wf1
  have reads3 : Mem.Reads s3.memory
      (ossifiableConstructorLengthImage image sevm.code.toList argsOffset) := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3, ← push32.memory]
    exact reads1
  obtain ⟨s4, loadLengthRun, guardRun⟩ :=
    runCompiledTo_prepend_inv guardRun
  obtain ⟨p4, wf4, reads4, state4⟩ :=
    of_run_loadWordAt_image (word := 4)
      (value := ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat)
      p3 wf3 reads3
      (ossifiableConstructorLengthImage_lengthWord _ _ _) loadLengthRun
  have logs4 := of_run_loadWordAt_logs loadLengthRun
  obtain ⟨testPre, q5, testRun⟩ := runCompiledTo_next_inv guardRun
  have r5 := Ninst.Run.of_runCompiled q5
  have pTest : ossifiableConstructorDataEnd argsOffset
      (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
      (ossifiableConstructorCodeWord sevm.code.toList
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64))).toNat) :: tail <<+ testPre.stack := by
    have endEq :
        ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat +
          ossifiableConstructorDataStart argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) =
        ossifiableConstructorDataEnd argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
          (ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat) := by
      unfold ossifiableConstructorDataEnd
      exact B256.add_comm
    rw [← endEq]
    exact prefix_of_add r5 p4
  have wfTest : Mem.Wf testPre.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r5]
    exact wf4
  have readsTest : Mem.Reads testPre.memory
      (ossifiableConstructorLengthImage image sevm.code.toList argsOffset) := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r5]
    exact reads4
  obtain ⟨callPre, callRun, pCall, wfCall, readsCall,
      stateCall, logsCall⟩ :=
    constructorDecode_step_codeSizeShort pTest wfTest readsTest hcodeSize
      hshort testRun
  exact .emptyRevert callPre
    (ossifiableConstructorLengthImage image sevm.code.toList argsOffset)
    hspec callRun pCall wfCall readsCall
    (stateGuard.trans (state1.trans (push32.state.trans
      ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        (state4.trans ((Ninst.Hinv.inv (f := Devm.state) r5).trans
          stateCall))))))
    (logsGuard.trans (logs1.trans (push32.logs.trans
      ((Ninst.Hinv.inv (f := Devm.logs) r3).trans
        (logs4.trans ((Ninst.Hinv.inv (f := Devm.logs) r5).trans
          logsCall))))))

/-! ## Exhaustive staged classification -/

private inductive OssifiableConstructorAddressClassification
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | exit
      (route : OssifiableConstructorDecodeRoute fs sevm entry body argsOffset
        tail image out)
  | ready
      (headComplete : argsOffset + 96 ≤ sevm.code.size)
      (implementationClean : addressMask &&&
        ossifiableConstructorCodeWord sevm.code.toList argsOffset = 0)
      (adminClean : addressMask &&&
        ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32) = 0)
      (boundary : OssifiableConstructorAddressBoundary fs sevm entry body
        argsOffset tail image out)

private theorem ossifiableConstructorDecode_classifyAddress
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : argsOffset + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm entry
      (ossifiableConstructorDecode argsOffset body) out) :
    OssifiableConstructorAddressClassification fs sevm entry body argsOffset
      tail image out := by
  by_cases hheadShort : sevm.code.size < argsOffset + 96
  · exact .exit (ossifiableConstructorDecode_shortHead_route
      hp hwf hreads hcoordinate hcodeSize hheadShort run)
  · have hheadComplete : argsOffset + 96 ≤ sevm.code.size :=
      Nat.le_of_not_gt hheadShort
    have head := ossifiableConstructorDecode_headBoundary hp hwf hreads
      hcoordinate hcodeSize hheadComplete run
    by_cases himplementationDirty : addressMask &&&
        ossifiableConstructorCodeWord sevm.code.toList argsOffset ≠ 0
    · have hspec := ossifiableConstructorDecodeSpec_dirtyImplementation
        (code := sevm.code.toList) (argsOffset := argsOffset)
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hheadComplete) himplementationDirty
      exact .exit
        (head.dirtyImplementation_route himplementationDirty hspec)
    · have himplementationClean : addressMask &&&
          ossifiableConstructorCodeWord sevm.code.toList argsOffset = 0 := by
        simpa using himplementationDirty
      have implementation := head.implementationClean himplementationClean
      by_cases hadminDirty : addressMask &&&
          ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 32) ≠ 0
      · have hspec := ossifiableConstructorDecodeSpec_dirtyAdmin
          (code := sevm.code.toList) (argsOffset := argsOffset)
          (by simpa only [← ByteArray.size_eq_length_toList] using
            hheadComplete) himplementationClean hadminDirty
        exact .exit (implementation.dirtyAdmin_route hadminDirty hspec)
      · have hadminClean : addressMask &&&
            ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 32) = 0 := by
          simpa using hadminDirty
        exact .ready hheadComplete himplementationClean hadminClean
          (implementation.adminClean hadminClean)

private inductive OssifiableConstructorPointerClassification
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | exit
      (route : OssifiableConstructorDecodeRoute fs sevm entry body argsOffset
        tail image out)
  | ready
      (headComplete : argsOffset + 96 ≤ sevm.code.size)
      (implementationClean : addressMask &&&
        ossifiableConstructorCodeWord sevm.code.toList argsOffset = 0)
      (adminClean : addressMask &&&
        ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32) = 0)
      (offsetBound : ¬ ossifiableConstructorAbiMaxUint64 <
        ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
      (boundary : OssifiableConstructorPointerBoundary fs sevm entry body
        argsOffset tail image out)

private theorem ossifiableConstructorDecode_classifyPointer
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (classified : OssifiableConstructorAddressClassification fs sevm entry
      body argsOffset tail image out) :
    OssifiableConstructorPointerClassification fs sevm entry body argsOffset
      tail image out := by
  rcases classified with route | ⟨hheadComplete, himplementationClean,
      hadminClean, address⟩
  · exact .exit route
  · by_cases hoffsetLarge : ossifiableConstructorAbiMaxUint64 <
        ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64)
    · have hspec := ossifiableConstructorDecodeSpec_largeOffset
        (code := sevm.code.toList) (argsOffset := argsOffset)
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hheadComplete) himplementationClean hadminClean
        hoffsetLarge
      exact .exit (address.largeOffset_route hoffsetLarge hspec)
    · exact .ready hheadComplete himplementationClean hadminClean
        hoffsetLarge ((address.offsetBound hoffsetLarge).storePointer)

private inductive OssifiableConstructorLengthClassification
    (fs : List Func) (sevm : Sevm) (entry : Devm) (body : Func)
    (argsOffset : Nat) (tail : Stack) (image : Bytes)
    (out : Execution) : Prop where
  | exit
      (route : OssifiableConstructorDecodeRoute fs sevm entry body argsOffset
        tail image out)
  | ready
      (headComplete : argsOffset + 96 ≤ sevm.code.size)
      (implementationClean : addressMask &&&
        ossifiableConstructorCodeWord sevm.code.toList argsOffset = 0)
      (adminClean : addressMask &&&
        ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32) = 0)
      (offsetBound : ¬ ossifiableConstructorAbiMaxUint64 <
        ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
      (lengthComplete :
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64)) + 32).toNat ≤ sevm.code.size)
      (lengthBound : ¬ ossifiableConstructorAbiMaxUint64 <
        ossifiableConstructorCodeWord sevm.code.toList
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat)
      (boundary : OssifiableConstructorLengthBoundBoundary fs sevm entry body
        argsOffset tail image out)

private theorem ossifiableConstructorDecode_classifyLength
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (classified : OssifiableConstructorPointerClassification fs sevm entry
      body argsOffset tail image out) :
    OssifiableConstructorLengthClassification fs sevm entry body argsOffset
      tail image out := by
  rcases classified with route | ⟨hheadComplete, himplementationClean,
      hadminClean, hoffsetBound, pointer⟩
  · exact .exit route
  · by_cases hlengthShort : sevm.code.size <
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList
            (argsOffset + 64)) + 32).toNat
    · have hspec := ossifiableConstructorDecodeSpec_incompleteLength
        (code := sevm.code.toList) (argsOffset := argsOffset)
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hheadComplete) himplementationClean hadminClean
        hoffsetBound (by simpa only [← ByteArray.size_eq_length_toList] using
          hlengthShort)
      exact .exit
        (pointer.incompleteLength_route hcodeSize hlengthShort hspec)
    · have hlengthComplete :
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64)) + 32).toNat ≤ sevm.code.size :=
        Nat.le_of_not_gt hlengthShort
      have length := (pointer.lengthComplete hcodeSize hlengthComplete).copyLength
      by_cases hlengthLarge : ossifiableConstructorAbiMaxUint64 <
          ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat
      · have hspec := ossifiableConstructorDecodeSpec_largeLength
          (code := sevm.code.toList) (argsOffset := argsOffset)
          (by simpa only [← ByteArray.size_eq_length_toList] using
            hheadComplete) himplementationClean hadminClean
          hoffsetBound
          (by simpa only [← ByteArray.size_eq_length_toList] using
            hlengthComplete)
          hlengthLarge
        exact .exit (length.largeLength_route hlengthLarge hspec)
      · exact .ready hheadComplete himplementationClean hadminClean
          hoffsetBound hlengthComplete hlengthLarge
          (length.lengthBound hlengthLarge)

private theorem ossifiableConstructorDecode_finishClassification
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (classified : OssifiableConstructorLengthClassification fs sevm entry
      body argsOffset tail image out) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  rcases classified with route | ⟨hheadComplete, himplementationClean,
      hadminClean, hoffsetBound, hlengthComplete, hlengthBound, length⟩
  · exact route
  · by_cases hpayloadShort : sevm.code.size <
        (ossifiableConstructorDataEnd argsOffset
          (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 64))
          (ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat)).toNat
    · have hspec := ossifiableConstructorDecodeSpec_payloadOutOfBounds
        (code := sevm.code.toList) (argsOffset := argsOffset)
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hheadComplete) himplementationClean hadminClean
        hoffsetBound
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hlengthComplete)
        hlengthBound
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hpayloadShort)
      exact length.payloadOutOfBounds_route hcodeSize hpayloadShort hspec
    · have hpayloadComplete :
          (ossifiableConstructorDataEnd argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))
            (ossifiableConstructorCodeWord sevm.code.toList
              (ossifiableConstructorDataPointer argsOffset
                (ossifiableConstructorCodeWord sevm.code.toList
                  (argsOffset + 64))).toNat)).toNat ≤ sevm.code.size :=
        Nat.le_of_not_gt hpayloadShort
      have boundary :=
        (length.payloadComplete hcodeSize hpayloadComplete).copyPayload
      have hspec := ossifiableConstructorDecodeSpec_accepted
        (code := sevm.code.toList) (argsOffset := argsOffset)
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hheadComplete) himplementationClean hadminClean
        hoffsetBound
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hlengthComplete)
        hlengthBound
        (by simpa only [← ByteArray.size_eq_length_toList] using
          hpayloadComplete)
      exact .accepted
        (ossifiableConstructorCodeWord sevm.code.toList argsOffset)
        (ossifiableConstructorCodeWord sevm.code.toList (argsOffset + 32))
        (sevm.code.toList.sliceD
          (ossifiableConstructorDataStart argsOffset
            (ossifiableConstructorCodeWord sevm.code.toList
              (argsOffset + 64))).toNat
          (ossifiableConstructorCodeWord sevm.code.toList
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord sevm.code.toList
                (argsOffset + 64))).toNat).toNat
          0)
        himplementationClean hadminClean hlengthBound rfl
        (by unfold List.sliceD; exact List.takeD_length _ _ _)
        hspec boundary

/-- Every executable constructor-decoder walk reaches exactly the result
selected by the total pure decoder: one of its two error calls, or the
proof-carrying protected-body boundary. -/
theorem ossifiableConstructorDecode_route
    {fs : List Func} {sevm : Sevm} {entry : Devm} {body : Func}
    {argsOffset : Nat} {tail : Stack} {image : Bytes} {out : Execution}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : argsOffset + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (run : Func.RunCompiledTo fs sevm entry
      (ossifiableConstructorDecode argsOffset body) out) :
    OssifiableConstructorDecodeRoute fs sevm entry body argsOffset tail image
      out := by
  have address := ossifiableConstructorDecode_classifyAddress hp hwf hreads
    hcoordinate hcodeSize run
  have pointer := ossifiableConstructorDecode_classifyPointer address
  have length := ossifiableConstructorDecode_classifyLength hcodeSize pointer
  exact ossifiableConstructorDecode_finishClassification hcodeSize length

end Blanc.ProxyPair
