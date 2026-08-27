import Blanc.LidoCircuitBreakerPauseOkRoute
import Blanc.LidoCircuitBreakerSuccess

/-!
# Public-entry pause outcomes

This module lifts the reached-state pause classification to the production
runtime's public `pause(address)` entry.  The entry bundle deliberately names
the environment facts that make the walk a production invocation; none of its
fields states or implies the terminal result.  In particular, arbitrary target
code remains represented by the execution carried by `Prog.RunCompiledTo`.

An accepted canonical `true` return is still only an observation about target
returndata, never enforcement that arbitrary target code really paused.
`PauseSuccessNoninterference` remains an explicit hypothesis and is consumed
only by that accepting arm.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- REG-4-style facts at a production `pause(address)` entry.

The installed target code is named separately from the CircuitBreaker's own
production bytes.  This makes code identity detachable for later composition
with a verified direct target or a proxy/implementation pair. -/
structure PublicPauseEntryPremises (sevm : Sevm) (pre : Devm)
    (owner : Adr) (target duration idx0 len0 last0 : B256)
    (img : Bytes) (targetCode : ByteArray) : Prop where
  productionBytes :
    sevm.code.toList = lidoCircuitBreakerCode officialParams
  currentTarget : sevm.currentTarget = owner
  codeAddress : sevm.codeAddress = some owner
  valueZero : sevm.value = 0
  dynamic : sevm.isStatic = false
  entered : sevm.depth ≠ 0
  image : MemImage pre img
  calldata : sevm.data = pauseCalldata target
  selectorEq : Sevm.selector sevm = selector "pause" [.address]
  targetCanonical : ValidAdr target
  targetNonzero : target ≠ 0
  callerNonzero : sevm.caller.toB256 ≠ 0
  unlocked : pre.getTransVal sevm.currentTarget lockKey = 0
  targetCodeAt : CodeAt pre target.toAdr targetCode
  assigned : pre.getStorVal sevm.currentTarget (assignmentSlot target) =
    sevm.caller.toB256
  live : sevm.benvStat.time <
    pre.getStorVal sevm.currentTarget (expirySlot sevm.caller.toB256)
  durationRead :
    pre.getStorVal sevm.currentTarget pauseDurationSlot = duration
  indexRead : pre.getStorVal sevm.currentTarget (indexSlot target) = idx0
  lengthRead : pre.getStorVal sevm.currentTarget arrayLengthSlot = len0
  lastRead :
    pre.getStorVal sevm.currentTarget (arrayEntrySlot len0) = last0
  assignmentCountNe :
    assignmentSlot target ≠ countSlot sevm.caller.toB256
  assignmentIndexNe : assignmentSlot target ≠ indexSlot target
  assignmentLengthNe : assignmentSlot target ≠ arrayLengthSlot
  assignmentEntryNe : assignmentSlot target ≠ arrayEntrySlot len0
  countIndexNe : countSlot sevm.caller.toB256 ≠ indexSlot target
  countLengthNe : countSlot sevm.caller.toB256 ≠ arrayLengthSlot
  countEntryNe :
    countSlot sevm.caller.toB256 ≠ arrayEntrySlot len0
  removePreservesCount : ∀ (a b postW : Devm),
    MemWordAt a (targetWord * 32).toNat target →
    a.getStorVal sevm.currentTarget (indexSlot target) = idx0 →
    a.getStorVal sevm.currentTarget arrayLengthSlot = len0 →
    a.getStorVal sevm.currentTarget (arrayEntrySlot len0) = last0 →
    Line.Run sevm a removeClearTargetIndexPrefix b →
    Ninst.RunCompiled sevm b Ninst.sstore postW →
    postW.getStorVal sevm.currentTarget
        (countSlot sevm.caller.toB256) =
      a.getStorVal sevm.currentTarget
        (countSlot sevm.caller.toB256)

/-- The exact `pauseAfterSet` entry reached by a public production walk.

Besides the continuation itself, the witness retains precisely the two
frame-local words consumed by the Stage 6 family and the Registry count
decrement established before either external target call. -/
def PublicPauseAfterSetAt (fs : List Func) (sevm : Sevm)
    (pre : Devm) (target duration : B256) (targetCode : ByteArray)
    (ex : Execution) (entry : Devm) : Prop :=
  MemWordAt entry (targetWord * 32).toNat target ∧
    MemWordAt entry (durationWord * 32).toNat duration ∧
    CodeAt entry target.toAdr targetCode ∧
    entry.getStorVal sevm.currentTarget
        (countSlot sevm.caller.toB256) =
      pre.getStorVal sevm.currentTarget
        (countSlot sevm.caller.toB256) - 1 ∧
    Func.RunCompiledTo fs sevm entry pauseAfterSet ex

/-- Existence of the exact public-entry `pauseAfterSet` state. -/
def PublicPauseAfterSetReach (fs : List Func) (sevm : Sevm)
    (pre : Devm) (target duration : B256) (targetCode : ByteArray)
    (ex : Execution) : Prop :=
  ∃ entry, PublicPauseAfterSetAt fs sevm pre target duration targetCode ex entry

/-- A production public-entry walk reaches the exact `pauseAfterSet` state
used by the Stage 6 outcome family, for every terminal execution polarity. -/
theorem publicPause_reaches_pauseAfterSet
    {sevm : Sevm} {pre : Devm} {owner : Adr}
    {target duration idx0 len0 last0 : B256}
    {img : Bytes} {targetCode : ByteArray} {ex : Execution}
    (premises : PublicPauseEntryPremises sevm pre owner target duration
      idx0 len0 last0 img targetCode)
    (run : Prog.RunCompiledTo sevm pre (runtime officialParams) ex) :
    PublicPauseAfterSetReach
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sevm pre target duration targetCode ex := by
  obtain ⟨mid, entryBurn, runtimeRun⟩ := run
  obtain ⟨dataLength, targetEq⟩ := pauseCalldata_facts premises.calldata
  have storageEq : Devm.getStor mid = Devm.getStor pre :=
    (getStor_of_state entryBurn.state).symm
  have cellEq (key : B256) :
      mid.getStorVal sevm.currentTarget key =
        pre.getStorVal sevm.currentTarget key :=
    congrArg (fun stor : Adr → Stor =>
      (stor sevm.currentTarget).get key) storageEq
  have imageMid : MemImage mid img :=
    MemImage.of_memory_eq entryBurn.memory.symm premises.image
  have codeMid : CodeAt mid target.toAdr targetCode :=
    premises.targetCodeAt.ofState entryBurn.state
  have unlockedPre := premises.unlocked
  have unlockedMid : mid.getTransVal sevm.currentTarget lockKey = 0 := by
    unfold Devm.getTransVal at unlockedPre ⊢
    rw [(Devm.Burn.of_burnBy entryBurn).transientStorage_eq]
    exact unlockedPre
  have assignedMid : mid.getStorVal sevm.currentTarget
      (assignmentSlot target) = sevm.caller.toB256 := by
    rw [cellEq]
    exact premises.assigned
  have liveMid : sevm.benvStat.time < mid.getStorVal sevm.currentTarget
      (expirySlot sevm.caller.toB256) := by
    rw [cellEq]
    exact premises.live
  have durationMid : mid.getStorVal sevm.currentTarget pauseDurationSlot =
      duration := by
    rw [cellEq]
    exact premises.durationRead
  refine runtimeMain_to_pauseKernel_any officialParams runtimeRun imageMid
    (targetEq ▸ codeMid) premises.valueZero dataLength
    (targetEq ▸ premises.targetCanonical) unlockedMid
    (targetEq ▸ assignedMid) liveMid premises.selectorEq
    (fun kernelStart windowT windowN windowC windowD kernelStorage
        kernelCode kernelRun => ?_)
  rw [targetEq] at windowT kernelCode
  have kernelCell (key : B256) :
      kernelStart.getStorVal sevm.currentTarget key =
        mid.getStorVal sevm.currentTarget key :=
    congrArg (fun stor : Adr → Stor =>
      (stor sevm.currentTarget).get key) kernelStorage
  have durationWindow :
      MemWordAt kernelStart (durationWord * 32).toNat duration := by
    rw [← durationMid]
    exact windowD
  have assignmentKernel : kernelStart.getStorVal sevm.currentTarget
      (assignmentSlot target) = sevm.caller.toB256 := by
    rw [kernelCell]
    exact assignedMid
  have assignmentKernelNonzero : kernelStart.getStorVal sevm.currentTarget
      (assignmentSlot target) ≠ 0 := by
    rw [assignmentKernel]
    exact premises.callerNonzero
  have indexKernel : kernelStart.getStorVal sevm.currentTarget
      (indexSlot target) = idx0 := by
    rw [kernelCell, cellEq]
    exact premises.indexRead
  have lengthKernel : kernelStart.getStorVal sevm.currentTarget
      arrayLengthSlot = len0 := by
    rw [kernelCell, cellEq]
    exact premises.lengthRead
  have lastKernel : kernelStart.getStorVal sevm.currentTarget
      (arrayEntrySlot len0) = last0 := by
    rw [kernelCell, cellEq]
    exact premises.lastRead
  refine setPauserKernel_to_pauseAfterSet_any officialParams kernelRun windowT
    premises.targetNonzero windowN windowC durationWindow kernelCode
    assignmentKernelNonzero assignmentKernel indexKernel lengthKernel lastKernel
    premises.assignmentCountNe premises.assignmentIndexNe
    premises.assignmentLengthNe premises.assignmentEntryNe
    premises.countIndexNe premises.countLengthNe premises.countEntryNe
    premises.removePreservesCount
    (fun entry targetWindow durationWindow targetCodeAt countDecrement
        afterSetRun => ?_)
  refine ⟨entry, targetWindow, durationWindow, targetCodeAt, ?_, afterSetRun⟩
  rw [countDecrement, kernelCell, cellEq]

/-! ## Actual external-edge facts -/

/-- The external edges actually crossed by one `pauseAfterSet` walk.

The codeless arm reaches neither edge.  Every codeful arm crosses the CALL
with a proved `PauseCallBoundary`; its successful child arm additionally
crosses the STATICCALL with a proved `PauseStatBoundary`.  The continuations
tie each named edge to the same terminal execution `ex`. -/
def PauseBoundaryEdges (fs : List Func) (sevm : Sevm) (entry : Devm)
    (target : Adr) (duration : B256) (ex : Execution) : Prop :=
  ((entry.getCode target).size.toB256 = 0 ∧
      ∃ post, ex = .error (.revert, post) ∧ post.output = []) ∨
    ((entry.getCode target).size.toB256 ≠ 0 ∧
      ∃ guardPost callPre callPost : Devm,
        Line.Run sevm guardPost pauseCallStaging callPre ∧
        Ninst.RunCompiled sevm callPre (.exec .call) callPost ∧
        PauseCallBoundary sevm target duration callPre callPost ∧
        Func.RunCompiledTo fs sevm callPost pauseAfterCallBranch ex ∧
        ((∃ callChild : Devm,
            callChild.error.isSome = true ∧
            callPost.returnData = callChild.output) ∨
          (∃ armPre statPre statPost : Devm,
            Line.Run sevm armPre pauseStatStaging statPre ∧
            Ninst.RunCompiled sevm statPre (.exec .statcall) statPost ∧
            PauseStatBoundary sevm target statPre statPost ∧
            Func.RunCompiledTo fs sevm statPost
              (Ninst.iszero :::
                ((Func.call bubbleRevertSlot) <?> decodePausedResult)) ex)))

/-- Stage 6's settled seven-outcome family together with non-vacuous boundary
facts for every external edge the same walk crosses. -/
def PauseAfterSetBoundaryCommittedOutcomes (fs : List Func) (sevm : Sevm)
    (entry : Devm) (target : Adr) (duration : B256)
    (ex : Execution) : Prop :=
  PauseBoundaryEdges fs sevm entry target duration ex ∧
    PauseAfterSetCommittedOutcomes fs sevm entry target duration ex

/-- Add actual CALL/STATICCALL boundaries to the settled Stage 6 family.
No premise constrains either child; the enclosing depth and dynamic facts are
the two frame facts required by the boundary satisfaction theorems. -/
theorem pauseAfterSet_boundary_committed_outcomes
    {fs : List Func} {sevm : Sevm} {entry : Devm}
    {target : Adr} {duration : B256} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.rev)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revData heartbeatArithmeticPanicData))
    (hTarget : MemWordAt entry
      (targetWord * 32).toNat target.toB256)
    (hDuration : MemWordAt entry (durationWord * 32).toNat duration)
    (hDepth : sevm.depth ≠ 0)
    (hDynamic : sevm.isStatic = false)
    (noninterference : ∀ successPre,
      Func.RunCompiledTo fs sevm successPre pauseSuccess ex →
        PauseSuccessNoninterference sevm entry successPre)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet ex) :
    PauseAfterSetBoundaryCommittedOutcomes fs sevm entry target duration ex := by
  have committed := pauseAfterSet_committed_outcomes h_empty h_bubble h_failed
    h_panic hTarget hDuration noninterference run
  refine ⟨?_, committed⟩
  rcases pauseAfterSet_codeGuard_arms_windows h_empty hTarget hDuration run with
    hnocode | ⟨hcode, guardPost, targetGuard, durationGuard, live⟩
  · exact Or.inl hnocode
  · obtain ⟨callPre, callStaging, live⟩ :=
      runCompiledTo_prepend_inv live
    obtain ⟨callPost, callRun, afterCall⟩ := runCompiledTo_next_inv live
    obtain ⟨_gasWord, _rest, callStack, targetCallPre⟩ :=
      pauseCallStaging_boundary_operands targetGuard callStaging
    have callBoundary :
        PauseCallBoundary sevm target duration callPre callPost :=
      pauseCall_boundary callStack
        (pauseCallStaging_calldata durationGuard callStaging)
        hDepth hDynamic callRun
    have targetCallPost :=
      pauseCall_targetWord_survives callBoundary targetCallPre
    have durationCallPre := durationGuard.acrossPauseCallStagingBoundary
      (by decide) callStaging
    have durationCallPost :=
      pauseCall_targetWord_survives callBoundary durationCallPre
    have afterCallForEdges := afterCall
    rw [pauseAfterCallBranch] at afterCallForEdges
    obtain ⟨callChild, armPre, callReturn, _armReturn, targetArm,
      _durationArm, callArms⟩ :=
      pauseAfterCall_arms_windows callBoundary targetCallPost durationCallPost
        afterCallForEdges
    refine Or.inr ⟨hcode, guardPost, callPre, callPost, callStaging, callRun,
      callBoundary, afterCall, ?_⟩
    rcases callArms with ⟨callError, _bubble⟩ | ⟨callSuccess, statRun⟩
    · exact Or.inl ⟨callChild, callError, callReturn⟩
    · rw [pauseStatArm] at statRun
      obtain ⟨statPre, statStaging, statRun⟩ :=
        runCompiledTo_prepend_inv statRun
      obtain ⟨statPost, statCall, observation⟩ :=
        runCompiledTo_next_inv statRun
      obtain ⟨_statGas, _statRest, statStack, targetStatPre⟩ :=
        pauseStatStaging_boundary_operands targetArm statStaging
      have statBoundary : PauseStatBoundary sevm target statPre statPost :=
        pauseStat_boundary statStack
          (pauseStatStaging_boundary_calldata targetArm.memImage statStaging)
          hDepth statCall
      exact Or.inr ⟨armPre, statPre, statPost, statStaging, statCall,
        statBoundary, observation⟩

/-! ## Production public-entry family -/

/-- The public-entry witness and its complete settled outcome family.

This is intentionally existential only in the exact state extracted from the
given production walk.  It does not assert liveness, choose an outcome, or
assume anything equivalent to the terminal result. -/
def PublicPauseCommittedOutcomes (sevm : Sevm) (pre : Devm)
    (target duration : B256) (targetCode : ByteArray)
    (ex : Execution) : Prop :=
  ∃ entry : Devm,
    PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sevm pre target duration targetCode ex entry ∧
    PauseAfterSetBoundaryCommittedOutcomes
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sevm entry target.toAdr duration ex

/-- **Public production `pause(address)` outcome family.**

The terminal execution may be successful or failing.  The only callback
assumption is the reached-state family's named `PauseSuccessNoninterference`,
scoped to an exact extracted `pauseAfterSet` state and consumed only on the
canonical-true observation arm.  An accepted canonical `true` remains an
observation about returndata, never enforcement that arbitrary target code
really paused. -/
theorem publicPause_committed_outcomes
    {sevm : Sevm} {pre : Devm} {owner : Adr}
    {target duration idx0 len0 last0 : B256}
    {img : Bytes} {targetCode : ByteArray} {ex : Execution}
    (premises : PublicPauseEntryPremises sevm pre owner target duration
      idx0 len0 last0 img targetCode)
    (run : Prog.RunCompiledTo sevm pre (runtime officialParams) ex)
    (noninterference : ∀ entry : Devm,
      PublicPauseAfterSetAt
        ((runtime officialParams).main :: (runtime officialParams).aux)
        sevm pre target duration targetCode ex entry →
      ∀ successPre : Devm,
        Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sevm successPre pauseSuccess ex →
        PauseSuccessNoninterference sevm entry successPre) :
    PublicPauseCommittedOutcomes sevm pre target duration targetCode ex := by
  obtain ⟨entry, reached⟩ := publicPause_reaches_pauseAfterSet premises run
  rcases reached with
    ⟨targetWindow, durationWindow, targetCodeAt, countDecrement, afterSetRun⟩
  have reachedAt : PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      sevm pre target duration targetCode ex entry :=
    ⟨targetWindow, durationWindow, targetCodeAt, countDecrement, afterSetRun⟩
  have canonicalTarget : target.toAdr.toB256 = target :=
    toB256_toAdr premises.targetCanonical
  have targetAdrWindow :
      MemWordAt entry (targetWord * 32).toNat target.toAdr.toB256 := by
    rw [canonicalTarget]
    exact targetWindow
  refine ⟨entry, reachedAt, ?_⟩
  exact pauseAfterSet_boundary_committed_outcomes
    (by rfl) (by rfl) (by rfl) (by rfl)
    targetAdrWindow durationWindow premises.entered premises.dynamic
    (noninterference entry reachedAt) afterSetRun

end Blanc.LidoCircuitBreaker
