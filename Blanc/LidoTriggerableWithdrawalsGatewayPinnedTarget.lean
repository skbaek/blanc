import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetInterface
import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute
import Blanc.MessageExecutionInversion
import Blanc.ReachableExecFree

/-!
# Account-level pinned-target boundary for the Triggerable Withdrawals Gateway

This family-owned module fixes the account protocol vocabulary that the TWG
runtime must discharge.  It intentionally imports no Circuit Breaker module:
the calldata builders, storage projection, and protected selector are the
gateway family's own definitions.

The final `PinnedPauseTarget` constructor is deliberately absent from this
checkpoint until the concrete A2 runtime proofs exist.  In particular, this
module does not introduce a structure of assumed semantic witnesses and does
not reflect an executable fixture into theorem evidence.  This module now
discharges the CircuitBreaker-cell noninterference clause from actual `Exec`
chronology and retained `ProcessMessage` slots.  The remaining bundle
declarations still require source-derived proofs:

* a clean exact `pauseFor` execution stores `pauseForProjection`;
* a clean exact `isPaused` execution preserves `resumeSinceSlot` and returns
  the canonical boolean for its entry projection;
* a selected trigger execution cannot settle cleanly while the entry
  projection is paused, including malformed and unauthorized calldata paths.

Once those source-derived facts are available, the intended public theorem is

```
theorem pinnedPauseTarget
    (dp : DeployParams) (circuitBreaker gateway : Adr)
    (circuitBreakerCells : List B256)
    (different : gateway ≠ circuitBreaker) :
    PinnedPauseTarget circuitBreaker gateway (runtime dp)
      pauseForCalldata isPausedCalldata pausedUntil
      circuitBreakerCells protectedSurface
```

The quantification over `dp` leaves the locator identity, its account, and all
callee code arbitrary.  Both pause/query routes are source-`.exec`-free.  The
pause route contains internal `Func.call` edges into the finite exec-free
component certified below, while `isPaused` has no internal call edge.  The
paused trigger must revert before consulting external accounts.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

/-! ## Route-local exec-freedom certificates -/

/-- The finite internal-call component used by the pause entry. -/
def pauseExecMembers : List Nat :=
  [missingRoleSlot, pausedExpectedSlot, zeroPauseDurationSlot,
    arithmeticPanicSlot, collisionRefusalSlot]

private theorem pauseEntry_localExecFree :
    (nonpayable pauseFor).localExecFree = true := by
  decide +kernel

private theorem pauseEntry_callsIn :
    (nonpayable pauseFor).callsIn
      (fun callee => callee ∈ pauseExecMembers) = true := by
  decide +kernel

private theorem pauseComponent_missingRole (dp : DeployParams) :
    (match (runtime dp).function? missingRoleSlot with
      | none => false
      | some body =>
          body.localExecFree &&
            body.callsIn (fun callee => callee ∈ pauseExecMembers)) = true := by
  rfl

private theorem pauseComponent_pausedExpected (dp : DeployParams) :
    (match (runtime dp).function? pausedExpectedSlot with
      | none => false
      | some body =>
          body.localExecFree &&
            body.callsIn (fun callee => callee ∈ pauseExecMembers)) = true := by
  rfl

private theorem pauseComponent_zeroDuration (dp : DeployParams) :
    (match (runtime dp).function? zeroPauseDurationSlot with
      | none => false
      | some body =>
          body.localExecFree &&
            body.callsIn (fun callee => callee ∈ pauseExecMembers)) = true := by
  rfl

private theorem pauseComponent_arithmeticPanic (dp : DeployParams) :
    (match (runtime dp).function? arithmeticPanicSlot with
      | none => false
      | some body =>
          body.localExecFree &&
            body.callsIn (fun callee => callee ∈ pauseExecMembers)) = true := by
  have lookup :
      (runtime dp).function? arithmeticPanicSlot =
        some (Func.revData
          ((signatureHash "Panic" [.uint256]).toBytes.take 4 ++
            (Nat.toB256 0x11).toBytes)) := by
    simp [Prog.function?, runtime, aux, baseAux, arithmeticPanicSlot]
  rw [lookup]
  decide +kernel

private theorem pauseComponent_collisionRefusal (dp : DeployParams) :
    (match (runtime dp).function? collisionRefusalSlot with
      | none => false
      | some body =>
          body.localExecFree &&
          body.callsIn (fun callee => callee ∈ pauseExecMembers)) = true := by
  rfl

private theorem pauseComponents_execFree (dp : DeployParams) :
    (runtime dp).componentExecFree pauseExecMembers = true := by
  apply List.all_eq_true.mpr
  intro index member
  simp only [pauseExecMembers, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact pauseComponent_missingRole dp
  · exact pauseComponent_pausedExpected dp
  · exact pauseComponent_zeroDuration dp
  · exact pauseComponent_arithmeticPanic dp
  · exact pauseComponent_collisionRefusal dp

/-- The exact pause entry and its finite internal-call closure contain no
source `.exec`; unselected trigger bodies remain unconstrained. -/
theorem pauseFor_reachableExecFree (dp : DeployParams) :
    (runtime dp).reachableExecFree (nonpayable pauseFor)
      pauseExecMembers = true := by
  simp only [Prog.reachableExecFree, Bool.and_eq_true]
  exact ⟨⟨pauseEntry_localExecFree, pauseEntry_callsIn⟩,
    pauseComponents_execFree dp⟩

/-- The exact query entry is locally source-exec-free and has no internal
call edge. -/
theorem isPaused_reachableExecFree (dp : DeployParams) :
    (runtime dp).reachableExecFree (nonpayable isPaused) [] = true := by
  rfl

/-! ## Exact selected-entry route -/

/-- Any same-frame source `.exec` reached by an exact runtime invocation must
lie in the calldata-selected entry.  A reachable-exec-free certificate for
that entry therefore rules the occurrence out without constraining any
unselected selector body. -/
private theorem noExec_of_selectedRuntimeEntry
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {dp : DeployParams} {gateway : Adr}
    {selector : B256} {body : Func}
    (run : Exec pc sevm pre out)
    (invocation :
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        (runtime dp) gateway gateway)
    (guardZero :
      B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (selectorEq : Sevm.selector sevm = selector)
    (member : (selector, body) ∈ funcs dp)
    (members : List Nat)
    (accepted :
      (runtime dp).reachableExecFree body members = true)
    {target : Exec.Deriv}
    (sameFrame : Exec.Deriv.ParentPrefix
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) target)
    (x : Xinst)
    (execAt : Ninst.At target.sevm.code target.pc (.exec x)) : False := by
  have compiled : some sevm.code.toList = (runtime dp).compile :=
    invocation.2.2.2
  rcases Exec.Deriv.SourceCursor.mainToward invocation sameFrame execAt with
    ⟨mainCursor, _compilerPrefix, mainReached⟩
  change Exec.Deriv.SourceCursor
    (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) (runtime dp) ⟨0, []⟩
      ([Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt] +++
        (Func.rev <?>
          (fsig +++ linearDispatchWith fallbackSlot (funcs dp))))
    at mainCursor
  have mainRoute := mainCursor.toward compiled mainReached
    (by trivial) execAt
  rcases mainRoute.dropLineRun (by simp [Ninst.pushB256]) with
    ⟨_guardPath, guardCursor, guardRun, _guardChronology, guardRoute⟩
  rcases Line.of_run_cons guardRun with
    ⟨afterPush, pushRun, restRun⟩
  rcases Line.of_run_cons restRun with
    ⟨afterSize, sizeRun, restRun⟩
  rcases Line.of_run_cons restRun with
    ⟨_afterLt, ltRun, nilRun⟩
  cases nilRun
  have pushPrefix : (4 : B256) :: [] <<+ afterPush.stack :=
    prefix_of_push (of_run_pushB256 pushRun) nil_pref
  have sizePrefix :
      sevm.data.length.toB256 :: (4 : B256) :: [] <<+
        afterSize.stack :=
    prefix_of_push (of_run_calldatasize sizeRun) pushPrefix
  have flagPrefix : (0 : B256) :: [] <<+ guardCursor.pre.stack := by
    have actualFlag :
        (sevm.data.length.toB256 <? (4 : B256)) :: [] <<+
          guardCursor.pre.stack :=
      prefix_of_lt ltRun sizePrefix
    rw [guardZero] at actualFlag
    exact actualFlag
  rcases guardRoute.selectBranchZero guardCursor compiled
      (by trivial) execAt flagPrefix with
    ⟨dispatchCursor, dispatchRoute, _guardTailPrefix⟩
  rcases dispatchRoute.dropLineRun (by
      simp [fsig, cdl, shiftRight, Ninst.pushB256]) with
    ⟨_selectorPath, selectorCursor, selectorRun,
      _selectorChronology, selectorRoute⟩
  have selectorPrefix : selector :: [] <<+ selectorCursor.pre.stack := by
    have actualSelector :
        Sevm.selector sevm :: [] <<+ selectorCursor.pre.stack :=
      prefix_of_fsig nil_pref selectorRun
    rw [selectorEq] at actualSelector
    exact actualSelector
  rcases
      Exec.Deriv.SourceCursor.Toward.linearDispatchWith_selectedBody
        compiled execAt (funcs dp) (funcs_selector_unique dp) member
          selectorCursor selectorRoute selectorPrefix with
    ⟨_bodyPath, bodyCursor, bodyRoute, _bodyStackPrefix⟩
  exact bodyCursor.noExec_of_reachableExecFree compiled members accepted
    bodyRoute.chronology.cursorToTarget x execAt

/-! ## Pinned-target clause (iii) -/

/-- Exact pause and query messages executing the concrete TWG runtime retain
no successful write to any nominated CircuitBreaker cell.  The proof splits
rollback first; in the committing arm it follows the actual calldata-selected
source route and excludes every same-frame `.exec`, which in turn excludes
all child-frame occurrences. -/
theorem pinnedPauseTarget_circuitBreaker_noninterference
    (dp : DeployParams) (circuitBreaker gateway : Adr)
    (circuitBreakerCells : List B256)
    (different : gateway ≠ circuitBreaker)
    {msg : Msg} {xl : Xlot} {ex : TargetMessageResult}
    (inbound : ExactPinnedInbound circuitBreaker gateway
      pauseForCalldata isPausedCalldata msg)
    (executes : MessageExecutesProgram msg xl (runtime dp))
    (process : ProcessMessage msg xl ex) :
    ∀ key ∈ circuitBreakerCells,
      TargetInvocationNoRetainedWriteTo xl circuitBreaker key := by
  intro key _member
  rcases executes with
    ⟨messageUses, ⟨pc, sevm, pre⟩, raw, xlEq, ⟨_witnessRun⟩⟩
  subst xl
  intro actualRun
  by_cases committed : Execution.commits raw = true
  · rcases MessageExecution.processMessage_entry_facts gateway process with
      ⟨pcZero, codeEq, current, codeAddress, data, _time,
        _entryStorage, _memoryWf⟩
    apply Exec.noRetainedWriteTo_of_no_sameFrame_execAt actualRun
      circuitBreaker key
    · rcases inbound with ⟨duration, exactCall⟩ | exactCall
      · rw [current.trans exactCall.currentTarget]
        exact different
      · rw [current.trans exactCall.currentTarget]
        exact different
    · intro target sameFrame x execAt
      rcases inbound with ⟨duration, exactCall⟩ | exactCall
      · have invocation :
            (⟨pc, sevm, pre, raw, actualRun⟩ : Exec.Deriv).exactInvocation
              (runtime dp) gateway gateway := by
          refine ⟨pcZero, current.trans exactCall.currentTarget,
            codeAddress.trans exactCall.codeAddress, ?_⟩
          rw [codeEq]
          exact messageUses
        have dataEq : sevm.data = pauseForCalldata duration :=
          data.trans exactCall.data
        have guardZero :
            B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0 := by
          rw [dataEq, pauseForCalldata_length]
          decide
        have selectorEq : Sevm.selector sevm = selPauseFor := by
          apply selector_eq_of_data_eq_abiSelectorBytes_append
            (selected := selPauseFor) (tail := duration.toBytes)
          · rfl
          · simpa [pauseForCalldata] using dataEq
        exact noExec_of_selectedRuntimeEntry actualRun invocation guardZero
          selectorEq (by simp [funcs]) pauseExecMembers
            (pauseFor_reachableExecFree dp) sameFrame x execAt
      · have invocation :
            (⟨pc, sevm, pre, raw, actualRun⟩ : Exec.Deriv).exactInvocation
              (runtime dp) gateway gateway := by
          refine ⟨pcZero, current.trans exactCall.currentTarget,
            codeAddress.trans exactCall.codeAddress, ?_⟩
          rw [codeEq]
          exact messageUses
        have dataEq : sevm.data = isPausedCalldata :=
          data.trans exactCall.data
        have guardZero :
            B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0 := by
          rw [dataEq, isPausedCalldata_length]
          decide
        have selectorEq : Sevm.selector sevm = selIsPaused := by
          apply selector_eq_of_data_eq_abiSelectorBytes_append
            (selected := selIsPaused) (tail := [])
          · rfl
          · simpa [isPausedCalldata] using dataEq
        exact noExec_of_selectedRuntimeEntry actualRun invocation guardZero
          selectorEq (by simp [funcs]) []
            (isPaused_reachableExecFree dp) sameFrame x execAt
  · exact Exec.noRetainedWriteTo_of_not_commits actualRun committed
      circuitBreaker key

end LidoTriggerableWithdrawalsGateway
end Blanc
