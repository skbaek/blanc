import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetInterface
import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute
import Blanc.LidoTriggerableWithdrawalsGatewayPauseFor
import Blanc.LidoTriggerableWithdrawalsGatewayIsPaused
import Blanc.LidoTriggerableWithdrawalsGatewayAuthorization
import Blanc.MessageExecutionInversion
import Blanc.ReachableExecFree

/-!
# Account-level pinned-target boundary for the Triggerable Withdrawals Gateway

This family-owned module fixes the account protocol vocabulary that the TWG
runtime must discharge.  It intentionally imports no Circuit Breaker module:
the calldata builders, storage projection, and protected selector are the
gateway family's own definitions.

The public constructor below is assembled only from source-derived A2 walks
and actual retained-message inversion.  It does not introduce a structure of
assumed semantic witnesses and does not reflect an executable fixture into
theorem evidence.  CircuitBreaker-cell noninterference follows the actual
calldata-selected route, while the protected trigger clause treats arbitrary
selector tails: a clean raw success must pass the ABI and role guards before
the live pause forces `ResumedExpected()`.

The resulting public theorem is

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

private theorem runtime_pcFree (dp : DeployParams) :
    (runtime dp).pcFree = true := by
  rw [show (runtime dp).pcFree = (runtime ⟨0⟩).pcFree by rfl]
  decide +kernel

/-! ## Route-local exec-freedom certificates -/

/-- The finite internal-call component used by the pause entry. -/
def pauseExecMembers : List Nat :=
  [missingRoleSlot, resumedExpectedSlot, zeroPauseDurationSlot,
    arithmeticPanicSlot, collisionRefusalSlot]

private theorem pauseEntry_localExecFree :
    (nonpayable pauseFor).localExecFree = true := by
  decide +kernel

private theorem pauseEntry_callsIn :
    (nonpayable pauseFor).callsIn
      (fun callee => callee ∈ pauseExecMembers) = true := by
  decide +kernel

private theorem pauseBody_localExecFree :
    pauseFor.localExecFree = true := by
  decide +kernel

private theorem pauseBody_callsIn :
    pauseFor.callsIn (fun callee => callee ∈ pauseExecMembers) = true := by
  decide +kernel

private theorem pauseComponent_missingRole (dp : DeployParams) :
    (match (runtime dp).function? missingRoleSlot with
      | none => false
      | some body =>
          body.localExecFree &&
            body.callsIn (fun callee => callee ∈ pauseExecMembers)) = true := by
  rfl

private theorem pauseComponent_resumedExpected (dp : DeployParams) :
    (match (runtime dp).function? resumedExpectedSlot with
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
        some (Func.revertData
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
  · exact pauseComponent_resumedExpected dp
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

/-- Direct-body companion used after the optimized runtime's shared
nonpayable guard has already been traversed. -/
theorem pauseForShared_reachableExecFree (dp : DeployParams) :
    (runtime dp).reachableExecFree pauseFor pauseExecMembers = true := by
  simp only [Prog.reachableExecFree, Bool.and_eq_true]
  exact ⟨⟨pauseBody_localExecFree, pauseBody_callsIn⟩,
    pauseComponents_execFree dp⟩

/-- The exact query entry is locally source-exec-free and has no internal
call edge. -/
theorem isPaused_reachableExecFree (dp : DeployParams) :
    (runtime dp).reachableExecFree (nonpayable isPaused) [] = true := by
  rfl

theorem isPausedShared_reachableExecFree (dp : DeployParams) :
    (runtime dp).reachableExecFree isPaused [] = true := by
  rfl

/-! ## Exact selected-entry route -/

private theorem processMessage_entry_value
    {msg : Msg} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {raw : Execution}
    {ex : Except (EvmError × State × AdrSet × Tra) Devm}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, raw⟩) ex) :
    sevm.value = msg.value := by
  have enter := (RunFrame.some_inv process).1
  rcases Frame.enter_run_inv enter with ⟨benv, _transfer, evmEq⟩
  have value := congrArg (fun evm : Evm => evm.sta.value) evmEq
  simpa [Frame.ofCall, initEvm, initSevm, Msg.withBenv] using value

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
    (valueZero : sevm.value = 0)
    (selectorEq : Sevm.selector sevm = selector)
    (notTrigger : selector ≠ selTriggerFullWithdrawals)
    (member : (selector, body) ∈ sharedNonpayableFuncs)
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
        (Func.revert <?>
          (fsig +++ Ninst.dup 0 :::
            Ninst.pushB256 selTriggerFullWithdrawals ::: Ninst.eq :::
            ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
              (Ninst.callvalue ::: Ninst.iszero :::
                (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
                  Func.revert))))))
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

  change Exec.Deriv.SourceCursor
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) (runtime dp)
      _selectorPath
      ([Ninst.dup 0, Ninst.pushB256 selTriggerFullWithdrawals, Ninst.eq] +++
        ((Ninst.pop ::: triggerFullWithdrawals dp) <?>
          (Ninst.callvalue ::: Ninst.iszero :::
            (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
              Func.revert)))) at selectorCursor
  rcases selectorRoute.dropLineRun (by simp [Ninst.pushB256]) with
    ⟨_triggerBranchPath, triggerBranchCursor, triggerLineRun,
      _triggerChronology, triggerBranchRoute⟩
  rcases Line.of_run_cons triggerLineRun with
    ⟨afterDup, dupRun, triggerLineRun⟩
  rcases Line.of_run_cons triggerLineRun with
    ⟨afterTriggerPush, triggerPushRun, triggerLineRun⟩
  rcases Line.of_run_cons triggerLineRun with
    ⟨_afterTriggerEq, triggerEqRun, triggerLineNil⟩
  cases triggerLineNil
  have duplicated : selector :: selector :: [] <<+ afterDup.stack :=
    prefix_of_dup_val dupRun (by show_nth) selectorPrefix
  have triggerPushed : selTriggerFullWithdrawals :: selector :: selector :: [] <<+
      afterTriggerPush.stack := by
    simpa using prefix_of_push (of_run_pushB256 triggerPushRun) duplicated
  have triggerFlagPrefix :
      (selTriggerFullWithdrawals =? selector) :: selector :: [] <<+
        triggerBranchCursor.pre.stack :=
    prefix_of_eq triggerEqRun triggerPushed
  rw [show (selTriggerFullWithdrawals =? selector) = 0 from by
    simp [B256.eqCheck, Ne.symm notTrigger]] at triggerFlagPrefix
  rcases triggerBranchRoute.selectBranchZero triggerBranchCursor compiled
      (by trivial) execAt triggerFlagPrefix with
    ⟨nonTriggerCursor, nonTriggerRoute, nonTriggerPrefix⟩

  change Exec.Deriv.SourceCursor
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) (runtime dp)
      ⟨_triggerBranchPath.functionIndex,
        _triggerBranchPath.steps ++ [.branchLeft]⟩
      ([Ninst.callvalue, Ninst.iszero] +++
        (linearDispatchWith fallbackSlot sharedNonpayableFuncs <?>
          Func.revert)) at nonTriggerCursor
  rcases nonTriggerRoute.dropLineRun (by simp) with
    ⟨_valueBranchPath, valueBranchCursor, valueLineRun,
      _valueChronology, valueBranchRoute⟩
  rcases Line.of_run_cons valueLineRun with
    ⟨afterValue, valueRun, valueLineRun⟩
  rcases Line.of_run_cons valueLineRun with
    ⟨_afterValueZero, valueZeroRun, valueLineNil⟩
  cases valueLineNil
  have valuePrefix : sevm.value :: selector :: [] <<+ afterValue.stack := by
    simpa using prefix_of_push (of_run_callvalue valueRun) nonTriggerPrefix
  have valueFlagPrefix : (sevm.value =? 0) :: selector :: [] <<+
      valueBranchCursor.pre.stack :=
    prefix_of_iszero valueZeroRun valuePrefix
  rw [valueZero, show ((0 : B256) =? 0) = 1 from by
    simp [B256.eqCheck]] at valueFlagPrefix
  rcases valueBranchRoute.selectBranchSucc valueBranchCursor compiled
      (by trivial) execAt (by decide) valueFlagPrefix with
    ⟨dispatchCursor, dispatchRoute, dispatchPrefix⟩
  rcases
      Exec.Deriv.SourceCursor.Toward.linearDispatchWith_selectedBody
        compiled execAt sharedNonpayableFuncs
          sharedNonpayableFuncs_selector_unique member dispatchCursor
          dispatchRoute dispatchPrefix with
    ⟨_bodyPath, bodyCursor, bodyRoute, _bodyStackPrefix⟩
  exact bodyCursor.noExec_of_reachableExecFree compiled members accepted
    bodyRoute.chronology.cursorToTarget x execAt

/-! ## Pinned-target account clauses -/

/-- Clause (i): an actual clean settled pause call exposes the successful raw
runtime walk, whose A2 pause theorem writes the family-faithful finite or
infinite projection. -/
theorem pinnedPauseTarget_pauseFor_effect
    (dp : DeployParams) (circuitBreaker gateway : Adr)
    {msg : Msg} {xl : Xlot} {post : Devm} {duration : B256}
    (exactCall : ExactTargetCall circuitBreaker gateway
      (pauseForCalldata duration) false msg)
    (executes : MessageExecutesProgram msg xl (runtime dp))
    (process : ProcessMessage msg xl (.ok post))
    (clean : post.error.isSome = false) :
    pausedUntil gateway (post.state.getStor gateway) =
      pauseForProjection msg.benv.stat.time duration := by
  rcases executes with
    ⟨messageUses, ⟨pc, sevm, pre⟩, raw, xlEq, ⟨run⟩⟩
  subst xl
  rcases MessageExecution.processMessage_entry_facts gateway process with
    ⟨pcZero, codeEq, current, _codeAddress, data, time,
      _entryStorage, _memoryWf⟩
  subst pc
  rcases MessageExecution.processMessage_clean_rawPost process clean with
    ⟨rawPost, rfl, _rawClean, stateEq, _outputEq⟩
  have uses : some sevm.code.toList = Prog.compile (runtime dp) := by
    rw [codeEq]
    exact messageUses
  have compiled : Prog.RunCompiledTo sevm pre (runtime dp) (.ok rawPost) :=
    Prog.RunCompiledTo.of_runCompiled
      (Prog.runCompiled_of_exec sevm pre (runtime dp) rawPost
        (runtime_pcFree dp) run uses)
  have effect := pauseFor_ok_authorized_effect compiled
    (MessageExecution.processMessage_entry_stack process)
    (data.trans exactCall.data)
  rw [stateEq]
  change rawPost.getStorVal gateway resumeSinceSlot =
    pauseForProjection msg.benv.stat.time duration
  simpa [current.trans exactCall.currentTarget, time] using effect.2.2

/-- Clause (ii): the exact clean static query preserves the pause projection
and returns the canonical word corresponding to the entry-time predicate. -/
theorem pinnedPauseTarget_isPaused_truthful
    (dp : DeployParams) (circuitBreaker gateway : Adr)
    {msg : Msg} {xl : Xlot} {ex : TargetMessageResult}
    (exactCall : ExactTargetCall circuitBreaker gateway
      isPausedCalldata true msg)
    (executes : MessageExecutesProgram msg xl (runtime dp))
    (process : ProcessMessage msg xl ex)
    (post : Devm) (exEq : ex = .ok post)
    (clean : post.error.isSome = false) :
    pausedUntil gateway (post.state.getStor gateway) =
        pausedUntil gateway (msg.benv.state.getStor gateway) ∧
      (AcceptedBoolExecution ex 1 ↔
        PausedAt pausedUntil msg.benv.state gateway msg.benv.stat.time) ∧
      (¬ PausedAt pausedUntil msg.benv.state gateway msg.benv.stat.time →
        AcceptedBoolExecution ex 0 ∨ BoolQueryExecutionFailure ex) := by
  subst ex
  rcases executes with
    ⟨messageUses, ⟨pc, sevm, pre⟩, raw, xlEq, ⟨run⟩⟩
  subst xl
  rcases MessageExecution.processMessage_entry_facts gateway process with
    ⟨pcZero, codeEq, current, _codeAddress, data, time,
      entryStorage, memoryWf⟩
  subst pc
  rcases MessageExecution.processMessage_clean_rawPost process clean with
    ⟨rawPost, rfl, rawClean, stateEq, outputEq⟩
  have uses : some sevm.code.toList = Prog.compile (runtime dp) := by
    rw [codeEq]
    exact messageUses
  have compiled : Prog.RunCompiledTo sevm pre (runtime dp) (.ok rawPost) :=
    Prog.RunCompiledTo.of_runCompiled
      (Prog.runCompiled_of_exec sevm pre (runtime dp) rawPost
        (runtime_pcFree dp) run uses)
  rcases isPaused_exact_of_prog_run compiled
      (MessageExecution.processMessage_entry_stack process)
      (data.trans exactCall.data) memoryWf with
    ⟨_valueZero, storageEq, rawOutput⟩
  have postClean : post.error = none := by
    cases errorEq : post.error with
    | none => rfl
    | some err => simp [errorEq] at clean
  let rawPaused : Prop :=
    sevm.benvStat.time <
      pre.getStorVal sevm.currentTarget resumeSinceSlot
  have postOutput : post.output =
      (if rawPaused then (1 : B256) else 0).toBytes := by
    exact outputEq.trans rawOutput
  have pausedEq : rawPaused ↔
      PausedAt pausedUntil msg.benv.state gateway msg.benv.stat.time := by
    unfold rawPaused PausedAt pausedUntil
    rw [← time]
    change sevm.benvStat.time <
        (pre.state.getStor sevm.currentTarget).get resumeSinceSlot ↔
      sevm.benvStat.time <
        (msg.benv.state.getStor gateway).get resumeSinceSlot
    rw [current.trans exactCall.currentTarget, entryStorage]
  have acceptedIff (word : B256) :
      AcceptedBoolExecution (.ok post) word ↔
        (if rawPaused then (1 : B256) else 0) = word :=
    (acceptedBoolExecution_ok_iff post word).trans
      (acceptedBoolWord_iff_of_output postClean postOutput)
  refine ⟨?_, ?_, ?_⟩
  · rw [stateEq]
    unfold pausedUntil
    change rawPost.getStorVal gateway resumeSinceSlot =
      (msg.benv.state.getStor gateway).get resumeSinceSlot
    calc
      rawPost.getStorVal gateway resumeSinceSlot =
          rawPost.getStorVal sevm.currentTarget resumeSinceSlot := by
        rw [current.trans exactCall.currentTarget]
      _ = pre.getStorVal sevm.currentTarget resumeSinceSlot := storageEq
      _ = (msg.benv.state.getStor gateway).get resumeSinceSlot := by
        change (pre.state.getStor sevm.currentTarget).get resumeSinceSlot =
          (msg.benv.state.getStor gateway).get resumeSinceSlot
        rw [current.trans exactCall.currentTarget, entryStorage]
  · exact (acceptedIff 1).trans <| by
      constructor
      · intro wordEq
        by_cases raw : rawPaused
        · exact pausedEq.mp raw
        · simp only [if_neg raw] at wordEq
          exfalso
          exact (show (0 : B256) ≠ 1 by decide) wordEq
      · intro paused
        have raw := pausedEq.mpr paused
        simp [raw]
  · intro notPaused
    left
    apply (acceptedIff 0).mpr
    have notRaw : ¬ rawPaused := fun paused => notPaused (pausedEq.mp paused)
    simp [notRaw]

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
        have valueZero : sevm.value = 0 :=
          (processMessage_entry_value process).trans exactCall.valueZero
        exact noExec_of_selectedRuntimeEntry actualRun invocation guardZero
          valueZero selectorEq (by decide)
          (by simp [sharedNonpayableFuncs]) pauseExecMembers
            (pauseForShared_reachableExecFree dp) sameFrame x execAt
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
        have valueZero : sevm.value = 0 :=
          (processMessage_entry_value process).trans exactCall.valueZero
        exact noExec_of_selectedRuntimeEntry actualRun invocation guardZero
          valueZero selectorEq (by decide)
          (by simp [sharedNonpayableFuncs]) []
            (isPausedShared_reachableExecFree dp) sameFrame x execAt
  · exact Exec.noRetainedWriteTo_of_not_commits actualRun committed
      circuitBreaker key

/-- Clause (iv): a nonexceptional selected trigger call cannot settle cleanly
while the entry projection is paused.  The clean arm exposes a successful raw
runtime walk, contradicting the arbitrary-tail trigger theorem; the remaining
ordinary arm is already exactly `.revert`. -/
theorem pinnedPauseTarget_protectedSurface_reverts
    (dp : DeployParams) (gateway : Adr)
    {msg : Msg} {xl : Xlot} {child : Devm} {selected : B256}
    (currentTarget : msg.currentTarget = gateway)
    (_targetAddress : msg.target = some gateway)
    (_codeAddress : msg.codeAddress = some gateway)
    (executes : MessageExecutesProgram msg xl (runtime dp))
    (hasSelector : HasSelector msg selected)
    (member : selected ∈ protectedSurface)
    (paused : PausedAt pausedUntil msg.benv.state gateway
      msg.benv.stat.time)
    (process : ProcessMessage msg xl (.ok child))
    (settled : SettledNormallyOrReverted child) :
    child.error = some .revert := by
  simp only [protectedSurface, List.mem_singleton] at member
  subst selected
  rcases settled with childClean | childRevert
  · have clean : child.error.isSome = false := by
      rw [childClean]
      rfl
    rcases executes with
      ⟨messageUses, ⟨pc, sevm, pre⟩, raw, xlEq, ⟨run⟩⟩
    subst xl
    rcases MessageExecution.processMessage_entry_facts gateway process with
      ⟨pcZero, codeEq, current, _entryCodeAddress, data, time,
        entryStorage, _memoryWf⟩
    subst pc
    rcases MessageExecution.processMessage_clean_rawPost process clean with
      ⟨rawPost, rfl, _rawClean, _stateEq, _outputEq⟩
    have uses : some sevm.code.toList = Prog.compile (runtime dp) := by
      rw [codeEq]
      exact messageUses
    have compiled : Prog.RunCompiledTo sevm pre (runtime dp) (.ok rawPost) :=
      Prog.RunCompiledTo.of_runCompiled
        (Prog.runCompiled_of_exec sevm pre (runtime dp) rawPost
          (runtime_pcFree dp) run uses)
    rcases hasSelector with ⟨tail, messageData⟩
    have selectedData : sevm.data =
        abiSelectorBytes selTriggerFullWithdrawals ++ tail :=
      data.trans messageData
    have rawPaused : sevm.benvStat.time <
        pre.getStorVal sevm.currentTarget resumeSinceSlot := by
      unfold PausedAt pausedUntil at paused
      change sevm.benvStat.time <
        (pre.state.getStor sevm.currentTarget).get resumeSinceSlot
      rw [time, current.trans currentTarget, entryStorage]
      exact paused
    have rawPausedCheck : B256.ltCheck sevm.benvStat.time
        (pre.getStorVal sevm.currentTarget resumeSinceSlot) ≠ 0 := by
      rw [B256.ltCheck, if_pos rawPaused]
      decide
    exact (triggerFullWithdrawals_selected_paused_not_ok compiled
      (MessageExecution.processMessage_entry_stack process) selectedData
      rawPausedCheck).elim
  · exact childRevert

/-- The compiled Triggerable Withdrawals Gateway discharges the complete
family-neutral pinned pause-target account protocol. -/
theorem pinnedPauseTarget
    (dp : DeployParams) (circuitBreaker gateway : Adr)
    (circuitBreakerCells : List B256)
    (different : gateway ≠ circuitBreaker) :
    PinnedPauseTarget circuitBreaker gateway (runtime dp)
      pauseForCalldata isPausedCalldata pausedUntil
      circuitBreakerCells protectedSurface := by
  refine {
    pauseFor_effect := ?_
    isPaused_truthful := ?_
    circuitBreaker_noninterference := ?_
    protectedSurface_reverts := ?_
  }
  · intro msg xl post duration exactCall executes process clean
    exact pinnedPauseTarget_pauseFor_effect dp circuitBreaker gateway
      exactCall executes process clean
  · intro msg xl ex exactCall executes process post exEq clean
    exact pinnedPauseTarget_isPaused_truthful dp circuitBreaker gateway
      exactCall executes process post exEq clean
  · intro msg xl ex inbound executes process key member
    exact pinnedPauseTarget_circuitBreaker_noninterference dp circuitBreaker
      gateway circuitBreakerCells different inbound executes process key member
  · intro msg xl child selected current targetAddress codeAddress executes
      hasSelector member paused process settled
    exact pinnedPauseTarget_protectedSurface_reverts dp gateway current
      targetAddress codeAddress executes hasSelector member paused process
      settled

end LidoTriggerableWithdrawalsGateway
end Blanc
