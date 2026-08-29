import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute
import Blanc.LidoTriggerableWithdrawalsGatewayTrigger

/-!
# Triggerable Withdrawals Gateway: trigger authorization route

This family-owned unit isolates the payable trigger's route.  Unlike the six
ordinary role-gated endpoints, `triggerFullWithdrawals` first runs its exact
dynamic-ABI validator and then uses `Trigger.coreFlatRoleGuard`; it does not use
the outer runtime's `onlyRole` combinator.

The flat guard and the authorized-to-paused suffix below are exact
`Func.RunCompiledTo` inversions over arbitrary terminal outcomes.  The final
section records the canonical zero-element validator walk which must connect
the selected runtime body to that guard.  No evaluator result, inhabitance
witness, or assumed body walk is accepted as evidence.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoTriggerableWithdrawalsGateway

/-! ## Trigger-owned canonical input and outcomes -/

/-- The smallest complete canonical trigger input: a three-word head followed
by the zero length of the dynamic validator tuple array. -/
def triggerEmptyAuthorizationCalldata
    (refundRecipient : Adr) (exitType : B256) : Bytes :=
  abiSelectorBytes selTriggerFullWithdrawals ++
    ((Nat.toB256 0x60).toBytes ++ refundRecipient.toB256.toBytes ++
      exitType.toBytes ++ (Nat.toB256 0).toBytes)

theorem triggerEmptyAuthorizationCalldata_length
    (refundRecipient : Adr) (exitType : B256) :
    (triggerEmptyAuthorizationCalldata refundRecipient exitType).length =
      132 := by
  simp [triggerEmptyAuthorizationCalldata, abiSelectorBytes_length,
    B256.length_toBytes]

theorem selector_of_triggerEmptyAuthorizationCalldata
    {sevm : Sevm} {refundRecipient : Adr} {exitType : B256}
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType) :
    Sevm.selector sevm = selTriggerFullWithdrawals := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selTriggerFullWithdrawals)
      (tail := (Nat.toB256 0x60).toBytes ++
        refundRecipient.toB256.toBytes ++ exitType.toBytes ++
        (Nat.toB256 0).toBytes)
  · rfl
  · simpa [triggerEmptyAuthorizationCalldata] using hdata

/-- Every failed check in the trigger's private flat guard reaches the runtime
AccessControl selector reverter. -/
def TriggerRoleFailure (out : Execution) : Prop :=
  (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
    (∃ post, out = .error (.revert, post) ∧
      post.output = customErrorData "AccessControlUnauthorizedAccount")

/-- Once authorized, a paused gateway reaches `ResumedExpected()` before the
value, array, and quota checks. -/
def PausedTriggerFailure (out : Execution) : Prop :=
  (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
    (∃ post, out = .error (.revert, post) ∧
      post.output = Trigger.resumedExpectedSelector.toBytes.drop 28)

/-! ## Runtime-rebased trigger slots and bodies -/

def rebasedTriggerResumedExpectedSlot : Nat :=
  triggerAuxDelta + Trigger.resumedExpectedSlot

def rebasedTriggerRoleFailureSlot : Nat :=
  triggerAuxDelta + Trigger.roleFailureBoundarySlot

def rebasedTriggerAfterValidationSlot : Nat :=
  triggerAuxDelta + Trigger.afterValidationSlot

theorem rebasedTriggerResumedExpectedSlot_eq :
    rebasedTriggerResumedExpectedSlot = 31 := rfl

theorem rebasedTriggerRoleFailureSlot_eq :
    rebasedTriggerRoleFailureSlot = 38 := rfl

theorem rebasedTriggerAfterValidationSlot_eq :
    rebasedTriggerAfterValidationSlot = 40 := rfl

theorem runtime_rebasedTriggerResumedExpected_get (dp : DeployParams) :
    ((runtime dp).main :: (runtime dp).aux)[rebasedTriggerResumedExpectedSlot]?
      = some (Trigger.rebaseLocalCalls triggerAuxDelta
        Trigger.resumedExpectedRevert) := by
  simp [rebasedTriggerResumedExpectedSlot_eq, runtime, aux, baseAux,
    Trigger.rebasedLocalAuxWithRoleFailure,
    Trigger.localAuxWithRoleFailure, triggerAuxDelta]

theorem runtime_rebasedTriggerRoleFailure_get (dp : DeployParams) :
    ((runtime dp).main :: (runtime dp).aux)[rebasedTriggerRoleFailureSlot]?
      = some triggerRoleFailure := by
  simp [rebasedTriggerRoleFailureSlot_eq, runtime, aux, baseAux,
    Trigger.rebasedLocalAuxWithRoleFailure,
    Trigger.localAuxWithRoleFailure, triggerAuxDelta, triggerRoleFailure,
    Trigger.rebaseLocalCalls, runtimeError, Func.revSelector]

theorem runtime_rebasedTriggerAfterValidation_get (dp : DeployParams) :
    ((runtime dp).main :: (runtime dp).aux)[rebasedTriggerAfterValidationSlot]?
      = some (Trigger.rebaseLocalCalls triggerAuxDelta
        Trigger.afterValidation) := by
  simp [rebasedTriggerAfterValidationSlot_eq, runtime, aux, baseAux,
    Trigger.rebasedLocalAuxWithRoleFailure,
    Trigger.localAuxWithRoleFailure, triggerAuxDelta]

/-- Rebasing only renumbers local calls, so it passes through a prepended
line untouched.  The walk needs this to expose a `+++` head that
`runCompiledTo_prepend_inv` can match under the rebase wrapper. -/
private theorem rebaseLocalCalls_prepend (delta : Nat) (line : Line)
    (rest : Func) :
    Trigger.rebaseLocalCalls delta (line +++ rest) =
      line +++ Trigger.rebaseLocalCalls delta rest := by
  induction line with
  | nil => rfl
  | cons op tail ih => simp [prepend, Trigger.rebaseLocalCalls, ih]

def rebasedTriggerAuthorizedContinuation : Func :=
  Trigger.rebaseLocalCalls triggerAuxDelta <|
    callvalue ::: selfbalance ::: lt :::
    ((.call Trigger.arithmeticPanicSlot) <?>
      (callvalue ::: selfbalance ::: sub :::
        Trigger.storeWord Trigger.balanceBeforeWord +++
       pushB256 resumeSinceSlot ::: sload ::: timestamp ::: lt :::
       ((.call Trigger.resumedExpectedSlot) <?>
         (callvalue ::: iszero :::
          ((.call Trigger.zeroMsgValueSlot) <?>
            (Trigger.loadWord Trigger.requestsCountWord +++ iszero :::
             ((.call Trigger.zeroValidatorsDataSlot) <?>
               .call Trigger.consumeQuotaSlot)))))))

/-- Rebasing changes only local calls; the flat storage walk itself is exactly
the source guard. -/
theorem rebasedTriggerAfterValidation_exact :
    Trigger.rebaseLocalCalls triggerAuxDelta Trigger.afterValidation =
      Trigger.coreFlatRoleGuard (.call rebasedTriggerRoleFailureSlot)
        rebasedTriggerAuthorizedContinuation := by
  rfl

theorem triggerFullWithdrawals_rebasedValidator_exact (dp : DeployParams) :
    triggerFullWithdrawals dp =
      Trigger.rebaseLocalCalls triggerAuxDelta Trigger.validateCalldata := by
  rfl

/-! ## Passing the validator's guards -/

/-- One passed validator guard: a zero flag takes the falling-through arm,
leaving storage and memory untouched by the branch itself. -/
private theorem trigger_guard_passes
    {dp : DeployParams} {sevm : Sevm} {guardPost : Devm} {out : Execution}
    {errSlot : Nat} {rest : Func} {tail : Stack}
    (pGuard : (0 : B256) :: tail <<+ guardPost.stack)
    (branchRun : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm guardPost (Func.branch rest (Func.call errSlot)) out) :
    ∃ restPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm restPre rest out ∧
      tail <<+ restPre.stack ∧
      guardPost.state = restPre.state ∧
      guardPost.memory = restPre.memory := by
  obtain ⟨restPre, hpop, restRun, pRest⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pGuard branchRun
  exact ⟨restPre, restRun, pRest, hpop.state, hpop.memory⟩

theorem rebasedTriggerRoleFailure_call_reverts_exact
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre (.call rebasedTriggerRoleFailureSlot) out) :
    TriggerRoleFailure out := by
  obtain ⟨_, _, bodyRun⟩ := runCompiledTo_call_inv
    (runtime_rebasedTriggerRoleFailure_get dp) run
  simpa [TriggerRoleFailure, triggerRoleFailure,
    runtimeError, customErrorData] using
      runCompiledTo_revSelector_inv
        (hlen := by simp [customErrorData, B256.length_toBytes]) bodyRun

theorem rebasedTriggerResumedExpected_call_reverts_exact
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre (.call rebasedTriggerResumedExpectedSlot) out) :
    PausedTriggerFailure out := by
  obtain ⟨_, _, bodyRun⟩ := runCompiledTo_call_inv
    (runtime_rebasedTriggerResumedExpected_get dp) run
  simpa [PausedTriggerFailure, Trigger.resumedExpectedRevert,
    Trigger.selectorRevert, Trigger.rebaseLocalCalls] using
      runCompiledTo_revSelector_inv
        (hlen := by simp [B256.length_toBytes]) bodyRun

/-! The canonical empty-array image pins every calldata word used by the
validator. -/

theorem triggerEmptyAuthorization_arg0
    {sevm : Sevm} {refundRecipient : Adr} {exitType : B256}
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType) :
    Sevm.argWord sevm 0 = 0x60 := by
  change Sevm.dataWord sevm 4 = (0x60 : B256)
  apply dataWord_of_append
    (pre := abiSelectorBytes selTriggerFullWithdrawals)
    (post := refundRecipient.toB256.toBytes ++ exitType.toBytes ++
      (Nat.toB256 0).toBytes)
  · rw [abiSelectorBytes_length]
    rfl
  · rw [hdata, triggerEmptyAuthorizationCalldata]
    simp [List.append_assoc]
    rfl

theorem triggerEmptyAuthorization_arg1
    {sevm : Sevm} {refundRecipient : Adr} {exitType : B256}
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType) :
    Sevm.argWord sevm 1 = refundRecipient.toB256 := by
  change Sevm.dataWord sevm 36 = refundRecipient.toB256
  apply dataWord_of_append
    (pre := abiSelectorBytes selTriggerFullWithdrawals ++
      (Nat.toB256 0x60).toBytes)
    (post := exitType.toBytes ++ (Nat.toB256 0).toBytes)
  · rw [List.length_append, abiSelectorBytes_length, B256.length_toBytes]
    rfl
  · rw [hdata, triggerEmptyAuthorizationCalldata]
    simp [List.append_assoc]

theorem triggerEmptyAuthorization_arg2
    {sevm : Sevm} {refundRecipient : Adr} {exitType : B256}
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType) :
    Sevm.argWord sevm 2 = exitType := by
  change Sevm.dataWord sevm 68 = exitType
  apply dataWord_of_append
    (pre := abiSelectorBytes selTriggerFullWithdrawals ++
      (Nat.toB256 0x60).toBytes ++ refundRecipient.toB256.toBytes)
    (post := (Nat.toB256 0).toBytes)
  · simp [abiSelectorBytes_length, B256.length_toBytes]
    rfl
  · simpa [triggerEmptyAuthorizationCalldata, List.append_assoc] using hdata

theorem triggerEmptyAuthorization_arrayLength
    {sevm : Sevm} {refundRecipient : Adr} {exitType : B256}
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType) :
    Sevm.dataWord sevm 100 = 0 := by
  apply dataWord_of_append
    (pre := abiSelectorBytes selTriggerFullWithdrawals ++
      (Nat.toB256 0x60).toBytes ++ refundRecipient.toB256.toBytes ++
      exitType.toBytes)
    (post := [])
  · simp [abiSelectorBytes_length, B256.length_toBytes]
    rfl
  · rw [hdata, triggerEmptyAuthorizationCalldata]
    simp [List.append_assoc]
    rfl

theorem triggerEmptyAuthorization_refundRecipient_valid
    (refundRecipient : Adr) : ValidAdr refundRecipient.toB256 :=
  ⟨refundRecipient, rfl⟩

/-! These two helpers expose only the concrete effects of the trigger's fixed
scratch-word accessors.  The read value remains a caller-supplied equality
about the actual byte image; in particular no read-over-write fact is assumed
by the executable walk. -/

private theorem triggerStoreWord_step
    {sevm : Sevm} {pre post : Devm} {word value : B256}
    {tail : Stack} {image : Bytes}
    (hp : value :: tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (run : Line.Run sevm pre (Trigger.storeWord word) post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt image (word * 32).toNat value.toBytes) ∧
      pre.state = post.state := by
  have storeRun : Line.Run sevm pre (mstoreAt word) post := by
    simpa [Trigger.storeWord] using run
  obtain ⟨stack, memory⟩ := of_run_mstoreAt_val storeRun hp
  refine ⟨stack, ?_, ?_, Line.of_inv Devm.state (by line_inv) storeRun⟩
  · rw [memory]
    exact hwf.write _ _
  · rw [memory]
    exact Mem.Reads.write hwf hreads _ _

private theorem triggerLoadWord_step
    {sevm : Sevm} {pre post : Devm} {word value : B256}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hvalue : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (run : Line.Run sevm pre (Trigger.loadWord word) post) :
    value :: tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory image ∧
      pre.state = post.state := by
  unfold Trigger.loadWord at run
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  rcases Line.of_run_cons run with ⟨_, loadRun, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 pushRun
  have pPush := prefix_of_push pushed hp
  have pushWf : Mem.Wf afterPush.memory := by
    rw [← pushed.memory]
    exact hwf
  have pushReads : Mem.Reads afterPush.memory image := by
    rw [← pushed.memory]
    exact hreads
  obtain ⟨loaded, memory, returnData⟩ :=
    prefix_of_mload_val loadRun pPush pushReads
  refine ⟨?_, ?_, ?_, Line.of_inv Devm.state (by line_inv)
    (Line.Run.cons pushRun (Line.Run.cons loadRun Line.Run.nil))⟩
  · simpa [hvalue] using loaded
  · rw [memory]
    exact pushWf.extend _ _
  · rw [memory]
    exact pushReads.extend _ _

/-! ## The validator's guarded suffixes

`Trigger.validateCalldata` is a linear chain of six guards, each of which
either calls the malformed-ABI reverter or falls through to the next.  Naming
the suffixes lets every guard be walked by its own small lemma instead of one
proof carrying the whole nested term; `validateCalldata_eq` pins the names to
the source so they cannot drift. -/

private def validatorAfterBounds : Func :=
  pushB256 0 ::: Trigger.storeWord Trigger.loopIndexWord +++
    pushB256 0 ::: Trigger.storeWord Trigger.pubkeysTailBytesWord +++
      pushB256 0 ::: Trigger.storeWord Trigger.routerTupleBytesWord +++
        Func.call Trigger.afterValidationSlot

private def validatorAfterCount : Func :=
  Trigger.loadWord Trigger.arrayLengthPtrWord +++
    pushB256 32 ::: Ninst.add :::
      Trigger.storeWord Trigger.arrayElementsBaseWord +++
        Trigger.loadWord Trigger.arrayElementsBaseWord +++
          Trigger.loadWord Trigger.requestsCountWord +++
            pushB256 32 ::: Ninst.mul ::: Ninst.add :::
              Trigger.loadWord Trigger.calldataSizeWord +++ Ninst.lt :::
                ((Func.call Trigger.malformedAbiSlot) <?> validatorAfterBounds)

private def validatorAfterHeader : Func :=
  Trigger.calldataloadAt Trigger.arrayLengthPtrWord +++
    Trigger.storeWord Trigger.requestsCountWord +++
      pushB256 Trigger.maxUint64 :::
        Trigger.loadWord Trigger.requestsCountWord +++ Ninst.gt :::
          ((Func.call Trigger.malformedAbiSlot) <?> validatorAfterCount)

private def validatorAfterOffset : Func :=
  arg 0 +++ Trigger.storeWord Trigger.validatorsOffsetWord +++
    arg 0 +++ pushB256 4 ::: Ninst.add :::
      Trigger.storeWord Trigger.arrayLengthPtrWord +++
        Trigger.loadWord Trigger.arrayLengthPtrWord +++
          pushB256 32 ::: Ninst.add :::
            Trigger.loadWord Trigger.calldataSizeWord +++ Ninst.lt :::
              ((Func.call Trigger.malformedAbiSlot) <?> validatorAfterHeader)

private def validatorAfterAddress : Func :=
  arg 1 +++ Trigger.storeWord Trigger.refundRecipientWord +++
    arg 2 +++ Trigger.storeWord Trigger.exitTypeWord +++
      pushB256 Trigger.maxUint64 ::: arg 0 +++ Ninst.gt :::
        ((Func.call Trigger.malformedAbiSlot) <?> validatorAfterOffset)

private def validatorAfterSize : Func :=
  Ninst.calldatasize ::: Trigger.storeWord Trigger.calldataSizeWord +++
    arg 1 +++ checkNonAddress +++
      ((Func.call Trigger.malformedAbiSlot) <?> validatorAfterAddress)

/-- The names above are exactly the source's nested suffixes. -/
private theorem validateCalldata_eq :
    Trigger.validateCalldata =
      pushB256 100 ::: Ninst.calldatasize ::: Ninst.lt :::
        ((Func.call Trigger.malformedAbiSlot) <?> validatorAfterSize) := rfl

/-! ## Walking the validator's guards

Each step consumes one guard at the canonical empty-array image, where every
flag is zero.  Memory travels as a `Mem.Wf`/`Mem.Reads` pair over an explicit
byte image, so a scratch word read back later resolves against the image the
validator itself wrote rather than against an assumed read-over-write fact. -/

/-- Guard 1 — the 132-byte canonical image clears the size floor. -/
private theorem validator_step_size
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {refundRecipient : Adr} {exitType : B256} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.rebaseLocalCalls triggerAuxDelta Trigger.validateCalldata)
        out) :
    ∃ next,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm next
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterSize) out ∧
      tail <<+ next.stack ∧
      pre.state = next.state ∧
      pre.memory = next.memory := by
  rw [validateCalldata_eq] at run
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  have r1 := Ninst.Run.of_runCompiled q1
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have p1 := prefix_of_push (of_run_pushB256 r1) hp
  have p2 := prefix_of_push (of_run_calldatasize r2) p1
  have p3 := prefix_of_lt r3 p2
  have hlen : sevm.data.length = 132 := by
    rw [hdata]
    exact triggerEmptyAuthorizationCalldata_length refundRecipient exitType
  have hflag : (Nat.toB256 sevm.data.length <? (100 : B256)) = 0 := by
    rw [hlen]; decide
  have g : (0 : B256) :: tail <<+ s3.stack := by simpa [hflag] using p3
  obtain ⟨next, nextRun, pNext, stateNext, memNext⟩ :=
    trigger_guard_passes g run
  refine ⟨next, nextRun, pNext, ?_, ?_⟩
  · exact ((Ninst.Hinv.inv (f := Devm.state) r1).trans
      ((Ninst.Hinv.inv (f := Devm.state) r2).trans
        ((Ninst.Hinv.inv (f := Devm.state) r3).trans stateNext)))
  · exact ((Ninst.Hinv.inv (f := Devm.memory) r1).trans
      ((Ninst.Hinv.inv (f := Devm.memory) r2).trans
        ((Ninst.Hinv.inv (f := Devm.memory) r3).trans memNext)))

/-- Guard 2 — the refund recipient is address-shaped, so the dirty-high-bit
check falls through.  The calldata size is banked in its scratch word. -/
private theorem validator_step_address
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {refundRecipient : Adr} {exitType : B256} {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterSize)
      out) :
    ∃ next,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm next
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterAddress) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory
        (Bytes.writeAt image 32 (Nat.toB256 132).toBytes) ∧
      pre.state = next.state := by
  have hlen : sevm.data.length = 132 := by
    rw [hdata]
    exact triggerEmptyAuthorizationCalldata_length refundRecipient exitType
  unfold validatorAfterSize at run
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  simp only [rebaseLocalCalls_prepend] at run
  have r1 := Ninst.Run.of_runCompiled q1
  have p1 : Nat.toB256 132 :: tail <<+ s1.stack := by
    simpa [hlen] using prefix_of_push (of_run_calldatasize r1) hp
  have wf1 : Mem.Wf s1.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r1]; exact hwf
  have reads1 : Mem.Reads s1.memory image := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r1]; exact hreads
  obtain ⟨s2, storeRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    triggerStoreWord_step p1 wf1 reads1 storeRun
  obtain ⟨s3, argRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨s4, checkRun, run⟩ := runCompiledTo_prepend_inv run
  have pArg := prefix_of_arg p2 argRun
  obtain ⟨y, pY, hiff⟩ := of_check_non_address pArg checkRun
  have hy : y = 0 :=
    hiff.mpr ⟨refundRecipient, (triggerEmptyAuthorization_arg1 hdata).symm⟩
  rw [hy] at pY
  obtain ⟨next, nextRun, pNext, stateNext, memNext⟩ :=
    trigger_guard_passes pY run
  have argMem : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv) argRun
  have checkMem : s3.memory = s4.memory :=
    Line.of_inv Devm.memory (by line_inv) checkRun
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_⟩
  · rw [← memNext, ← checkMem, ← argMem]; exact wf2
  · rw [← memNext, ← checkMem, ← argMem]
    rw [show ((Trigger.calldataSizeWord * 32 : B256)).toNat = 32 from by
      decide] at reads2
    exact reads2
  · exact ((Ninst.Hinv.inv (f := Devm.state) r1).trans
      (state2.trans
        ((Line.of_inv Devm.state (by line_inv) argRun).trans
          ((Line.of_inv Devm.state (by line_inv) checkRun).trans
            stateNext))))

/-- Guard 3 — the head offset `0x60` is far below the `uint64` decoder bound.
The refund recipient and exit type are banked on the way. -/
private theorem validator_step_offset
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {refundRecipient : Adr} {exitType : B256} {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterAddress) out) :
    ∃ next,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm next
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterOffset) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory
        (Bytes.writeAt
          (Bytes.writeAt image 192 refundRecipient.toB256.toBytes)
          224 exitType.toBytes) ∧
      pre.state = next.state := by
  unfold validatorAfterAddress at run
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s1, arg1Run, run⟩ := runCompiledTo_prepend_inv run
  have p1 : refundRecipient.toB256 :: tail <<+ s1.stack := by
    rw [← triggerEmptyAuthorization_arg1 hdata]
    exact prefix_of_arg hp arg1Run
  have wf1 : Mem.Wf s1.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg1Run]; exact hwf
  have reads1 : Mem.Reads s1.memory image := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg1Run]; exact hreads
  obtain ⟨s2, store1Run, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    triggerStoreWord_step p1 wf1 reads1 store1Run
  rw [show ((Trigger.refundRecipientWord * 32 : B256)).toNat = 192 from by
    decide] at reads2
  obtain ⟨s3, arg2Run, run⟩ := runCompiledTo_prepend_inv run
  have p3 : exitType :: tail <<+ s3.stack := by
    rw [← triggerEmptyAuthorization_arg2 hdata]
    exact prefix_of_arg p2 arg2Run
  have wf3 : Mem.Wf s3.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg2Run]; exact wf2
  have reads3 : Mem.Reads s3.memory
      (Bytes.writeAt image 192 refundRecipient.toB256.toBytes) := by
    rw [← Line.of_inv Devm.memory (by line_inv) arg2Run]; exact reads2
  obtain ⟨s4, store2Run, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p4, wf4, reads4, state4⟩ :=
    triggerStoreWord_step p3 wf3 reads3 store2Run
  rw [show ((Trigger.exitTypeWord * 32 : B256)).toNat = 224 from by
    decide] at reads4
  obtain ⟨s5, q5, run⟩ := runCompiledTo_next_inv run
  have r5 := Ninst.Run.of_runCompiled q5
  have p5 := prefix_of_push (of_run_pushB256 r5) p4
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s6, arg0Run, run⟩ := runCompiledTo_prepend_inv run
  have p6 : (0x60 : B256) :: Trigger.maxUint64 :: tail <<+ s6.stack := by
    rw [← triggerEmptyAuthorization_arg0 hdata]
    simpa using prefix_of_arg p5 arg0Run
  obtain ⟨s7, q7, run⟩ := runCompiledTo_next_inv run
  have r7 := Ninst.Run.of_runCompiled q7
  have p7 := prefix_of_gt r7 p6
  have g : (0 : B256) :: tail <<+ s7.stack := by
    simpa [show ((0x60 : B256) >? Trigger.maxUint64) = 0 from by decide]
      using p7
  obtain ⟨next, nextRun, pNext, stateNext, memNext⟩ :=
    trigger_guard_passes g run
  have mem5 : s4.memory = s5.memory := Ninst.Hinv.inv (f := Devm.memory) r5
  have mem6 : s5.memory = s6.memory :=
    Line.of_inv Devm.memory (by line_inv) arg0Run
  have mem7 : s6.memory = s7.memory := Ninst.Hinv.inv (f := Devm.memory) r7
  refine ⟨next, nextRun, pNext, ?_, ?_, ?_⟩
  · rw [← memNext, ← mem7, ← mem6, ← mem5]; exact wf4
  · rw [← memNext, ← mem7, ← mem6, ← mem5]; exact reads4
  · exact ((Line.of_inv Devm.state (by line_inv) arg1Run).trans
      (state2.trans
        ((Line.of_inv Devm.state (by line_inv) arg2Run).trans
          (state4.trans
            ((Ninst.Hinv.inv (f := Devm.state) r5).trans
              ((Line.of_inv Devm.state (by line_inv) arg0Run).trans
                ((Ninst.Hinv.inv (f := Devm.state) r7).trans
                  stateNext)))))))

/-- Guard 4 — the array-length pointer `0x60 + 4 = 100` leaves a whole word
inside the 132-byte image, so the header bound holds with no slack.  Reads
resolve against the banked size word rather than an assumed memory fact. -/
private theorem validator_step_header
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {refundRecipient : Adr} {exitType : B256} {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hsize : Bytes.toB256 (image.sliceD 32 32 0) = Nat.toB256 132)
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterOffset) out) :
    ∃ next image',
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm next
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterHeader) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory image' ∧
      Bytes.toB256 (image'.sliceD 32 32 0) = Nat.toB256 132 ∧
      Bytes.toB256 (image'.sliceD 96 32 0) = Nat.toB256 100 ∧
      pre.state = next.state := by
  unfold validatorAfterOffset at run
  simp only [rebaseLocalCalls_prepend] at run
  -- arg 0, banked as the validators offset
  obtain ⟨s1, argA, run⟩ := runCompiledTo_prepend_inv run
  have p1 : (0x60 : B256) :: tail <<+ s1.stack := by
    rw [← triggerEmptyAuthorization_arg0 hdata]; exact prefix_of_arg hp argA
  have wf1 : Mem.Wf s1.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) argA]; exact hwf
  have reads1 : Mem.Reads s1.memory image := by
    rw [← Line.of_inv Devm.memory (by line_inv) argA]; exact hreads
  obtain ⟨s2, storeA, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    triggerStoreWord_step p1 wf1 reads1 storeA
  rw [show ((Trigger.validatorsOffsetWord * 32 : B256)).toNat = 64 from by
    decide] at reads2
  -- arg 0 again, plus four, banked as the array-length pointer
  obtain ⟨s3, argB, run⟩ := runCompiledTo_prepend_inv run
  have p3 : (0x60 : B256) :: tail <<+ s3.stack := by
    rw [← triggerEmptyAuthorization_arg0 hdata]; exact prefix_of_arg p2 argB
  have wf3 : Mem.Wf s3.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) argB]; exact wf2
  have reads3 : Mem.Reads s3.memory
      (Bytes.writeAt image 64 (0x60 : B256).toBytes) := by
    rw [← Line.of_inv Devm.memory (by line_inv) argB]; exact reads2
  obtain ⟨s4, q4, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s5, q5, run⟩ := runCompiledTo_next_inv run
  have r4 := Ninst.Run.of_runCompiled q4
  have r5 := Ninst.Run.of_runCompiled q5
  have p4 := prefix_of_push (of_run_pushB256 r4) p3
  have p5 : (100 : B256) :: tail <<+ s5.stack := by
    simpa [show ((4 : B256) + 0x60) = 100 from by decide]
      using prefix_of_add r5 p4
  have wf5 : Mem.Wf s5.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← Ninst.Hinv.inv (f := Devm.memory) r4]
    exact wf3
  have reads5 : Mem.Reads s5.memory
      (Bytes.writeAt image 64 (0x60 : B256).toBytes) := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r5,
      ← Ninst.Hinv.inv (f := Devm.memory) r4]
    exact reads3
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s6, storeB, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p6, wf6, reads6, state6⟩ :=
    triggerStoreWord_step p5 wf5 reads5 storeB
  rw [show ((Trigger.arrayLengthPtrWord * 32 : B256)).toNat = 96 from by
    decide] at reads6
  -- the two reads this guard compares
  have hptr : Bytes.toB256
      ((Bytes.writeAt (Bytes.writeAt image 64 (0x60 : B256).toBytes) 96
        (100 : B256).toBytes).sliceD 96 32 0) = 100 :=
    Bytes.readWord_writeAt_self _ 96 100
  have hsize' : Bytes.toB256
      ((Bytes.writeAt (Bytes.writeAt image 64 (0x60 : B256).toBytes) 96
        (100 : B256).toBytes).sliceD 32 32 0) = Nat.toB256 132 := by
    rw [Bytes.readWord_writeAt_of_disjoint _ 32 96 100 (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ 32 64 (0x60 : B256)
        (Or.inl (by omega))]
    exact hsize
  obtain ⟨s7, loadA, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p7, wf7, reads7, state7⟩ :=
    triggerLoadWord_step (value := 100) p6 wf6 reads6
      (by rw [show ((Trigger.arrayLengthPtrWord * 32 : B256)).toNat = 96 from
        by decide]; exact hptr) loadA
  obtain ⟨s8, q8, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s9, q9, run⟩ := runCompiledTo_next_inv run
  have r8 := Ninst.Run.of_runCompiled q8
  have r9 := Ninst.Run.of_runCompiled q9
  have p8 := prefix_of_push (of_run_pushB256 r8) p7
  have p9 : (132 : B256) :: tail <<+ s9.stack := by
    simpa [show ((32 : B256) + 100) = 132 from by decide]
      using prefix_of_add r9 p8
  have wf9 : Mem.Wf s9.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r9,
      ← Ninst.Hinv.inv (f := Devm.memory) r8]
    exact wf7
  have reads9 : Mem.Reads s9.memory
      (Bytes.writeAt (Bytes.writeAt image 64 (0x60 : B256).toBytes) 96
        (100 : B256).toBytes) := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r9,
      ← Ninst.Hinv.inv (f := Devm.memory) r8]
    exact reads7
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s10, loadB, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p10, wf10, reads10, state10⟩ :=
    triggerLoadWord_step (value := Nat.toB256 132) p9 wf9 reads9
      (by rw [show ((Trigger.calldataSizeWord * 32 : B256)).toNat = 32 from
        by decide]; exact hsize') loadB
  obtain ⟨s11, q11, run⟩ := runCompiledTo_next_inv run
  have r11 := Ninst.Run.of_runCompiled q11
  have g : (0 : B256) :: tail <<+ s11.stack := by
    simpa [show ((Nat.toB256 132 : B256) <? 132) = 0 from by decide]
      using prefix_of_lt r11 p10
  obtain ⟨next, nextRun, pNext, stateNext, memNext⟩ :=
    trigger_guard_passes g run
  refine ⟨next,
    Bytes.writeAt (Bytes.writeAt image 64 (0x60 : B256).toBytes) 96
      (100 : B256).toBytes,
    nextRun, pNext, ?_, ?_, hsize', hptr, ?_⟩
  · rw [← memNext, ← Ninst.Hinv.inv (f := Devm.memory) r11]; exact wf10
  · rw [← memNext, ← Ninst.Hinv.inv (f := Devm.memory) r11]; exact reads10
  · exact ((Line.of_inv Devm.state (by line_inv) argA).trans
      (state2.trans ((Line.of_inv Devm.state (by line_inv) argB).trans
        ((Ninst.Hinv.inv (f := Devm.state) r4).trans
          ((Ninst.Hinv.inv (f := Devm.state) r5).trans
            (state6.trans (state7.trans
              ((Ninst.Hinv.inv (f := Devm.state) r8).trans
                ((Ninst.Hinv.inv (f := Devm.state) r9).trans
                  (state10.trans
                    ((Ninst.Hinv.inv (f := Devm.state) r11).trans
                      stateNext)))))))))))

/-- Guard 5 — the canonical image declares an empty validator array, and zero
is trivially within the `uint64` count bound. -/
private theorem validator_step_count
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {refundRecipient : Adr} {exitType : B256} {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hsize : Bytes.toB256 (image.sliceD 32 32 0) = Nat.toB256 132)
    (hptr : Bytes.toB256 (image.sliceD 96 32 0) = Nat.toB256 100)
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterHeader) out) :
    ∃ next image',
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm next
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterCount) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory image' ∧
      Bytes.toB256 (image'.sliceD 32 32 0) = Nat.toB256 132 ∧
      Bytes.toB256 (image'.sliceD 96 32 0) = Nat.toB256 100 ∧
      Bytes.toB256 (image'.sliceD 160 32 0) = 0 ∧
      pre.state = next.state := by
  unfold validatorAfterHeader at run
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s1, clRun, run⟩ := runCompiledTo_prepend_inv run
  unfold Trigger.calldataloadAt at clRun
  rcases of_run_append (Trigger.loadWord Trigger.arrayLengthPtrWord) clRun
    with ⟨m, loadRun, tailRun⟩
  obtain ⟨pm, wfm, readsm, statem⟩ :=
    triggerLoadWord_step (value := Nat.toB256 100) hp hwf hreads
      (by rw [show ((Trigger.arrayLengthPtrWord * 32 : B256)).toNat = 96 from
        by decide]; exact hptr) loadRun
  rcases Line.of_run_cons tailRun with ⟨_, clStep, hnil⟩
  cases hnil
  have p1 : (0 : B256) :: tail <<+ s1.stack := by
    rw [← triggerEmptyAuthorization_arrayLength hdata]
    simpa [show (Nat.toB256 100 : B256) = 100 from by decide]
      using prefix_of_calldataload_val clStep pm
  have wf1 : Mem.Wf s1.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) clStep]; exact wfm
  have reads1 : Mem.Reads s1.memory image := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) clStep]; exact readsm
  obtain ⟨s2, storeRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    triggerStoreWord_step p1 wf1 reads1 storeRun
  rw [show ((Trigger.requestsCountWord * 32 : B256)).toNat = 160 from by
    decide] at reads2
  have hcount : Bytes.toB256
      ((Bytes.writeAt image 160 (0 : B256).toBytes).sliceD 160 32 0) = 0 :=
    Bytes.readWord_writeAt_self _ 160 0
  have hsize' : Bytes.toB256
      ((Bytes.writeAt image 160 (0 : B256).toBytes).sliceD 32 32 0) =
        Nat.toB256 132 := by
    rw [Bytes.readWord_writeAt_of_disjoint _ 32 160 0 (Or.inl (by omega))]
    exact hsize
  have hptr' : Bytes.toB256
      ((Bytes.writeAt image 160 (0 : B256).toBytes).sliceD 96 32 0) =
        Nat.toB256 100 := by
    rw [Bytes.readWord_writeAt_of_disjoint _ 96 160 0 (Or.inl (by omega))]
    exact hptr
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  have r3 := Ninst.Run.of_runCompiled q3
  have p3 := prefix_of_push (of_run_pushB256 r3) p2
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s4, loadRun2, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p4, wf4, reads4, state4⟩ :=
    triggerLoadWord_step (value := 0) p3
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r3]; exact wf2)
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r3]; exact reads2)
      (by rw [show ((Trigger.requestsCountWord * 32 : B256)).toNat = 160 from
        by decide]; exact hcount) loadRun2
  obtain ⟨s5, q5, run⟩ := runCompiledTo_next_inv run
  have r5 := Ninst.Run.of_runCompiled q5
  have g : (0 : B256) :: tail <<+ s5.stack := by
    simpa [show ((0 : B256) >? Trigger.maxUint64) = 0 from by decide]
      using prefix_of_gt r5 p4
  obtain ⟨next, nextRun, pNext, stateNext, memNext⟩ :=
    trigger_guard_passes g run
  refine ⟨next, Bytes.writeAt image 160 (0 : B256).toBytes,
    nextRun, pNext, ?_, ?_, hsize', hptr', hcount, ?_⟩
  · rw [← memNext, ← Ninst.Hinv.inv (f := Devm.memory) r5]; exact wf4
  · rw [← memNext, ← Ninst.Hinv.inv (f := Devm.memory) r5]; exact reads4
  · exact (statem.trans ((Ninst.Hinv.inv (f := Devm.state) clStep).trans
      (state2.trans ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        (state4.trans ((Ninst.Hinv.inv (f := Devm.state) r5).trans
          stateNext))))))

/-- Guard 6 — with an empty array the element region is exactly the end of the
image, so the final bound holds and the validator reaches its continuation. -/
private theorem validator_step_bounds
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hsize : Bytes.toB256 (image.sliceD 32 32 0) = Nat.toB256 132)
    (hptr : Bytes.toB256 (image.sliceD 96 32 0) = Nat.toB256 100)
    (hcount : Bytes.toB256 (image.sliceD 160 32 0) = 0)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterCount) out) :
    ∃ next image',
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm next
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterBounds) out ∧
      tail <<+ next.stack ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory image' ∧
      pre.state = next.state := by
  unfold validatorAfterCount at run
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s1, loadA, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    triggerLoadWord_step (value := Nat.toB256 100) hp hwf hreads
      (by rw [show ((Trigger.arrayLengthPtrWord * 32 : B256)).toNat = 96 from
        by decide]; exact hptr) loadA
  obtain ⟨s2, q2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  have r2 := Ninst.Run.of_runCompiled q2
  have r3 := Ninst.Run.of_runCompiled q3
  have p2 := prefix_of_push (of_run_pushB256 r2) p1
  have p3 : (132 : B256) :: tail <<+ s3.stack := by
    simpa [show ((32 : B256) + Nat.toB256 100) = 132 from by decide]
      using prefix_of_add r3 p2
  have wf3 : Mem.Wf s3.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← Ninst.Hinv.inv (f := Devm.memory) r2]
    exact wf1
  have reads3 : Mem.Reads s3.memory image := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r3,
      ← Ninst.Hinv.inv (f := Devm.memory) r2]
    exact reads1
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s4, storeRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p4, wf4, reads4, state4⟩ :=
    triggerStoreWord_step p3 wf3 reads3 storeRun
  rw [show ((Trigger.arrayElementsBaseWord * 32 : B256)).toNat = 128 from by
    decide] at reads4
  have hbase : Bytes.toB256
      ((Bytes.writeAt image 128 (132 : B256).toBytes).sliceD 128 32 0) = 132 :=
    Bytes.readWord_writeAt_self _ 128 132
  have hcount' : Bytes.toB256
      ((Bytes.writeAt image 128 (132 : B256).toBytes).sliceD 160 32 0) = 0 := by
    rw [Bytes.readWord_writeAt_of_disjoint _ 160 128 132 (Or.inr (by omega))]
    exact hcount
  have hsize' : Bytes.toB256
      ((Bytes.writeAt image 128 (132 : B256).toBytes).sliceD 32 32 0) =
        Nat.toB256 132 := by
    rw [Bytes.readWord_writeAt_of_disjoint _ 32 128 132 (Or.inl (by omega))]
    exact hsize
  obtain ⟨s5, loadB, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p5, wf5, reads5, state5⟩ :=
    triggerLoadWord_step (value := 132) p4 wf4 reads4
      (by rw [show ((Trigger.arrayElementsBaseWord * 32 : B256)).toNat = 128
        from by decide]; exact hbase) loadB
  obtain ⟨s6, loadC, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p6, wf6, reads6, state6⟩ :=
    triggerLoadWord_step (value := 0) p5 wf5 reads5
      (by rw [show ((Trigger.requestsCountWord * 32 : B256)).toNat = 160 from
        by decide]; exact hcount') loadC
  obtain ⟨s7, q7, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s8, q8, run⟩ := runCompiledTo_next_inv run
  obtain ⟨s9, q9, run⟩ := runCompiledTo_next_inv run
  have r7 := Ninst.Run.of_runCompiled q7
  have r8 := Ninst.Run.of_runCompiled q8
  have r9 := Ninst.Run.of_runCompiled q9
  have p7 := prefix_of_push (of_run_pushB256 r7) p6
  have p8 : (0 : B256) :: (132 : B256) :: tail <<+ s8.stack := by
    simpa [show ((32 : B256) * 0) = 0 from by decide]
      using prefix_of_mul r8 p7
  have p9 : (132 : B256) :: tail <<+ s9.stack := by
    simpa [show ((0 : B256) + 132) = 132 from by decide]
      using prefix_of_add r9 p8
  have wf9 : Mem.Wf s9.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r9,
      ← Ninst.Hinv.inv (f := Devm.memory) r8,
      ← Ninst.Hinv.inv (f := Devm.memory) r7]
    exact wf6
  have reads9 : Mem.Reads s9.memory
      (Bytes.writeAt image 128 (132 : B256).toBytes) := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) r9,
      ← Ninst.Hinv.inv (f := Devm.memory) r8,
      ← Ninst.Hinv.inv (f := Devm.memory) r7]
    exact reads6
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s10, loadD, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p10, wf10, reads10, state10⟩ :=
    triggerLoadWord_step (value := Nat.toB256 132) p9 wf9 reads9
      (by rw [show ((Trigger.calldataSizeWord * 32 : B256)).toNat = 32 from
        by decide]; exact hsize') loadD
  obtain ⟨s11, q11, run⟩ := runCompiledTo_next_inv run
  have r11 := Ninst.Run.of_runCompiled q11
  have g : (0 : B256) :: tail <<+ s11.stack := by
    simpa [show ((Nat.toB256 132 : B256) <? 132) = 0 from by decide]
      using prefix_of_lt r11 p10
  obtain ⟨next, nextRun, pNext, stateNext, memNext⟩ :=
    trigger_guard_passes g run
  refine ⟨next, Bytes.writeAt image 128 (132 : B256).toBytes,
    nextRun, pNext, ?_, ?_, ?_⟩
  · rw [← memNext, ← Ninst.Hinv.inv (f := Devm.memory) r11]; exact wf10
  · rw [← memNext, ← Ninst.Hinv.inv (f := Devm.memory) r11]; exact reads10
  · exact (state1.trans ((Ninst.Hinv.inv (f := Devm.state) r2).trans
      ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        (state4.trans (state5.trans (state6.trans
          ((Ninst.Hinv.inv (f := Devm.state) r7).trans
            ((Ninst.Hinv.inv (f := Devm.state) r8).trans
              ((Ninst.Hinv.inv (f := Devm.state) r9).trans
                (state10.trans ((Ninst.Hinv.inv (f := Devm.state) r11).trans
                  stateNext)))))))))))

/-- Guard 7 has no test: the loop counters are zeroed and control transfers to
`afterValidation`, whose slot is the rebased one the runtime actually holds. -/
private theorem validator_step_enter
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.rebaseLocalCalls triggerAuxDelta validatorAfterBounds) out) :
    ∃ next,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm next
        (Trigger.rebaseLocalCalls triggerAuxDelta Trigger.afterValidation)
        out ∧
      tail <<+ next.stack ∧
      pre.state = next.state := by
  unfold validatorAfterBounds at run
  obtain ⟨s1, q1, run⟩ := runCompiledTo_next_inv run
  have r1 := Ninst.Run.of_runCompiled q1
  have p1 := prefix_of_push (of_run_pushB256 r1) hp
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s2, storeA, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    triggerStoreWord_step p1
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r1]; exact hwf)
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r1]; exact hreads) storeA
  obtain ⟨s3, q3, run⟩ := runCompiledTo_next_inv run
  have r3 := Ninst.Run.of_runCompiled q3
  have p3 := prefix_of_push (of_run_pushB256 r3) p2
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s4, storeB, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p4, wf4, reads4, state4⟩ :=
    triggerStoreWord_step p3
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r3]; exact wf2)
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r3]; exact reads2) storeB
  obtain ⟨s5, q5, run⟩ := runCompiledTo_next_inv run
  have r5 := Ninst.Run.of_runCompiled q5
  have p5 := prefix_of_push (of_run_pushB256 r5) p4
  simp only [rebaseLocalCalls_prepend] at run
  obtain ⟨s6, storeC, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p6, wf6, reads6, state6⟩ :=
    triggerStoreWord_step p5
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r5]; exact wf4)
      (by rw [← Ninst.Hinv.inv (f := Devm.memory) r5]; exact reads4) storeC
  obtain ⟨next, burn, bodyRun⟩ :=
    runCompiledTo_call_inv (runtime_rebasedTriggerAfterValidation_get dp) run
  refine ⟨next, bodyRun, ?_, ?_⟩
  · rw [← burn.stack]; exact p6
  · exact ((Ninst.Hinv.inv (f := Devm.state) r1).trans
      (state2.trans ((Ninst.Hinv.inv (f := Devm.state) r3).trans
        (state4.trans ((Ninst.Hinv.inv (f := Devm.state) r5).trans
          (state6.trans burn.state))))))

/-! ## The canonical trigger input reaches `afterValidation` -/

/-- The smallest complete canonical trigger input clears every validator guard
and transfers to `Trigger.afterValidation`.  Storage is untouched along the
way, so a role or pause fact stated at the entry survives to the guard.  The
walk assumes nothing about the entry memory beyond well-formedness: the
validator stores each scratch word before it reads it. -/
theorem triggerFullWithdrawals_reaches_afterValidation
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {refundRecipient : Adr} {exitType : B256} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hmem : pre.memory = Mem.empty)
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre (triggerFullWithdrawals dp) out) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm bodyPre
        (Trigger.rebaseLocalCalls triggerAuxDelta Trigger.afterValidation)
        out ∧
      tail <<+ bodyPre.stack ∧
      pre.state = bodyPre.state := by
  rw [triggerFullWithdrawals_rebasedValidator_exact] at run
  obtain ⟨n1, run1, p1, state1, mem1⟩ := validator_step_size hp hdata run
  have wf1 : Mem.Wf n1.memory := by rw [← mem1, hmem]; exact Mem.wf_empty
  have reads1 : Mem.Reads n1.memory [] := by
    rw [← mem1, hmem]; exact Mem.reads_empty
  obtain ⟨n2, run2, p2, wf2, reads2, state2⟩ :=
    validator_step_address p1 wf1 reads1 hdata run1
  obtain ⟨n3, run3, p3, wf3, reads3, state3⟩ :=
    validator_step_offset p2 wf2 reads2 hdata run2
  have hsize : Bytes.toB256
      ((Bytes.writeAt
        (Bytes.writeAt (Bytes.writeAt [] 32 (Nat.toB256 132).toBytes) 192
          refundRecipient.toB256.toBytes) 224 exitType.toBytes).sliceD
        32 32 0) = Nat.toB256 132 := by
    rw [Bytes.readWord_writeAt_of_disjoint _ 32 224 exitType
        (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ 32 192 refundRecipient.toB256
        (Or.inl (by omega))]
    exact Bytes.readWord_writeAt_self _ 32 (Nat.toB256 132)
  obtain ⟨n4, image4, run4, p4, wf4, reads4, hsize4, hptr4, state4⟩ :=
    validator_step_header p3 wf3 reads3 hsize hdata run3
  obtain ⟨n5, image5, run5, p5, wf5, reads5, hsize5, hptr5, hcount5, state5⟩ :=
    validator_step_count p4 wf4 reads4 hsize4 hptr4 hdata run4
  obtain ⟨n6, image6, run6, p6, wf6, reads6, state6⟩ :=
    validator_step_bounds p5 wf5 reads5 hsize5 hptr5 hcount5 run5
  obtain ⟨n7, run7, p7, state7⟩ := validator_step_enter p6 wf6 reads6 run6
  exact ⟨n7, run7, p7,
    state1.trans (state2.trans (state3.trans (state4.trans
      (state5.trans (state6.trans state7)))))⟩

/-! ## Exact flat-role classification -/

/-- The two semantic destinations of the trigger's role guard.  All three
failed record checks use the same rebased AccessControl boundary. -/
inductive TriggerFlatRoleRoute
    (dp : DeployParams) (sevm : Sevm) (pre : Devm)
    (onAuthorized : Func) (tail : Stack) (out : Execution) : Prop
  | authorized (bodyPre : Devm)
      (hasRole : CallerHasRole (Devm.getStor pre sevm.currentTarget)
        addFullWithdrawalRequestRole sevm.caller.toB256)
      (bodyRun : Func.RunCompiledTo
        ((runtime dp).main :: (runtime dp).aux) sevm bodyPre onAuthorized out)
      (stack : tail <<+ bodyPre.stack)
      (storage : Devm.getStor pre = Devm.getStor bodyPre)
      (balance : pre.getBal sevm.currentTarget =
        bodyPre.getBal sevm.currentTarget)
  | roleFailure (callPre : Devm)
      (lacksRole : ¬ CallerHasRole (Devm.getStor pre sevm.currentTarget)
        addFullWithdrawalRequestRole sevm.caller.toB256)
      (callRun : Func.RunCompiledTo
        ((runtime dp).main :: (runtime dp).aux) sevm callPre
          (.call rebasedTriggerRoleFailureSlot) out)
      (stack : tail <<+ callPre.stack)
      (storage : Devm.getStor pre = Devm.getStor callPre)
      (balance : pre.getBal sevm.currentTarget =
        callPre.getBal sevm.currentTarget)

private theorem triggerRoleKeyWord_eq (account : B256) (region : Nat) :
    regionWord region |||
        (low252Mask &&& ((addressMask &&& account) ^^^
          addFullWithdrawalRequestRole)) =
      taggedSlot region
        (roleLookupPayload addFullWithdrawalRequestRole account) := by
  rw [B256.and_comm addressMask account,
    B256.xor_comm (account &&& addressMask)
      addFullWithdrawalRequestRole,
    B256.and_comm low252Mask
      (addFullWithdrawalRequestRole ^^^ (account &&& addressMask)),
    ← B256.and_idem_right
      (addFullWithdrawalRequestRole ^^^ (account &&& addressMask))
      low252Mask]
  rfl

private lemma prefix_of_triggerRoleKeyForCaller
    {sevm : Sevm} {pre post : Devm} {tail : Stack} (region : Nat)
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre (Trigger.roleKeyForCaller region) post) :
    taggedSlot region
        (roleLookupPayload addFullWithdrawalRequestRole sevm.caller.toB256) ::
      tail <<+ post.stack := by
  unfold Trigger.roleKeyForCaller at run
  rcases Line.of_run_cons run with ⟨s1, qrole, run⟩
  rcases Line.of_run_cons run with ⟨s2, qcaller, run⟩
  rcases Line.of_run_cons run with ⟨s3, qmask, run⟩
  rcases Line.of_run_cons run with ⟨s4, qand1, run⟩
  rcases Line.of_run_cons run with ⟨s5, qxor, run⟩
  rcases Line.of_run_cons run with ⟨s6, qlow, run⟩
  rcases Line.of_run_cons run with ⟨s7, qand2, run⟩
  rcases Line.of_run_cons run with ⟨s8, qregion, run⟩
  rcases Line.of_run_cons run with ⟨_, qor, hnil⟩
  cases hnil
  have p1 := prefix_of_push (of_run_pushB256 qrole) hp
  have p2 := prefix_of_push (of_run_caller qcaller) p1
  have p3 := prefix_of_push (of_run_pushB256 qmask) p2
  have p4 := prefix_of_and qand1 p3
  have p5 := prefix_of_xor qxor p4
  have p6 := prefix_of_push (of_run_pushB256 qlow) p5
  have p7 := prefix_of_and qand2 p6
  have p8 := prefix_of_push (of_run_pushB256 qregion) p7
  have p9 := prefix_of_or qor p8
  simpa [triggerRoleKeyWord_eq] using p9

/-- Exact arbitrary-outcome traversal of the trigger's concrete flat role
guard.  This is deliberately separate from `onlyRole_route`: every failed
check here reaches one shared role-error continuation. -/
theorem triggerCoreFlatRoleGuard_route
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {onAuthorized : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.coreFlatRoleGuard (.call rebasedTriggerRoleFailureSlot)
          onAuthorized) out) :
    TriggerFlatRoleRoute dp sevm pre onAuthorized tail out := by
  unfold Trigger.coreFlatRoleGuard at run
  obtain ⟨indexLoadPre, indexKeyRun, run⟩ :=
    runCompiledTo_prepend_inv run
  have pIndexKey0 := prefix_of_triggerRoleKeyForCaller
    roleLookupIndexRegion hp indexKeyRun
  have pIndexKey :
      roleLookupIndexSlot addFullWithdrawalRequestRole sevm.caller.toB256 ::
        tail <<+ indexLoadPre.stack := by
    simpa [roleLookupIndexSlot] using pIndexKey0
  obtain ⟨indexLoadPost, qindexLoad, run⟩ :=
    runCompiledTo_next_inv run
  obtain ⟨indexTest, qindexZero, indexBranch⟩ :=
    runCompiledTo_next_inv run
  have rindexLoad := Ninst.Run.of_runCompiled qindexLoad
  have rindexZero := Ninst.Run.of_runCompiled qindexZero
  obtain ⟨indexValue, pIndexValue, hIndexValue⟩ :=
    prefix_of_sload rindexLoad pIndexKey
  have pIndexTest := prefix_of_iszero rindexZero pIndexValue
  have indexKeyStor : Devm.getStor pre = Devm.getStor indexLoadPre :=
    Line.of_inv Devm.getStor (by line_inv) indexKeyRun
  have indexKeyBal : pre.getBal sevm.currentTarget =
      indexLoadPre.getBal sevm.currentTarget :=
    Line.of_inv (fun d => d.getBal sevm.currentTarget) (by line_inv)
      indexKeyRun
  have hIndexAtEntry : indexValue =
      pre.getStorVal sevm.currentTarget
        (roleLookupIndexSlot addFullWithdrawalRequestRole
          sevm.caller.toB256) := by
    rw [hIndexValue]
    exact congrArg
      (fun s : Stor =>
        s.get (roleLookupIndexSlot addFullWithdrawalRequestRole
          sevm.caller.toB256))
      (congrFun indexKeyStor sevm.currentTarget).symm
  by_cases hindexZero : indexValue = 0
  · have pIndexOne : (1 : B256) :: tail <<+ indexTest.stack := by
      simpa [hindexZero, B256.eqCheck] using pIndexTest
    obtain ⟨callPre, _, -, hpop, callRun, pCall⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) pIndexOne indexBranch
    have callStor : Devm.getStor pre = Devm.getStor callPre :=
      indexKeyStor.trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rindexLoad).trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rindexZero).trans
            (funext (getStor_eq_of_state_eq hpop.state))))
    have callBal : pre.getBal sevm.currentTarget =
        callPre.getBal sevm.currentTarget :=
      indexKeyBal.trans
        ((Ninst.Hinv.inv
          (f := fun d => d.getBal sevm.currentTarget) rindexLoad).trans
          ((Ninst.Hinv.inv
            (f := fun d => d.getBal sevm.currentTarget) rindexZero).trans
            (getBal_eq_of_state_eq hpop.state sevm.currentTarget)))
    have entryIndexZero : pre.getStorVal sevm.currentTarget
        (roleLookupIndexSlot addFullWithdrawalRequestRole
          sevm.caller.toB256) = 0 :=
      hIndexAtEntry.symm.trans hindexZero
    have lacksRole : ¬ CallerHasRole
        (Devm.getStor pre sevm.currentTarget)
        addFullWithdrawalRequestRole sevm.caller.toB256 := by
      intro hasRole
      exact hasRole.1 entryIndexZero
    exact .roleFailure callPre lacksRole callRun pCall callStor callBal
  · have pIndexZero : (0 : B256) :: tail <<+ indexTest.stack := by
      simpa [B256.eqCheck, hindexZero] using pIndexTest
    obtain ⟨roleKeyPre, hindexPop, roleRun, pRole⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix pIndexZero indexBranch
    have entryIndexNonzero : pre.getStorVal sevm.currentTarget
        (roleLookupIndexSlot addFullWithdrawalRequestRole
          sevm.caller.toB256) ≠ 0 := by
      simpa [hIndexAtEntry] using hindexZero
    have roleKeyStor : Devm.getStor pre = Devm.getStor roleKeyPre :=
      indexKeyStor.trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rindexLoad).trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rindexZero).trans
            (funext (getStor_eq_of_state_eq hindexPop.state))))
    have roleKeyBal : pre.getBal sevm.currentTarget =
        roleKeyPre.getBal sevm.currentTarget :=
      indexKeyBal.trans
        ((Ninst.Hinv.inv
          (f := fun d => d.getBal sevm.currentTarget) rindexLoad).trans
          ((Ninst.Hinv.inv
            (f := fun d => d.getBal sevm.currentTarget) rindexZero).trans
            (getBal_eq_of_state_eq hindexPop.state sevm.currentTarget)))

    obtain ⟨roleLoadPre, roleKeyRun, roleRun⟩ :=
      runCompiledTo_prepend_inv roleRun
    have pRoleKey0 := prefix_of_triggerRoleKeyForCaller
      roleLookupRoleRegion pRole roleKeyRun
    have pRoleKey :
        roleLookupRoleSlot addFullWithdrawalRequestRole sevm.caller.toB256 ::
          tail <<+ roleLoadPre.stack := by
      simpa [roleLookupRoleSlot] using pRoleKey0
    obtain ⟨roleLoadPost, qroleLoad, roleRun⟩ :=
      runCompiledTo_next_inv roleRun
    obtain ⟨rolePushPost, qrolePush, roleRun⟩ :=
      runCompiledTo_next_inv roleRun
    obtain ⟨roleTest, qroleEq, roleBranch⟩ :=
      runCompiledTo_next_inv roleRun
    have rroleLoad := Ninst.Run.of_runCompiled qroleLoad
    have rrolePush := Ninst.Run.of_runCompiled qrolePush
    have rroleEq := Ninst.Run.of_runCompiled qroleEq
    obtain ⟨storedRole, pStoredRole, hStoredRole⟩ :=
      prefix_of_sload rroleLoad pRoleKey
    have pRolePush :=
      prefix_of_push (of_run_pushB256 rrolePush) pStoredRole
    have pRoleTest := prefix_of_eq rroleEq pRolePush
    have roleLoadStor : Devm.getStor pre = Devm.getStor roleLoadPre :=
      roleKeyStor.trans (Line.of_inv Devm.getStor (by line_inv) roleKeyRun)
    have roleLoadBal : pre.getBal sevm.currentTarget =
        roleLoadPre.getBal sevm.currentTarget :=
      roleKeyBal.trans
        (Line.of_inv (fun d => d.getBal sevm.currentTarget) (by line_inv)
          roleKeyRun)
    have hStoredRoleAtEntry : storedRole =
        pre.getStorVal sevm.currentTarget
          (roleLookupRoleSlot addFullWithdrawalRequestRole
            sevm.caller.toB256) := by
      rw [hStoredRole]
      exact congrArg
        (fun s : Stor =>
          s.get (roleLookupRoleSlot addFullWithdrawalRequestRole
            sevm.caller.toB256))
        (congrFun roleLoadStor sevm.currentTarget).symm
    by_cases hroleMatch : storedRole = addFullWithdrawalRequestRole
    · have pRoleOne : (1 : B256) :: tail <<+ roleTest.stack := by
        simpa [hroleMatch, B256.eqCheck] using pRoleTest
      obtain ⟨accountKeyPre, _, -, hrolePop, accountRun, pAccount⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) pRoleOne roleBranch
      have entryRoleMatch : pre.getStorVal sevm.currentTarget
          (roleLookupRoleSlot addFullWithdrawalRequestRole
            sevm.caller.toB256) = addFullWithdrawalRequestRole :=
        hStoredRoleAtEntry.symm.trans hroleMatch
      have accountKeyStor : Devm.getStor pre = Devm.getStor accountKeyPre :=
        roleLoadStor.trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rroleLoad).trans
            ((Ninst.Hinv.inv (f := Devm.getStor) rrolePush).trans
              ((Ninst.Hinv.inv (f := Devm.getStor) rroleEq).trans
                (funext (getStor_eq_of_state_eq hrolePop.state)))))
      have accountKeyBal : pre.getBal sevm.currentTarget =
          accountKeyPre.getBal sevm.currentTarget :=
        roleLoadBal.trans
          ((Ninst.Hinv.inv
            (f := fun d => d.getBal sevm.currentTarget) rroleLoad).trans
            ((Ninst.Hinv.inv
              (f := fun d => d.getBal sevm.currentTarget) rrolePush).trans
              ((Ninst.Hinv.inv
                (f := fun d => d.getBal sevm.currentTarget) rroleEq).trans
                (getBal_eq_of_state_eq hrolePop.state
                  sevm.currentTarget))))

      obtain ⟨accountLoadPre, accountKeyRun, accountRun⟩ :=
        runCompiledTo_prepend_inv accountRun
      have pAccountKey0 := prefix_of_triggerRoleKeyForCaller
        roleLookupAccountRegion pAccount accountKeyRun
      have pAccountKey :
          roleLookupAccountSlot addFullWithdrawalRequestRole
              sevm.caller.toB256 :: tail <<+ accountLoadPre.stack := by
        simpa [roleLookupAccountSlot] using pAccountKey0
      obtain ⟨accountLoadPost, qaccountLoad, accountRun⟩ :=
        runCompiledTo_next_inv accountRun
      obtain ⟨accountCallerPost, qaccountCaller, accountRun⟩ :=
        runCompiledTo_next_inv accountRun
      obtain ⟨accountMaskPost, qaccountMask, accountRun⟩ :=
        runCompiledTo_next_inv accountRun
      obtain ⟨accountCanonicalPost, qaccountAnd, accountRun⟩ :=
        runCompiledTo_next_inv accountRun
      obtain ⟨accountTest, qaccountEq, accountBranch⟩ :=
        runCompiledTo_next_inv accountRun
      have raccountLoad := Ninst.Run.of_runCompiled qaccountLoad
      have raccountCaller := Ninst.Run.of_runCompiled qaccountCaller
      have raccountMask := Ninst.Run.of_runCompiled qaccountMask
      have raccountAnd := Ninst.Run.of_runCompiled qaccountAnd
      have raccountEq := Ninst.Run.of_runCompiled qaccountEq
      obtain ⟨storedAccount, pStoredAccount, hStoredAccount⟩ :=
        prefix_of_sload raccountLoad pAccountKey
      have pAccountCaller :=
        prefix_of_push (of_run_caller raccountCaller) pStoredAccount
      have pAccountMask :=
        prefix_of_push (of_run_pushB256 raccountMask) pAccountCaller
      have pCanonical0 := prefix_of_and raccountAnd pAccountMask
      have pCanonical : canonicalAccount sevm.caller.toB256 ::
          storedAccount :: tail <<+ accountCanonicalPost.stack := by
        have hcomm : canonicalAccount sevm.caller.toB256 =
            addressMask &&& sevm.caller.toB256 :=
          B256.and_comm sevm.caller.toB256 addressMask
        rw [hcomm]
        exact pCanonical0
      have pAccountTest := prefix_of_eq raccountEq pCanonical
      have accountLoadStor : Devm.getStor pre = Devm.getStor accountLoadPre :=
        accountKeyStor.trans
          (Line.of_inv Devm.getStor (by line_inv) accountKeyRun)
      have accountLoadBal : pre.getBal sevm.currentTarget =
          accountLoadPre.getBal sevm.currentTarget :=
        accountKeyBal.trans
          (Line.of_inv (fun d => d.getBal sevm.currentTarget) (by line_inv)
            accountKeyRun)
      have hStoredAccountAtEntry : storedAccount =
          pre.getStorVal sevm.currentTarget
            (roleLookupAccountSlot addFullWithdrawalRequestRole
              sevm.caller.toB256) := by
        rw [hStoredAccount]
        exact congrArg
          (fun s : Stor =>
            s.get (roleLookupAccountSlot addFullWithdrawalRequestRole
              sevm.caller.toB256))
          (congrFun accountLoadStor sevm.currentTarget).symm
      by_cases haccountMatch :
          storedAccount = canonicalAccount sevm.caller.toB256
      · have pAccountOne : (1 : B256) :: tail <<+ accountTest.stack := by
          simpa [haccountMatch, B256.eqCheck] using pAccountTest
        obtain ⟨bodyPre, _, -, haccountPop, bodyRun, pBody⟩ :=
          Func.RunCompiledTo.succ_branch_of_prefix
            (by decide : (1 : B256) ≠ 0) pAccountOne accountBranch
        have entryAccountMatch : pre.getStorVal sevm.currentTarget
            (roleLookupAccountSlot addFullWithdrawalRequestRole
              sevm.caller.toB256) = canonicalAccount sevm.caller.toB256 :=
          hStoredAccountAtEntry.symm.trans haccountMatch
        have bodyStor : Devm.getStor pre = Devm.getStor bodyPre :=
          accountLoadStor.trans
            ((Ninst.Hinv.inv (f := Devm.getStor) raccountLoad).trans
              ((Ninst.Hinv.inv (f := Devm.getStor) raccountCaller).trans
                ((Ninst.Hinv.inv (f := Devm.getStor) raccountMask).trans
                  ((Ninst.Hinv.inv (f := Devm.getStor) raccountAnd).trans
                    ((Ninst.Hinv.inv (f := Devm.getStor) raccountEq).trans
                      (funext
                        (getStor_eq_of_state_eq haccountPop.state)))))))
        have bodyBal : pre.getBal sevm.currentTarget =
            bodyPre.getBal sevm.currentTarget :=
          accountLoadBal.trans
            ((Ninst.Hinv.inv
              (f := fun d => d.getBal sevm.currentTarget)
                raccountLoad).trans
              ((Ninst.Hinv.inv
                (f := fun d => d.getBal sevm.currentTarget)
                  raccountCaller).trans
                ((Ninst.Hinv.inv
                  (f := fun d => d.getBal sevm.currentTarget)
                    raccountMask).trans
                  ((Ninst.Hinv.inv
                    (f := fun d => d.getBal sevm.currentTarget)
                      raccountAnd).trans
                    ((Ninst.Hinv.inv
                      (f := fun d => d.getBal sevm.currentTarget)
                        raccountEq).trans
                      (getBal_eq_of_state_eq haccountPop.state
                        sevm.currentTarget))))))
        have hasRole : CallerHasRole
            (Devm.getStor pre sevm.currentTarget)
            addFullWithdrawalRequestRole sevm.caller.toB256 :=
          callerHasRole_exact_lookup entryRoleMatch entryAccountMatch
            entryIndexNonzero
        exact .authorized bodyPre hasRole bodyRun pBody bodyStor bodyBal
      · have pAccountZero : (0 : B256) :: tail <<+ accountTest.stack := by
          simpa [B256.eqCheck, Ne.symm haccountMatch] using pAccountTest
        obtain ⟨callPre, haccountPop, callRun, pCall⟩ :=
          Func.RunCompiledTo.zero_branch_of_prefix pAccountZero accountBranch
        have entryAccountMismatch : pre.getStorVal sevm.currentTarget
            (roleLookupAccountSlot addFullWithdrawalRequestRole
              sevm.caller.toB256) ≠ canonicalAccount sevm.caller.toB256 := by
          intro hentry
          exact haccountMatch (hStoredAccountAtEntry.trans hentry)
        have callStor : Devm.getStor pre = Devm.getStor callPre :=
          accountLoadStor.trans
            ((Ninst.Hinv.inv (f := Devm.getStor) raccountLoad).trans
              ((Ninst.Hinv.inv (f := Devm.getStor) raccountCaller).trans
                ((Ninst.Hinv.inv (f := Devm.getStor) raccountMask).trans
                  ((Ninst.Hinv.inv (f := Devm.getStor) raccountAnd).trans
                    ((Ninst.Hinv.inv (f := Devm.getStor) raccountEq).trans
                      (funext
                        (getStor_eq_of_state_eq haccountPop.state)))))))
        have callBal : pre.getBal sevm.currentTarget =
            callPre.getBal sevm.currentTarget :=
          accountLoadBal.trans
            ((Ninst.Hinv.inv
              (f := fun d => d.getBal sevm.currentTarget)
                raccountLoad).trans
              ((Ninst.Hinv.inv
                (f := fun d => d.getBal sevm.currentTarget)
                  raccountCaller).trans
                ((Ninst.Hinv.inv
                  (f := fun d => d.getBal sevm.currentTarget)
                    raccountMask).trans
                  ((Ninst.Hinv.inv
                    (f := fun d => d.getBal sevm.currentTarget)
                      raccountAnd).trans
                    ((Ninst.Hinv.inv
                      (f := fun d => d.getBal sevm.currentTarget)
                        raccountEq).trans
                      (getBal_eq_of_state_eq haccountPop.state
                        sevm.currentTarget))))))
        have lacksRole : ¬ CallerHasRole
            (Devm.getStor pre sevm.currentTarget)
            addFullWithdrawalRequestRole sevm.caller.toB256 := by
          intro hasRole
          exact entryAccountMismatch hasRole.2.2
        exact .roleFailure callPre lacksRole callRun pCall callStor callBal
    · have pRoleZero : (0 : B256) :: tail <<+ roleTest.stack := by
        simpa [B256.eqCheck, Ne.symm hroleMatch] using pRoleTest
      obtain ⟨callPre, hrolePop, callRun, pCall⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix pRoleZero roleBranch
      have entryRoleMismatch : pre.getStorVal sevm.currentTarget
          (roleLookupRoleSlot addFullWithdrawalRequestRole
            sevm.caller.toB256) ≠ addFullWithdrawalRequestRole := by
        intro hentry
        exact hroleMatch (hStoredRoleAtEntry.trans hentry)
      have callStor : Devm.getStor pre = Devm.getStor callPre :=
        roleLoadStor.trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rroleLoad).trans
            ((Ninst.Hinv.inv (f := Devm.getStor) rrolePush).trans
              ((Ninst.Hinv.inv (f := Devm.getStor) rroleEq).trans
                (funext (getStor_eq_of_state_eq hrolePop.state)))))
      have callBal : pre.getBal sevm.currentTarget =
          callPre.getBal sevm.currentTarget :=
        roleLoadBal.trans
          ((Ninst.Hinv.inv
            (f := fun d => d.getBal sevm.currentTarget) rroleLoad).trans
            ((Ninst.Hinv.inv
              (f := fun d => d.getBal sevm.currentTarget) rrolePush).trans
              ((Ninst.Hinv.inv
                (f := fun d => d.getBal sevm.currentTarget) rroleEq).trans
                (getBal_eq_of_state_eq hrolePop.state
                  sevm.currentTarget))))
      have lacksRole : ¬ CallerHasRole
          (Devm.getStor pre sevm.currentTarget)
          addFullWithdrawalRequestRole sevm.caller.toB256 := by
        intro hasRole
        exact entryRoleMismatch hasRole.2.1
      exact .roleFailure callPre lacksRole callRun pCall callStor callBal

/-- An absent trigger role eliminates the authorized constructor and leaves
the exact rebased AccessControl failure payload. -/
theorem triggerCoreFlatRoleGuard_absent_reverts
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {onAuthorized : Func} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (absent : ¬ CallerHasRole (Devm.getStor pre sevm.currentTarget)
      addFullWithdrawalRequestRole sevm.caller.toB256)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.coreFlatRoleGuard (.call rebasedTriggerRoleFailureSlot)
          onAuthorized) out) :
    TriggerRoleFailure out := by
  rcases triggerCoreFlatRoleGuard_route hp run with
    ⟨bodyPre, hasRole, bodyRun, stack, storage, balance⟩ |
    ⟨callPre, lacksRole, callRun, stack, storage, balance⟩
  · exact (absent hasRole).elim
  · exact rebasedTriggerRoleFailure_call_reverts_exact callRun

theorem triggerAfterValidation_absent_reverts
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack}
    (hp : tail <<+ pre.stack)
    (absent : ¬ CallerHasRole (Devm.getStor pre sevm.currentTarget)
      addFullWithdrawalRequestRole sevm.caller.toB256)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.rebaseLocalCalls triggerAuxDelta Trigger.afterValidation)
        out) :
    TriggerRoleFailure out := by
  rw [rebasedTriggerAfterValidation_exact] at run
  exact triggerCoreFlatRoleGuard_absent_reverts hp absent run

/-! ## Authorized continuation reaches the paused failure first -/

/-- Once authorization has selected the continuation, a safe entry balance and
the live paused projection force the rebased `ResumedExpected()` call before
the value, nonempty-array, or quota checks. -/
theorem triggerAuthorizedContinuation_paused_route
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hbalance : B256.ltCheck (pre.getBal sevm.currentTarget) sevm.value = 0)
    (hpaused : B256.ltCheck sevm.benvStat.time
      (pre.getStorVal sevm.currentTarget resumeSinceSlot) ≠ 0)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre rebasedTriggerAuthorizedContinuation out) :
    ∃ callPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm callPre (.call rebasedTriggerResumedExpectedSlot) out ∧
      tail <<+ callPre.stack ∧
      Devm.getStor pre = Devm.getStor callPre := by
  unfold rebasedTriggerAuthorizedContinuation Trigger.rebaseLocalCalls at run
  obtain ⟨callvaluePost, qcallvalue, run⟩ := runCompiledTo_next_inv run
  obtain ⟨balancePost, qbalance, run⟩ := runCompiledTo_next_inv run
  obtain ⟨balanceTest, qlt, balanceBranch⟩ := runCompiledTo_next_inv run
  have rcallvalue := Ninst.Run.of_runCompiled qcallvalue
  have rbalance := Ninst.Run.of_runCompiled qbalance
  have rlt := Ninst.Run.of_runCompiled qlt
  have pCallvalue := prefix_of_push (of_run_callvalue rcallvalue) hp
  have pBalance0 := prefix_of_push (of_run_selfbalance rbalance) pCallvalue
  have balancePreserved : pre.getBal sevm.currentTarget =
      callvaluePost.getBal sevm.currentTarget := by
    exact Ninst.Hinv.inv (f := fun d => d.getBal sevm.currentTarget) rcallvalue
  have pBalance : pre.getBal sevm.currentTarget :: sevm.value :: tail <<+
      balancePost.stack := by
    simpa [← balancePreserved] using pBalance0
  have pBalanceTest := prefix_of_lt rlt pBalance
  have pBalanceZero : (0 : B256) :: tail <<+ balanceTest.stack := by
    simpa [hbalance] using pBalanceTest
  obtain ⟨afterBalance, hbalancePop, run, pAfterBalance⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix pBalanceZero balanceBranch
  have afterBalanceStor : Devm.getStor pre = Devm.getStor afterBalance :=
    (Ninst.Hinv.inv (f := Devm.getStor) rcallvalue).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) rbalance).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rlt).trans
          (funext (getStor_eq_of_state_eq hbalancePop.state))))

  obtain ⟨callvalue2Post, qcallvalue2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨balance2Post, qbalance2, run⟩ := runCompiledTo_next_inv run
  obtain ⟨differencePost, qsub, run⟩ := runCompiledTo_next_inv run
  rw [rebaseLocalCalls_prepend] at run
  obtain ⟨afterStore, storeRun, run⟩ := runCompiledTo_prepend_inv run
  have rcallvalue2 := Ninst.Run.of_runCompiled qcallvalue2
  have rbalance2 := Ninst.Run.of_runCompiled qbalance2
  have rsub := Ninst.Run.of_runCompiled qsub
  have pCallvalue2 :=
    prefix_of_push (of_run_callvalue rcallvalue2) pAfterBalance
  have pBalance2 :=
    prefix_of_push (of_run_selfbalance rbalance2) pCallvalue2
  have pDifference := prefix_of_sub rsub pBalance2
  have storeWordRun : Line.Run sevm differencePost
      (mstoreAt Trigger.balanceBeforeWord) afterStore := by
    simpa [Trigger.storeWord] using storeRun
  have pAfterStore := prefix_of_mstoreAt storeWordRun pDifference
  have storeStor : Devm.getStor afterBalance = Devm.getStor afterStore :=
    (Ninst.Hinv.inv (f := Devm.getStor) rcallvalue2).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) rbalance2).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rsub).trans
          (Line.of_inv Devm.getStor (by line_inv) storeWordRun)))

  obtain ⟨resumeLoadPre, qresumeSlot, run⟩ := runCompiledTo_next_inv run
  obtain ⟨resumeLoadPost, qresumeLoad, run⟩ := runCompiledTo_next_inv run
  obtain ⟨timestampPost, qtimestamp, run⟩ := runCompiledTo_next_inv run
  obtain ⟨pauseTest, qpauseLt, pauseBranch⟩ := runCompiledTo_next_inv run
  have rresumeSlot := Ninst.Run.of_runCompiled qresumeSlot
  have rresumeLoad := Ninst.Run.of_runCompiled qresumeLoad
  have rtimestamp := Ninst.Run.of_runCompiled qtimestamp
  have rpauseLt := Ninst.Run.of_runCompiled qpauseLt
  have pResumeSlot := prefix_of_push (of_run_pushB256 rresumeSlot) pAfterStore
  obtain ⟨resumeSince, pResumeSince, hResumeSince⟩ :=
    prefix_of_sload rresumeLoad pResumeSlot
  have pTimestamp := prefix_of_timestamp pResumeSince rtimestamp
  have pPauseTest := prefix_of_lt rpauseLt pTimestamp
  have resumeLoadStor : Devm.getStor pre = Devm.getStor resumeLoadPre :=
    afterBalanceStor.trans
      (storeStor.trans (Ninst.Hinv.inv (f := Devm.getStor) rresumeSlot))
  have hResumeSinceAtEntry : resumeSince =
      pre.getStorVal sevm.currentTarget resumeSinceSlot := by
    rw [hResumeSince]
    exact congrArg (fun s : Stor => s.get resumeSinceSlot)
      (congrFun resumeLoadStor sevm.currentTarget).symm
  have pPauseNonzero :
      B256.ltCheck sevm.benvStat.time resumeSince :: tail <<+
        pauseTest.stack := pPauseTest
  obtain ⟨callPre, _, -, hpausePop, callRun, pCall⟩ :=
    Func.RunCompiledTo.succ_branch_of_prefix
      (by simpa [hResumeSinceAtEntry] using hpaused)
      pPauseNonzero pauseBranch
  have callStor : Devm.getStor pre = Devm.getStor callPre :=
    resumeLoadStor.trans
      ((Ninst.Hinv.inv (f := Devm.getStor) rresumeLoad).trans
        ((Ninst.Hinv.inv (f := Devm.getStor) rtimestamp).trans
          ((Ninst.Hinv.inv (f := Devm.getStor) rpauseLt).trans
            (funext (getStor_eq_of_state_eq hpausePop.state)))))
  exact ⟨callPre, callRun, pCall, callStor⟩

theorem triggerAuthorizedContinuation_paused_reverts
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hbalance : B256.ltCheck (pre.getBal sevm.currentTarget) sevm.value = 0)
    (hpaused : B256.ltCheck sevm.benvStat.time
      (pre.getStorVal sevm.currentTarget resumeSinceSlot) ≠ 0)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre rebasedTriggerAuthorizedContinuation out) :
    PausedTriggerFailure out := by
  obtain ⟨_, callRun, _, _⟩ :=
    triggerAuthorizedContinuation_paused_route hp hbalance hpaused run
  exact rebasedTriggerResumedExpected_call_reverts_exact callRun

/-- The role guard is traversed before the pause check: an exact role record
selects the authorized continuation, and a live pause then reaches
`ResumedExpected()` before the value, array, and quota checks. -/
theorem triggerAfterValidation_authorized_paused_reverts
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hasRole : CallerHasRole (Devm.getStor pre sevm.currentTarget)
      addFullWithdrawalRequestRole sevm.caller.toB256)
    (hbalance : B256.ltCheck (pre.getBal sevm.currentTarget) sevm.value = 0)
    (hpaused : B256.ltCheck sevm.benvStat.time
      (pre.getStorVal sevm.currentTarget resumeSinceSlot) ≠ 0)
    (run : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm pre
        (Trigger.rebaseLocalCalls triggerAuxDelta Trigger.afterValidation)
        out) :
    PausedTriggerFailure out := by
  rw [rebasedTriggerAfterValidation_exact] at run
  rcases triggerCoreFlatRoleGuard_route hp run with
    ⟨bodyPre, bodyHasRole, bodyRun, bodyStack, bodyStor, bodyBal⟩ |
    ⟨callPre, lacksRole, callRun, callStack, callStor, callBal⟩
  · have bodyBalance :
        B256.ltCheck (bodyPre.getBal sevm.currentTarget) sevm.value = 0 := by
      rw [← bodyBal]
      exact hbalance
    have resumeSincePreserved :
        pre.getStorVal sevm.currentTarget resumeSinceSlot =
          bodyPre.getStorVal sevm.currentTarget resumeSinceSlot := by
      exact congrArg (fun s : Stor => s.get resumeSinceSlot)
        (congrFun bodyStor sevm.currentTarget)
    have bodyPaused : B256.ltCheck sevm.benvStat.time
        (bodyPre.getStorVal sevm.currentTarget resumeSinceSlot) ≠ 0 := by
      rw [← resumeSincePreserved]
      exact hpaused
    exact triggerAuthorizedContinuation_paused_reverts bodyStack bodyBalance
      bodyPaused bodyRun
  · exact (lacksRole hasRole).elim

/-! ## Canonical empty-array validator route

For `triggerEmptyAuthorizationCalldata refundRecipient exitType`, the exact
source values are:

* calldata size `132`;
* argument heads `0x60`, `refundRecipient.toB256`, and `exitType`;
* array length pointer `100`, array length `0`, and elements base `132`.

Consequently every malformed-ABI flag is zero, the loop counters and encoded
size accumulators are stored as zero, and the validator's last source node is
`.call rebasedTriggerAfterValidationSlot`.  Entering that call yields
`Trigger.rebaseLocalCalls triggerAuxDelta Trigger.afterValidation`, which is
definitionally `rebasedTriggerAfterValidation_exact` above.

The remaining executable declaration is intentionally omitted in this cold
draft.  Its intended signature is:

```lean
triggerEmpty_afterValidation_route
    (run : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (entryStack : entry.stack = [])
    (entryMemory : entry.memory = Mem.empty)
    (data : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType) :
    ∃ afterPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm afterPre
        (Trigger.rebaseLocalCalls triggerAuxDelta Trigger.afterValidation) out ∧
      afterPre.stack = [] ∧
      Devm.getStor entry = Devm.getStor afterPre ∧
      entry.getBal sevm.currentTarget = afterPre.getBal sevm.currentTarget
```

The proof must use `dispatcher_body_of_prog_run_empty_frame`, then thread the
concrete memory image through the validator's `mstoreAt`/`loadWord` pairs.  The
shared symmetric non-overlap read-over-write lemma is pending on the mainline
`Blanc.BytesWrite` landing; this branch deliberately neither copies nor
redeclares it.  Until that source walk is present, no public trigger
authorization theorem may claim the validator-to-role route.
-/

end LidoTriggerableWithdrawalsGateway
end Blanc
