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
