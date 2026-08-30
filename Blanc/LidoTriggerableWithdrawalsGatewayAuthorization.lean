import Blanc.LidoTriggerableWithdrawalsGatewayA2
import Blanc.LidoTriggerableWithdrawalsGatewayRoleRoute
import Blanc.LidoTriggerableWithdrawalsGatewayTriggerAuthorizationRoute
import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetInterface

/-!
# Triggerable Withdrawals Gateway: authorization packet

This file is the source-side A2 authorization census.  It records the exact
role-gated bodies and the two distinct failure boundaries used by the runtime:
the zero-index path calls `missingRoleSlot`, while a nonzero record whose role
or canonical account does not match calls `collisionRefusalSlot`.  The latter
is intentionally an empty revert, not an `AccessControlUnauthorizedAccount`
payload.

The public selector-to-body/role-storage inversions are left as explicit route
obligations below.  The six endpoints using the family's shared `onlyRole`
modifier must consume the family-owned arbitrary-out route theorem; this file
does not duplicate that storage walk.  The trigger needs its own route through
the exact dynamic-ABI validator and `Trigger.coreFlatRoleGuard`.  Neither route
is replaced here by an evaluator result, `Nonempty`, or an assumed execution
premise.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoTriggerableWithdrawalsGateway

/-! ## Exact role-gate census -/

def roleGatedEntries (dp : DeployParams) :
    List (B256 × B256 × Func) :=
  [ (selPauseFor, pauseRole, pauseFor),
    (selPauseUntil, pauseRole, pauseUntil),
    (selResume, resumeRole, resume),
    (selSetExitRequestLimit, twExitLimitManagerRole, setExitRequestLimit),
    (selTriggerFullWithdrawals, addFullWithdrawalRequestRole,
      triggerFullWithdrawals dp),
    (selGrantRole, defaultAdminRole, grantRole),
    (selRevokeRole, defaultAdminRole, revokeRole) ]

theorem roleGatedEntries_exact (dp : DeployParams) :
    roleGatedEntries dp =
      [ (selPauseFor, pauseRole, pauseFor),
        (selPauseUntil, pauseRole, pauseUntil),
        (selResume, resumeRole, resume),
        (selSetExitRequestLimit, twExitLimitManagerRole,
          setExitRequestLimit),
        (selTriggerFullWithdrawals, addFullWithdrawalRequestRole,
          triggerFullWithdrawals dp),
        (selGrantRole, defaultAdminRole, grantRole),
        (selRevokeRole, defaultAdminRole, revokeRole) ] :=
  rfl

/-- The same census at the actual `funcs` dispatcher boundary.  In particular,
the payable trigger is not wrapped in `nonpayable`; every other protected entry
is. -/
def roleGatedDispatchEntries (dp : DeployParams) :
    List (B256 × B256 × Func) :=
  [ (selPauseFor, pauseRole, nonpayable pauseFor),
    (selPauseUntil, pauseRole, nonpayable pauseUntil),
    (selResume, resumeRole, nonpayable resume),
    (selSetExitRequestLimit, twExitLimitManagerRole,
      nonpayable setExitRequestLimit),
    (selTriggerFullWithdrawals, addFullWithdrawalRequestRole,
      triggerFullWithdrawals dp),
    (selGrantRole, defaultAdminRole, nonpayable grantRole),
    (selRevokeRole, defaultAdminRole, nonpayable revokeRole) ]

theorem roleGatedDispatchEntries_exact (dp : DeployParams) :
    roleGatedDispatchEntries dp =
      [ (selPauseFor, pauseRole, nonpayable pauseFor),
        (selPauseUntil, pauseRole, nonpayable pauseUntil),
        (selResume, resumeRole, nonpayable resume),
        (selSetExitRequestLimit, twExitLimitManagerRole,
          nonpayable setExitRequestLimit),
        (selTriggerFullWithdrawals, addFullWithdrawalRequestRole,
          triggerFullWithdrawals dp),
        (selGrantRole, defaultAdminRole, nonpayable grantRole),
        (selRevokeRole, defaultAdminRole, nonpayable revokeRole) ] :=
  rfl

/-! ## Exact authorization calldata

These images are deliberately canonical rather than merely selector-bearing.
The trigger fixture uses an empty dynamic tuple array: its first head is the
ABI-relative offset `0x60`, and the zero array-length word begins at byte 100.
That is the smallest complete input which passes the live trigger validator and
reaches its flat role guard.  Address words are built from `Adr`, so the
`canonicalArg` and strict trigger address checks cannot fail first.
-/

def pauseUntilAuthorizationCalldata (expiry : B256) : Bytes :=
  abiSelectorBytes selPauseUntil ++ expiry.toBytes

def resumeAuthorizationCalldata : Bytes :=
  abiSelectorBytes selResume

def setExitRequestLimitAuthorizationCalldata
    (maximum exitsPerFrame frameDuration : B256) : Bytes :=
  abiSelectorBytes selSetExitRequestLimit ++
    (maximum.toBytes ++ exitsPerFrame.toBytes ++ frameDuration.toBytes)

def grantRoleAuthorizationCalldata (role : B256) (account : Adr) : Bytes :=
  abiSelectorBytes selGrantRole ++ (role.toBytes ++ account.toB256.toBytes)

def revokeRoleAuthorizationCalldata (role : B256) (account : Adr) : Bytes :=
  abiSelectorBytes selRevokeRole ++ (role.toBytes ++ account.toB256.toBytes)

theorem pauseUntilAuthorizationCalldata_length (expiry : B256) :
    (pauseUntilAuthorizationCalldata expiry).length = 36 := by
  simp [pauseUntilAuthorizationCalldata, abiSelectorBytes_length,
    B256.length_toBytes]

theorem resumeAuthorizationCalldata_length :
    resumeAuthorizationCalldata.length = 4 := by
  simp [resumeAuthorizationCalldata, abiSelectorBytes_length]

theorem setExitRequestLimitAuthorizationCalldata_length
    (maximum exitsPerFrame frameDuration : B256) :
    (setExitRequestLimitAuthorizationCalldata maximum exitsPerFrame
      frameDuration).length = 100 := by
  simp [setExitRequestLimitAuthorizationCalldata, abiSelectorBytes_length,
    B256.length_toBytes]

theorem grantRoleAuthorizationCalldata_length (role : B256) (account : Adr) :
    (grantRoleAuthorizationCalldata role account).length = 68 := by
  simp [grantRoleAuthorizationCalldata, abiSelectorBytes_length,
    B256.length_toBytes]

theorem revokeRoleAuthorizationCalldata_length (role : B256) (account : Adr) :
    (revokeRoleAuthorizationCalldata role account).length = 68 := by
  simp [revokeRoleAuthorizationCalldata, abiSelectorBytes_length,
    B256.length_toBytes]

/-! Every image above, together with the existing `pauseForCalldata`, fixes the
public selector by the shared canonical-selector theorem.  These facts are
source equalities only; they do not assert that a runtime walk exists. -/

theorem selector_of_pauseForAuthorizationCalldata
    {sevm : Sevm} {duration : B256}
    (hdata : sevm.data = pauseForCalldata duration) :
    Sevm.selector sevm = selPauseFor := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selPauseFor) (tail := duration.toBytes)
  · rfl
  · simpa [pauseForCalldata] using hdata

theorem selector_of_pauseUntilAuthorizationCalldata
    {sevm : Sevm} {expiry : B256}
    (hdata : sevm.data = pauseUntilAuthorizationCalldata expiry) :
    Sevm.selector sevm = selPauseUntil := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selPauseUntil) (tail := expiry.toBytes)
  · rfl
  · simpa [pauseUntilAuthorizationCalldata] using hdata

theorem selector_of_resumeAuthorizationCalldata
    {sevm : Sevm} (hdata : sevm.data = resumeAuthorizationCalldata) :
    Sevm.selector sevm = selResume := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selResume) (tail := [])
  · rfl
  · simpa [resumeAuthorizationCalldata] using hdata

theorem selector_of_setExitRequestLimitAuthorizationCalldata
    {sevm : Sevm} {maximum exitsPerFrame frameDuration : B256}
    (hdata : sevm.data = setExitRequestLimitAuthorizationCalldata maximum
      exitsPerFrame frameDuration) :
    Sevm.selector sevm = selSetExitRequestLimit := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selSetExitRequestLimit)
      (tail := maximum.toBytes ++ exitsPerFrame.toBytes ++
        frameDuration.toBytes)
  · rfl
  · simpa [setExitRequestLimitAuthorizationCalldata] using hdata

theorem selector_of_grantRoleAuthorizationCalldata
    {sevm : Sevm} {role : B256} {account : Adr}
    (hdata : sevm.data = grantRoleAuthorizationCalldata role account) :
    Sevm.selector sevm = selGrantRole := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selGrantRole)
      (tail := role.toBytes ++ account.toB256.toBytes)
  · rfl
  · simpa [grantRoleAuthorizationCalldata] using hdata

theorem selector_of_revokeRoleAuthorizationCalldata
    {sevm : Sevm} {role : B256} {account : Adr}
    (hdata : sevm.data = revokeRoleAuthorizationCalldata role account) :
    Sevm.selector sevm = selRevokeRole := by
  apply selector_eq_of_data_eq_abiSelectorBytes_append
      (selected := selRevokeRole)
      (tail := role.toBytes ++ account.toB256.toBytes)
  · rfl
  · simpa [revokeRoleAuthorizationCalldata] using hdata

/- These equalities are deliberately redundant with the runtime definitions:
   they pin the modifier order which the later route proofs must preserve. -/

theorem pauseFor_role_gate_exact :
    pauseFor =
      (requireStaticArgs 1 <| onlyRole pauseRole <|
        ([pushB256 resumeSinceSlot, sload, timestamp, lt, iszero] +++
          (pauseForUnpaused <?> .call resumedExpectedSlot))) :=
  rfl

theorem pauseUntil_role_gate_exact :
    pauseUntil =
      (requireStaticArgs 1 <| onlyRole pauseRole <|
        ([pushB256 resumeSinceSlot, sload, timestamp, lt, iszero] +++
          (pauseUntilUnpaused <?> .call resumedExpectedSlot))) :=
  rfl

theorem resume_role_gate_exact :
    resume =
      (onlyRole resumeRole <|
        ([pushB256 resumeSinceSlot, sload, timestamp, lt] +++
          ((([timestamp, pushB256 resumeSinceSlot, sstore] ++
              emitNoData (signatureHash "Resumed" [])) +++ Func.stop)
            <?> .call pausedExpectedSlot))) :=
  rfl

theorem setExitRequestLimit_role_gate_exact :
    setExitRequestLimit =
      (requireStaticArgs 3 <| onlyRole twExitLimitManagerRole <|
        ([pushB256 (Nat.toB256 (2 ^ 32 - 1))] ++ arg 0 ++ [gt]) +++
          ((.call tooLargeMaxExitRequestsLimitSlot) <?>
            setExitRequestLimitDurationChecked)) :=
  rfl

theorem grantRole_role_gate_exact :
    grantRole =
      (requireStaticArgs 2 <| canonicalArg 1 <|
        onlyRole defaultAdminRole <|
          ((arg 0 ++ mstoreAt 0 ++ arg 1 ++ mstoreAt 1 ++
            roleKeyFromMemory roleLookupIndexRegion ++ [sload, iszero]) +++
            ((([pushB256 roleRecordLengthSlot, sload] ++ mstoreAt 2 ++
                mloadWord 2 ++ [pushB256 1, add] ++
                  roleKeyFromMemory roleLookupIndexRegion ++ [sstore] ++
                mloadWord 0 ++ roleKeyFromMemory roleLookupRoleRegion ++
                  [sstore] ++
                mloadWord 1 ++ roleKeyFromMemory roleLookupAccountRegion ++
                  [sstore] ++
                mloadWord 0 ++ enumKeyFromMemory enumRoleRegion ++ [sstore] ++
                mloadWord 1 ++ enumKeyFromMemory enumAccountRegion ++ [sstore] ++
                mloadWord 2 ++
                  [pushB256 1, add, pushB256 roleRecordLengthSlot, sstore] ++
                emitRoleGranted) +++ Func.stop)
              <?>
              (roleIdentityMatchesMemory +++
                (Func.stop <?> .call collisionRefusalSlot))))) :=
  rfl

theorem revokeRole_role_gate_exact :
    revokeRole =
      (requireStaticArgs 2 <| canonicalArg 1 <|
        onlyRole defaultAdminRole <| clearRoleMembership) :=
  rfl

/-! The trigger's role guard is inside the compiled local trigger body. -/

theorem trigger_role_precedes_pause_exact (dp : DeployParams) :
    Trigger.afterValidation =
      (Trigger.coreFlatRoleGuard (.call Trigger.roleFailureBoundarySlot) <|
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
                          .call Trigger.consumeQuotaSlot)))))))) :=
  rfl

/-! ## Exact auxiliary failure outcomes -/

/-- The live shared `onlyRole` zero-index boundary.  The final dynamic-memory
read of the selector reverter may itself exhaust gas, which is why the exact
outcome retains that alternative. -/
def MissingRoleFailure (out : Execution) : Prop :=
  (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
    (∃ post, out = .error (.revert, post) ∧
      post.output = customErrorData "AccessControlUnauthorizedAccount")

/-- A nonzero flat-record collision is refused by an empty-data revert. -/
def CollisionRoleFailure (out : Execution) : Prop :=
  ∃ post, out = .error (.revert, post) ∧ post.output = []

/-- Public shared-role absence is the disjunction forced by the exact flat
record: index zero uses the AccessControl payload; a nonzero mismatching role
or account uses collision refusal. -/
def AbsentRoleFailure (out : Execution) : Prop :=
  MissingRoleFailure out ∨ CollisionRoleFailure out

/-- The trigger's flat guard reaches the same shared AccessControl boundary as
every other role gate, so its outcome is exactly `MissingRoleFailure`. -/
theorem triggerRoleFailure_eq_missingRole :
    TriggerRoleFailure = MissingRoleFailure := rfl

theorem collisionRefusal_call_reverts_exact
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hcall : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm entry (.call collisionRefusalSlot) out) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] := by
  have hget : ((runtime dp).main :: (runtime dp).aux)[collisionRefusalSlot]? =
      some Func.rev := by
    simp [runtime, aux, baseAux, collisionRefusalSlot]
  obtain ⟨_, _, hbody⟩ := runCompiledTo_call_inv hget hcall
  exact runCompiledTo_rev_inv hbody

/-! These route consumers are the exact negative-gate conclusions once the
   corresponding role-key walk has been inverted.  Keeping the route premise
   visible prevents accidental laundering through a model or mere inhabitation.
   Every one of the seven public gates uses one of these two conclusions. -/

theorem zeroIndex_role_failure_of_route
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hroute : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm entry (.call missingRoleSlot) out) :
    (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, out = .error (.revert, post) ∧
        post.output = customErrorData "AccessControlUnauthorizedAccount") :=
  missingRole_call_reverts_exact hroute

theorem zeroIndex_role_failure_outcome_of_route
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hroute : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm entry (.call missingRoleSlot) out) :
    MissingRoleFailure out := by
  simpa [MissingRoleFailure] using missingRole_call_reverts_exact hroute

theorem collision_role_failure_of_route
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hroute : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm entry (.call collisionRefusalSlot) out) :
    ∃ post, out = .error (.revert, post) ∧ post.output = [] :=
  collisionRefusal_call_reverts_exact hroute

theorem collision_role_failure_outcome_of_route
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hroute : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm entry (.call collisionRefusalSlot) out) :
    CollisionRoleFailure out := by
  simpa [CollisionRoleFailure] using collisionRefusal_call_reverts_exact hroute

/-! ## From an `onlyRole` route to the exact absent-role outcome -/

/-- A caller without the exact flat record cannot take the authorized arm, so
every remaining `onlyRole` continuation is one of the two exact auxiliary
failures.  This is the only place the four-way route is collapsed. -/
theorem absentRole_of_onlyRole_route
    {dp : DeployParams} {sevm : Sevm} {pre : Devm} {out : Execution}
    {role : B256} {body : Func} {tail : Stack}
    (lacksRole : ¬ CallerHasRole (Devm.getStor pre sevm.currentTarget)
      role sevm.caller.toB256)
    (route : OnlyRoleRoute dp sevm pre role body tail out) :
    AbsentRoleFailure out := by
  cases route with
  | authorized _ hasRole _ _ _ => exact (lacksRole hasRole).elim
  | missingRole _ _ callRun _ _ =>
      exact Or.inl (zeroIndex_role_failure_outcome_of_route callRun)
  | roleCollision _ _ _ callRun _ _ =>
      exact Or.inr (collision_role_failure_outcome_of_route callRun)
  | accountCollision _ _ _ _ callRun _ _ =>
      exact Or.inr (collision_role_failure_outcome_of_route callRun)

/-- The shared opening for a statically-shaped nonpayable role gate: the
dispatcher hands over the exact wrapped body, `nonpayable` and
`requireStaticArgs` are peeled by their own arbitrary-outcome lemmas, and the
caller's absent record is transported along the storage chain to the route's
entry.  No body-walk premise is introduced. -/
private theorem absentRole_of_static_entry
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector role : B256} {words : Nat} {body wrapped : Func}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hsize : B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * words)) = 0)
    (hselector : Sevm.selector sevm = selector)
    (hmember : (selector, nonpayable wrapped) ∈ funcs dp)
    (hshape : wrapped = requireStaticArgs words (onlyRole role body))
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      role sevm.caller.toB256) :
    AbsentRoleFailure out := by
  subst hshape
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, dispatchFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame hprog hentryStack hguard
      hselector hmember
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  obtain ⟨staticPre, staticRun, pStatic, staticStor⟩ :=
    Func.RunCompiledTo.nonpayable_body_of_value_zero hvalue pDispatch
      dispatchRun
  obtain ⟨rolePre, roleRun, pRole, roleStor⟩ :=
    requireStaticArgs_body_of_sufficient_calldata pStatic hsize staticRun
  have chain : Devm.getStor entry = Devm.getStor rolePre :=
    (funext (getStor_eq_of_state_eq dispatchFrame.state)).trans
      (staticStor.trans roleStor)
  refine absentRole_of_onlyRole_route ?_ (onlyRole_route pRole roleRun)
  rw [← congrFun chain sevm.currentTarget]
  exact lacksRole

/-- The same opening for the one protected entry that takes no static
arguments, so the dispatcher body is `nonpayable (onlyRole ..)` directly. -/
private theorem absentRole_of_plain_entry
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector role : B256} {body wrapped : Func}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selector)
    (hmember : (selector, nonpayable wrapped) ∈ funcs dp)
    (hshape : wrapped = onlyRole role body)
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      role sevm.caller.toB256) :
    AbsentRoleFailure out := by
  subst hshape
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, dispatchFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame hprog hentryStack hguard
      hselector hmember
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  obtain ⟨rolePre, roleRun, pRole, roleStor⟩ :=
    Func.RunCompiledTo.nonpayable_body_of_value_zero hvalue pDispatch
      dispatchRun
  have chain : Devm.getStor entry = Devm.getStor rolePre :=
    (funext (getStor_eq_of_state_eq dispatchFrame.state)).trans roleStor
  refine absentRole_of_onlyRole_route ?_ (onlyRole_route pRole roleRun)
  rw [← congrFun chain sevm.currentTarget]
  exact lacksRole

/-- The opening for the two admin entries, which additionally canonicalise
their account argument before the role gate. -/
private theorem absentRole_of_canonical_entry
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector role index : B256} {words : Nat} {body wrapped : Func}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hsize : B256.ltCheck sevm.data.length.toB256
      (Nat.toB256 (4 + 32 * words)) = 0)
    (hvalid : ValidAdr (Sevm.argWord sevm index))
    (hselector : Sevm.selector sevm = selector)
    (hmember : (selector, nonpayable wrapped) ∈ funcs dp)
    (hshape : wrapped =
      requireStaticArgs words (canonicalArg index (onlyRole role body)))
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      role sevm.caller.toB256) :
    AbsentRoleFailure out := by
  subst hshape
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, dispatchFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame hprog hentryStack hguard
      hselector hmember
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  obtain ⟨staticPre, staticRun, pStatic, staticStor⟩ :=
    Func.RunCompiledTo.nonpayable_body_of_value_zero hvalue pDispatch
      dispatchRun
  obtain ⟨canonPre, canonRun, pCanon, canonStor⟩ :=
    requireStaticArgs_body_of_sufficient_calldata pStatic hsize staticRun
  obtain ⟨rolePre, roleRun, pRole, roleStor⟩ :=
    canonicalArg_body_of_valid hvalid pCanon canonRun
  have chain : Devm.getStor entry = Devm.getStor rolePre :=
    (funext (getStor_eq_of_state_eq dispatchFrame.state)).trans
      (staticStor.trans (canonStor.trans roleStor))
  refine absentRole_of_onlyRole_route ?_ (onlyRole_route pRole roleRun)
  rw [← congrFun chain sevm.currentTarget]
  exact lacksRole

/-! ## Public absent-role negatives -/

/-- `pauseFor` reverts for a caller without `PAUSE_ROLE`, at the exact
canonical calldata image and with no premise about the guarded body. -/
theorem pauseFor_absent_role_reverts
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {duration : B256}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hdata : sevm.data = pauseForCalldata duration)
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      pauseRole sevm.caller.toB256) :
    AbsentRoleFailure out := by
  have hlen : sevm.data.length = 36 := by
    rw [hdata]; exact pauseForCalldata_length duration
  refine absentRole_of_static_entry (words := 1) hprog hentryStack hvalue
    ?_ ?_ (selector_of_pauseForAuthorizationCalldata hdata) (by simp [funcs])
    pauseFor_role_gate_exact lacksRole
  · rw [hlen]; decide
  · rw [hlen]; decide

/-- `pauseUntil` reverts for a caller without `PAUSE_ROLE`. -/
theorem pauseUntil_absent_role_reverts
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {expiry : B256}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hdata : sevm.data = pauseUntilAuthorizationCalldata expiry)
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      pauseRole sevm.caller.toB256) :
    AbsentRoleFailure out := by
  have hlen : sevm.data.length = 36 := by
    rw [hdata]; exact pauseUntilAuthorizationCalldata_length expiry
  refine absentRole_of_static_entry (words := 1) hprog hentryStack hvalue
    ?_ ?_ (selector_of_pauseUntilAuthorizationCalldata hdata)
    (by simp [funcs]) pauseUntil_role_gate_exact lacksRole
  · rw [hlen]; decide
  · rw [hlen]; decide

/-- `setExitRequestLimit` reverts for a caller without
`TW_EXIT_LIMIT_MANAGER_ROLE`. -/
theorem setExitRequestLimit_absent_role_reverts
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {maximum exitsPerFrame frameDuration : B256}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hdata : sevm.data = setExitRequestLimitAuthorizationCalldata maximum
      exitsPerFrame frameDuration)
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      twExitLimitManagerRole sevm.caller.toB256) :
    AbsentRoleFailure out := by
  have hlen : sevm.data.length = 100 := by
    rw [hdata]
    exact setExitRequestLimitAuthorizationCalldata_length maximum
      exitsPerFrame frameDuration
  refine absentRole_of_static_entry (words := 3) hprog hentryStack hvalue
    ?_ ?_ (selector_of_setExitRequestLimitAuthorizationCalldata hdata)
    (by simp [funcs]) setExitRequestLimit_role_gate_exact lacksRole
  · rw [hlen]; decide
  · rw [hlen]; decide

/-- `resume` reverts for a caller without `RESUME_ROLE`. -/
theorem resume_absent_role_reverts
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hdata : sevm.data = resumeAuthorizationCalldata)
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      resumeRole sevm.caller.toB256) :
    AbsentRoleFailure out := by
  have hlen : sevm.data.length = 4 := by
    rw [hdata]; exact resumeAuthorizationCalldata_length
  refine absentRole_of_plain_entry hprog hentryStack hvalue ?_
    (selector_of_resumeAuthorizationCalldata hdata) (by simp [funcs])
    resume_role_gate_exact lacksRole
  · rw [hlen]; decide

/-- The admin entries' account argument is address-shaped by construction. -/
theorem grantRoleAuthorization_arg1
    {sevm : Sevm} {role : B256} {account : Adr}
    (hdata : sevm.data = grantRoleAuthorizationCalldata role account) :
    Sevm.argWord sevm 1 = account.toB256 := by
  change Sevm.dataWord sevm 36 = account.toB256
  apply dataWord_of_append
    (pre := abiSelectorBytes selGrantRole ++ role.toBytes)
    (post := [])
  · simp [abiSelectorBytes_length, B256.length_toBytes]
    rfl
  · rw [hdata, grantRoleAuthorizationCalldata]
    simp [List.append_assoc]

theorem revokeRoleAuthorization_arg1
    {sevm : Sevm} {role : B256} {account : Adr}
    (hdata : sevm.data = revokeRoleAuthorizationCalldata role account) :
    Sevm.argWord sevm 1 = account.toB256 := by
  change Sevm.dataWord sevm 36 = account.toB256
  apply dataWord_of_append
    (pre := abiSelectorBytes selRevokeRole ++ role.toBytes)
    (post := [])
  · simp [abiSelectorBytes_length, B256.length_toBytes]
    rfl
  · rw [hdata, revokeRoleAuthorizationCalldata]
    simp [List.append_assoc]

/-- `grantRole` reverts for a caller without the default admin role. -/
theorem grantRole_absent_role_reverts
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {role : B256} {account : Adr}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hdata : sevm.data = grantRoleAuthorizationCalldata role account)
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      defaultAdminRole sevm.caller.toB256) :
    AbsentRoleFailure out := by
  have hlen : sevm.data.length = 68 := by
    rw [hdata]; exact grantRoleAuthorizationCalldata_length role account
  refine absentRole_of_canonical_entry (words := 2) hprog hentryStack hvalue
    ?_ ?_ ?_ (selector_of_grantRoleAuthorizationCalldata hdata)
    (by simp [funcs]) grantRole_role_gate_exact lacksRole
  · rw [hlen]; decide
  · rw [hlen]; decide
  · rw [grantRoleAuthorization_arg1 hdata]; exact ⟨account, rfl⟩

/-- `revokeRole` reverts for a caller without the default admin role. -/
theorem revokeRole_absent_role_reverts
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {role : B256} {account : Adr}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hdata : sevm.data = revokeRoleAuthorizationCalldata role account)
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      defaultAdminRole sevm.caller.toB256) :
    AbsentRoleFailure out := by
  have hlen : sevm.data.length = 68 := by
    rw [hdata]; exact revokeRoleAuthorizationCalldata_length role account
  refine absentRole_of_canonical_entry (words := 2) hprog hentryStack hvalue
    ?_ ?_ ?_ (selector_of_revokeRoleAuthorizationCalldata hdata)
    (by simp [funcs]) revokeRole_role_gate_exact lacksRole
  · rw [hlen]; decide
  · rw [hlen]; decide
  · rw [revokeRoleAuthorization_arg1 hdata]; exact ⟨account, rfl⟩

/-! ## The payable trigger

Unlike the six entries above, `triggerFullWithdrawals` is payable and carries
its role guard inside the compiled trigger body, after the live calldata
validator.  Both theorems below therefore walk the validator rather than
assuming its outcome, and neither takes a body-walk premise. -/

/-- The trigger reverts for a caller without `ADD_FULL_WITHDRAWAL_REQUEST_ROLE`
at the canonical empty-array input — whatever the pause projection says.  This
is the first half of the modifier-precedence pair. -/
theorem triggerFullWithdrawals_absent_role_reverts
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {refundRecipient : Adr} {exitType : B256}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hentryMemory : entry.memory = Mem.empty)
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType)
    (lacksRole : ¬ CallerHasRole (Devm.getStor entry sevm.currentTarget)
      addFullWithdrawalRequestRole sevm.caller.toB256) :
    TriggerRoleFailure out := by
  have hlen : sevm.data.length = 132 := by
    rw [hdata]
    exact triggerEmptyAuthorizationCalldata_length refundRecipient exitType
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, dispatchFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame (body := triggerFullWithdrawals dp)
      hprog hentryStack (by rw [hlen]; decide)
      (selector_of_triggerEmptyAuthorizationCalldata hdata) (by simp [funcs])
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  have memDispatch : dispatchPre.memory = Mem.empty := by
    rw [← dispatchFrame.memory]; exact hentryMemory
  obtain ⟨bodyPre, bodyRun, pBody, stateBody⟩ :=
    triggerFullWithdrawals_reaches_afterValidation pDispatch memDispatch hdata
      dispatchRun
  refine triggerAfterValidation_absent_reverts pBody ?_ bodyRun
  rw [← funext (getStor_eq_of_state_eq
    (dispatchFrame.state.trans stateBody))]
  exact lacksRole

/-- The second half: with the role present but the gateway paused, the trigger
reaches the `ResumedExpected()` boundary before any value, array or quota
processing. -/
theorem triggerFullWithdrawals_authorized_paused_reverts
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {refundRecipient : Adr} {exitType : B256}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hentryMemory : entry.memory = Mem.empty)
    (hdata : sevm.data =
      triggerEmptyAuthorizationCalldata refundRecipient exitType)
    (hasRole : CallerHasRole (Devm.getStor entry sevm.currentTarget)
      addFullWithdrawalRequestRole sevm.caller.toB256)
    (hbalance : B256.ltCheck (entry.getBal sevm.currentTarget) sevm.value = 0)
    (hpaused : B256.ltCheck sevm.benvStat.time
      (entry.getStorVal sevm.currentTarget resumeSinceSlot) ≠ 0) :
    PausedTriggerFailure out := by
  have hlen : sevm.data.length = 132 := by
    rw [hdata]
    exact triggerEmptyAuthorizationCalldata_length refundRecipient exitType
  obtain ⟨dispatchPre, dispatchRun, dispatchStack, dispatchFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame (body := triggerFullWithdrawals dp)
      hprog hentryStack (by rw [hlen]; decide)
      (selector_of_triggerEmptyAuthorizationCalldata hdata) (by simp [funcs])
  have pDispatch : ([] : Stack) <<+ dispatchPre.stack :=
    ⟨dispatchPre.stack, rfl⟩
  have memDispatch : dispatchPre.memory = Mem.empty := by
    rw [← dispatchFrame.memory]; exact hentryMemory
  obtain ⟨bodyPre, bodyRun, pBody, stateBody⟩ :=
    triggerFullWithdrawals_reaches_afterValidation pDispatch memDispatch hdata
      dispatchRun
  have hstate : entry.state = bodyPre.state :=
    dispatchFrame.state.trans stateBody
  refine triggerAfterValidation_authorized_paused_reverts pBody ?_ ?_ ?_ bodyRun
  · rw [← funext (getStor_eq_of_state_eq hstate)]; exact hasRole
  · rw [← getBal_eq_of_state_eq hstate sevm.currentTarget]; exact hbalance
  · show B256.ltCheck sevm.benvStat.time
      (bodyPre.getStorVal sevm.currentTarget resumeSinceSlot) ≠ 0
    rw [show bodyPre.getStorVal sevm.currentTarget resumeSinceSlot =
        entry.getStorVal sevm.currentTarget resumeSinceSlot from
      congrArg (fun s : Stor => s.get resumeSinceSlot)
        (getStor_eq_of_state_eq hstate sevm.currentTarget).symm]
    exact hpaused

/-!
## What the negatives above do and do not say

Each of the seven entries reverts for a caller without its role, stated from
the program run, the exact canonical calldata image, an empty entry frame and
(for the six nonpayable entries) zero value.  None takes a body-walk premise,
so none can be satisfied by a route that never reaches the guard.

The conclusions are the exact auxiliary outcomes, not merely "some revert":
`AbsentRoleFailure` is the shared `onlyRole` disjunction of the AccessControl
payload and collision refusal, and `TriggerRoleFailure` is the trigger's own
AccessControl boundary — identified with the shared one by
`triggerRoleFailure_eq_missingRole`.  Each retains the out-of-gas alternative,
because the selector reverter's final dynamic-memory read may itself exhaust
gas; that is a resource fact, not an authorization one.

Modifier precedence is pinned for the payable trigger by the two theorems
above it: absence reaches the role failure *whatever* the pause projection
says, while an exact role record together with a paused projection reaches
`PausedTriggerFailure` before any value, array or quota processing.  Both walk
the live validator rather than assuming it.
-/

end LidoTriggerableWithdrawalsGateway
end Blanc
