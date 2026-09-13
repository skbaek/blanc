import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute

/-!
# Triggerable Withdrawals Gateway: Phase-A exact-runtime consumers

This unit deliberately keeps its boundary executable.  Source projections are
paired with either an exact `Func.RunCompiledTo` route or an exact instruction
run; no evaluator result or mere inhabitance is used as evidence.  In
particular, a call-to-auxiliary theorem proves the payload of the live runtime
reverter, while leaving the route from each protected public selector to that
call for the later ABI/role packets.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

/-! ## Source projections used by the pause/query rows -/

def isPausedSourceProjection (resumeSince timestamp : B256) : B256 :=
  timestamp <? resumeSince

theorem isPausedSourceProjection_effect (resumeSince timestamp : B256) :
    isPausedSourceProjection resumeSince timestamp = timestamp <? resumeSince :=
  rfl

theorem pauseFor_store_effect_of_exact_step
    {sevm : Sevm} {pre post : Devm}
    {key value : B256} {rest : Stack}
    (hstore : Ninst.Run sevm pre Ninst.sstore post)
    (hstack : pre.stack = key :: value :: rest) :
    Devm.getStor post sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set key value := by
  apply sstore_getStor_set hstore
  show key :: value :: [] <<+ pre.stack
  exact ⟨rest, by simpa [Split] using hstack⟩

/-! ## Exact auxiliary reverter consumers

`runtime` stores the base auxiliary table after the main entry.  The index
equalities below are intentionally proved against that exact table, so these
lemmas cannot accidentally consume the trigger packet's private table. -/

theorem missingRole_call_reverts_exact
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hcall : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm entry (.call missingRoleSlot) out) :
    (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, out = .error (.revert, post) ∧
        post.output = customErrorData "AccessControlUnauthorizedAccount") := by
  have hget : ((runtime dp).main :: (runtime dp).aux)[missingRoleSlot]? =
      some (runtimeError "AccessControlUnauthorizedAccount") := by
    simp [runtime, aux, baseAux, missingRoleSlot]
  obtain ⟨_, _, hbody⟩ := runCompiledTo_call_inv hget hcall
  simpa [runtimeError, customErrorData] using
    (runCompiledTo_revertSelector_inv hbody)

theorem pausedExpected_call_reverts_exact
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hcall : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm entry (.call pausedExpectedSlot) out) :
    (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, out = .error (.revert, post) ∧
        post.output = customErrorData "PausedExpected") := by
  have hget : ((runtime dp).main :: (runtime dp).aux)[pausedExpectedSlot]? =
      some (runtimeError "PausedExpected") := by
    simp [runtime, aux, baseAux, pausedExpectedSlot]
  obtain ⟨_, _, hbody⟩ := runCompiledTo_call_inv hget hcall
  simpa [runtimeError, customErrorData] using
    (runCompiledTo_revertSelector_inv hbody)

/-! The A2 route consumer for the public dispatcher.  It exposes the exact
    selected body after the program entry guard and selector load. -/

theorem selected_body_of_exact_runtime
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    {selector : B256} {body : Func}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selector)
    (hnotTrigger : selector ≠ selTriggerFullWithdrawals)
    (hmember : (selector, body) ∈ sharedNonpayableFuncs) :
    DispatchBodyWitness ((runtime dp).main :: (runtime dp).aux)
      sevm entry sharedNonpayableFuncs selector [] body out := by
  obtain ⟨bodyPre, bodyRun, bodyStack, bodyFrame⟩ :=
    dispatcher_body_of_prog_run_empty_frame hprog hentryStack hvalue hguard
      hselector hnotTrigger hmember
  exact ⟨bodyPre, hmember, bodyRun, bodyStack, bodyFrame⟩

end LidoTriggerableWithdrawalsGateway
end Blanc
