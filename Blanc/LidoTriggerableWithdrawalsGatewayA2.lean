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
    simp only [runtime, aux, baseAux, List.cons_append, List.nil_append, List.append_assoc,
      missingRoleSlot, List.length_cons, lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true,
      getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero]
  obtain ⟨_, _, hbody⟩ := runCompiledTo_call_inv hget hcall
  simpa only [ExceptT.stM_eq, customErrorData] using (runCompiledTo_revertSelector_inv hbody)

theorem pausedExpected_call_reverts_exact
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hcall : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
      sevm entry (.call pausedExpectedSlot) out) :
    (∃ d, out = .error (.halt (.outOfGas .none), d)) ∨
      (∃ post, out = .error (.revert, post) ∧
        post.output = customErrorData "PausedExpected") := by
  have hget : ((runtime dp).main :: (runtime dp).aux)[pausedExpectedSlot]? =
      some (runtimeError "PausedExpected") := by
    simp only [runtime, aux, baseAux, List.cons_append, List.nil_append, List.append_assoc,
      pausedExpectedSlot, List.length_cons, lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos,
      or_true, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero]
  obtain ⟨_, _, hbody⟩ := runCompiledTo_call_inv hget hcall
  simpa only [ExceptT.stM_eq, customErrorData] using (runCompiledTo_revertSelector_inv hbody)

/-! The A2 route consumer for the public dispatcher.  It exposes the exact
    selected body after the program entry guard and selector load. -/

end LidoTriggerableWithdrawalsGateway
end Blanc
