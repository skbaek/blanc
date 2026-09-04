import Blanc.LidoTriggerableWithdrawalsGatewayPinnedTargetInterface
import Blanc.LidoTriggerableWithdrawalsGatewayRuntimeRoute

/-!
# Triggerable Withdrawals Gateway: pause/query Phase-A surface

This module records the exact public-runtime route and the source projections
used by the pause/query rows.  The route theorem below starts from
`Prog.RunCompiledTo`, uses the runtime guard and selector inversion from
`dispatcher_body_of_prog_run`, and specializes the selected body to the
family's pause/query functions.  Storage effects are stated at the exact
`SSTORE` instruction boundary; the remaining work is to compose those
instruction boundaries through the ABI/role branches into public postconditions.
No evaluator, `Nonempty`, sibling-family import, or assumed dispatcher walk is
used.
-/

namespace Blanc

open Jaune

namespace LidoTriggerableWithdrawalsGateway

/-! ## Source projections -/

def pauseUntilProjection (expiry : B256) : B256 :=
  if expiry = pauseInfinitely then pauseInfinitely else expiry + 1

def isPausedProjection (timestamp resumeSince : B256) : B256 :=
  timestamp <? resumeSince

theorem pauseUntilProjection_sentinel :
    pauseUntilProjection pauseInfinitely = pauseInfinitely := by
  simp [pauseUntilProjection]

theorem pauseUntilProjection_finite {expiry : B256}
    (hfinite : expiry ≠ pauseInfinitely) :
    pauseUntilProjection expiry = expiry + 1 := by
  simp [pauseUntilProjection, hfinite]

theorem isPausedProjection_effect (timestamp resumeSince : B256) :
    isPausedProjection timestamp resumeSince = timestamp <? resumeSince := rfl

/-! ## Exact public selector routes -/

theorem pauseFor_selected_body_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseFor) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre pauseFor out ∧
      bodyPre.stack = [] ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  exact dispatcher_body_of_prog_run_empty_frame hprog hentryStack hvalue
    hguard hselector (by decide) (by simp [sharedNonpayableFuncs])

theorem pauseUntil_selected_body_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseUntil) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre pauseUntil out ∧
      bodyPre.stack = [] ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  exact dispatcher_body_of_prog_run_empty_frame hprog hentryStack hvalue
    hguard hselector (by decide) (by simp [sharedNonpayableFuncs])

theorem resume_selected_body_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selResume) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre resume out ∧
      bodyPre.stack = [] ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  exact dispatcher_body_of_prog_run_empty_frame hprog hentryStack hvalue
    hguard hselector (by decide) (by simp [sharedNonpayableFuncs])

theorem isPaused_selected_body_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hentryStack : entry.stack = [])
    (hvalue : sevm.value = 0)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selIsPaused) :
    ∃ bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre isPaused out ∧
      bodyPre.stack = [] ∧
      Devm.DispatchFramePreserved entry bodyPre := by
  exact dispatcher_body_of_prog_run_empty_frame hprog hentryStack hvalue
    hguard hselector (by decide) (by simp [sharedNonpayableFuncs])

/-! ## Exact instruction-level storage boundary -/

end LidoTriggerableWithdrawalsGateway
end Blanc
