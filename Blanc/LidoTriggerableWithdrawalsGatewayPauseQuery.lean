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
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseFor)
    (huniq : selectorUnique (funcs dp)) :
    ∃ dispatchEntry tail bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre (nonpayable pauseFor) out ∧
      bodyPre.stack = tail ∧
      Devm.DispatchFramePreserved dispatchEntry bodyPre := by
  have hmember : (selPauseFor, nonpayable pauseFor) ∈ funcs dp := by
    simp [funcs]
  obtain ⟨dispatchEntry, tail, witness⟩ :=
    dispatcher_body_of_prog_run hprog hguard hselector huniq hmember
  rcases witness with ⟨bodyPre, -, hbody, hstack, hframe⟩
  exact ⟨dispatchEntry, tail, bodyPre, hbody, hstack, hframe⟩

theorem pauseUntil_selected_body_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selPauseUntil)
    (huniq : selectorUnique (funcs dp)) :
    ∃ dispatchEntry tail bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre (nonpayable pauseUntil) out ∧
      bodyPre.stack = tail ∧
      Devm.DispatchFramePreserved dispatchEntry bodyPre := by
  have hmember : (selPauseUntil, nonpayable pauseUntil) ∈ funcs dp := by
    simp [funcs]
  obtain ⟨dispatchEntry, tail, witness⟩ :=
    dispatcher_body_of_prog_run hprog hguard hselector huniq hmember
  rcases witness with ⟨bodyPre, -, hbody, hstack, hframe⟩
  exact ⟨dispatchEntry, tail, bodyPre, hbody, hstack, hframe⟩

theorem resume_selected_body_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selResume)
    (huniq : selectorUnique (funcs dp)) :
    ∃ dispatchEntry tail bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre (nonpayable resume) out ∧
      bodyPre.stack = tail ∧
      Devm.DispatchFramePreserved dispatchEntry bodyPre := by
  have hmember : (selResume, nonpayable resume) ∈ funcs dp := by
    simp [funcs]
  obtain ⟨dispatchEntry, tail, witness⟩ :=
    dispatcher_body_of_prog_run hprog hguard hselector huniq hmember
  rcases witness with ⟨bodyPre, -, hbody, hstack, hframe⟩
  exact ⟨dispatchEntry, tail, bodyPre, hbody, hstack, hframe⟩

theorem isPaused_selected_body_of_prog_run
    {dp : DeployParams} {sevm : Sevm} {entry : Devm} {out : Execution}
    (hprog : Prog.RunCompiledTo sevm entry (runtime dp) out)
    (hguard : B256.ltCheck sevm.data.length.toB256 (4 : B256) = 0)
    (hselector : Sevm.selector sevm = selIsPaused)
    (huniq : selectorUnique (funcs dp)) :
    ∃ dispatchEntry tail bodyPre,
      Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm bodyPre (nonpayable isPaused) out ∧
      bodyPre.stack = tail ∧
      Devm.DispatchFramePreserved dispatchEntry bodyPre := by
  have hmember : (selIsPaused, nonpayable isPaused) ∈ funcs dp := by
    simp [funcs]
  obtain ⟨dispatchEntry, tail, witness⟩ :=
    dispatcher_body_of_prog_run hprog hguard hselector huniq hmember
  rcases witness with ⟨bodyPre, -, hbody, hstack, hframe⟩
  exact ⟨dispatchEntry, tail, bodyPre, hbody, hstack, hframe⟩

/-! ## Exact instruction-level storage boundary -/

end LidoTriggerableWithdrawalsGateway
end Blanc
