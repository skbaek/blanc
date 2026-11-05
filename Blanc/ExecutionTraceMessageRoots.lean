import Blanc.ExecutionTraceFrames

/-!
Raw entered-frame roots of an actual non-creation message-call trace. The
original no-authorization, no-delegation and entered-frame hypotheses remain.
-/

namespace Blanc

open Jaune Blanc.ExecutionTrace

/-- A message whose code carries no delegation designator resolves to itself. -/
private theorem resolveCodeDelegation_of_none {msg : Msg}
    (h : getDelegatedCodeAddress msg.code = none) : msg.resolveCodeDelegation = msg := by
  unfold Msg.resolveCodeDelegation ForkRules.delegatedCodeAddress
  split
  · rfl
  · rename_i address hsome
    split at hsome
    · rw [h] at hsome
      cases hsome
    · cases hsome

/-- **A call trace's raw frames are the raw roots of its entered frame's derivation.** -/
theorem messageCallTrace_rawFrames_run {msg : Msg} {state : Jaune.State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (target : msg.target.isNone = false)
    (auths : msg.tenv.stat.auths.isEmpty = true)
    (nodeleg : getDelegatedCodeAddress msg.code = none) {cevm : Evm}
    (enter : (Frame.ofCall msg).enter = .run cevm) :
    ∃ (raw : Execution) (run : Exec cevm.pc cevm.sta cevm.dyna raw),
      trace.rawFrames = Exec.rawFrameRoots run := by
  cases trace with
  | createCollision htarget => simp only [target, Bool.false_eq_true] at htarget
  | createRun htarget => simp only [target, Bool.false_eq_true] at htarget
  | callRun htarget delegated refund hdelegation execMsg execMsgEq evm core coreTrace result =>
    have delegatedEq : delegated = msg := by
      unfold messageCallDelegation processMessageCall.legacyAuthorization at hdelegation
      simp only [auths, Bool.or_true, ↓reduceIte] at hdelegation
      exact (Prod.mk.inj (Except.ok.inj hdelegation)).1.symm
    subst delegated
    have execEq : execMsg = msg := by
      rw [execMsgEq]
      exact resolveCodeDelegation_of_none nodeleg
    subst execEq
    rcases coreTrace with ⟨slot, retained, run⟩
    have hrun := run
    unfold ProcessMessage RunFrame at hrun
    rw [enter] at hrun
    obtain ⟨raw, slotEq, -⟩ := hrun
    subst slotEq
    rcases cevm with ⟨pc, sevm, pre⟩
    cases retained with
    | some exn => exact ⟨raw, exn, rfl⟩

end Blanc
