import Blanc.ExecutionMessageEffects

/-!
# Recovering the clean CREATE retained by a successful creation message

Message success rules out the collision arm and identifies the error marker
of the same retained CREATE core. An outer `Except.ok` alone is insufficient.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Success of the actual creation-message output exposes its clean retained
CREATE. Collision exclusion and the core state are conclusions, not premises. -/
theorem MessageCallTrace.exists_clean_create_with_deletions
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (target : msg.target.isNone = true)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (clean : out.error = none) :
    ∃ installed, Nonempty (ProcessCreateMessageTrace msg (.ok installed)) ∧
      processCreateMessage msg = .ok installed ∧
      messageCreateCollision msg = false ∧ installed.error = none ∧
      state = installed.state ∧ out.accountsToDelete = installed.accountsToDelete := by
  cases trace with
  | createCollision _ collision result =>
      unfold processMessageCall processMessageCall.create at result
      simp only [target, ↓reduceIte, hsg] at result
      unfold messageCreateCollision at collision
      simp only [collision, ↓reduceIte, pure] at result
      have output := (Prod.mk.inj (Except.ok.inj result)).2
      have error := congrArg MsgCallOutput.error output
      rw [clean] at error
      cases error
  | createRun _ collision installed core retained result =>
      have sameState := processMessageCall_createRun_state_eq_noStateGas
        target collision core result hsg
      have wrapper := result
      unfold processMessageCall processMessageCall.create at wrapper
      simp only [target, ↓reduceIte, hsg] at wrapper
      have collision' := collision
      unfold messageCreateCollision at collision'
      simp only [collision', Bool.false_eq_true, ↓reduceIte, core,
        Except.bimap, id, bind, Except.bind] at wrapper
      have sameError : installed.error = out.error := by
        split at wrapper
        · rcases Except.bind_eq_ok wrapper with ⟨refund, _, output⟩
          exact congrArg MsgCallOutput.error
            (Prod.mk.inj (Except.ok.inj output)).2
        · exact congrArg MsgCallOutput.error
            (Prod.mk.inj (Except.ok.inj wrapper)).2
      have installedClean := sameError.trans clean
      have sameDeletions : out.accountsToDelete = installed.accountsToDelete := by
        rw [installedClean] at wrapper
        simp only [Option.isNone_none, ↓reduceIte] at wrapper
        obtain ⟨refund, _, output⟩ := Except.bind_eq_ok wrapper
        exact (congrArg MsgCallOutput.accountsToDelete
          (Prod.mk.inj (Except.ok.inj output)).2).symm
      exact ⟨installed, ⟨retained⟩, core, collision, installedClean, sameState, sameDeletions⟩
  | callRun called _ _ _ _ _ _ _ _ _ =>
      rw [target] at called
      cases called

/-- Success exposes the same clean retained CREATE and installed state. -/
theorem MessageCallTrace.exists_clean_create
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (target : msg.target.isNone = true)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (clean : out.error = none) :
    ∃ installed, Nonempty (ProcessCreateMessageTrace msg (.ok installed)) ∧
      processCreateMessage msg = .ok installed ∧
      messageCreateCollision msg = false ∧ installed.error = none ∧
      state = installed.state := by
  obtain ⟨installed, retained, core, collision, error, stateEq, _⟩ :=
    trace.exists_clean_create_with_deletions target hsg clean
  exact ⟨installed, retained, core, collision, error, stateEq⟩

end Blanc.ExecutionTrace
