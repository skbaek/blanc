import Blanc.ProofRecipeTactic
import Blanc.CompiledStackSafety

/-! Actual leaf discovery controls. Elaborate this script with current imports;
the pure Python registry gate does not execute these checks. -/

namespace Blanc

open Jaune Lean.Elab.Tactic CompiledStackSafety

-- These checks intentionally observe the goal without changing it.
set_option linter.unusedTactic false

private def checkRecipe (id : String) (expected : Bool) : TacticM Unit := do
  let target ← Lean.instantiateMVars (← getMainTarget)
  let some recipe := ProofRecipes.recipes.find? (fun r => r.id == id)
    | throwError "missing recipe {id}"
  let actual ← proofRecipeMatches target recipe
  unless actual == expected do
    throwError "recipe {id}: expected {expected}, got {actual}"

private def checkTrigger (trigger : String) (leaf legacy : Bool) : TacticM Unit := do
  let target ← Lean.instantiateMVars (← getMainTarget)
  unless (← proofRecipeLeafTriggerMatches target trigger) == leaf do
    throwError "wrong leaf result for {trigger}"
  unless (← proofRecipeTriggerMatches target trigger) == legacy do
    throwError "wrong legacy result for {trigger}"

private def checkOneDevm : TacticM Unit := do
  unless (← proofRecipeLocalTypeCount `Jaune.Devm) == 1 do
    throwError "new-head control must use exactly one actual Devm local"

-- Actual positive StepSafe goal, with no assumed safety proposition.
example (pre : Devm) : StepSafe (fun _ _ => True) (.halt (.ok pre)) := by
  run_tac checkOneDevm
  run_tac checkTrigger "goal-head:CompiledStackSafety.StepSafe" true false
  run_tac checkTrigger "goal-head:CompiledStackSafety.ResumeSafe" false false
  run_tac checkTrigger "goal-head:Unregistered.StackSafety" false false
  run_tac checkRecipe "same-frame-stack-certificate" true
  blanc_suggest
  intro err post impossible
  cases impossible

-- Actual positive ResumeSafe goal; room constructs the resume, not an assumed run.
example (parent : Devm) (room : parent.stack.length < 1024) :
    ResumeSafe (fun _ _ => True) 0 (.call parent 0 0) := by
  run_tac checkOneDevm
  run_tac checkTrigger "goal-head:CompiledStackSafety.ResumeSafe" true false
  run_tac checkTrigger "goal-head:CompiledStackSafety.StepSafe" false false
  run_tac checkRecipe "same-frame-stack-certificate" true
  blanc_suggest
  exact resume_call_safe parent 0 0 room (by intros; trivial)

-- A representative old goal head still dispatches to the original matcher.
example (sevm : Sevm) (pre : Devm) :
    Func.RunCompiled [] sevm pre (.last .stop) pre := by
  run_tac checkTrigger "goal-head:Func.RunCompiled" false true
  run_tac checkRecipe "runcompiled-construction" true
  run_tac checkRecipe "same-frame-stack-certificate" false
  blanc_suggest
  exact .last rfl

-- An old implication-premise matcher is preserved too.
example (sevm : Sevm) (pre post : Devm) (line : Line) :
    Line.Run sevm pre line post → True := by
  run_tac checkTrigger "implication-premise:Line.Run" false true
  run_tac checkRecipe "line-run-split" true
  run_tac checkRecipe "same-frame-stack-certificate" false
  blanc_suggest
  intro _
  trivial

-- False target head and unknown trigger stay false through both dispatchers.
example : True := by
  run_tac checkTrigger "goal-head:CompiledStackSafety.StepSafe" false false
  run_tac checkTrigger "goal-head:CompiledStackSafety.ResumeSafe" false false
  run_tac checkTrigger "goal-head:Unregistered.StackSafety" false false
  run_tac checkRecipe "same-frame-stack-certificate" false
  blanc_suggest
  trivial

/-- error: wrong leaf result for goal-head:Unregistered.StackSafety -/
#guard_msgs in
example : True := by
  run_tac checkTrigger "goal-head:Unregistered.StackSafety" true false
  trivial

/-- error: recipe same-frame-stack-certificate: expected true, got false -/
#guard_msgs in
example : True := by
  run_tac checkRecipe "same-frame-stack-certificate" true
  trivial

end Blanc
