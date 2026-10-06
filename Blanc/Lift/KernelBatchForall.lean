import Blanc.Lift.KernelBatch

/-!
# One kernel check for a universally quantified conjunction of equalities

`kernel_forall_rfl_and` closes `∀ x₁ … xₘ, a₁ = b₁ ∧ … ∧ aₙ = bₙ` with one auxiliary lemma whose
proof is `fun x₁ … xₘ => ⟨Eq.refl a₁, …, Eq.refl aₙ⟩`, checked by the kernel alone (as
`kernel_rfl_and`, under binders): the kernel evaluates every left side with the bound
variables free, in one declaration.  Nothing here is contract-specific.
-/

open Lean Meta Elab Tactic in
/-- Close `∀ xs, a₁ = b₁ ∧ … ∧ aₙ = bₙ` by `Eq.refl` on each left side, in one kernel check. -/
elab "kernel_forall_rfl_and" : tactic =>
  closeMainGoalUsing `kernel_forall_rfl_and fun type _ => do
    let type ← instantiateMVars type
    let pf ← forallTelescope type fun xs body => do
      mkLambdaFVars xs (← Blanc.KernelBatch.mkReflAnd 1000 body)
    let levelsInType := (collectLevelParams {} type).params
    let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
    let name ← withOptions (Elab.async.set · false) do
      mkAuxLemma lemmaLevels type pf
    return mkConst name (lemmaLevels.map .param)
