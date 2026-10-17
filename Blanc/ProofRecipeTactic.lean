-- ProofRecipeTactic.lean : leaf-only access to generated proof-recipe advice.

import Blanc.Tactics
import Blanc.ProofRecipesGenerated

namespace Blanc

open Lean.Elab.Tactic

/-- Inspect only a direct compiler equality and its function argument. -/
def proofRecipeCompileFunction? (target : Lean.Expr) : Option Lean.Expr := do
  let lhs ← proofRecipeEqLhs? target
  match lhs with
  | .app (.app (.app (.const name _) _) _) function =>
      if name == `Blanc.Func.compile then some function else none
  | _ => none

/-- Advice-only extensions for downstream goal heads. Keeping these matches
in this leaf avoids invalidating the globally imported proof tactics.
`StepSafe` stays owned by the core `proofRecipeTriggerMatches`; only the
downstream arms below are leaf-only. -/
def proofRecipeLeafTriggerMatches (target : Lean.Expr) (trigger : String) : TacticM Bool := do
  let head := proofRecipeHeadName? target
  match trigger with
  | "goal-shape:extcodesize-compiled-step" =>
      -- One exact compiled-instruction shape and one named definition lookup.
      -- Do not normalize the goal or inspect unrelated operands.
      match target.consumeMData with
      | .app (.app (.app (.app (.const name _) _) _) instruction) _ =>
          if name != `Blanc.Ninst.RunCompiled then
            return false
          let instruction := instruction.consumeMData
          if instruction.isConstOf `Blanc.Ninst.extcodesize then
            return true
          let info ← Lean.getConstInfo `Blanc.Ninst.extcodesize
          match info.value? with
          | some value => return instruction == value.consumeMData
          | none => return false
      | _ => pure false
  | "goal-head:Lift.StaticWordChild" =>
      return head == some `Blanc.Lift.StaticWordChild
  | "goal-head:CompiledStackSafety.ResumeSafe" =>
      return head == some `Blanc.CompiledStackSafety.ResumeSafe
  | "goal-shape:finite-coalition-ledger" =>
      return proofRecipeContainsName `Blanc.ledgerSumOn target
  | "goal-shape:changed-frame-projection" =>
      -- Inspect only the equality's left side. Never reduce a source machine
      -- or unfold an alias to discover an update.
      let projectionSource? (structureName projectionName : Lean.Name)
          (index : Nat) (expr : Lean.Expr) : Option Lean.Expr :=
        match expr.consumeMData with
        | .proj name field source =>
            if name == structureName && field == index then
              some source.consumeMData else none
        | .app (.const name _) source =>
            if name == projectionName then some source.consumeMData else none
        | _ => none
      let isRe (expr : Lean.Expr) :=
        expr.getAppFn.isConstOf `Blanc.Lift.Witness.CallPrep.re &&
          expr.getAppArgs.size == 3
      let reProjection? (projectionName : Lean.Name) (index : Nat)
          (expr : Lean.Expr) : Option Lean.Expr := do
        let source ← projectionSource? `Blanc.Lift.Witness.CallPrep projectionName index expr
        if isRe source then some source else none
      match proofRecipeEqLhs? target with
      | none => return false
      | some lhs =>
          if let some source := projectionSource? `Jaune.Sevm `Jaune.Sevm.code 7 lhs then
            return source.getAppFn.isConstOf `Jaune.Sevm.withOrig &&
              source.getAppArgs.size == 2
          if (reProjection? `Blanc.Lift.Witness.CallPrep.adrs 4 lhs).isSome then
            return true
          let lhs := lhs.consumeMData
          unless lhs.getAppFn.isConstOf `Blanc.Lift.Witness.resumeCallB do
            return false
          let args := lhs.getAppArgs
          match args with
          | #[parent, offset, size, _] =>
              match reProjection? `Blanc.Lift.Witness.CallPrep.p 1 parent,
                  reProjection? `Blanc.Lift.Witness.CallPrep.oi 2 offset,
                  reProjection? `Blanc.Lift.Witness.CallPrep.os 3 size with
              | some p, some i, some s => return p == i && p == s
              | _, _, _ => return false
          | _ => return false
  | "goal-shape:machine-state-debit" =>
      return (proofRecipeEqLhs? target).bind proofRecipeHeadName? ==
        some `Jaune.State.subBal
  | "goal-shape:word-exponentiation" =>
      return (proofRecipeEqLhs? target).bind proofRecipeHeadName? ==
        some `Jaune.B256.bexp
  | "goal-shape:compile-prepend" =>
      return (proofRecipeCompileFunction? target).bind proofRecipeHeadName? ==
        some `Blanc.prepend
  | "goal-shape:compile-branch" =>
      return (proofRecipeCompileFunction? target).bind proofRecipeHeadName? ==
        some `Blanc.Func.branch
  | _ => return false

def proofRecipeMatches (target : Lean.Expr)
    (recipe : ProofRecipes.Recipe) : TacticM Bool := do
  for trigger in recipe.triggers do
    if ← proofRecipeLeafTriggerMatches target trigger then
      return true
    if ← proofRecipeTriggerMatches target trigger then
      return true
  return false

elab "blanc_suggest" : tactic =>
  withMainContext do
    let target ← Lean.instantiateMVars (← getMainTarget)
    let mut found := false
    for recipe in ProofRecipes.recipes do
      if ← proofRecipeMatches target recipe then
        found := true
        let symbols := String.intercalate ", " recipe.symbols
        Lean.logInfo m!"[proof-recipe:{recipe.id}] {recipe.preferredPath}\n\
          Registered symbols: {symbols}\n\
          Boundary: {recipe.boundary}"
    unless found do
      Lean.logInfo "blanc_suggest: no matching proof recipe\n\
        Declaration discovery: consult docs/COMMON_API.md before adding a \
        contract-local helper."

end Blanc
