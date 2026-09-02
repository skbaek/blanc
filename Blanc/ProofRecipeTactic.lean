-- ProofRecipeTactic.lean : leaf-only access to generated proof-recipe advice.

import Blanc.Tactics
import Blanc.ProofRecipesGenerated

namespace Blanc

open Lean.Elab.Tactic

def proofRecipeMatches (target : Lean.Expr)
    (recipe : ProofRecipes.Recipe) : TacticM Bool := do
  for trigger in recipe.triggers do
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
