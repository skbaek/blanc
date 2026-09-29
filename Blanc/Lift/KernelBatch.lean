import Lean

/-!
# One kernel check for a conjunction of closed equalities

`kernel_rfl_and` closes a goal `a₁ = b₁ ∧ … ∧ aₙ = bₙ` with one auxiliary lemma whose proof
is `⟨Eq.refl a₁, …, Eq.refl aₙ⟩`, checked by the kernel alone: no elaborator unification is
attempted (as `Blanc.ConcreteRun`'s `kernel_rfl`), and the kernel evaluates every left side
in one declaration, so a definition several equalities depend on (a boundary of a long
concrete walk) is evaluated once instead of once per equality.  Nothing here is
contract-specific.
-/

open Lean Meta in
/-- `⟨Eq.refl a₁, …, Eq.refl aₙ⟩` for `a₁ = b₁ ∧ … ∧ aₙ = bₙ`, at most `fuel` conjuncts deep. -/
def Blanc.KernelBatch.mkReflAnd : Nat → Expr → MetaM Expr
  | 0, _ => throwError "kernel_rfl_and: too many conjuncts"
  | fuel + 1, t => do
    match t.and? with
    | some (a, b) =>
      return mkApp4 (mkConst ``And.intro) a b (← Blanc.KernelBatch.mkReflAnd fuel a)
        (← Blanc.KernelBatch.mkReflAnd fuel b)
    | none =>
      let some (α, lhs, _) := t.eq? | throwError "kernel_rfl_and: not a conjunction of equalities"
      let u ← getLevel α
      return mkApp2 (mkConst ``Eq.refl [u]) α lhs

open Lean Meta Elab Tactic in
/-- Close a conjunction of equalities by `Eq.refl` on each left side, in one kernel check. -/
elab "kernel_rfl_and" : tactic => closeMainGoalUsing `kernel_rfl_and fun type _ => do
  let type ← instantiateMVars type
  let pf ← Blanc.KernelBatch.mkReflAnd 1000 type
  let levelsInType := (collectLevelParams {} type).params
  let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma lemmaLevels type pf
  return mkConst name (lemmaLevels.map .param)
