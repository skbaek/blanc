-- CompiledFixedInvariance.lean : invariants for fixed compiled call tables.

import Blanc.CompiledWalkInversion
import Blanc.WordArithmetic

/-!
# Fixed-table compiled invariance

`Func.Inv` must refuse `Func.call`: its function table is universally
quantified, so an index can name an arbitrary body.  Concrete compiled proofs
already fix that table.  `Func.CompiledInv` records the corresponding
fixed-table invariant and therefore admits a sound call rule from an exact
lookup plus the callee invariant.

The `compiled_inv` tactic mirrors `func_inv` for this fixed-table relation.
At a call leaf it consumes an already-proved `Func.CompiledInv` hypothesis;
it never guesses a callee or unfolds a table lookup.
-/

namespace Blanc

open Jaune

/-- A successful compiled walk against one fixed function table carries an
observable from entry to exit. -/
def Func.CompiledInv {ξ : Type}
    (fs : List Func) (entry exit : Devm → ξ) (body : Func) : Prop :=
  ∀ {sevm pre post},
    Func.RunCompiledTo fs sevm pre body (.ok post) →
      entry pre = exit post

namespace Func.CompiledInv

theorem of_run {ξ : Type} {fs : List Func} {entry exit : Devm → ξ}
    {body : Func} {sevm : Sevm} {pre post : Devm}
    (invariant : Func.CompiledInv fs entry exit body)
    (run : Func.RunCompiledTo fs sevm pre body (.ok post)) :
    entry pre = exit post :=
  invariant run

theorem last {ξ : Type} {fs : List Func} {entry exit : Devm → ξ}
    {terminal : Linst}
    (invariant : Linst.Inv entry exit terminal) :
    Func.CompiledInv fs entry exit (.last terminal) := by
  intro sevm pre post run
  exact invariant (runCompiledTo_last_inv run)

theorem next {ξ : Type} {fs : List Func} {entry exit : Devm → ξ}
    {instruction : Ninst} {body : Func}
    (instructionInv : Ninst.Inv entry instruction)
    (bodyInv : Func.CompiledInv fs entry exit body) :
    Func.CompiledInv fs entry exit (.next instruction body) := by
  intro sevm pre post run
  obtain ⟨bodyPre, instructionRun, bodyRun⟩ :=
    runCompiledTo_next_inv run
  exact (instructionInv (Ninst.Run.of_runCompiled instructionRun)).trans
    (bodyInv bodyRun)

theorem prepend {ξ : Type} {fs : List Func} {entry exit : Devm → ξ}
    {line : Line} {body : Func}
    (lineInv : Line.Inv entry line)
    (bodyInv : Func.CompiledInv fs entry exit body) :
    Func.CompiledInv fs entry exit (line +++ body) := by
  intro sevm pre post run
  obtain ⟨bodyPre, lineRun, bodyRun⟩ := runCompiledTo_prepend_inv run
  exact (lineInv lineRun).trans (bodyInv bodyRun)

theorem branch {ξ : Type} {fs : List Func} {entry exit : Devm → ξ}
    [PopBurn.Inv entry] {left right : Func}
    (leftInv : Func.CompiledInv fs entry exit left)
    (rightInv : Func.CompiledInv fs entry exit right) :
    Func.CompiledInv fs entry exit (.branch left right) := by
  intro sevm pre post run
  cases run with
  | zero room pop tail =>
      exact (PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy pop)).trans
        (leftInv tail)
  | succ nonzero room pop tail =>
      exact (PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy pop)).trans
        (rightInv tail)

theorem call {ξ : Type} {fs : List Func} {entry exit : Devm → ξ}
    [Burn.Inv entry] {index : Nat} {body : Func}
    (lookup : fs[index]? = some body)
    (bodyInv : Func.CompiledInv fs entry exit body) :
    Func.CompiledInv fs entry exit (.call index) := by
  intro sevm pre post run
  obtain ⟨bodyPre, callBurn, bodyRun⟩ :=
    runCompiledTo_call_inv lookup run
  exact (Burn.Inv.inv (Devm.Burn.of_burnBy callBurn)).trans
    (bodyInv bodyRun)

end Func.CompiledInv

/-! ## Complete opt-in log support for ordinary arithmetic walks -/

namespace LogOutputHinv

syntax "show_hinv_logs_ternary" : tactic
macro_rules
  | `(tactic| show_hinv_logs_ternary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      exact
        (Devm.diffBurn_of_applyTernary run).choose_spec.choose_spec.choose_spec.logs)

scoped instance : PopBurn.Inv Devm.logs := ⟨fun run => run.logs⟩
scoped instance : Burn.Inv Devm.logs := ⟨fun run => run.logs⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.mul := by
  show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.sub := by
  show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.div := by
  show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.mod := by
  show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.addmod := by
  show_hinv_logs_ternary
scoped instance : Rinst.Hinv Devm.logs Rinst.mulmod := by
  show_hinv_logs_ternary
scoped instance : Rinst.Hinv Devm.logs Rinst.xor := by
  show_hinv_logs_binary

scoped instance : Rinst.Hinv Devm.logs Rinst.returndatasize := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs

scoped instance : Rinst.Hinv Devm.logs Rinst.mload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨offset, popped⟩, pop, run⟩
  rcases Except.bind_eq_ok run with ⟨burned, burn, pushed⟩
  rcases Devm.pop_of_popToNat pop with ⟨actual, popDiff⟩
  have burnDiff := Devm.burn_of_chargeGas burn
  have pushDiff := Devm.push_of_push pushed
  exact ((popDiff.logs.trans burnDiff.logs).trans rfl).trans pushDiff.logs⟩

scoped instance : Linst.Hinv Devm.logs Devm.logs Linst.revert := by
  constructor
  intro sevm pre post run
  simp only [Linst.Run, Linst.run] at run
  rcases Except.bind_eq_ok run with ⟨s1, popStart, run⟩
  rcases Except.bind_eq_ok run with ⟨s2, popSize, run⟩
  rcases Except.bind_eq_ok run with ⟨s3, burn, impossible⟩
  contradiction

end LogOutputHinv

/-! ## Structural automation -/

open Lean
open Lean.Elab.Tactic
open Qq

private def compiledInvTactic : Nat → TacticM Unit
  | 0 =>
      Lean.throwError "compiled_inv: structural recursion limit reached"
  | fuel + 1 => withMainContext do
    let target : Q(Prop) ← getMainTarget
    match target with
    | ~q(@Func.CompiledInv $ξx $fsx $entryx $exitx $bodyx) =>
      match bodyx with
      | ~q(_ +++ _) =>
          Lean.Expr.apply q(@Func.CompiledInv.prepend)
          lineInv
          compiledInvTactic fuel
      | _ =>
        let body : Q(Func) ← Lean.Meta.whnf bodyx
        match body with
        | ~q(Func.next _ _) =>
            Lean.Expr.apply q(@Func.CompiledInv.next)
            instInv
            compiledInvTactic fuel
        | ~q(Func.last _) =>
            Lean.Expr.apply q(@Func.CompiledInv.last)
            hopInv
        | ~q(Func.branch _ _) =>
            Lean.Expr.apply q(@Func.CompiledInv.branch)
            compiledInvTactic fuel
            compiledInvTactic fuel
        | ~q(Func.call _) =>
            evalTactic (← `(tactic| assumption))
        | _ =>
            let rendered ← Lean.Meta.ppExpr body
            Lean.throwError m!"compiled_inv: no rule for{Lean.indentD rendered}"
    | _ =>
        Lean.throwError
          m!"compiled_inv: the goal is not a `Func.CompiledInv`{Lean.indentExpr target}"

/-- Prove a fixed-table compiled invariant structurally.  Call leaves must
already be present as exact `Func.CompiledInv` hypotheses. -/
elab "compiled_inv" : tactic => compiledInvTactic 65536

end Blanc
