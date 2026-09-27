import Jaune.Exec

/-!
Concrete stepping glue for kernel-checked existential executions.

`stepN n evm` follows at most `n` `.cont` outcomes of Jaune's own `Evm.step`
and reports `none` on any other outcome, so a closed instance
`stepN n evm = some evm'` can be checked by kernel evaluation of Jaune's
semantics, without a second step function. The theorems here compose such a
run into the canonical `Exec` derivation, directly or across one `.spawn`
through Jaune's own `runOk` constructor. Nothing here is contract-specific.
-/

namespace Blanc.ConcreteRun

open Jaune

/-- Follow `n` continuing steps of `Evm.step`; any halt or spawn is `none`. -/
def stepN : Nat → Evm → Option Evm
  | 0, evm => some evm
  | n + 1, evm =>
    match Evm.step evm with
    | .cont pc devm => stepN n ⟨pc, evm.sta, devm⟩
    | _ => none

/-- Continuing steps never change the static environment. -/
theorem stepN_sta : ∀ {n : Nat} {evm evm' : Evm},
    stepN n evm = some evm' → evm'.sta = evm.sta
  | 0, evm, evm', h => by
    simp only [stepN, Option.some.injEq] at h
    rw [h]
  | n + 1, evm, evm', h => by
    simp only [stepN] at h
    split at h
    · have hs := stepN_sta h
      exact hs
    · cases h

/-- Runs compose. -/
theorem stepN_add : ∀ (m : Nat) {n : Nat} {evm evm' evm'' : Evm},
    stepN m evm = some evm' → stepN n evm' = some evm'' →
    stepN (m + n) evm = some evm''
  | 0, n, evm, evm', evm'', h1, h2 => by
    simp only [stepN, Option.some.injEq] at h1
    subst h1
    simpa using h2
  | m + 1, n, evm, evm', evm'', h1, h2 => by
    rw [Nat.add_right_comm]
    simp only [stepN] at h1 ⊢
    split at h1
    · rename_i pc devm hstep
      exact stepN_add m h1 h2
    · cases h1

/-- A continuing run extends any derivation at its end state backwards to its
start state. -/
def Exec.ofStepN : ∀ (n : Nat) {evm evm' : Evm} {ex : Execution},
    stepN n evm = some evm' →
    Exec evm'.pc evm'.sta evm'.dyna ex → Exec evm.pc evm.sta evm.dyna ex
  | 0, evm, evm', ex, h, d => by
    simp only [stepN, Option.some.injEq] at h
    subst h
    exact d
  | n + 1, evm, evm', ex, h, d => by
    simp only [stepN] at h
    split at h
    · rename_i pc devm hstep
      exact Exec.cont hstep (Exec.ofStepN n (evm := ⟨pc, evm.sta, devm⟩) h d)
    · exact absurd h (by simp)

/-- The `Prop` form of `Exec.ofStepN`. -/
theorem exec_of_stepN {n : Nat} {evm evm' : Evm} {ex : Execution}
    (h : stepN n evm = some evm')
    (d : Nonempty (Exec evm'.pc evm'.sta evm'.dyna ex)) :
    Nonempty (Exec evm.pc evm.sta evm.dyna ex) :=
  d.elim fun d => ⟨Exec.ofStepN n h d⟩

/-- A run that ends at a halting step is a complete derivation. -/
theorem exec_of_stepN_halt {n : Nat} {evm evm' : Evm} {ex : Execution}
    (h : stepN n evm = some evm') (hhalt : Evm.step evm' = .halt ex) :
    Nonempty (Exec evm.pc evm.sta evm.dyna ex) :=
  exec_of_stepN h ⟨Exec.halt hhalt⟩

/-- A run that ends at a spawn whose child runs and settles successfully, and
whose parent then continues to `ex`, is a derivation of `ex` (Jaune's
`Exec.runOk`). -/
theorem exec_of_stepN_spawn_runOk {n : Nat} {evm evm' : Evm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm} {raw : Execution}
    {devm' : Devm} {ex : Execution}
    (h : stepN n evm = some evm')
    (hspawn : Evm.step evm' = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Nonempty (Exec cevm.pc cevm.sta cevm.dyna raw))
    (hsettle : rsm.run (f.settle raw) = .ok devm')
    (rest : Nonempty (Exec pc' evm.sta devm' ex)) :
    Nonempty (Exec evm.pc evm.sta evm.dyna ex) := by
  have hsta := stepN_sta h
  refine exec_of_stepN h ?_
  rcases child with ⟨child⟩
  rcases rest with ⟨rest⟩
  rw [hsta]
  exact ⟨Exec.runOk (by rw [← hsta]; exact hspawn) henter child hsettle rest⟩

/-- A kernel-decidable success test yields the run equation with the end state
named by `stepN` itself. -/
theorem stepN_eq_get {n : Nat} {evm : Evm} (h : (stepN n evm).isSome = true) :
    stepN n evm = some ((stepN n evm).get h) :=
  (Option.some_get h).symm

open Lean Meta Elab Tactic in
/-- Close `a = b` with `Eq.refl a`, checked by the kernel alone (the way
`decide +kernel` checks its proof): no elaborator unification of `a` with `b`
is attempted, so a closed concrete run is evaluated only by the kernel. -/
elab "kernel_rfl" : tactic => closeMainGoalUsing `kernel_rfl fun type _ => do
  let type ← instantiateMVars type
  let some (α, lhs, _) := type.eq? | throwError "kernel_rfl: the goal is not an equality"
  let u ← getLevel α
  let pf := mkApp2 (mkConst ``Eq.refl [u]) α lhs
  let levelsInType := (collectLevelParams {} type).params
  let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma lemmaLevels type pf
  return mkConst name (lemmaLevels.map .param)

end Blanc.ConcreteRun
