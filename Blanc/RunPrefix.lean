import Blanc.ExecutionOccurrence
import Blanc.GasErasure

/-!
Contract-neutral loose walk prefixes with source-path accumulation.

`Func.RunPrefix` exposes, for a successful source `Func.Run`, the loose walk
prefix that reaches an intermediate cut: the same step rules as `Func.Run` but
ending at an explicit target `(path, state, body)` instead of a terminal
result. Every crossed `.next` carries a `Ninst.gasFree` certificate, so the
DRIP prefix transport can replay a prefix against the actual `Exec` with
per-step `EqModGas` congruence. Path accumulation mirrors
`Func.sourceSites`: each crossed instruction appends `.rest`, each taken
branch arm appends `.branchLeft`/`.branchRight`, and each call resets to the
callee entry `⟨j, []⟩`.
-/

namespace Blanc

open Jaune

/-- A loose gas-free walk prefix from `(path, state, body)` to an explicit
target `(target, t, rest)`. The extended path (`steps ++ [.rest]` and its
branch/call siblings) sits in the *premise*, never computed in a conclusion,
so `rcases` on a prefix never has to reduce a path. -/
inductive Func.RunPrefix (fs : List Func) (e : Sevm) :
    Prog.SourcePath → Devm → Func → Prog.SourcePath → Devm → Func → Prop
  | refl {path s body} : RunPrefix fs e path s body path s body
  | next {k steps s i s' f target t rest} :
      Ninst.gasFree i = true →
      Ninst.Run e s i s' →
      RunPrefix fs e ⟨k, steps ++ [.rest]⟩ s' f target t rest →
      RunPrefix fs e ⟨k, steps⟩ s (.next i f) target t rest
  | zero {k steps s s' f g target t rest} :
      Devm.PopBurn [0] s s' →
      RunPrefix fs e ⟨k, steps ++ [.branchLeft]⟩ s' f target t rest →
      RunPrefix fs e ⟨k, steps⟩ s (.branch f g) target t rest
  | succ {k steps s w s' s'' f g target t rest} :
      w ≠ 0 →
      Devm.PopBurn [w] s s' →
      Devm.Burn s' s'' →
      RunPrefix fs e ⟨k, steps ++ [.branchRight]⟩ s'' g target t rest →
      RunPrefix fs e ⟨k, steps⟩ s (.branch f g) target t rest
  | call {path s s' j f target t rest} :
      fs[j]? = some f →
      Devm.Burn s s' →
      RunPrefix fs e ⟨j, []⟩ s' f target t rest →
      RunPrefix fs e path s (.call j) target t rest

/-- A gas-free line run is a prefix ending at the line's end. Crossing `l`
appends one `.rest` per instruction. -/
theorem Func.RunPrefix.line {fs : List Func} {e : Sevm} {k : Nat}
    {steps : List Prog.SourceStep} {s : Devm} {l : Line} {mid : Devm} {f : Func}
    (hline : Line.Run e s l mid) (hfree : Line.gasFree l = true) :
    RunPrefix fs e ⟨k, steps⟩ s (l +++ f)
      ⟨k, steps ++ List.replicate l.length .rest⟩ mid f := by
  induction l generalizing s steps with
  | nil =>
    have hmid : mid = s := by cases hline; rfl
    subst mid
    show RunPrefix fs e ⟨k, steps⟩ s f ⟨k, steps ++ []⟩ s f
    rw [List.append_nil]
    exact RunPrefix.refl
  | cons hd tl ih =>
    cases hline with
    | cons hstep htail =>
      simp only [Line.gasFree, Bool.and_eq_true] at hfree
      have hpath : steps ++ List.replicate (hd :: tl).length .rest =
          (steps ++ [.rest]) ++ List.replicate tl.length .rest := by
        rw [List.length_cons, List.replicate_succ,
          ← List.singleton_append, ← List.append_assoc]
      rw [hpath]
      exact RunPrefix.next hfree.1 hstep (ih (steps := steps ++ [.rest]) htail hfree.2)

/-- Prefixes compose. -/
theorem Func.RunPrefix.trans {fs : List Func} {e : Sevm}
    {p1 : Prog.SourcePath} {s1 : Devm} {b1 : Func}
    {p2 : Prog.SourcePath} {s2 : Devm} {b2 : Func}
    {p3 : Prog.SourcePath} {s3 : Devm} {b3 : Func}
    (h1 : RunPrefix fs e p1 s1 b1 p2 s2 b2)
    (h2 : RunPrefix fs e p2 s2 b2 p3 s3 b3) :
    RunPrefix fs e p1 s1 b1 p3 s3 b3 := by
  induction h1 with
  | refl => exact h2
  | next c1 c2 _ ih => exact RunPrefix.next c1 c2 (ih h2)
  | zero c1 _ ih => exact RunPrefix.zero c1 (ih h2)
  | succ c1 c2 c3 _ ih => exact RunPrefix.succ c1 c2 c3 (ih h2)
  | call c1 c2 _ ih => exact RunPrefix.call c1 c2 (ih h2)

/-- Splicing a completion run onto a prefix recovers the full run. -/
theorem Func.Run.of_prefix {fs : List Func} {e : Sevm}
    {cur : Prog.SourcePath} {s : Devm} {body : Func}
    {tgt : Prog.SourcePath} {t : Devm} {rest : Func} {r : Devm}
    (hpre : Func.RunPrefix fs e cur s body tgt t rest)
    (hrun : Func.Run fs e t rest r) :
    Func.Run fs e s body r := by
  induction hpre with
  | refl => exact hrun
  | next _ hstep _ ih => exact Func.Run.next hstep (ih hrun)
  | zero hpop _ ih => exact Func.Run.zero hpop (ih hrun)
  | succ hne hpop hburn _ ih => exact Func.Run.succ hne hpop hburn (ih hrun)
  | call hget hburn _ ih => exact Func.Run.call hget hburn (ih hrun)

/-- Introduction twin of `run_prepend_elim`: splitting a run over `l +++ p`
also exposes the gas-free line prefix. -/
theorem Func.RunPrefix.of_run_prepend {fs : List Func} {e : Sevm} {s : Devm}
    {l : Line} {p : Func} {r : Devm} {k : Nat} {steps : List Prog.SourceStep}
    (hfree : Line.gasFree l = true) (h : Func.Run fs e s (l +++ p) r) :
    ∃ s', Line.Run e s l s' ∧ Func.Run fs e s' p r ∧
      RunPrefix fs e ⟨k, steps⟩ s (l +++ p)
        ⟨k, steps ++ List.replicate l.length .rest⟩ s' p := by
  rcases Blanc.of_run_prepend _ _ h with ⟨s', hline, hrun⟩
  exact ⟨s', hline, hrun, RunPrefix.line hline hfree⟩

/-- Introduction twin of `of_run_branch`: the taken arm also exposes its
one-step branch prefix. -/
theorem Func.RunPrefix.of_run_branch {fs : List Func} {e : Sevm} {s : Devm}
    {r : Devm} {f g : Func} {k : Nat} {steps : List Prog.SourceStep}
    (h : Func.Run fs e s (.branch f g) r) :
    (∃ s', Devm.PopBurn [0] s s' ∧ Func.Run fs e s' f r ∧
      RunPrefix fs e ⟨k, steps⟩ s (.branch f g)
        ⟨k, steps ++ [.branchLeft]⟩ s' f)
    ∨ (∃ w s' s'', w ≠ 0 ∧ Devm.PopBurn [w] s s' ∧ Devm.Burn s' s'' ∧
      Func.Run fs e s'' g r ∧
      RunPrefix fs e ⟨k, steps⟩ s (.branch f g)
        ⟨k, steps ++ [.branchRight]⟩ s'' g) := by
  rcases Blanc.of_run_branch h with ⟨s', hpop, hrun⟩ | ⟨w, s', s'', hne, hpop, hburn, hrun⟩
  · exact Or.inl ⟨s', hpop, hrun, RunPrefix.zero hpop RunPrefix.refl⟩
  · exact Or.inr ⟨w, s', s'', hne, hpop, hburn, hrun,
      RunPrefix.succ hne hpop hburn RunPrefix.refl⟩

/-- Introduction twin of `of_run_call`: entering the callee also exposes its
one-step call prefix. -/
theorem Func.RunPrefix.of_run_call {fs : List Func} {e : Sevm} {s : Devm}
    {r : Devm} {j : Nat} {path : Prog.SourcePath}
    (h : Func.Run fs e s (.call j) r) :
    ∃ f s', fs[j]? = some f ∧ Devm.Burn s s' ∧ Func.Run fs e s' f r ∧
      RunPrefix fs e path s (.call j) ⟨j, []⟩ s' f := by
  rcases Blanc.of_run_call h with ⟨f, s', hget, hburn, hrun⟩
  exact ⟨f, s', hget, hburn, hrun, RunPrefix.call hget hburn RunPrefix.refl⟩

/-- A gas-free walk prefix never moves ETH. -/
theorem Func.RunPrefix.getBal_eq {fs : List Func} {e : Sevm}
    {path target : Prog.SourcePath} {s t : Devm} {body rest : Func}
    (walk : Func.RunPrefix fs e path s body target t rest) :
    Devm.getBal t = Devm.getBal s := by
  induction walk with
  | refl => rfl
  | @next k steps s i s' f target t rest free step _ ih =>
      have stepEq : Devm.getBal s = Devm.getBal s' := by
        cases i with
        | reg r => exact (inferInstance : Ninst.Hinv Devm.getBal (.reg r)).inv step
        | push xs p =>
            exact (inferInstance : Ninst.Hinv Devm.getBal (.push xs p)).inv step
        | exec x => simp [Ninst.gasFree] at free
        | dupn imm => simp [Ninst.gasFree] at free
        | swapn imm => simp [Ninst.gasFree] at free
        | exchange imm => simp [Ninst.gasFree] at free
      exact ih.trans stepEq.symm
  | zero pop _ ih =>
      exact ih.trans (funext fun a => getBal_eq_of_state_eq pop.state.symm a)
  | succ _ pop burn _ ih =>
      exact ih.trans (funext fun a =>
        getBal_eq_of_state_eq (pop.state.trans burn.state).symm a)
  | call _ burn _ ih =>
      exact ih.trans (funext fun a => getBal_eq_of_state_eq burn.state.symm a)

end Blanc
