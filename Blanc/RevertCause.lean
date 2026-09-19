-- RevertCause.lean : which step of a reverting compiled walk caused it, and
-- the exec-to-walk inversion for reverting frames.

import Blanc.Reverts
import Blanc.CompiledWalkInversion

namespace Blanc

open Jaune

/-- A gas-exact compiled walk that settles at `ex` and runs, on its way, at
least one `.next` instruction step satisfying `P`.  Rule for rule this is
`Func.RunCompiledTo` (`Blanc/Reverts.lean`); `here` designates the visited
step and continues with an ordinary walk. -/
inductive Func.RunCompiledToVisiting (P : Sevm → Devm → Ninst → Devm → Prop) :
    List Func → Sevm → Devm → Func → Execution → Prop
  | here :
    ∀ {fs sevm devm i devm' f ex},
      Ninst.RunCompiled sevm devm i devm' →
      P sevm devm i devm' →
      Func.RunCompiledTo fs sevm devm' f ex →
      Func.RunCompiledToVisiting P fs sevm devm (next i f) ex
  | next :
    ∀ {fs sevm devm i devm' f ex},
      Ninst.RunCompiled sevm devm i devm' →
      Func.RunCompiledToVisiting P fs sevm devm' f ex →
      Func.RunCompiledToVisiting P fs sevm devm (next i f) ex
  | zero :
    ∀ {fs sevm devm devm' f g ex},
      devm.stack.length < 1024 →
      Devm.PopBurnBy [0] (gVerylow + gHigh) devm devm' →
      Func.RunCompiledToVisiting P fs sevm devm' f ex →
      Func.RunCompiledToVisiting P fs sevm devm (branch f g) ex
  | succ :
    ∀ {fs sevm devm w devm' f g ex},
      w ≠ 0 →
      devm.stack.length < 1024 →
      Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm devm' →
      Func.RunCompiledToVisiting P fs sevm devm' g ex →
      Func.RunCompiledToVisiting P fs sevm devm (branch f g) ex
  | call :
    ∀ {fs sevm devm devm' k f ex},
      fs[k]? = some f →
      devm.stack.length < 1024 →
      Devm.BurnBy (gVerylow + gMid + gJumpdest) devm devm' →
      Func.RunCompiledToVisiting P fs sevm devm' f ex →
      Func.RunCompiledToVisiting P fs sevm devm (call k) ex

/-- The program-altitude visiting walk, entered at pc 0 exactly as
`Prog.RunCompiledTo` is. -/
def Prog.RunCompiledToVisiting (P : Sevm → Devm → Ninst → Devm → Prop)
    (sevm : Sevm) (devm : Devm) (p : Prog) (ex : Execution) : Prop :=
  ∃ mid, Devm.BurnBy gJumpdest devm mid ∧
    Func.RunCompiledToVisiting P (p.main :: p.aux) sevm mid p.main ex

/-- A visiting walk is a walk: forget the designation. -/
theorem Func.RunCompiledToVisiting.toRunCompiledTo
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f : Func} {ex : Execution}
    (h : Func.RunCompiledToVisiting P fs sevm devm f ex) :
    Func.RunCompiledTo fs sevm devm f ex := by
  induction h with
  | here h_step _ h_tail => exact .next h_step h_tail
  | next h_step _ ih => exact .next h_step ih
  | zero h_room h_pop _ ih => exact .zero h_room h_pop ih
  | succ h_ne h_room h_pop _ ih => exact .succ h_ne h_room h_pop ih
  | call h_get h_room h_burn _ ih => exact .call h_get h_room h_burn ih

/-- A visiting walk really runs a `P`-step.  This is the anti-vacuity face of
the relation: a constructor that designated nothing would break this proof. -/
theorem Func.RunCompiledToVisiting.exists_step
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f : Func} {ex : Execution}
    (h : Func.RunCompiledToVisiting P fs sevm devm f ex) :
    ∃ (stepPre : Devm) (instruction : Ninst) (stepPost : Devm),
      Ninst.RunCompiled sevm stepPre instruction stepPost ∧
        P sevm stepPre instruction stepPost := by
  induction h with
  | here h_step h_pred _ => exact ⟨_, _, _, h_step, h_pred⟩
  | next _ _ ih => exact ih
  | zero _ _ _ ih => exact ih
  | succ _ _ _ _ ih => exact ih
  | call _ _ _ _ ih => exact ih

/-- The program-altitude inclusion. -/
theorem Prog.RunCompiledToVisiting.toRunCompiledTo
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {devm : Devm}
    {p : Prog} {ex : Execution}
    (h : Prog.RunCompiledToVisiting P sevm devm p ex) :
    Prog.RunCompiledTo sevm devm p ex := by
  rcases h with ⟨mid, h_burn, h_run⟩
  exact ⟨mid, h_burn, h_run.toRunCompiledTo⟩

/-- A visiting walk of the deployed code is the frame's actual execution. -/
theorem Prog.RunCompiledToVisiting.exec_eq
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {pre : Devm}
    {p : Prog} {ex : Execution}
    (h : Prog.RunCompiledToVisiting P sevm pre p ex)
    (h_eq : some sevm.code.toList = p.compile) :
    exec ⟨0, sevm, pre⟩ = ex := by
  exact Prog.exec_of_runCompiledTo h.toRunCompiledTo h_eq

end Blanc
