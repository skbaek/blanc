import Blanc.RootedExecution

/-!
Line-level discharge of `NonExecInstruction`: a structural Boolean test that
reduces on each instruction constructor even under symbolic operands
(`pushB256 w`), so `∀ n ∈ line, NonExecInstruction n` for a concrete line is
`NonExecInstruction.forall_of_all rfl` rather than a per-site `simp only` list.
-/

namespace Blanc

open Jaune

/-- Structural Boolean test for `NonExecInstruction`: `false` exactly on `.exec`. -/
def Ninst.isNonExec : Ninst → Bool
  | .exec _ => false
  | _ => true

theorem NonExecInstruction.of_isNonExec {instruction : Ninst}
    (h : Ninst.isNonExec instruction = true) : NonExecInstruction instruction :=
  ⟨by intro x hx; subst hx; cases h⟩

/-- A concrete line has no execution instruction: `forall_of_all rfl`. -/
theorem NonExecInstruction.forall_of_all {line : List Ninst}
    (h : line.all Ninst.isNonExec = true) : ∀ n ∈ line, NonExecInstruction n :=
  fun _ hn => of_isNonExec (List.all_eq_true.mp h _ hn)

end Blanc
