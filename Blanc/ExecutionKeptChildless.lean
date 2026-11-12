import Blanc.ExecutionKeptFrames
import Jaune.ExecChronology

/-! Retention for childless same-frame runs, without a byte-offset opcode scan. -/
namespace Blanc
open Jaune

theorem Exec.keptAt_nil_of_parent_noExec (R : Exec.Deriv) (a : Adr)
    (none : ∀ n, Exec.Deriv.ParentPrefix R n → ∀ x, ¬ Ninst.At n.sevm.code n.pc (.exec x)) :
    Exec.keptAt a R.exc = [] := by
  have go : ∀ n : Exec.Deriv, Exec.Deriv.ParentPrefix R n → Exec.keptAt a n.exc = [] := by
    intro n
    obtain ⟨pc, s, d, out, run⟩ := n
    intro pref
    revert pref
    induction run with
    | halt _ | doneErr _ _ _ | runErr _ _ _ _ => intro _; rw [Exec.keptAt]
    | cont step next ih =>
        intro pref
        rw [Exec.keptAt]
        exact ih (pref.snoc (.cont step next))
    | doneOk step _ _ _ _ | runOk step _ _ _ _ _ _ =>
        intro pref
        obtain ⟨x, atX, _, _⟩ := Evm.step_spawn_inv step
        exact ((none _ pref x) atX).elim
  exact go R (.refl _)

theorem Exec.keptAt_settled_away {a : Adr} {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {childEvm : Evm} {raw out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post) (next : Exec pc' sevm post out)
    (settles : Frame.settlementCommits frame raw = true) (away : childEvm.sta.currentTarget ≠ a) :
    Exec.keptAt a (.runOk step enter child resumed next) = Exec.keptAt a child ++ Exec.keptAt a next := by
  rw [Exec.keptAt, dite_eq_left settles, ite_eq_right away]


end Blanc
