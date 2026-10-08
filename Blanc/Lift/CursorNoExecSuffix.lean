import Blanc.Lift.CursorCuts
import Blanc.Lift.ReachWalk

namespace Blanc.Lift

open Jaune

/-- A relative same-frame prefix transports the actual checked cursor.
The start may be any returned parent node, rather than the pc-zero root. -/
theorem cursor_reach_of_parentPrefix {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F N : Exec.Deriv}
    (path : Exec.Deriv.ParentPrefix F N) {κ : Cursor}
    (placed : CursorOK code c F κ) (fork : CoveredFork F.sevm.benvStat.fork) :
    ∃ κ', Reach Ninst.Run c.prog F.sevm (κ.conf F.devm) (κ'.conf N.devm) ∧
      CursorOK code c N κ' := by
  induction path generalizing κ with
  | refl root => exact ⟨κ, .refl, placed⟩
  | step edge _ ih =>
    obtain ⟨next, _, primitive, nextPlaced⟩ := cursor_stepS checked placed edge fork
    have same := Cursor.parentStep_sevm edge
    obtain ⟨last, rest, lastPlaced⟩ := ih nextPlaced (same ▸ fork)
    refine ⟨last, .head (primitive.mono fun run => run.toRun) ?_, lastPlaced⟩
    simpa only [same] using rest

/-- A checked closed suffix and its actual pending continuations exclude every
later same-frame external occurrence. -/
theorem CursorOK.noExecSuffix {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (placed : CursorOK code c F κ) (fork : CoveredFork F.sevm.benvStat.fork)
    {E : List Nat} (closed : ExecFreeSet c.prog E = true)
    (tree : κ.f.execFreeIn E = true)
    (continuations : ∀ f ∈ κ.K.map Cont.f, f.execFreeIn E = true) :
    ∀ N, Exec.Deriv.ParentPrefix F N → ∀ x,
      ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  intro N path x decoded
  obtain ⟨next, reach, nextPlaced⟩ := cursor_reach_of_parentPrefix checked path placed fork
  obtain ⟨tail, shape, _⟩ := nextPlaced.tree_of_exec decoded
  exact Reach.false_of_execFree closed reach ⟨x, tail, shape⟩ tree continuations

end Blanc.Lift
