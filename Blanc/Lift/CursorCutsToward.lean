import Blanc.Lift.CursorOccurrence
import Blanc.Lift.CursorTreeNinst

/-! Checked raw prefix cuts whose progress is witnessed by a later SSTORE. -/

namespace Blanc.Lift

open Jaune

/-- An actual later SSTORE forces progress at a checked tree whose head is
not SSTORE, regardless of the enclosing frame's final outcome. -/
theorem cursor_step_toward_sstore_noStateGas
    {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    {F target : Exec.Deriv} {κ : Cursor} (placed : CursorOK code c F κ)
    (path : Exec.Deriv.ParentPrefix F target)
    (store : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (different : ∀ tail, κ.f ≠ .next (.reg .sstore) tail)
    (hsg : F.sevm.benvStat.rules.stateGas = none) :
    ∃ (N : Exec.Deriv) (next : Cursor),
      Exec.Deriv.ParentStep N F ∧ Exec.Deriv.ParentPrefix N target ∧
      SStep c κ next ∧
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        (κ.conf F.devm) (next.conf N.devm) ∧ CursorOK code c N next := by
  cases path with
  | refl =>
      obtain ⟨tail, tree, _⟩ := placed.tree_of_sstore store
      exact (different tail tree).elim
  | step edge rest =>
      obtain ⟨next, synthetic, stateful, placed⟩ :=
        cursor_stepS_noStateGas checked placed edge hsg
      exact ⟨_, next, edge, rest, synthetic, stateful, placed⟩

end Blanc.Lift
