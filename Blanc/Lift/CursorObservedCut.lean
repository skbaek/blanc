import Blanc.Lift.Cursor
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionNoninterference

/-! Continue an original observed execution from an already placed cursor. -/
namespace Blanc.Lift

open Jaune

/-- A checked interior cursor retains the original root's child population and
raw edges through any later same-frame node, regardless of the frame outcome. -/
theorem CursorOK.observedReach_from_cut {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {root start stop : Exec.Deriv}
    {cursor : Cursor} (placed : CursorOK code c start cursor)
    (earlier : Exec.Deriv.ParentPrefix root start)
    (later : Exec.Deriv.ParentPrefix start stop)
    (hsg : root.sevm.benvStat.rules.stateGas = none) :
    ∃ next, ObservedReach (StepIn root) (Cursor.RawEdgeAt code c root stop)
      c.prog root.sevm (cursor.conf start.devm) (next.conf stop.devm) ∧
      CursorOK code c stop next := by
  induction later generalizing cursor with
  | refl => exact ⟨cursor, .refl, placed⟩
  | step edge tail ih =>
      have env := Exec.Deriv.ParentPrefix.sevm_eq earlier
      obtain ⟨middle, synthetic, primitive, nextPlaced⟩ :=
        cursor_stepS_noStateGas checked placed edge (env ▸ hsg)
      obtain ⟨next, suffix, finalPlaced⟩ := ih nextPlaced (earlier.snoc edge)
      refine ⟨next, .head ⟨?_, ?_⟩ suffix, finalPlaced⟩
      · rw [← env]
        exact primitive.mono fun h => h.mono fun _ _ _ _ _ child r member =>
          List.mem_cons_of_mem _
            (Exec.mem_rawFrameDescendants_of_parentPrefix earlier (child r member))
      · exact ⟨_, _, cursor, middle, earlier, edge, tail, env,
          rfl, rfl, synthetic, placed, nextPlaced⟩

end Blanc.Lift
