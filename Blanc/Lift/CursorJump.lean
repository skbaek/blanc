import Blanc.Lift.CursorStateCuts

namespace Blanc.Lift
open Jaune

/-- The checked original cursor at a referenced goto decodes the actual JUMP byte. -/
theorem CursorOK.jumpAt_of_jump {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {k : Nat} {cursor : Cursor}
    (ok : CursorOK code c F cursor) (tree : cursor.f = .jump k) :
    Jinst.At F.sevm.code F.pc .jump := by
  have check := ok.check
  rw [tree] at check
  rw [ok.code_eq, ok.pc_eq]
  apply byteAt_jinst_at
  simp only [checkNode] at check
  split at check
  · simp only [Bool.and_eq_true, beq_iff_eq] at check
    exact check.1.1.1
  · cases check

end Blanc.Lift
