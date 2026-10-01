import Blanc.Lift.Check

/-! Shared assembly of a checked single-entry lift certificate. -/

namespace Blanc.Lift

open Jaune

/-- Assemble the unchanged checker from its startup condition and sole node check. -/
theorem Cert.check_singleton {code : ByteArray} {entry : Entry} {node : SFunc}
    (hstart : (entry.pc == 0 && entry.frame == []) = true)
    (hnode : checkNode code [entry] entry.rets entry.pc entry.frame node = true) :
    Cert.check code [(entry, node)] = true := by
  change ((entry.pc == 0 && entry.frame == []) &&
    (checkNode code [entry] entry.rets entry.pc entry.frame node && true)) = true
  rw [hstart, hnode]
  rfl

end Blanc.Lift
