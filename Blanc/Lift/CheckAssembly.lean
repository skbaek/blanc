import Blanc.Lift.Check
import Blanc.Lift.Exact

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

/-- Assemble a single-entry jump certificate from its sole node check, the
`jumpsOk` counterpart of `check_singleton` for hand-written `Jumps` modules. -/
theorem Cert.jumpsOk_singleton {code : ByteArray} {entry : Entry} {node : SFunc}
    (hnode : jumpsOkNode code [entry] node entry.frame = true) :
    Cert.jumpsOk code [(entry, node)] = true := by
  change (jumpsOkNode code [entry] node entry.frame && true) = true
  rw [hnode]
  rfl

end Blanc.Lift
