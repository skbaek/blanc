import Blanc.Lift.Check

namespace Blanc.Lift
open Jaune

/-- Assemble a singleton certificate rooted at pc zero with an empty frame. -/
theorem Cert.check_singleton {code : ByteArray} {rets : Nat} {f : SFunc}
    (entry : checkNode code [⟨0, [], rets⟩] rets 0 [] f = true) :
    Cert.check code [(⟨0, [], rets⟩, f)] = true := by
  change (checkNode code [⟨0, [], rets⟩] rets 0 [] f && true) = true
  rw [entry]
  rfl

end Blanc.Lift
