import Blanc.Lift.Exact
import Blanc.Lift.SystemDrainer.Check

/-!
# System-drainer valid jump destinations

The drainer has one straight-line entry; its jumpability is one kernel decision.
-/

namespace Blanc.Lift.SystemDrainer

open Jaune

theorem jumps_0 :
    jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  exact jumps_0

end Blanc.Lift.SystemDrainer
