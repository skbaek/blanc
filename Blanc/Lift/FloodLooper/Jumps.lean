import Blanc.Lift.Exact
import Blanc.Lift.FloodLooper.Check

/-!
# Flood-looper valid jump destinations

Each of the two certificate entries' jumpability is a separate kernel decision,
assembled into `Cert.jumpsOk` as `lift_exact` consumes it.
-/

namespace Blanc.Lift.FloodLooper

open Jaune

theorem jumps_0 :
    jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  decide +kernel

theorem jumps_1 :
    jumpsOkNode code (Cert.entries cert) t_0007_c1 [.unk] = true := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact jumps_0
  · exact jumps_1

end Blanc.Lift.FloodLooper
