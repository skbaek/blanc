import Blanc.Lift.Exact
import Blanc.Lift.BeaconRoots.Check

namespace Blanc.Lift.BeaconRoots

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

end Blanc.Lift.BeaconRoots
