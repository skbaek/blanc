import Blanc.Lift.Exact
import Blanc.Lift.BeaconRoots.Check
import Blanc.Lift.CheckAssembly

namespace Blanc.Lift.BeaconRoots

open Jaune

theorem jumps_0 :
    jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true :=
  Cert.jumpsOk_singleton jumps_0

end Blanc.Lift.BeaconRoots
