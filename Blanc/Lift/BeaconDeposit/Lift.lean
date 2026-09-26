import Blanc.Lift.Sound
import Blanc.Lift.BeaconDeposit.Check
import Blanc.Lift.BeaconDeposit.Prog

/-!
# Every successful Jaune execution of the deployed beacon deposit runtime is a synthetic run

The deployed runtime of mainnet `0x00000000219ab540356cBB839Cbe05303d7705Fa` (`code`, 6358
bytes; SHA-256 of the bytes `5aaa8327c5765ec883224895ca02cade2871e12dad0197bdc791efc91c7ef18d`,
of Blanc's pinned hex text `scripts/reference/beacon-deposit/inputs/deployed-runtime.norm.hex`
`867e261f9811c5227ff0e2ec5d7803156f1af3428e49d6ffc041102da3050432`) with its kernel-checked
certificate (`cert_check`) instantiates the generic lifting theorem at its use sites:
`lift_sound cert_check hcode hfork exc` turns a successful execution into a run of the
synthetic program `prog`, which the contract proofs reason about.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

end Blanc.Lift.BeaconDeposit
