import Blanc.Lift.Sound
import Blanc.Lift.Curve3Crv.Check
import Blanc.Lift.Curve3Crv.Prog

/-!
# Every successful Jaune execution of the deployed 3Crv runtime is a synthetic run

The deployed runtime of mainnet `0x6c3F90f043a72FA612cbac8115EE7e52BDe6E490` (Curve's 3Crv LP
token, Vyper 0.2.4; `code`, Code: 2276 bytes; SHA-256 of the bytes `bb95e5787fa843002128fbe09575a115700650f4bca6efb51e70da316497438f`,
of the hex text `267babead7107126e4a59ec00cdcc929fc9df724355d08818a8238014f6ee1bc`) with its kernel-checked certificate (`cert_check`)
instantiates the generic lifting theorem at its use sites: `lift_sound cert_check hcode hfork exc`
turns a successful execution into a run of the synthetic program `prog`, which contract proofs
reason about.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

end Blanc.Lift.Curve3Crv
