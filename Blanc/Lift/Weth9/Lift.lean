import Blanc.Lift.Sound
import Blanc.Lift.Weth9.Check

/-!
# Gate G1: every successful Jaune execution of the WETH9 runtime is a synthetic run

The pinned deployed WETH9 runtime (`code`, 3124 bytes, SHA-256
`5566bf50796faf93c9b6f6adacd3b32c70bfe16b48ffc59db6cd144cbdc89739`) with its
kernel-checked certificate (`cert_check`) instantiates the generic lifting
theorem.  The synthetic program is `prog`; phase-2 proofs reason about it.
-/

namespace Blanc.Lift.Weth9

open Jaune

/-- The lifted WETH9 program. -/
abbrev prog : List SFunc := Cert.prog cert

/-- **G1.** On a covered fork, a successful execution of the WETH9 runtime from
pc `0` with an empty operand stack is a run of the lifted program. -/
theorem exec_lift {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstack : pre.stack = []) (exc : Exec 0 sevm pre (.ok post)) :
    SProg.Run prog sevm pre post :=
  lift_sound cert_check hcode hfork hstack exc

end Blanc.Lift.Weth9
