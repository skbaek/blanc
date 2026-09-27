import Blanc.Lift.LidoCircuitBreakerDeployed.Prog
import Blanc.Lift.InvWalkWorld

/-! The entries the two Registry writers' walks call never halt the frame: each
ends only in `revert` or an internal return.  One kernel check over their
closure, kept in its own module so no language-server file elaborates it. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Blanc.Lift

/-- The call closure of the `registerPauser` body (21) and the `pause` body (13). -/
def writerNoHalt : List Nat :=
  [2, 3, 4, 5, 7, 13, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 32, 33, 37, 38, 39, 40, 42]

theorem writerNoHalt_set : NoHaltSet prog writerNoHalt = true := by
  decide +kernel

end Blanc.Lift.LidoCircuitBreakerDeployed
