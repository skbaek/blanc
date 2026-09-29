import Blanc.Lift.LidoCircuitBreakerDeployed.FrameMem
import Blanc.Lift.ReachWalk

/-! Certificate facts for the reach walk of `Reentry.lean`, kernel-checked in their
own module so no language-server file elaborates them: every entry except the
dispatcher (0), the `pause` body (13) and the `pause` wrapper (49) is exec-free
and referenced only within that set, and the dispatcher is a goto tree into the
selector wrappers. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Blanc.Lift

/-- Every entry except 0, 13 and 49. -/
def execFreeEntries : List Nat :=
  (List.range 60).filter fun k => k != 0 && k != 13 && k != 49

theorem execFreeEntries_set : ExecFreeSet prog execFreeEntries = true := by
  decide +kernel

theorem entry0_gotoTree : t_0000_c0.gotoTree wrapperEntries instMemSafe = true := by
  decide +kernel

end Blanc.Lift.LidoCircuitBreakerDeployed
