import Blanc.Lift.Weth9.Lift
import Blanc.Lift.ReachWalk

/-!
# Kernel checks for the WETH9 reach route

The entries of the deployed WETH9 that never reach an external instruction: every entry but the dispatcher
(`0`), `withdraw` (`8`) and its wrapper (`24`).  Kept in a module of its own so that the language server
never elaborates the kernel check.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift

/-- Every entry but `0`, `8` and `24`. -/
def execFreeEntries : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28]

/-- These entries make no external call and only call each other. -/
theorem execFreeEntries_set : ExecFreeSet prog execFreeEntries = true := by
  decide +kernel

/-- The payable fallback is exec-free as well. -/
theorem fallback_execFree : t_00af_c0.execFreeIn execFreeEntries = true := by
  decide +kernel

end Blanc.Lift.Weth9
