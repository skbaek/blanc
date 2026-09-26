import Blanc.Lift.Quiet
import Blanc.Lift.BeaconDeposit.Prog

/-!
# The view wrappers are quiet

The entries reachable from the three view wrappers (31 `supportsInterface`, 33
`get_deposit_count`, 34 `get_deposit_root`) form a `QuietSet`: no `SSTORE`, no `LOG`, the only
call the SHA-256 `STATICCALL`s of `get_deposit_root`.  A kernel decision, kept apart from the
files the language server elaborates.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The view wrappers and every entry they reach. -/
def viewSet : List Nat := [1, 2, 5, 6, 8, 9, 10, 24, 25, 27, 28, 29, 30, 31, 33, 34]

theorem viewSet_quiet : QuietSet prog viewSet = true := by
  decide +kernel

end Blanc.Lift.BeaconDeposit
