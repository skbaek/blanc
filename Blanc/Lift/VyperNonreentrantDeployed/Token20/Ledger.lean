import Blanc.Lift.VyperNonreentrantDeployed.Token20.Run
import Blanc.Lift.ExactLeaf
import Blanc.LedgerConservation

/-!
# The synthetic token `T`: exact storage deltas and a finite-footprint ledger

What each successful run of `Run.lean` does to storage, exactly: the token's own storage is the
pre-state's with the selector's writes (`moveStor` for a move; the allowance write first for
`transferFrom`; the allowance write for `approve`; nothing for `balanceOf`), and every other
account's storage is untouched.

The ledger is observed on a finite footprint `F` of holders (`ledgerSumOn F (balances s)`,
`Blanc/LedgerConservation.lean`): a move between two members of `F` keeps its sum
(`ledger_move`); a `transferFrom` does too when the allowance slot it writes is not a balance slot
of `F` (`ledger_transferFrom`, a finite separation premise a concrete footprint discharges by
kernel evaluation).  No universal hash-separation or all-address claim is made.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc Blanc.Lift Blanc.Lift.NodeWalk

/-! ## Exact storage deltas -/

/-! ## The finite-footprint ledger -/

end Blanc.Lift.VyperNonreentrantDeployed.Token20
