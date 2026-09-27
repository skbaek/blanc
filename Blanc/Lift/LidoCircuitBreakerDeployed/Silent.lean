import Blanc.Lift.Silent
import Blanc.Lift.LidoCircuitBreakerDeployed.Prog

/-!
# State-silent entry set for the deployed Lido CircuitBreaker runtime

`silentEntries` is a set of entries of the lifted program that are state-silent
(no `SSTORE`, no `.exec` node, no `SELFDESTRUCT`) and closed under references
(`SilentSet`, `Blanc/Lift/Silent.lean`).  The 18 entries left out are the storage
writers (4, 22, 30, 31, 32), the body making the external calls (13), and the
dispatcher, wrapper and tail entries on those paths (0, 2, 9, 12, 14, 20, 21, 44,
48, 49, 52, 59), which the frame proof handles individually.  The set is not
claimed to be maximal.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc.Lift

private instance : Inhabited SFunc := ⟨.undefined⟩

/-- The state-silent entries used by the frame proof. -/
def silentEntries : List Nat :=
  [1, 3, 5, 6, 7, 8, 10, 11, 15, 16, 17, 18, 19, 23, 24, 25, 26, 27, 28, 29, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
   43, 45, 46, 47, 50, 51, 53, 54, 55, 56, 57, 58]

theorem silent_entries : SilentSet prog silentEntries = true := by
  decide +kernel

end Blanc.Lift.LidoCircuitBreakerDeployed
