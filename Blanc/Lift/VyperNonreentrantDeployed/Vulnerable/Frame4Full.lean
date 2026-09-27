import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4

/-!
V- witness, frame 4 whole, the kernel decision: from its real spawn (`c4`), the
reentrant `add_liquidity` (4,505 steps) halts by `RETURN` with the EELS gas and return
data, no error, and the shadows `keys4`/`adrs4`/`storA`/`acsA`.  Checked by the kernel
alone; do not open this file in the language server.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

theorem frame4_kernel : obs4 (wrun fs1 e4.sta 4505 c4) = obs4EELS := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
