import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Run

/-!
V- witness, frame 1 whole, the kernel decision: for every settled attacker child with the
EELS gas and output (all its other parts free), frame 1, with its token child run,
halts by `RETURN` with the EELS observation.  The attacker child's world is never
inspected: the interpreter reads storage and accounts from the shadows.  Checked by the kernel alone
(`kernel_forall_rfl`); do not open this file in the language server.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

open Jaune Blanc.Lift Blanc.Lift.Witness

theorem frame1_kernel : ∀ d1 : Devm, obs1 (run1 (childObs gasA [] d1)) = obs1EELS := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
