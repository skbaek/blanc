import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Run

/-!
V- witness, frame 1 whole, the kernel decision: for every settled attacker child and token
child with the EELS gas and output (all their other parts free), frame 1 halts by
`RETURN` with the EELS observation.  The children's worlds are never inspected: the
interpreter reads storage and accounts from the shadows.  Checked by the kernel alone
(`kernel_forall_rfl`); do not open this file in the language server.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

open Jaune Blanc.Lift Blanc.Lift.Witness

theorem frame1_kernel : ∀ d1 d2 : Devm,
    obs1 (run1 (childObs gasA [] d1) (childObs gasT (word 1) d2)) = obs1EELS := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
