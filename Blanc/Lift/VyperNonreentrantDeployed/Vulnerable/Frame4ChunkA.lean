import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Chunks

/-! V- witness, frame 4's first chunk (2,625 steps from the real spawn to the boundary).
Kernel only; do not open this file in the language server. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

theorem chunkA : obsB (wrun fs1 e4.sta 2625 c4) = obsBEELS := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
