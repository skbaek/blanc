import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Chunks

/-! V- witness, frame 4's second chunk (from the boundary, over a free world and free
bookkeeping, to the `RETURN`).  Kernel only; do not open this file in the language
server. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

theorem chunkB : ∀ (m : Meta) (w : World), obs4 (wrun fs1 e4.sta 1880 (cfgB m w)) = obs4EELS := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
