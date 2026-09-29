import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4ChunkA
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4ChunkB

/-!
V- witness, frame 4 whole (the reentrant `add_liquidity`, 4,505 steps from its real spawn,
halting by `RETURN` with the EELS gas and return data, no error, and the shadows
`keys4`/`adrs4`/`storA`/`acsA`), from its two kernel chunks: the first chunk reaches the boundary
configuration (its machine and shadows as `chunkA` states them), which is `cfgB` at that
configuration's own world and bookkeeping, and the second chunk runs from there over any
world and bookkeeping (`chunkB`); the composition is `Boundary.run_of_obsB`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-- **Frame 4 whole, from the chunks.** -/
theorem frame4_kernel : obs4 r4 = obs4EELS :=
  run_of_obsB (P := fun r => obs4 r = obs4EELS) (n := 2625) (k := 1880) chunkA.1 chunkA.2 rfl
    (fun m w => chunkB m w)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
