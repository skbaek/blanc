import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5ChunkA
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5ChunkB

/-!
V- as an admitted transaction, frame 5 whole (the reentrant `add_liquidity`, 4,505 steps from its
real spawn, halting by `RETURN` with the EELS gas and return data, no error, and the shadows
`keys5T`/`adrs5T`/`storAT`/`acsAT`), from its two kernel chunks: the first chunk reaches the
boundary configuration, which is `cfgB5` at that configuration's own world and bookkeeping, and
the second runs from there over any world and bookkeeping; the composition is
`Boundary.run_of_obsB`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-- **Frame 5 whole, from the chunks.** -/
theorem frame5_kernel : obs5 r5 = obs5EELS :=
  run_of_obsB (P := fun r => obs5 r = obs5EELS) (n := 2625) (k := 1880) chunk5A.1 chunk5A.2 rfl
    (fun m w => chunk5B m w)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
