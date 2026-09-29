import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5ChunkA
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5ChunkB
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5Full

/-!
V- as an admitted transaction, frame 5 whole (the reentrant `add_liquidity`, 4,505 steps from its
real spawn, halting by `RETURN` with the EELS gas and return data, no error, and the shadows
`keys5T`/`adrs5C`/`storAT`/`acsAT`), from its two kernel chunks: the first chunk reaches the
boundary configuration, which is `cfgB5C` at that configuration's own world and bookkeeping, and
the second runs from there over any world and bookkeeping; the composition is
`Boundary.run_of_obsB`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-- **Frame 5 whole, from the chunks.** -/
theorem frame5C_kernel : obs5C r5C = obs5EELSC :=
  run_of_obsB (P := fun r => obs5C r = obs5EELSC) (n := 2625) (k := 1880) chunk5AC.1 chunk5AC.2 rfl
    (fun m w => chunk5BC m w)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
