import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Chunks
import Blanc.Lift.WitnessBoundary
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5Chunks

/-!
V- as an admitted transaction, frame 5 in two kernel chunks (the transaction's analog of
`Subtree.mach2625`): the boundary at step 2625, where frame 5 arrives by a jump at the
certificate's entry 63 (`t_0370_c63`) with no pending internal call.  The boundary
configuration's machine and shadows are literals (printed by an untrusted scratch evaluation;
each chunk's kernel decision checks them): the message-level witness's boundary with the
attacker address `A'`, the transaction's gas and the `balanceOf[A']` slot.  Its world and
bookkeeping are free in the second chunk.  Each chunk is itself a few kernel decisions
(`Boundary.Bnd`, `Boundary.obsD_chain`, from `Blanc.Lift.WitnessBoundary`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

/-- Frame 5's machine at step 2625. -/
def machC2625 : Mach := { machT2625 with gasLeft := 14675618 }

/-- The first chunk's observation (`Boundary.obsB`): the configuration reached, all but its
world and bookkeeping. -/
def obsB5EELSC : Option Bnd :=
  some (machC2625, t_0370_c63, [], keys2625, adrs5C, storT2625, acsAT, 2800, [], [], none)

/-- The static machine of frame 5 with the fields its interpreter reads as literals (the code,
which it never reads, stays `e5C`'s), so that a chunk from a boundary does not evaluate the
spawn chain behind `e5C` again. -/
def sta5C : Sevm :=
  { (default : Sevm) with
    caller := a2Address
    target := some proxyAddress
    currentTarget := proxyAddress
    gas := 14719332
    value := (100 : Nat).toB256
    data := addCalldata2
    codeAddress := some implementationAddress
    code := e5C.sta.code
    depth := 1019
    benvStat := benvStatTx
    tenvStat := tenv0C.stat }

theorem e5C_sta_eq : e5C.sta = sta5C := by kernel_rfl

/-- The boundary configuration over a free world and free bookkeeping. -/
def cfgB5C (m : Meta) (w : World) : Cfg :=
  ⟨⟨machC2625, { { m with refundCounter := 2800, output := [], returnData := [], error := none } with
    accountsToDelete := .emptyWithCapacity }, w⟩,
    t_0370_c63, [], keys2625, adrs5C, storT2625, acsAT⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
