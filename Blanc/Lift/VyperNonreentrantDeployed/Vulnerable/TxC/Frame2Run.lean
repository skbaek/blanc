import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame3
import Blanc.Lift.WitnessBoundary
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame2Run

/-!
V- as an admitted transaction, frame 2 whole: the run of the implementation's
`remove_liquidity(200, [0, 0], A')` under the proxy's `DELEGATECALL`, from its start
configuration `c2C` to its `RETURN`, with the callback child supplied as data and the token
child run.

Frame 2 (763 EELS steps) makes six `CALL`s: the identity precompile at steps 323, 506, 559 and
607 (run by the interpreter), `A'` at step 339 (value 100: `A'` re-enters the pool, tx frames 3-5)
and the token `T` at step 574 (`transfer(A', 100)`).  The callback child is not executed here: it
is a settled machine `d` whose gas, output and error are fixed, and whose accessed sets, storage
and accounts are the shadows `keysAT`/`adrsAC`/`storAT`/`acsAT` (`Tx.Frame3` proves it).  The
token child is run by its own lifted certificate.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- Frame 2's static machine with the fields its interpreter reads as literals (the code, which
it never reads, stays `e2C`'s), so that a decision from a boundary does not evaluate the spawn
chain behind `e2C` again. -/
def sta2C : Sevm :=
  { (default : Sevm) with
    caller := a2Address
    target := some proxyAddress
    currentTarget := proxyAddress
    gas := 15475925
    value := 0
    data := removeCalldata2
    codeAddress := some implementationAddress
    code := e2C.sta.code
    depth := 1022
    benvStat := benvStatTx
    tenvStat := tenv0C.stat }

theorem e2C_sta_eq : e2C.sta = sta2C := by kernel_rfl

/-- Frame 2 after its first 339 steps (with result `r`), with the callback child `d` supplied; the
token child (step 574) is run by its own certificate (`childRun`) and resumed from with the
shadows of its halting configuration. -/
def run2FromC (r : Res) (d : Devm) : Res :=
  callPairFrom fs1 sta2C fsT Token.code 234 23 188 keysAT adrsAC storAT acsAT r d

/-- The whole of frame 2, from `c2C`, with the callback child `d` supplied. -/
def run2C (d : Devm) : Res := run2FromC (wrun fs1 sta2C 339 c2C) d

/-- The EELS observation at frame 2's `RETURN`: gas 15,327,639, return data `[100, 100]`,
`totalSupply = 1800 < 1906 = balanceOf[A']`, lock released, success. -/
def obs2CEELS : Option (Nat × List Nat × Nat × Nat × Nat × Bool × AdrSet) :=
  some (15327639, (word 100 ++ word 100).map UInt8.toNat, 1800, 1906, 0, true, .emptyWithCapacity)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
