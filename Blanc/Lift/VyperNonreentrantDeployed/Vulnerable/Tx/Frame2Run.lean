import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame3
import Blanc.Lift.WitnessBoundary

/-!
V- as an admitted transaction, frame 2 whole: the run of the implementation's
`remove_liquidity(200, [0, 0], A')` under the proxy's `DELEGATECALL`, from its start
configuration `c2T` to its `RETURN`, with the callback child supplied as data and the token
child run.

Frame 2 (763 EELS steps) makes six `CALL`s: the identity precompile at steps 323, 506, 559 and
607 (run by the interpreter), `A'` at step 339 (value 100: `A'` re-enters the pool, tx frames 3-5)
and the token `T` at step 574 (`transfer(A', 100)`).  The callback child is not executed here: it
is a settled machine `d` whose gas, output and error are fixed, and whose accessed sets, storage
and accounts are the shadows `keysAT`/`adrsAT`/`storAT`/`acsAT` (`Tx.Frame3` proves it).  The
token child is run by its own lifted certificate.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- Frame 2's static machine with the fields its interpreter reads as literals (the code, which
it never reads, stays `e2T`'s), so that a decision from a boundary does not evaluate the spawn
chain behind `e2T` again. -/
def sta2T : Sevm :=
  { (default : Sevm) with
    caller := a2Address
    target := some proxyAddress
    currentTarget := proxyAddress
    gas := 29064579
    value := 0
    data := removeCalldata2
    codeAddress := some implementationAddress
    code := e2T.sta.code
    depth := 1022
    benvStat := benvStatTx
    tenvStat := tenvStat0 }

theorem e2T_sta_eq : e2T.sta = sta2T := by kernel_rfl

/-- Frame 2 after its first 339 steps (with result `r`), with the callback child `d` supplied; the
token child (step 574) is run by its own certificate (`childRun`) and resumed from with the
shadows of its halting configuration. -/
def run2From (r : Res) (d : Devm) : Res :=
  callPairFrom fs1 sta2T fsT Token.code 234 23 188 keysAT adrsAT storAT acsAT r d

/-- The whole of frame 2, from `c2T`, with the callback child `d` supplied. -/
def run2T (d : Devm) : Res := run2From (wrun fs1 sta2T 339 c2T) d

/-- What frame 2's halt shows: gas, return data, and `P`'s `totalSupply` (slot 26),
`balanceOf[A']` and remove-lock (slot 2) in the halting configuration's storage shadow, success
(no error) with the refund counter, and its set of accounts to delete as a term. -/
def obs2T : Res → Option (Nat × List Nat × Nat × Nat × Nat × Bool × AdrSet)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat,
      (lookupS cl.stor proxyAddress (26 : Nat).toB256).toNat,
      (lookupS cl.stor proxyAddress balanceOfA2Slot.toB256).toNat,
      (lookupS cl.stor proxyAddress (2 : Nat).toB256).toNat,
      d.error.isNone && decide (d.refundCounter = refund2), d.accountsToDelete)
  | _ => none

/-- The EELS observation at frame 2's `RETURN`: gas 28,916,293, return data `[100, 100]`,
`totalSupply = 1800 < 1906 = balanceOf[A']`, lock released, success. -/
def obs2TEELS : Option (Nat × List Nat × Nat × Nat × Nat × Bool × AdrSet) :=
  some (28916293, (word 100 ++ word 100).map UInt8.toNat, 1800, 1906, 0, true, .emptyWithCapacity)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
