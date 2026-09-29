import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Run
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5

/-!
V- as an admitted transaction, frame 5: the implementation's reentrant `add_liquidity([100, 0],
0, A')` under the proxy's `DELEGATECALL` (storage owner `P`, value 100, EELS depth 4), entered
from its real spawn (`c5C`: the world and accessed sets the transaction's frames 1-4 left, the
remove-lock (slot 2) held and `balances[0] = 900`).  What its halt shows: gas, return data,
success, and the halting configuration's shadows (also the shadows frames 4 and 3 hand back:
storage and accounts pass through them).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- Frame 5's settled gas (the EELS Prague trace's `RETURN` at the transaction's gas). -/
def gas5C : Nat := 14656753

/-- Frame 5's accessed addresses at its `RETURN`. -/
def adrs5C : List Adr :=
  [implementationAddress, proxyAddress, a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ warmC

/-- Frame 5's halt: gas, return data, no error, the refund counter and whether the halting
configuration's storage keys, addresses and storage shadows are `keys5T`/`adrs5C`/`storAT`
(decided), and its account shadow and set of accounts to delete (compared by the kernel as
terms). -/
def obs5C : Res → Option (Nat × List Nat × Bool × AcctShadow × AdrSet)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone &&
      decide (cl.keys = keys5T) && decide (cl.adrs = adrs5C) && decide (cl.stor = storAT) &&
      decide (d.refundCounter = refund5), cl.acs, d.accountsToDelete)
  | _ => none

/-- The EELS observation at frame 5's `RETURN`: gas 14,656,753, returning 106 (the LP minted to
`A'`), with `totalSupply = balanceOf[A'] = 2106` in `P`'s storage shadow. -/
def obs5EELSC : Option (Nat × List Nat × Bool × AcctShadow × AdrSet) :=
  some (gas5C, (word 106).map UInt8.toNat, true, acsAT, .emptyWithCapacity)

/-- Frame 5's run from its real spawn. -/
def r5C : Res := wrun fs1 e5C.sta 4505 c5C

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
