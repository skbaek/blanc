import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.SubtreeRun

/-!
V- witness, frame 4: the implementation's reentrant `add_liquidity([100, 0], 0, A)` under
the proxy's `DELEGATECALL` (storage owner `P`, value 100, EELS depth 4), entered from its
real spawn (`Subtree.c4`: the world and accessed sets frame 1 and the attacker left, the
lock of `remove_liquidity` (slot 2) held and `balances[0] = 900`).  What its halt shows:
gas, return data, success, and the halting configuration's shadows.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-- Frame 4's halt: gas, return data, no error and whether the halting configuration's
storage keys, addresses and storage shadows are `keys4`/`adrs4`/`storA` (decided), and its
account shadow (compared by the kernel as a term: its codes are the fixture's constants). -/
def obs4 : Res → Option (Nat × List Nat × Bool × AcctShadow)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone &&
      decide (cl.keys = keys4) && decide (cl.adrs = adrs4) && decide (cl.stor = storA), cl.acs)
  | _ => none

/-- The EELS observation at frame 4's `RETURN`: gas 28,053,821, returning 106 (the LP
minted to `A`), with `totalSupply = balanceOf[A] = 2106` in `P`'s storage shadow. -/
def obs4EELS : Option (Nat × List Nat × Bool × AcctShadow) :=
  some (gas4, (word 106).map UInt8.toNat, true, acsA)

/-- Frame 4's run from its real spawn. -/
def r4 : Res := wrun fs1 e4.sta 4505 c4

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
