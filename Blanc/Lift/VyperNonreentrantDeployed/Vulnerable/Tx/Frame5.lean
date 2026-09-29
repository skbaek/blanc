import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Run

/-!
V- as an admitted transaction, frame 5: the implementation's reentrant `add_liquidity([100, 0],
0, A')` under the proxy's `DELEGATECALL` (storage owner `P`, value 100, EELS depth 4), entered
from its real spawn (`c5T`: the world and accessed sets the transaction's frames 1-4 left, the
remove-lock (slot 2) held and `balances[0] = 900`).  What its halt shows: gas, return data,
success, and the halting configuration's shadows (also the shadows frames 4 and 3 hand back:
storage and accounts pass through them).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- `add_liquidity([100, 0], 0, A')`'s calldata: the one the callback builds. -/
def addCalldata2 : Bytes :=
  [0x0c, 0x3e, 0x4b, 0x54] ++ word 100 ++ word 0 ++ word 0 ++ word a2Address.toNat

/-- Frame 5's settled gas (the EELS Prague trace's `RETURN`). -/
def gas5T : Nat := 27618340

/-- Frame 5's accessed storage keys at its `RETURN`. -/
def keys5T : List (Adr × B256) :=
  [(proxyAddress, balanceOfA2Slot.toB256),
   (proxyAddress, (10 : Nat).toB256),
   (proxyAddress, (16 : Nat).toB256),
   (proxyAddress, (15 : Nat).toB256),
   (proxyAddress, (9 : Nat).toB256),
   (proxyAddress, (12 : Nat).toB256),
   (proxyAddress, (14 : Nat).toB256),
   (proxyAddress, (0 : Nat).toB256),
   (proxyAddress, (8 : Nat).toB256),
   (proxyAddress, (26 : Nat).toB256),
   (proxyAddress, (2 : Nat).toB256)]

/-- Frame 5's accessed addresses at its `RETURN`. -/
def adrs5T : List Adr :=
  [implementationAddress, proxyAddress, a2Address, (4 : Adr), implementationAddress, proxyAddress] ++ praguePrecompiles ++ [eAddress, a2Address]

/-- The storage shadow after the reentrant `add_liquidity` (newest first): its lock (slot 0)
taken and released, `totalSupply = balanceOf[A'] = 2106`, `balances = [1000, 1000]`; below them
the writes before frame 2's `CALL` (lock 2 held, `balances[0] := 900`) and the pre-state. -/
def storAT : StorShadow :=
  [((proxyAddress, (0 : Nat).toB256), (0 : Nat).toB256),
   ((proxyAddress, (26 : Nat).toB256), (2106 : Nat).toB256),
   ((proxyAddress, balanceOfA2Slot.toB256), (2106 : Nat).toB256),
   ((proxyAddress, (9 : Nat).toB256), (1000 : Nat).toB256),
   ((proxyAddress, (8 : Nat).toB256), (1000 : Nat).toB256),
   ((proxyAddress, (0 : Nat).toB256), (1 : Nat).toB256),
   ((proxyAddress, (8 : Nat).toB256), (900 : Nat).toB256),
   ((proxyAddress, (2 : Nat).toB256), (1 : Nat).toB256),
   ((tokenAddress, proxyAddress.toNat.toB256), (1000 : Nat).toB256),
   ((proxyAddress, balanceOfA2Slot.toB256), (2000 : Nat).toB256),
   ((proxyAddress, (26 : Nat).toB256), (2000 : Nat).toB256),
   ((proxyAddress, (16 : Nat).toB256), (1000000000000000000 : Nat).toB256),
   ((proxyAddress, (15 : Nat).toB256), (1000000000000000000 : Nat).toB256),
   ((proxyAddress, (12 : Nat).toB256), (10000 : Nat).toB256),
   ((proxyAddress, (9 : Nat).toB256), (1000 : Nat).toB256),
   ((proxyAddress, (8 : Nat).toB256), (1000 : Nat).toB256),
   ((proxyAddress, (7 : Nat).toB256), tokenAddress.toNat.toB256)]

/-- The accounts after the callback subtree. -/
def acsAT : AcctShadow :=
  [(proxyAddress, ⟨1, (1000 : Nat).toB256, .empty, proxyCode⟩),
   (a2Address, ⟨1, (0 : Nat).toB256, .empty, Attacker2.code⟩),
   (a2Address, ⟨1, (100 : Nat).toB256, .empty, Attacker2.code⟩),
   (proxyAddress, ⟨1, (900 : Nat).toB256, .empty, proxyCode⟩),
   ((4 : Adr), ⟨0, (0 : Nat).toB256, .empty, .empty⟩),
   (proxyAddress, ⟨1, (1000 : Nat).toB256, .empty, proxyCode⟩),
   (proxyAddress, ⟨1, (1000 : Nat).toB256, .empty, proxyCode⟩),
   (a2Address, ⟨1, (0 : Nat).toB256, .empty, Attacker2.code⟩),
   (a2Address, ⟨1, (0 : Nat).toB256, .empty, Attacker2.code⟩),
   (eAddress, ⟨1, (0 : Nat).toB256, .empty, .empty⟩),
   (eAddress, ⟨1, (0 : Nat).toB256, .empty, .empty⟩),
   (tokenAddress, ⟨1, (0 : Nat).toB256, .empty, tokenCode⟩),
   (a2Address, ⟨1, (0 : Nat).toB256, .empty, Attacker2.code⟩),
   (implementationAddress, ⟨1, (0 : Nat).toB256, .empty, code⟩),
   (proxyAddress, ⟨1, (1000 : Nat).toB256, .empty, proxyCode⟩)]

/-- Frame 5's halt: gas, return data, no error, the refund counter and whether the halting
configuration's storage keys, addresses and storage shadows are `keys5T`/`adrs5T`/`storAT`
(decided), and its account shadow and set of accounts to delete (compared by the kernel as
terms). -/
def obs5 : Res → Option (Nat × List Nat × Bool × AcctShadow × AdrSet)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone &&
      decide (cl.keys = keys5T) && decide (cl.adrs = adrs5T) && decide (cl.stor = storAT) &&
      decide (d.refundCounter = refund5), cl.acs, d.accountsToDelete)
  | _ => none

/-- The EELS observation at frame 5's `RETURN`: gas 27,618,340, returning 106 (the LP minted to
`A'`), with `totalSupply = balanceOf[A'] = 2106` in `P`'s storage shadow. -/
def obs5EELS : Option (Nat × List Nat × Bool × AcctShadow × AdrSet) :=
  some (gas5T, (word 106).map UInt8.toNat, true, acsAT, .emptyWithCapacity)

/-- Frame 5's run from its real spawn. -/
def r5 : Res := wrun fs1 e5T.sta 4505 c5T

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
