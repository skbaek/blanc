import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-!
V- witness, frame 4: the implementation's reentrant `add_liquidity([100, 0], 0, A)` under
`DELEGATECALL` from the proxy `P` (storage owner `P`, value 100, EELS depth 4), entered while
`remove_liquidity` holds its lock (slot 2 = 1) and has written `balances[0] := 900`.
The entry state is the EELS Prague trace's frame-4 entry (Plans
`evidence/deployed-lido-vyper-v1/vminus-witness-w1/trace_steps.py`): gas 28,116,400, the P
balance 1000 (the attacker's 100 back), accessed addresses {impl, 0x4, A, P} and accessed
keys {(P, 2), (P, 26), (P, 8)}.  Accounts other than `P` are not read by this frame and are
left out of this probe world.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-- `add_liquidity(uint256[2],uint256,address)` = `0x0c3e4b54`, `([100, 0], 0, A)`. -/
def addCalldata : Bytes :=
  [0x0c, 0x3e, 0x4b, 0x54] ++ word 100 ++ word 0 ++ word 0 ++ word attackerAddress.toNat

/-- P's storage at frame-4 entry: frame 1 has set the lock (slot 2) and `balances[0] := 900`. -/
def poolStorage4 : List (Nat × Nat) :=
  [(2, 1), (7, tokenAddress.toNat), (8, 900), (9, 1000), (12, 10000),
   (15, 10 ^ 18), (16, 10 ^ 18), (26, 2000), (balanceOfASlot, 2000)]

def poolAcct4 : Acct :=
  { poolAcct with
    stor := poolStorage4.foldl (fun s kv => Std.TreeMap.insert s kv.1.toB256 kv.2.toB256) .empty }

def world4 : State := Std.TreeMap.insert .empty proxyAddress poolAcct4

def gas4 : Nat := 28116400

def sevm4 : Sevm :=
  { (default : Sevm) with
    caller := attackerAddress
    target := some proxyAddress
    currentTarget := proxyAddress
    gas := gas4
    value := (100 : Nat).toB256
    data := addCalldata
    codeAddress := some implementationAddress
    code := code
    depth := 1020
    benvStat := { (default : BenvStat) with origState := world0 } }

def adrs4 : List Adr := [proxyAddress, attackerAddress, 4, implementationAddress]
def keys4 : List (Adr × B256) :=
  [(proxyAddress, (8 : Nat).toB256), (proxyAddress, (26 : Nat).toB256),
   (proxyAddress, (2 : Nat).toB256)]

def pre4 : Devm :=
  let d := ((default : Devm).withGasLeft gas4).withState world4
  let d := adrs4.foldr (fun a d => addAccessedAddress d a) d
  keys4.foldr (fun k d => addAccessedStorageKey d k.1 k.2) d

def c4 : Cfg := ⟨pre4, t_0000_c0, [], keys4, adrs4⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4
