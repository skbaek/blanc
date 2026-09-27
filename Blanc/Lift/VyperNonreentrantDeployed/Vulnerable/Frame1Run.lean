import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Token.Check
import Blanc.Lift.WitnessChild

/-!
V- witness, frame 1 whole: the run of `remove_liquidity(200, [0, 0], A)` from `c0` to its
`RETURN`, with the attacker child supplied as data and the token child run.

Frame 1 (763 EELS steps) makes six `CALL`s: the identity precompile at steps 323, 506,
559 and 607 (run by the interpreter), the attacker `A` at step 339 (value 100: `A`
re-enters the pool, EELS frames 2-4) and the token `T` at step 574 (`transfer(A, 100)`,
EELS frame 5).  The attacker child is not executed here: it is a settled machine `d1`
whose gas, output and error are fixed below, and whose accessed sets, storage and
accounts are described by the shadows below (untrusted here: the frame theorem takes
them as hypotheses, and the attacker frame's theorem proves them).  The token child is
run by its own lifted certificate.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed

/-! ### The attacker child (step 339): its settled shadows -/

def gasA : Nat := 28953417

def keysA : List (Adr × B256) :=
  [(proxyAddress, (0 : Nat).toB256), (proxyAddress, (2 : Nat).toB256),
   (proxyAddress, (8 : Nat).toB256), (proxyAddress, (9 : Nat).toB256),
   (proxyAddress, (10 : Nat).toB256), (proxyAddress, (12 : Nat).toB256),
   (proxyAddress, (14 : Nat).toB256), (proxyAddress, (15 : Nat).toB256),
   (proxyAddress, (16 : Nat).toB256), (proxyAddress, (26 : Nat).toB256),
   (proxyAddress, balanceOfASlot.toB256)]

def adrsA : List Adr := [attackerAddress, 4, proxyAddress, implementationAddress]

/-- `P`'s storage after the reentrant `add_liquidity`: lock 2 still held, `balances =
[1000, 1000]`, `totalSupply = balanceOf[A] = 2106`; `T` untouched. -/
def storA : StorShadow :=
  [((proxyAddress, (2 : Nat).toB256), (1 : Nat).toB256),
   ((proxyAddress, (7 : Nat).toB256), tokenAddress.toNat.toB256),
   ((proxyAddress, (8 : Nat).toB256), (1000 : Nat).toB256),
   ((proxyAddress, (9 : Nat).toB256), (1000 : Nat).toB256),
   ((proxyAddress, (12 : Nat).toB256), (10000 : Nat).toB256),
   ((proxyAddress, (15 : Nat).toB256), (10 ^ 18 : Nat).toB256),
   ((proxyAddress, (16 : Nat).toB256), (10 ^ 18 : Nat).toB256),
   ((proxyAddress, (26 : Nat).toB256), (2106 : Nat).toB256),
   ((proxyAddress, balanceOfASlot.toB256), (2106 : Nat).toB256),
   ((tokenAddress, proxyAddress.toNat.toB256), (1000 : Nat).toB256)]

/-- The accounts after the attacker's subtree: the 100 wei went to `A` and came back. -/
def acsA : AcctShadow :=
  [(proxyAddress, ⟨1, (1000 : Nat).toB256, .empty, proxyCode⟩),
   (implementationAddress, ⟨1, 0, .empty, implementationCode⟩),
   (attackerAddress, ⟨1, 0, .empty, attackerCode⟩),
   (tokenAddress, ⟨1, 0, .empty, tokenCode⟩)]

/-! ### The run -/

/-- Frame 1's program. -/
abbrev fs1 : List SFunc := Cert.prog cert

/-- Frame 1 at its `CALL` to the attacker (EELS step 339). -/
def cfg339 : Cfg :=
  match wrun fs1 sevm1 339 c0 with
  | .cont c => c
  | _ => c0

/-- The token's program (its lifted certificate). -/
abbrev fsT : List SFunc := Cert.prog Token.cert

/-- The whole of frame 1, from `c0`, with the attacker child `d1` supplied; the token
child (step 574) is run by its own certificate (`childRun`) and resumed from with the
shadows of its halting configuration. -/
def run1 (d1 : Devm) : Res :=
  match wrun fs1 sevm1 339 c0 with
  | .cont c1 =>
    match callResume sevm1 c1 d1 keysA adrsA storA acsA with
    | some c2 =>
      match wrun fs1 sevm1 234 c2 with
      | .cont c3 =>
        match childRun fsT Token.code sevm1 23 c3 with
        | .done (.halted d2) cl =>
          match callResume sevm1 c3 d2 cl.keys cl.adrs cl.stor cl.acs with
          | some c4 => wrun fs1 sevm1 188 c4
          | none => .stuck
        | _ => .stuck
      | _ => .stuck
    | none => .stuck
  | _ => .stuck

/-- What frame 1's halt shows: gas, return data, and `P`'s `totalSupply` (slot 26),
`balanceOf[A]` and remove-lock (slot 2) in the halting configuration's storage shadow. -/
def obs1 : Res → Option (Nat × List Nat × Nat × Nat × Nat)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat,
      (lookupS cl.stor proxyAddress (26 : Nat).toB256).toNat,
      (lookupS cl.stor proxyAddress balanceOfASlot.toB256).toNat,
      (lookupS cl.stor proxyAddress (2 : Nat).toB256).toNat)
  | _ => none

/-- The EELS observation at frame 1's `RETURN` (step 762): gas 29,372,882, return data
`[100, 100]`, `totalSupply = 1800 < 1906 = balanceOf[A]`, lock released. -/
def obs1EELS : Option (Nat × List Nat × Nat × Nat × Nat) :=
  some (29372882, (word 100 ++ word 100).map UInt8.toNat, 1800, 1906, 0)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
