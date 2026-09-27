import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Run

/-!
V- witness, the attacker's subtree (EELS frames 2-4) from frame 1's `CALL` at step 339:
the machines each frame enters with, all computed from the real spawns.

* Frame 2, the attacker `A` (its lifted certificate): `childStart` at `cfg339`, then 24
  nodes to its `CALL` of `P` (value 100).
* Frame 3, the proxy `P` (45 bytes, not lifted: Jaune's `Evm.step` through `stepN`):
  eleven steps to its `DELEGATECALL` at pc 31, whose spawn is computed on the shadows
  (`dcallPrep`).
* Frame 4, the implementation's reentrant `add_liquidity([100, 0], 0, A)`, entered with
  the real world and accessed sets: its start configuration `c4` carries the shadows of
  frame 2's `CALL` (the implementation added to the address shadow).

Each machine is named by a definition and pinned by a kernel equation (`kernel_rfl`);
the frames' own theorems live in `Frame4*`, `Frame3`, `Frame2`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-! ### Frame 1 at step 339 -/

theorem cfg339_eq : wrun fs1 sevm1 339 c0 = .cont cfg339 := by kernel_rfl

theorem agree_cfg339 : Agree cfg339 := (wrun_cont cfg339_eq).1 c0_agree

/-! ### Frame 2: the attacker -/

/-- The attacker's program (its lifted certificate). -/
abbrev fs2 : List SFunc := Cert.prog Attacker.cert

def start2 : Option (Evm × Cfg) := childStart sevm1 cfg339 Attacker.t_0000_c0

/-- The machine the attacker frame enters with. -/
def e2 : Evm := match start2 with | some (e, _) => e | none => default

/-- The attacker frame's start configuration. -/
def cc2 : Cfg := match start2 with | some (_, c) => c | none => c0

theorem start2_eq : childStart sevm1 cfg339 Attacker.t_0000_c0 = some (e2, cc2) := by kernel_rfl

/-- The attacker at its `CALL` of `P`. -/
def aCall : Cfg := match wrun fs2 e2.sta 24 cc2 with | .cont c => c | _ => c0

theorem aCall_eq : wrun fs2 e2.sta 24 cc2 = .cont aCall := by kernel_rfl

theorem agree_aCall : Agree aCall :=
  (wrun_cont aCall_eq).1 (childStart_agree agree_cfg339 start2_eq)

/-- A placeholder spawn (never reached: every use is pinned by a kernel equation). -/
def noPrep : CallPrep := ⟨Frame.ofCall default, default, 0, 0, []⟩

/-- The attacker's `CALL` of `P` up to its spawn. -/
def cp3 : CallPrep := (callPrep e2.sta aCall).getD noPrep

theorem cp3_eq : callPrep e2.sta aCall = some cp3 := by kernel_rfl

/-! ### Frame 3: the proxy -/

/-- The machine the proxy frame enters with. -/
def e3 : Evm := match frameEnterS cp3.f aCall.acs with | .run e => e | .done _ => default

theorem e3_eq : frameEnterS cp3.f aCall.acs = .run e3 := by kernel_rfl

/-- The proxy frame's address shadow and account shadow (after the 100 wei moved). -/
def adrs3 : List Adr := cp3.adrs
def acs3 : AcctShadow := acsTransfer cp3.f.inner aCall.acs

/-- The proxy at its `DELEGATECALL` (pc 31): the calldata copied to memory, the seven
call words on the stack, 54 gas burned. -/
def e31 : Evm :=
  ⟨31, e3.sta, e3.dyna.setMach
    ⟨[(28562792 : Nat).toB256, implementationAddress.toB256, 0, (132 : Nat).toB256, 0, 0, 0],
      Mem.empty.write 0 e3.sta.data, 28562792, e3.dyna.stateGas⟩⟩

theorem prefix3 : stepN 11 e3 = some e31 := by kernel_rfl

/-- The proxy's `DELEGATECALL` up to its spawn. -/
def cp4 : CallPrep := (dcallPrep e31.sta e31.dyna adrs3 acs3).getD noPrep

theorem cp4_eq : dcallPrep e31.sta e31.dyna adrs3 acs3 = some cp4 := by kernel_rfl

/-! ### Frame 4: the implementation, from its real spawn -/

/-- The machine the implementation frame enters with. -/
def e4 : Evm := match frameEnterS cp4.f acs3 with | .run e => e | .done _ => default

theorem e4_eq : frameEnterS cp4.f acs3 = .run e4 := by kernel_rfl

/-- Frame 4's start configuration: the shadows of frame 2's `CALL` (storage keys and
storage), the proxy's address shadow with the implementation added, and its accounts. -/
def c4 : Cfg := ⟨e4.dyna, t_0000_c0, [], aCall.keys, cp4.adrs, aCall.stor,
  acsTransfer cp4.f.inner acs3⟩

/-- Frame 4's settled gas (the EELS Prague trace's `RETURN`). -/
def gas4 : Nat := 28053821

/-- Frame 4's accessed storage keys at its `RETURN`. -/
def keys4 : List (Adr × B256) :=
  [(proxyAddress, balanceOfASlot.toB256), (proxyAddress, (10 : Nat).toB256),
   (proxyAddress, (16 : Nat).toB256), (proxyAddress, (15 : Nat).toB256),
   (proxyAddress, (9 : Nat).toB256), (proxyAddress, (12 : Nat).toB256),
   (proxyAddress, (14 : Nat).toB256), (proxyAddress, (0 : Nat).toB256),
   (proxyAddress, (8 : Nat).toB256), (proxyAddress, (26 : Nat).toB256),
   (proxyAddress, (2 : Nat).toB256)]

/-- Frame 4's accessed addresses at its `RETURN`. -/
def adrs4 : List Adr :=
  [implementationAddress, proxyAddress, attackerAddress, (4 : Adr), implementationAddress]

/-- The shadows frame 3 hands back to the attacker: its own (the parent's at the spawn)
and frame 4's; frame 4's storage and accounts (`storA`, `acsA`) pass through. -/
def keys3 : List (Adr × B256) := aCall.keys ++ keys4
def adrs3' : List Adr := cp4.adrs ++ adrs4

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
