import Blanc.Lift.KernelBatch
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Outer
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Run
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Attacker2.Check
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Run

/-!
V- as an admitted transaction, the deep chain's entries: the machines each frame of the
transaction's reentrancy chain enters with, all computed from the real spawns.

* Frame 1, the proxy `P` (`remove_liquidity`), spawned by `A'`'s `CALL` (`cp0C`); eleven
  steps to its `DELEGATECALL` (`e1C31`), whose spawn is `cp2C`.
* Frame 2, the implementation's `remove_liquidity` (`e2C`, start configuration `c2C`), run
  339 steps to its `CALL` of `A'` (`cfg339C`).
* Frame 3, `A'` re-entered with value 100 (its lifted certificate: the dispatcher falls
  through on empty calldata): `childStart` at `cfg339C`, then 32 nodes to its `CALL` of `P`
  (`aCallC`).
* Frame 4, `P` (`add_liquidity`): eleven steps to its `DELEGATECALL` (`e4C31`).
* Frame 5, the implementation's reentrant `add_liquidity` (`e5C`, `c5C`).

Each machine is named by a definition and pinned by a kernel equation (`kernel_rfl`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-! ### Frame 1: the proxy, spawned by `A'` -/

/-- The machine the proxy frame (`remove_liquidity`) enters with. -/
def e1C : Evm := match frameEnterS cp0C.f callCfgC.acs with | .run e => e | .done _ => default

/-- The proxy at its `DELEGATECALL` (pc 31): the calldata copied to memory, the seven call
words on the stack, 54 gas burned. -/
def e1C31 : Evm :=
  ⟨31, e1C.sta, e1C.dyna.setMach
    ⟨[(15724174 : Nat).toB256, implementationAddress.toB256, 0, (132 : Nat).toB256, 0, 0, 0],
      Mem.empty.write 0 e1C.sta.data, 15724174, e1C.dyna.stateGas⟩⟩

/-- The proxy's address shadow and account shadow at its `DELEGATECALL` (the zero-value
transfer of `A'`'s `CALL` applied). -/
def adrs1C : List Adr := cp0C.adrs
def acs1C : AcctShadow := acsTransfer cp0C.f.inner callCfgC.acs

/-- The proxy's `DELEGATECALL` up to its spawn. -/
def cp2C : CallPrep := (dcallPrep e1C31.sta e1C31.dyna adrs1C acs1C).getD noPrep

/-! ### Frame 2: the implementation's `remove_liquidity` -/

/-- The machine the implementation frame enters with. -/
def e2C : Evm := match frameEnterS cp2C.f acs1C with | .run e => e | .done _ => default

/-- Frame 2's start configuration. -/
def c2C : Cfg := ⟨e2C.dyna, t_0000_c0, [], callCfgC.keys, cp2C.adrs, callCfgC.stor,
  acsTransfer cp2C.f.inner acs1C⟩

/-- Frame 2 at its `CALL` of `A'` (step 339). -/
def cfg339C : Cfg :=
  match wrun fs1 e2C.sta 339 c2C with
  | .cont c => c
  | _ => c2C

/-! ### Frame 3: `A'` re-entered -/

def start3C : Option (Evm × Cfg) := childStart e2C.sta cfg339C Attacker2.t_0000_c0

/-- The machine the callback frame enters with. -/
def e3C : Evm := match start3C with | some (e, _) => e | none => default

/-- The callback frame's start configuration. -/
def cc3C : Cfg := match start3C with | some (_, c) => c | none => c2C

/-- `A'` (callback) at its `CALL` of `P`. -/
def aCallC : Cfg := match wrun fs3 e3C.sta 32 cc3C with | .cont c => c | _ => c2C

/-- `A'`'s `CALL` of `P` up to its spawn. -/
def cp4C : CallPrep := (callPrep e3C.sta aCallC).getD noPrep

/-! ### Frame 4: the proxy, `add_liquidity` -/

/-- The machine the proxy frame (`add_liquidity`) enters with. -/
def e4C : Evm := match frameEnterS cp4C.f aCallC.acs with | .run e => e | .done _ => default

def adrs4C : List Adr := cp4C.adrs
def acs4C : AcctShadow := acsTransfer cp4C.f.inner aCallC.acs

/-- The proxy at its `DELEGATECALL` (pc 31). -/
def e4C31 : Evm :=
  ⟨31, e4C.sta, e4C.dyna.setMach
    ⟨[(14953072 : Nat).toB256, implementationAddress.toB256, 0, (132 : Nat).toB256, 0, 0, 0],
      Mem.empty.write 0 e4C.sta.data, 14953072, e4C.dyna.stateGas⟩⟩

/-- The proxy's `DELEGATECALL` up to its spawn. -/
def cp5C : CallPrep := (dcallPrep e4C31.sta e4C31.dyna adrs4C acs4C).getD noPrep

/-! ### Frame 5: the implementation's reentrant `add_liquidity` -/

/-- The machine the implementation frame enters with. -/
def e5C : Evm := match frameEnterS cp5C.f acs4C with | .run e => e | .done _ => default

/-- Frame 5's start configuration: the shadows of frame 3's `CALL` with the implementation
added to the address shadow. -/
def c5C : Cfg := ⟨e5C.dyna, t_0000_c0, [], aCallC.keys, cp5C.adrs, aCallC.stor,
  acsTransfer cp5C.f.inner acs4C⟩

-- Check the related equations together so the kernel can reuse the spawn chain.
private theorem spawnChainFacts :
    (frameEnterS cp0C.f callCfgC.acs = .run e1C) ∧
    (stepN 11 e1C = some e1C31) ∧
    (dcallPrep e1C31.sta e1C31.dyna adrs1C acs1C = some cp2C) ∧
    (frameEnterS cp2C.f acs1C = .run e2C) ∧
    (wrun fs1 e2C.sta 339 c2C = .cont cfg339C) ∧
    (childStart e2C.sta cfg339C Attacker2.t_0000_c0 = some (e3C, cc3C)) ∧
    (wrun fs3 e3C.sta 32 cc3C = .cont aCallC) ∧
    (callPrep e3C.sta aCallC = some cp4C) ∧
    (frameEnterS cp4C.f aCallC.acs = .run e4C) ∧
    (stepN 11 e4C = some e4C31) ∧
    (dcallPrep e4C31.sta e4C31.dyna adrs4C acs4C = some cp5C) ∧
    (frameEnterS cp5C.f acs4C = .run e5C) := by
  kernel_rfl_and

theorem e1C_eq : frameEnterS cp0C.f callCfgC.acs = .run e1C := by
  exact spawnChainFacts.1

theorem prefix1C : stepN 11 e1C = some e1C31 := by
  exact spawnChainFacts.2.1

theorem cp2C_eq : dcallPrep e1C31.sta e1C31.dyna adrs1C acs1C = some cp2C := by
  exact spawnChainFacts.2.2.1

theorem e2C_eq : frameEnterS cp2C.f acs1C = .run e2C := by
  exact spawnChainFacts.2.2.2.1

theorem cfg339C_eq : wrun fs1 e2C.sta 339 c2C = .cont cfg339C := by
  exact spawnChainFacts.2.2.2.2.1

theorem start3C_eq : childStart e2C.sta cfg339C Attacker2.t_0000_c0 = some (e3C, cc3C) := by
  exact spawnChainFacts.2.2.2.2.2.1

theorem aCallC_eq : wrun fs3 e3C.sta 32 cc3C = .cont aCallC := by
  exact spawnChainFacts.2.2.2.2.2.2.1

theorem cp4C_eq : callPrep e3C.sta aCallC = some cp4C := by
  exact spawnChainFacts.2.2.2.2.2.2.2.1

theorem e4C_eq : frameEnterS cp4C.f aCallC.acs = .run e4C := by
  exact spawnChainFacts.2.2.2.2.2.2.2.2.1

theorem prefix4C : stepN 11 e4C = some e4C31 := by
  exact spawnChainFacts.2.2.2.2.2.2.2.2.2.1

theorem cp5C_eq : dcallPrep e4C31.sta e4C31.dyna adrs4C acs4C = some cp5C := by
  exact spawnChainFacts.2.2.2.2.2.2.2.2.2.2.1

theorem e5C_eq : frameEnterS cp5C.f acs4C = .run e5C := by
  exact spawnChainFacts.2.2.2.2.2.2.2.2.2.2.2

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
