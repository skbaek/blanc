import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Outer
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Run
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Attacker2.Check

/-!
V- as an admitted transaction, the deep chain's entries: the machines each frame of the
transaction's reentrancy chain enters with, all computed from the real spawns.

* Frame 1, the proxy `P` (`remove_liquidity`), spawned by `A'`'s `CALL` (`TxTop.cp0`); eleven
  steps to its `DELEGATECALL` (`e1T31`), whose spawn is `cp2T`.
* Frame 2, the implementation's `remove_liquidity` (`e2T`, start configuration `c2T`), run
  339 steps to its `CALL` of `A'` (`cfg339T`).
* Frame 3, `A'` re-entered with value 100 (its lifted certificate: the dispatcher falls
  through on empty calldata): `childStart` at `cfg339T`, then 32 nodes to its `CALL` of `P`
  (`aCallT`).
* Frame 4, `P` (`add_liquidity`): eleven steps to its `DELEGATECALL` (`e4T31`).
* Frame 5, the implementation's reentrant `add_liquidity` (`e5T`, `c5T`).

Each machine is named by a definition and pinned by a kernel equation (`kernel_rfl`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-! ### Frame 1: the proxy, spawned by `A'` -/

/-- The machine the proxy frame (`remove_liquidity`) enters with. -/
def e1T : Evm := match frameEnterS cp0.f callCfg.acs with | .run e => e | .done _ => default

theorem e1T_eq : frameEnterS cp0.f callCfg.acs = .run e1T := by kernel_rfl

/-- The proxy at its `DELEGATECALL` (pc 31): the calldata copied to memory, the seven call
words on the stack, 54 gas burned. -/
def e1T31 : Evm :=
  ⟨31, e1T.sta, e1T.dyna.setMach
    ⟨[(29528521 : Nat).toB256, implementationAddress.toB256, 0, (132 : Nat).toB256, 0, 0, 0],
      Mem.empty.write 0 e1T.sta.data, 29528521, e1T.dyna.stateGas⟩⟩

theorem prefix1T : stepN 11 e1T = some e1T31 := by kernel_rfl

/-- The proxy's address shadow and account shadow at its `DELEGATECALL` (the zero-value
transfer of `A'`'s `CALL` applied). -/
def adrs1T : List Adr := cp0.adrs
def acs1T : AcctShadow := acsTransfer cp0.f.inner callCfg.acs

/-- The proxy's `DELEGATECALL` up to its spawn. -/
def cp2T : CallPrep := (dcallPrep e1T31.sta e1T31.dyna adrs1T acs1T).getD noPrep

theorem cp2T_eq : dcallPrep e1T31.sta e1T31.dyna adrs1T acs1T = some cp2T := by kernel_rfl

/-! ### Frame 2: the implementation's `remove_liquidity` -/

/-- The machine the implementation frame enters with. -/
def e2T : Evm := match frameEnterS cp2T.f acs1T with | .run e => e | .done _ => default

theorem e2T_eq : frameEnterS cp2T.f acs1T = .run e2T := by kernel_rfl

/-- Frame 2's start configuration. -/
def c2T : Cfg := ⟨e2T.dyna, t_0000_c0, [], callCfg.keys, cp2T.adrs, callCfg.stor,
  acsTransfer cp2T.f.inner acs1T⟩

/-- Frame 2 at its `CALL` of `A'` (step 339). -/
def cfg339T : Cfg :=
  match wrun fs1 e2T.sta 339 c2T with
  | .cont c => c
  | _ => c2T

theorem cfg339T_eq : wrun fs1 e2T.sta 339 c2T = .cont cfg339T := by kernel_rfl

/-! ### Frame 3: `A'` re-entered -/

/-- `A'`'s program (its lifted certificate). -/
abbrev fs3 : List SFunc := Cert.prog Attacker2.cert

def start3T : Option (Evm × Cfg) := childStart e2T.sta cfg339T Attacker2.t_0000_c0

/-- The machine the callback frame enters with. -/
def e3T : Evm := match start3T with | some (e, _) => e | none => default

/-- The callback frame's start configuration. -/
def cc3T : Cfg := match start3T with | some (_, c) => c | none => c2T

theorem start3T_eq : childStart e2T.sta cfg339T Attacker2.t_0000_c0 = some (e3T, cc3T) := by
  kernel_rfl

/-- `A'` (callback) at its `CALL` of `P`. -/
def aCallT : Cfg := match wrun fs3 e3T.sta 32 cc3T with | .cont c => c | _ => c2T

theorem aCallT_eq : wrun fs3 e3T.sta 32 cc3T = .cont aCallT := by kernel_rfl

/-- `A'`'s `CALL` of `P` up to its spawn. -/
def cp4T : CallPrep := (callPrep e3T.sta aCallT).getD noPrep

theorem cp4T_eq : callPrep e3T.sta aCallT = some cp4T := by kernel_rfl

/-! ### Frame 4: the proxy, `add_liquidity` -/

/-- The machine the proxy frame (`add_liquidity`) enters with. -/
def e4T : Evm := match frameEnterS cp4T.f aCallT.acs with | .run e => e | .done _ => default

theorem e4T_eq : frameEnterS cp4T.f aCallT.acs = .run e4T := by kernel_rfl

def adrs4T : List Adr := cp4T.adrs
def acs4T : AcctShadow := acsTransfer cp4T.f.inner aCallT.acs

/-- The proxy at its `DELEGATECALL` (pc 31). -/
def e4T31 : Evm :=
  ⟨31, e4T.sta, e4T.dyna.setMach
    ⟨[(28120398 : Nat).toB256, implementationAddress.toB256, 0, (132 : Nat).toB256, 0, 0, 0],
      Mem.empty.write 0 e4T.sta.data, 28120398, e4T.dyna.stateGas⟩⟩

theorem prefix4T : stepN 11 e4T = some e4T31 := by kernel_rfl

/-- The proxy's `DELEGATECALL` up to its spawn. -/
def cp5T : CallPrep := (dcallPrep e4T31.sta e4T31.dyna adrs4T acs4T).getD noPrep

theorem cp5T_eq : dcallPrep e4T31.sta e4T31.dyna adrs4T acs4T = some cp5T := by kernel_rfl

/-! ### Frame 5: the implementation's reentrant `add_liquidity` -/

/-- The machine the implementation frame enters with. -/
def e5T : Evm := match frameEnterS cp5T.f acs4T with | .run e => e | .done _ => default

theorem e5T_eq : frameEnterS cp5T.f acs4T = .run e5T := by kernel_rfl

/-- Frame 5's start configuration: the shadows of frame 3's `CALL` with the implementation
added to the address shadow. -/
def c5T : Cfg := ⟨e5T.dyna, t_0000_c0, [], aCallT.keys, cp5T.adrs, aCallT.stor,
  acsTransfer cp5T.f.inner acs4T⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
