import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Run
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Entry

/-!
V- as an admitted transaction, the entry facts of the deep chain: each frame's start
configuration agrees with the shadows (its accessed sets, storage and accounts are the spawn's),
so that a run from it is a run of the real frame.  The proxy frames (1 and 4) are entered by a
`CALL` whose spawn `callPrep_spec` describes; the implementation frames (2 and 5) by the
proxy's `DELEGATECALL` (`dcallPrep_spec`); the callback frame 3 by `childStart_agree`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

attribute [local irreducible] callCfgC cp0C e1C cp2C e2C cfg339C e3C cc3C aCallC cp4C e4C cp5C e5C

/-! ### The proxy frame 1's entry (spawned by `A'`'s `CALL`) -/

/-- The proxy frame's entry machine keeps the spawn message's accessed sets, and its world is
the one the value transfer made. -/
theorem e1C_meta : ∃ benv, benvAfterTransferS cp0C.f.inner callCfgC.acs = .ok benv ∧
    e1C.dyna.accessedAddresses = cp0C.f.inner.accessedAddresses ∧
    e1C.dyna.accessedStorageKeys = cp0C.f.inner.accessedStorageKeys ∧
    e1C.dyna.state = benv.state := by
  obtain ⟨benv, hb, he⟩ := frameEnterS_run e1C_eq
  exact ⟨benv, hb, by rw [he]; rfl, by rw [he]; rfl, by rw [he]; rfl⟩

/-- The proxy's accessed addresses at entry agree with `adrs1C`. -/
theorem e1C_adrs : ∀ a, a ∈ e1C.dyna.accessedAddresses ↔ a ∈ adrs1C := by
  obtain ⟨-, hpa, -, -, hia, -, -, -⟩ := cp0C_spec
  obtain ⟨benv, -, ha, -, -⟩ := e1C_meta
  intro a
  rw [ha, hia]; exact hpa a

/-- The proxy's accessed storage keys at entry agree with `A'`'s at its `CALL`. -/
theorem e1C_keys : ∀ x, x ∈ e1C.dyna.accessedStorageKeys ↔ x ∈ callCfgC.keys := by
  obtain ⟨-, -, hpk, -, -, hik, -, -⟩ := cp0C_spec
  obtain ⟨benv, -, -, hk, -⟩ := e1C_meta
  intro x
  rw [hk, hik, hpk]; exact callCfgC_agree.1 x

/-- The proxy's world at entry: `A'`'s storage, the accounts after the transfer. -/
theorem e1C_world : (∀ a k, storOf e1C.dyna.state a k = lookupS callCfgC.stor a k) ∧
    AcctAgree e1C.dyna.state acs1C := by
  obtain ⟨-, -, -, -, -, -, -, hst⟩ := cp0C_spec
  have hC : AcctAgree cp0C.f.inner.benv.state callCfgC.acs := by
    rw [hst]; exact callCfgC_agree.2.2.2
  obtain ⟨benv, hb, -, -, hs⟩ := e1C_meta
  have hbB : benvAfterTransferB cp0C.f.inner = .ok benv := by
    rw [benvAfterTransfer_eq_S hC]; exact hb
  rw [hs]
  refine ⟨fun a k => ?_, acctAgree_transfer hC hb⟩
  rw [benvAfterTransferB_stor hbB, hst]; exact callCfgC_agree.2.2.1 a k

theorem e1C31_acc : e1C31.dyna.accessedAddresses = e1C.dyna.accessedAddresses := rfl
theorem e1C31_keys : e1C31.dyna.accessedStorageKeys = e1C.dyna.accessedStorageKeys := rfl
theorem e1C31_state : e1C31.dyna.state = e1C.dyna.state := rfl

theorem cp2C_spec :
    Xinst.step e1C31.sta e1C31.dyna .delegatecall = .spawn cp2C.f (.call cp2C.p cp2C.oi cp2C.os) ∧
      (∀ a, a ∈ cp2C.p.accessedAddresses ↔ a ∈ cp2C.adrs) ∧
      cp2C.p.accessedStorageKeys = e1C31.dyna.accessedStorageKeys ∧
      cp2C.f.isCreate = false ∧ cp2C.f.inner.accessedAddresses = cp2C.p.accessedAddresses ∧
      cp2C.f.inner.accessedStorageKeys = cp2C.p.accessedStorageKeys ∧
      cp2C.f.inner.benv.stat.rules.stateGas = none ∧ cp2C.f.inner.benv.state = e1C31.dyna.state ∧
      cp2C.p.state = e1C31.dyna.state :=
  dcallPrep_spec cp2C_eq (fun a => by rw [e1C31_acc]; exact e1C_adrs a)
    (by rw [e1C31_state]; exact e1C_world.2)

/-- **Frame 2 starts in agreement**: its accessed sets, storage and accounts are the proxy
frame's, the implementation added. -/
theorem c2C_agree : Agree c2C := by
  obtain ⟨-, hpa, hpk, -, hia, hik, -, hst, -⟩ := cp2C_spec
  exact frameStart_agree t_0000_c0 e2C_eq
    (fun x => by rw [hik, hpk, e1C31_keys]; exact e1C_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e1C31_state]; exact e1C_world.1 a k)
    (by rw [hst, e1C31_state]; exact e1C_world.2)

theorem agree_cfg339C : Agree cfg339C := (wrun_cont cfg339C_eq).1 c2C_agree

/-- `A'` at its `CALL` of `P` (frame 3) agrees. -/
theorem agree_aCallC : Agree aCallC :=
  (wrun_cont aCallC_eq).1 (childStart_agree agree_cfg339C start3C_eq)

/-! ### The proxy frame 4's entry (spawned by `A'`'s callback `CALL`) -/

theorem cp4C_spec :
    Xinst.step e3C.sta aCallC.devm .call = .spawn cp4C.f (.call cp4C.p cp4C.oi cp4C.os) ∧
      (∀ a, a ∈ cp4C.p.accessedAddresses ↔ a ∈ cp4C.adrs) ∧
      cp4C.p.accessedStorageKeys = aCallC.devm.accessedStorageKeys ∧
      cp4C.f.isCreate = false ∧ cp4C.f.inner.accessedAddresses = cp4C.p.accessedAddresses ∧
      cp4C.f.inner.accessedStorageKeys = cp4C.p.accessedStorageKeys ∧
      cp4C.f.inner.benv.stat.rules.stateGas = none ∧ cp4C.f.inner.benv.state = aCallC.devm.state :=
  callPrep_spec cp4C_eq agree_aCallC.2.1 agree_aCallC.2.2.2

theorem e4C_meta : ∃ benv, benvAfterTransferS cp4C.f.inner aCallC.acs = .ok benv ∧
    e4C.dyna.accessedAddresses = cp4C.f.inner.accessedAddresses ∧
    e4C.dyna.accessedStorageKeys = cp4C.f.inner.accessedStorageKeys ∧
    e4C.dyna.state = benv.state := by
  obtain ⟨benv, hb, he⟩ := frameEnterS_run e4C_eq
  exact ⟨benv, hb, by rw [he]; rfl, by rw [he]; rfl, by rw [he]; rfl⟩

theorem e4C_adrs : ∀ a, a ∈ e4C.dyna.accessedAddresses ↔ a ∈ adrs4C := by
  obtain ⟨-, hpa, -, -, hia, -, -, -⟩ := cp4C_spec
  obtain ⟨benv, -, ha, -, -⟩ := e4C_meta
  intro a
  rw [ha, hia]; exact hpa a

theorem e4C_keys : ∀ x, x ∈ e4C.dyna.accessedStorageKeys ↔ x ∈ aCallC.keys := by
  obtain ⟨-, -, hpk, -, -, hik, -, -⟩ := cp4C_spec
  obtain ⟨benv, -, -, hk, -⟩ := e4C_meta
  intro x
  rw [hk, hik, hpk]; exact agree_aCallC.1 x

theorem e4C_world : (∀ a k, storOf e4C.dyna.state a k = lookupS aCallC.stor a k) ∧
    AcctAgree e4C.dyna.state acs4C := by
  obtain ⟨-, -, -, -, -, -, -, hst⟩ := cp4C_spec
  have hC : AcctAgree cp4C.f.inner.benv.state aCallC.acs := by
    rw [hst]; exact agree_aCallC.2.2.2
  obtain ⟨benv, hb, -, -, hs⟩ := e4C_meta
  have hbB : benvAfterTransferB cp4C.f.inner = .ok benv := by
    rw [benvAfterTransfer_eq_S hC]; exact hb
  rw [hs]
  refine ⟨fun a k => ?_, acctAgree_transfer hC hb⟩
  rw [benvAfterTransferB_stor hbB, hst]; exact agree_aCallC.2.2.1 a k

theorem e4C31_acc : e4C31.dyna.accessedAddresses = e4C.dyna.accessedAddresses := rfl
theorem e4C31_keys : e4C31.dyna.accessedStorageKeys = e4C.dyna.accessedStorageKeys := rfl
theorem e4C31_state : e4C31.dyna.state = e4C.dyna.state := rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
