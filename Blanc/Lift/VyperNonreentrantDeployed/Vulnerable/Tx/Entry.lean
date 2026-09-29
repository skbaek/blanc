import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Run

/-!
V- as an admitted transaction, the entry facts of the deep chain: each frame's start
configuration agrees with the shadows (its accessed sets, storage and accounts are the spawn's),
so that a run from it is a run of the real frame.  The proxy frames (1 and 4) are entered by a
`CALL` whose spawn `callPrep_spec` describes; the implementation frames (2 and 5) by the
proxy's `DELEGATECALL` (`dcallPrep_spec`); the callback frame 3 by `childStart_agree`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

attribute [local irreducible] callCfg cp0 e1T cp2T e2T cfg339T e3T cc3T aCallT cp4T e4T cp5T e5T

/-! ### The proxy frame 1's entry (spawned by `A'`'s `CALL`) -/

/-- The proxy frame's entry machine keeps the spawn message's accessed sets, and its world is
the one the value transfer made. -/
theorem e1T_meta : ∃ benv, benvAfterTransferS cp0.f.inner callCfg.acs = .ok benv ∧
    e1T.dyna.accessedAddresses = cp0.f.inner.accessedAddresses ∧
    e1T.dyna.accessedStorageKeys = cp0.f.inner.accessedStorageKeys ∧
    e1T.dyna.state = benv.state := by
  obtain ⟨benv, hb, he⟩ := frameEnterS_run e1T_eq
  exact ⟨benv, hb, by rw [he]; rfl, by rw [he]; rfl, by rw [he]; rfl⟩

/-- The proxy's accessed addresses at entry agree with `adrs1T`. -/
theorem e1T_adrs : ∀ a, a ∈ e1T.dyna.accessedAddresses ↔ a ∈ adrs1T := by
  obtain ⟨-, hpa, -, -, hia, -, -, -⟩ := cp0_spec
  obtain ⟨benv, -, ha, -, -⟩ := e1T_meta
  intro a
  rw [ha, hia]; exact hpa a

/-- The proxy's accessed storage keys at entry agree with `A'`'s at its `CALL`. -/
theorem e1T_keys : ∀ x, x ∈ e1T.dyna.accessedStorageKeys ↔ x ∈ callCfg.keys := by
  obtain ⟨-, -, hpk, -, -, hik, -, -⟩ := cp0_spec
  obtain ⟨benv, -, -, hk, -⟩ := e1T_meta
  intro x
  rw [hk, hik, hpk]; exact callCfg_agree.1 x

/-- The proxy's world at entry: `A'`'s storage, the accounts after the transfer. -/
theorem e1T_world : (∀ a k, storOf e1T.dyna.state a k = lookupS callCfg.stor a k) ∧
    AcctAgree e1T.dyna.state acs1T := by
  obtain ⟨-, -, -, -, -, -, -, hst⟩ := cp0_spec
  have hC : AcctAgree cp0.f.inner.benv.state callCfg.acs := by
    rw [hst]; exact callCfg_agree.2.2.2
  obtain ⟨benv, hb, -, -, hs⟩ := e1T_meta
  have hbB : benvAfterTransferB cp0.f.inner = .ok benv := by
    rw [benvAfterTransfer_eq_S hC]; exact hb
  rw [hs]
  refine ⟨fun a k => ?_, acctAgree_transfer hC hb⟩
  rw [benvAfterTransferB_stor hbB, hst]; exact callCfg_agree.2.2.1 a k

theorem e1T31_acc : e1T31.dyna.accessedAddresses = e1T.dyna.accessedAddresses := rfl
theorem e1T31_keys : e1T31.dyna.accessedStorageKeys = e1T.dyna.accessedStorageKeys := rfl
theorem e1T31_state : e1T31.dyna.state = e1T.dyna.state := rfl

theorem cp2T_spec :
    Xinst.step e1T31.sta e1T31.dyna .delegatecall = .spawn cp2T.f (.call cp2T.p cp2T.oi cp2T.os) ∧
      (∀ a, a ∈ cp2T.p.accessedAddresses ↔ a ∈ cp2T.adrs) ∧
      cp2T.p.accessedStorageKeys = e1T31.dyna.accessedStorageKeys ∧
      cp2T.f.isCreate = false ∧ cp2T.f.inner.accessedAddresses = cp2T.p.accessedAddresses ∧
      cp2T.f.inner.accessedStorageKeys = cp2T.p.accessedStorageKeys ∧
      cp2T.f.inner.benv.stat.rules.stateGas = none ∧ cp2T.f.inner.benv.state = e1T31.dyna.state ∧
      cp2T.p.state = e1T31.dyna.state :=
  dcallPrep_spec cp2T_eq (fun a => by rw [e1T31_acc]; exact e1T_adrs a)
    (by rw [e1T31_state]; exact e1T_world.2)

/-- **Frame 2 starts in agreement**: its accessed sets, storage and accounts are the proxy
frame's, the implementation added. -/
theorem c2T_agree : Agree c2T := by
  obtain ⟨-, hpa, hpk, -, hia, hik, -, hst, -⟩ := cp2T_spec
  exact frameStart_agree t_0000_c0 e2T_eq
    (fun x => by rw [hik, hpk, e1T31_keys]; exact e1T_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e1T31_state]; exact e1T_world.1 a k)
    (by rw [hst, e1T31_state]; exact e1T_world.2)

theorem agree_cfg339T : Agree cfg339T := (wrun_cont cfg339T_eq).1 c2T_agree

/-- `A'` at its `CALL` of `P` (frame 3) agrees. -/
theorem agree_aCallT : Agree aCallT :=
  (wrun_cont aCallT_eq).1 (childStart_agree agree_cfg339T start3T_eq)

/-! ### The proxy frame 4's entry (spawned by `A'`'s callback `CALL`) -/

theorem cp4T_spec :
    Xinst.step e3T.sta aCallT.devm .call = .spawn cp4T.f (.call cp4T.p cp4T.oi cp4T.os) ∧
      (∀ a, a ∈ cp4T.p.accessedAddresses ↔ a ∈ cp4T.adrs) ∧
      cp4T.p.accessedStorageKeys = aCallT.devm.accessedStorageKeys ∧
      cp4T.f.isCreate = false ∧ cp4T.f.inner.accessedAddresses = cp4T.p.accessedAddresses ∧
      cp4T.f.inner.accessedStorageKeys = cp4T.p.accessedStorageKeys ∧
      cp4T.f.inner.benv.stat.rules.stateGas = none ∧ cp4T.f.inner.benv.state = aCallT.devm.state :=
  callPrep_spec cp4T_eq agree_aCallT.2.1 agree_aCallT.2.2.2

theorem e4T_meta : ∃ benv, benvAfterTransferS cp4T.f.inner aCallT.acs = .ok benv ∧
    e4T.dyna.accessedAddresses = cp4T.f.inner.accessedAddresses ∧
    e4T.dyna.accessedStorageKeys = cp4T.f.inner.accessedStorageKeys ∧
    e4T.dyna.state = benv.state := by
  obtain ⟨benv, hb, he⟩ := frameEnterS_run e4T_eq
  exact ⟨benv, hb, by rw [he]; rfl, by rw [he]; rfl, by rw [he]; rfl⟩

theorem e4T_adrs : ∀ a, a ∈ e4T.dyna.accessedAddresses ↔ a ∈ adrs4T := by
  obtain ⟨-, hpa, -, -, hia, -, -, -⟩ := cp4T_spec
  obtain ⟨benv, -, ha, -, -⟩ := e4T_meta
  intro a
  rw [ha, hia]; exact hpa a

theorem e4T_keys : ∀ x, x ∈ e4T.dyna.accessedStorageKeys ↔ x ∈ aCallT.keys := by
  obtain ⟨-, -, hpk, -, -, hik, -, -⟩ := cp4T_spec
  obtain ⟨benv, -, -, hk, -⟩ := e4T_meta
  intro x
  rw [hk, hik, hpk]; exact agree_aCallT.1 x

theorem e4T_world : (∀ a k, storOf e4T.dyna.state a k = lookupS aCallT.stor a k) ∧
    AcctAgree e4T.dyna.state acs4T := by
  obtain ⟨-, -, -, -, -, -, -, hst⟩ := cp4T_spec
  have hC : AcctAgree cp4T.f.inner.benv.state aCallT.acs := by
    rw [hst]; exact agree_aCallT.2.2.2
  obtain ⟨benv, hb, -, -, hs⟩ := e4T_meta
  have hbB : benvAfterTransferB cp4T.f.inner = .ok benv := by
    rw [benvAfterTransfer_eq_S hC]; exact hb
  rw [hs]
  refine ⟨fun a k => ?_, acctAgree_transfer hC hb⟩
  rw [benvAfterTransferB_stor hbB, hst]; exact agree_aCallT.2.2.1 a k

theorem e4T31_acc : e4T31.dyna.accessedAddresses = e4T.dyna.accessedAddresses := rfl
theorem e4T31_keys : e4T31.dyna.accessedStorageKeys = e4T.dyna.accessedStorageKeys := rfl
theorem e4T31_state : e4T31.dyna.state = e4T.dyna.state := rfl

theorem cp5T_spec :
    Xinst.step e4T31.sta e4T31.dyna .delegatecall = .spawn cp5T.f (.call cp5T.p cp5T.oi cp5T.os) ∧
      (∀ a, a ∈ cp5T.p.accessedAddresses ↔ a ∈ cp5T.adrs) ∧
      cp5T.p.accessedStorageKeys = e4T31.dyna.accessedStorageKeys ∧
      cp5T.f.isCreate = false ∧ cp5T.f.inner.accessedAddresses = cp5T.p.accessedAddresses ∧
      cp5T.f.inner.accessedStorageKeys = cp5T.p.accessedStorageKeys ∧
      cp5T.f.inner.benv.stat.rules.stateGas = none ∧ cp5T.f.inner.benv.state = e4T31.dyna.state ∧
      cp5T.p.state = e4T31.dyna.state :=
  dcallPrep_spec cp5T_eq (fun a => by rw [e4T31_acc]; exact e4T_adrs a)
    (by rw [e4T31_state]; exact e4T_world.2)

/-- **Frame 5 starts in agreement.** -/
theorem c5T_agree : Agree c5T := by
  obtain ⟨-, hpa, hpk, -, hia, hik, -, hst, -⟩ := cp5T_spec
  exact frameStart_agree t_0000_c0 e5T_eq
    (fun x => by rw [hik, hpk, e4T31_keys]; exact e4T_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e4T31_state]; exact e4T_world.1 a k)
    (by rw [hst, e4T31_state]; exact e4T_world.2)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
