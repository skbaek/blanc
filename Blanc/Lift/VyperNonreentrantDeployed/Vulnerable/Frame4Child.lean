import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Full
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Full
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Check

/-!
V- witness, frame 4 as a child: the implementation frame the proxy's `DELEGATECALL`
spawns is an `Exec` of the 0x6326 certificate's code (`lift_exactM`) from the machine it
enters with, settles to its halted machine `post4`, and `post4`'s accessed sets, storage
and accounts are `keys4`/`adrs4`/`storA`/`acsA`.  Also the proxy frame's entry facts the
spawn needs (its accessed sets and world are the attacker's at its `CALL`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

/-! ### The proxy frame's entry -/

attribute [local irreducible] cfg339 e2 cc2 aCall cp3 e3 cp4 e4

theorem cp3_spec :
    Xinst.step e2.sta aCall.devm .call = .spawn cp3.f (.call cp3.p cp3.oi cp3.os) ∧
      (∀ a, a ∈ cp3.p.accessedAddresses ↔ a ∈ cp3.adrs) ∧
      cp3.p.accessedStorageKeys = aCall.devm.accessedStorageKeys ∧
      cp3.f.isCreate = false ∧ cp3.f.inner.accessedAddresses = cp3.p.accessedAddresses ∧
      cp3.f.inner.accessedStorageKeys = cp3.p.accessedStorageKeys ∧
      cp3.f.inner.benv.stat.rules.stateGas = none ∧ cp3.f.inner.benv.state = aCall.devm.state :=
  callPrep_spec cp3_eq agree_aCall.2.1 agree_aCall.2.2.2

/-- The proxy frame's entry machine keeps the spawn message's accessed sets, and its world
is the one the value transfer made. -/
theorem e3_meta : ∃ benv, benvAfterTransferS cp3.f.inner aCall.acs = .ok benv ∧
    e3.dyna.accessedAddresses = cp3.f.inner.accessedAddresses ∧
    e3.dyna.accessedStorageKeys = cp3.f.inner.accessedStorageKeys ∧
    e3.dyna.state = benv.state := by
  obtain ⟨benv, hb, he⟩ := frameEnterS_run e3_eq
  exact ⟨benv, hb, by rw [he]; rfl, by rw [he]; rfl, by rw [he]; rfl⟩

/-- The proxy's accessed addresses at entry agree with `adrs3`. -/
theorem e3_adrs : ∀ a, a ∈ e3.dyna.accessedAddresses ↔ a ∈ adrs3 := by
  obtain ⟨-, hpa, -, -, hia, -, -, -⟩ := cp3_spec
  obtain ⟨benv, -, ha, -, -⟩ := e3_meta
  intro a
  rw [ha, hia]; exact hpa a

/-- The proxy's accessed storage keys at entry agree with the attacker's at its `CALL`. -/
theorem e3_keys : ∀ x, x ∈ e3.dyna.accessedStorageKeys ↔ x ∈ aCall.keys := by
  obtain ⟨-, -, hpk, -, -, hik, -, -⟩ := cp3_spec
  obtain ⟨benv, -, -, hk, -⟩ := e3_meta
  intro x
  rw [hk, hik, hpk]; exact agree_aCall.1 x

/-- The proxy's world at entry: the attacker's storage, the accounts after the transfer. -/
theorem e3_world : (∀ a k, storOf e3.dyna.state a k = lookupS aCall.stor a k) ∧
    AcctAgree e3.dyna.state acs3 := by
  obtain ⟨-, -, -, -, -, -, -, hst⟩ := cp3_spec
  have hC : AcctAgree cp3.f.inner.benv.state aCall.acs := by rw [hst]; exact agree_aCall.2.2.2
  obtain ⟨benv, hb, -, -, hs⟩ := e3_meta
  have hbB : benvAfterTransferB cp3.f.inner = .ok benv := by
    rw [benvAfterTransfer_eq_S hC]; exact hb
  rw [hs]
  refine ⟨fun a k => ?_, acctAgree_transfer hC hb⟩
  rw [benvAfterTransferB_stor hbB, hst]; exact agree_aCall.2.2.1 a k

theorem e31_acc : e31.dyna.accessedAddresses = e3.dyna.accessedAddresses := rfl
theorem e31_keys : e31.dyna.accessedStorageKeys = e3.dyna.accessedStorageKeys := rfl
theorem e31_state : e31.dyna.state = e3.dyna.state := rfl

theorem cp4_spec :
    Xinst.step e31.sta e31.dyna .delegatecall = .spawn cp4.f (.call cp4.p cp4.oi cp4.os) ∧
      (∀ a, a ∈ cp4.p.accessedAddresses ↔ a ∈ cp4.adrs) ∧
      cp4.p.accessedStorageKeys = e31.dyna.accessedStorageKeys ∧
      cp4.f.isCreate = false ∧ cp4.f.inner.accessedAddresses = cp4.p.accessedAddresses ∧
      cp4.f.inner.accessedStorageKeys = cp4.p.accessedStorageKeys ∧
      cp4.f.inner.benv.stat.rules.stateGas = none ∧ cp4.f.inner.benv.state = e31.dyna.state ∧
      cp4.p.state = e31.dyna.state :=
  dcallPrep_spec cp4_eq (fun a => by rw [e31_acc]; exact e3_adrs a) (by rw [e31_state]; exact e3_world.2)

/-! ### Frame 4 -/

/-- Frame 4 runs the registered certificate's code: the fixture's implementation account
holds that very constant. -/
theorem e4_code_fork : (e4.sta.code, e4.sta.benvStat.fork) = (code, .prague) := by kernel_rfl

theorem e4_code : e4.sta.code = code := (Prod.mk.inj e4_code_fork).1

theorem e4_fork : CoveredFork e4.sta.benvStat.fork := by
  rw [(Prod.mk.inj e4_code_fork).2]; exact CoveredFork.prague

/-- The halted machine of a run's outcome (named, so that an equation about the run
transports to it without the kernel re-evaluating the run). -/
def haltedOf : Res → Devm
  | .done (.halted d) _ => d
  | _ => default

/-- The halting configuration of a run's outcome. -/
def haltCfgOf : Res → Cfg
  | .done (.halted _) cl => cl
  | _ => c0

/-- Frame 4's halted (and settled) machine. -/
def post4 : Devm := haltedOf r4

/-- Frame 4's halting configuration. -/
def cl4 : Cfg := haltCfgOf r4

/-- What a halt with frame 4's observation is. -/
theorem obs4_facts {r : Res} (h : obs4 r = obs4EELS) : ∃ d cl, r = .done (.halted d) cl ∧
    d.gasLeft = gas4 ∧ d.output = word 106 ∧ d.error = none ∧ cl.keys = keys4 ∧
    cl.adrs = adrs4 ∧ cl.stor = storA ∧ cl.acs = acsA := by
  rcases r with c | ⟨d | d, cl⟩ | _
  · simp [obs4, obs4EELS] at h
  · simp only [obs4, obs4EELS, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨hg, ho, ⟨⟨⟨he, hk⟩, ha⟩, hs⟩, hc⟩ := h
    exact ⟨d, cl, rfl, hg, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho,
      Option.isNone_iff_eq_none.mp he, hk, ha, hs, hc⟩
  · simp [obs4, obs4EELS] at h
  · simp [obs4, obs4EELS] at h

theorem r4_facts : r4 = .done (.halted post4) cl4 ∧ post4.gasLeft = gas4 ∧
    post4.output = word 106 ∧ post4.error = none ∧ cl4.keys = keys4 ∧ cl4.adrs = adrs4 ∧
    cl4.stor = storA ∧ cl4.acs = acsA := by
  obtain ⟨d, cl, hr, h⟩ := obs4_facts frame4_kernel
  have hd : post4 = d := congrArg haltedOf hr
  have hc : cl4 = cl := congrArg haltCfgOf hr
  subst hd hc
  exact ⟨hr, h⟩

/-- **Frame 4 as the proxy's child.** -/
theorem frame4_child : Nonempty (Exec e4.pc e4.sta e4.dyna (.ok post4)) ∧
    cp4.f.settle (.ok post4) = .ok post4 ∧ ChildAgree post4 keys4 adrs4 storA acsA := by
  obtain ⟨hrun, -, -, herr, hk, ha, hs, hc⟩ := r4_facts
  obtain ⟨-, hpa, hpk, hcr, hia, hik, hsg, hst, -⟩ := cp4_spec
  have h := frame_of_wrun (fs := fs1) (f := cp4.f) (acs := acs3) (keys := aCall.keys)
    (adrs := cp4.adrs) (stor := aCall.stor) (n := 4505) e4_eq
    (fun x => by rw [hik, hpk, e31_keys]; exact e3_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e31_state]; exact e3_world.1 a k)
    (by rw [hst, e31_state]; exact e3_world.2) hcr hsg
    (fun hr => lift_exactM cert_checkM cert_jumpsOkM e4_code e4_fork hr) fs1_zero
    ⟨id, fun _ _ r => r⟩ hrun herr
  rw [hk, ha, hs, hc] at h
  exact h

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
