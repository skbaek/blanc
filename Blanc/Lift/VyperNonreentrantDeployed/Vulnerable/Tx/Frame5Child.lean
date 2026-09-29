import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5Full
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Entry
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Child

/-!
V- as an admitted transaction, frame 5 as a child: the implementation frame the proxy's
`DELEGATECALL` spawns is an `Exec` of the 0x6326 certificate's code (`lift_exactM`) from the
machine it enters with, settles to its halted machine `post5T`, and `post5T`'s accessed sets,
storage and accounts are `keys5T`/`adrs5T`/`storAT`/`acsAT`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree (haltedOf haltCfgOf)

attribute [local irreducible] callCfg cp0 e1T cp2T e2T cfg339T e3T cc3T aCallT cp4T e4T cp5T e5T

/-- Frame 5 runs the registered certificate's code: the fixture's implementation account holds
that very constant. -/
theorem e5T_code_fork : (e5T.sta.code, e5T.sta.benvStat.fork) = (code, .prague) := by kernel_rfl

theorem e5T_code : e5T.sta.code = code := (Prod.mk.inj e5T_code_fork).1

theorem e5T_fork : CoveredFork e5T.sta.benvStat.fork := by
  rw [(Prod.mk.inj e5T_code_fork).2]; exact CoveredFork.prague

/-- Frame 5's halted (and settled) machine. -/
def post5T : Devm := haltedOf r5

/-- Frame 5's halting configuration. -/
def cl5T : Cfg := haltCfgOf r5

/-- What a halt with frame 5's observation is. -/
theorem obs5_facts {r : Res} (h : obs5 r = obs5EELS) : ∃ d cl, r = .done (.halted d) cl ∧
    d.gasLeft = gas5T ∧ d.output = word 106 ∧ d.error = none ∧ cl.keys = keys5T ∧
    cl.adrs = adrs5T ∧ cl.stor = storAT ∧ cl.acs = acsAT ∧ d.refundCounter = refund5 ∧
    d.accountsToDelete = .emptyWithCapacity := by
  rcases r with c | ⟨d | d, cl⟩ | _
  · simp [obs5, obs5EELS] at h
  · simp only [obs5, obs5EELS, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨hg, ho, ⟨⟨⟨⟨he, hk⟩, ha⟩, hs⟩, hrf⟩, hc, hatd⟩ := h
    exact ⟨d, cl, rfl, hg, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho,
      Option.isNone_iff_eq_none.mp he, hk, ha, hs, hc, hrf, hatd⟩
  · simp [obs5, obs5EELS] at h
  · simp [obs5, obs5EELS] at h

theorem r5_facts : r5 = .done (.halted post5T) cl5T ∧ post5T.gasLeft = gas5T ∧
    post5T.output = word 106 ∧ post5T.error = none ∧ cl5T.keys = keys5T ∧ cl5T.adrs = adrs5T ∧
    cl5T.stor = storAT ∧ cl5T.acs = acsAT ∧ post5T.refundCounter = refund5 ∧
    post5T.accountsToDelete = .emptyWithCapacity := by
  obtain ⟨d, cl, hr, h⟩ := obs5_facts frame5_kernel
  have hd : post5T = d := congrArg haltedOf hr
  have hc : cl5T = cl := congrArg haltCfgOf hr
  subst hd hc
  exact ⟨hr, h⟩

/-- **Frame 5 as the proxy's child.** -/
theorem frame5_child : Nonempty (Exec e5T.pc e5T.sta e5T.dyna (.ok post5T)) ∧
    cp5T.f.settle (.ok post5T) = .ok post5T ∧ ChildAgree post5T keys5T adrs5T storAT acsAT := by
  obtain ⟨hrun, -, -, herr, hk, ha, hs, hc, -, -⟩ := r5_facts
  obtain ⟨-, hpa, hpk, hcr, hia, hik, hsg, hst, -⟩ := cp5T_spec
  have h := frame_of_wrun (fs := fs1) (f := cp5T.f) (acs := acs4T) (keys := aCallT.keys)
    (adrs := cp5T.adrs) (stor := aCallT.stor) (n := 4505) e5T_eq
    (fun x => by rw [hik, hpk, e4T31_keys]; exact e4T_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e4T31_state]; exact e4T_world.1 a k)
    (by rw [hst, e4T31_state]; exact e4T_world.2) hcr hsg
    (fun hr => lift_exactM cert_checkM cert_jumpsOkM e5T_code e5T_fork hr) fs1_zero
    ⟨id, fun _ _ r => r⟩ hrun herr
  rw [hk, ha, hs, hc] at h
  exact h

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
