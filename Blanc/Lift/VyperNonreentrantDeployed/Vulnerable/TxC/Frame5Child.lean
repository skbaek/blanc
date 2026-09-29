import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5Full
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Fork
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Child
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5Child

/-!
V- as an admitted transaction, frame 5 as a child: the implementation frame the proxy's
`DELEGATECALL` spawns is an `Exec` of the 0x6326 certificate's code (`lift_exactM`) from the
machine it enters with, settles to its halted machine `post5C`, and `post5C`'s accessed sets,
storage and accounts are `keys5T`/`adrs5C`/`storAT`/`acsAT`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree (haltedOf haltCfgOf)

attribute [local irreducible] callCfgC cp0C e1C cp2C e2C cfg339C e3C cc3C aCallC cp4C e4C cp5C e5C

variable {g : Fork}

/-- Frame 5 runs the registered certificate's code: the fixture's implementation account holds
that very constant. -/
theorem e5C_code : e5C.sta.code = code := by kernel_rfl

/-- Frame 5's halted (and settled) machine. -/
def post5C : Devm := haltedOf r5C

/-- Frame 5's halting configuration. -/
def cl5C : Cfg := haltCfgOf r5C

/-- What a halt with frame 5's observation is. -/
theorem obs5C_facts {r : Res} (h : obs5C r = obs5EELSC) : ∃ d cl, r = .done (.halted d) cl ∧
    d.gasLeft = gas5C ∧ d.output = word 106 ∧ d.error = none ∧ cl.keys = keys5T ∧
    cl.adrs = adrs5C ∧ cl.stor = storAT ∧ cl.acs = acsAT ∧ d.refundCounter = refund5 ∧
    d.accountsToDelete = .emptyWithCapacity := by
  rcases r with c | ⟨d | d, cl⟩ | _
  · simp [obs5C, obs5EELSC] at h
  · simp only [obs5C, obs5EELSC, Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨hg, ho, ⟨⟨⟨⟨he, hk⟩, ha⟩, hs⟩, hrf⟩, hc, hatd⟩ := h
    exact ⟨d, cl, rfl, hg, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho,
      Option.isNone_iff_eq_none.mp he, hk, ha, hs, hc, hrf, hatd⟩
  · simp [obs5C, obs5EELSC] at h
  · simp [obs5C, obs5EELSC] at h

theorem r5C_facts : r5C = .done (.halted post5C) cl5C ∧ post5C.gasLeft = gas5C ∧
    post5C.output = word 106 ∧ post5C.error = none ∧ cl5C.keys = keys5T ∧ cl5C.adrs = adrs5C ∧
    cl5C.stor = storAT ∧ cl5C.acs = acsAT ∧ post5C.refundCounter = refund5 ∧
    post5C.accountsToDelete = .emptyWithCapacity := by
  obtain ⟨d, cl, hr, h⟩ := obs5C_facts frame5C_kernel
  have hd : post5C = d := congrArg haltedOf hr
  have hc : cl5C = cl := congrArg haltCfgOf hr
  subst hd hc
  exact ⟨hr, h⟩

/-- **Frame 5 as the proxy's child, under any covered fork.** -/
theorem frame5C_child_at (hg : CoveredFork g) :
    Nonempty (Exec (e5C.withFork g).pc (e5C.withFork g).sta (e5C.withFork g).dyna (.ok post5C)) ∧
      (cp5C.withFork g).f.settle (.ok post5C) = .ok post5C ∧
      ChildAgree post5C keys5T adrs5C storAT acsAT := by
  obtain ⟨hrun, -, -, herr, hk, ha, hs, hc, -, -⟩ := r5C_facts
  obtain ⟨-, hpa, hpk, hcr, hia, hik, hsg, hst, -⟩ := cp5C_spec_at hg
  have h := frame_of_wrun (fs := fs1) (f := (cp5C.withFork g).f) (acs := acs4C)
    (keys := aCallC.keys) (adrs := cp5C.adrs) (stor := aCallC.stor) (n := 4505)
    (cevm := e5C.withFork g) (e5C_at hg)
    (fun x => by rw [hik, hpk, e4C31_keys]; exact e4C_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst, e4C31_state]; exact e4C_world.1 a k)
    (by rw [hst, e4C31_state]; exact e4C_world.2) hcr hsg
    (fun hr => lift_exactM cert_checkM cert_jumpsOkM e5C_code (hg : CoveredFork g) hr) fs1_zero
    ⟨id, fun _ _ r => r⟩ ((r5C_at hg).trans hrun) herr
  rw [hk, ha, hs, hc] at h
  exact h

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
