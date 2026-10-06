import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedAddInputs

/-! Exact old and Reach boundary applications of the same symbolic mint cut.
Only the851/37prefixes supply finite input evidence; the40step cut itself is
proved by `mint_from_obs`. No complete old frame or desired-cut premise is used. -/
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedAddInputsInstances

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedAddInputs

/-- One summary observes the selected continuation, all local inputs and gas.
The interpreter remains the existing `wrun`; this is only a result projection. -/
def mintChecked (s : Sevm) (A : Adr) : Res → SFunc × Bool × Nat
  | .cont c => (c.f, mintObs s A (.cont c), c.devm.gasLeft)
  | _ => (.undefined, false, 0)

def oldStart (m : Meta) (w : World) : Cfg := Boundary.cfgOf Subtree.bnd3563 m w

def newStart (m : Meta) (w : World) : Cfg :=
  Boundary.cfgOfT Reach.Viol.bRe4377 [] [] m w

def oldRun (m : Meta) (w : World) : Res :=
  wrun (Cert.prog cert) Subtree.sta4 851 (oldStart m w)

def newRun (m : Meta) (w : World) : Res :=
  wrun (Cert.prog cert) Reach.Viol.sRe 37 (newStart m w)

/-- Bounded actual old prefix, all required finite observations checked together. -/
private theorem old_summary : ∀ (m : Meta) (w : World),
    mintChecked Subtree.sta4 Frame1.attackerAddress (oldRun m w) =
      (t_071a_c4, true, 28066535) := by
  kernel_forall_rfl

/-- Bounded actual Reach prefix, with the same summary and symbolic consumer. -/
private theorem new_summary : ∀ (m : Meta) (w : World),
    mintChecked Reach.Viol.sRe Reach.attackerAddr (newRun m w) =
      (t_071a_c4, true, 822206) := by
  kernel_forall_rfl

private theorem mintChecked_cfg (s : Sevm) (A : Adr) (r : Res) (fallback : Cfg) (gas : Nat)
    (h : mintChecked s A r = (t_071a_c4, true, gas)) :
    let c := match (generalizing := false) r with | .cont c => c | _ => fallback
    r = .cont c ∧ c.f = t_071a_c4 ∧ mintObs s A (.cont c) = true ∧ c.devm.gasLeft = gas := by
  cases r with
  | cont c =>
    simp only [mintChecked, Prod.mk.injEq] at h
    exact ⟨rfl, h.1, h.2.1, h.2.2⟩
  | done o c =>
    have hb := congrArg (fun x : SFunc × Bool × Nat => x.2.1) h
    simp only [mintChecked, Bool.false_eq_true] at hb
  | stuck =>
    have hb := congrArg (fun x : SFunc × Bool × Nat => x.2.1) h
    simp only [mintChecked, Bool.false_eq_true] at hb


def old4414 (m : Meta) (w : World) : Cfg :=
  match oldRun m w with | .cont c => c | _ => oldStart m w

def new4414 (m : Meta) (w : World) : Cfg :=
  match newRun m w with | .cont c => c | _ => newStart m w

private theorem old_facts (m : Meta) (w : World) :
    oldRun m w = .cont (old4414 m w) ∧
    (old4414 m w).f = t_071a_c4 ∧
    mintObs Subtree.sta4 Frame1.attackerAddress (.cont (old4414 m w)) = true ∧
    (old4414 m w).devm.gasLeft = 28066535 :=
  mintChecked_cfg Subtree.sta4 Frame1.attackerAddress (oldRun m w) (oldStart m w)
    28066535 (old_summary m w)

private theorem new_facts (m : Meta) (w : World) :
    newRun m w = .cont (new4414 m w) ∧
    (new4414 m w).f = t_071a_c4 ∧
    mintObs Reach.Viol.sRe Reach.attackerAddr (.cont (new4414 m w)) = true ∧
    (new4414 m w).devm.gasLeft = 822206 :=
  mintChecked_cfg Reach.Viol.sRe Reach.attackerAddr (newRun m w) (newStart m w)
    822206 (new_summary m w)

/-- Named real old prefix fact rules out the fallback configuration. -/
theorem old_prefix (m : Meta) (w : World) :
    wrun (Cert.prog cert) Subtree.sta4 851 (oldStart m w) = .cont (old4414 m w) :=
  (old_facts m w).1

/-- Named real Reach prefix fact rules out the fallback configuration. -/
theorem new_prefix (m : Meta) (w : World) :
    wrun (Cert.prog cert) Reach.Viol.sRe 37 (newStart m w) = .cont (new4414 m w) :=
  (new_facts m w).1

/-- The historical recipient/hash consumes the shared symbolic40-step theorem. -/
theorem old_mint (m : Meta) (w : World) :
    let c := old4414 m w
    wrun (Cert.prog cert) Subtree.sta4 40 c =
      .cont (mintPost Subtree.sta4 c.devm c.devm.memory (c.devm.gasLeft - 5155)
        Frame1.attackerAddress (c.devm.stack.drop 3) c.K c.keys c.adrs c.stor c.acs) :=
  mint_from_obs Subtree.sta4 (old4414 m w) Frame1.attackerAddress
    (old_facts m w).2.1 (old_facts m w).2.2.1

/-- The Reach recipient/hash consumes that same theorem, without execution dispatch. -/
theorem new_mint (m : Meta) (w : World) :
    let c := new4414 m w
    wrun (Cert.prog cert) Reach.Viol.sRe 40 c =
      .cont (mintPost Reach.Viol.sRe c.devm c.devm.memory (c.devm.gasLeft - 5155)
        Reach.attackerAddr (c.devm.stack.drop 3) c.K c.keys c.adrs c.stor c.acs) :=
  mint_from_obs Reach.Viol.sRe (new4414 m w) Reach.attackerAddr
    (new_facts m w).2.1 (new_facts m w).2.2.1

theorem old_entryGas (m : Meta) (w : World) : (old4414 m w).devm.gasLeft = 28066535 :=
  (old_facts m w).2.2.2

theorem new_entryGas (m : Meta) (w : World) : (new4414 m w).devm.gasLeft = 822206 :=
  (new_facts m w).2.2.2


/-- Actual old boundary3563→4454, by851checked-prefix +40proved-cut composition. -/
theorem old_prefix_mint (m : Meta) (w : World) :
    let c := old4414 m w
    wrun (Cert.prog cert) Subtree.sta4 891 (oldStart m w) =
      .cont (mintPost Subtree.sta4 c.devm c.devm.memory (c.devm.gasLeft - 5155)
        Frame1.attackerAddress (c.devm.stack.drop 3) c.K c.keys c.adrs c.stor c.acs) :=
  wrun_add_cont (old_prefix m w) (old_mint m w)

/-- Actual Reach boundary4377→4454, by37checked-prefix +that same40proved-cut. -/
theorem new_prefix_mint (m : Meta) (w : World) :
    let c := new4414 m w
    wrun (Cert.prog cert) Reach.Viol.sRe 77 (newStart m w) =
      .cont (mintPost Reach.Viol.sRe c.devm c.devm.memory (c.devm.gasLeft - 5155)
        Reach.attackerAddr (c.devm.stack.drop 3) c.K c.keys c.adrs c.stor c.acs) :=
  wrun_add_cont (new_prefix m w) (new_mint m w)

theorem old_postGas (m : Meta) (w : World) :
    (mintPost Subtree.sta4 (old4414 m w).devm (old4414 m w).devm.memory
      ((old4414 m w).devm.gasLeft - 5155) Frame1.attackerAddress
      ((old4414 m w).devm.stack.drop 3) (old4414 m w).K (old4414 m w).keys
      (old4414 m w).adrs (old4414 m w).stor (old4414 m w).acs).devm.gasLeft = 28061380 := by
  simp only [mintPost, St, Devm.gasLeft, Devm.setMach, old_entryGas, Nat.reduceSub]

theorem new_postGas (m : Meta) (w : World) :
    (mintPost Reach.Viol.sRe (new4414 m w).devm (new4414 m w).devm.memory
      ((new4414 m w).devm.gasLeft - 5155) Reach.attackerAddr
      ((new4414 m w).devm.stack.drop 3) (new4414 m w).K (new4414 m w).keys
      (new4414 m w).adrs (new4414 m w).stor (new4414 m w).acs).devm.gasLeft = 817051 := by
  simp only [mintPost, St, Devm.gasLeft, Devm.setMach, new_entryGas, Nat.reduceSub]


end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedAddInputsInstances
