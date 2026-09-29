import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5Child
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame3
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame4

/-!
V- as an admitted transaction, frame 4: the proxy `P` (45 bytes) called by `A'`'s callback with
value 100 (`add_liquidity`).  Its eleven childless steps (`stepN`, `prefix4C`), its `DELEGATECALL`
spawning frame 5 (`dcallPrep_spec`), frame 5 as its child (`frame5C_child`), the resume, and its
ten-step tail to `RETURN` (the child's 32 return bytes copied out).  The resume and the tail are
kernel checks over a free child with frame 5's gas and output (`childObs`): frame 5's run is not
re-evaluated.  The result: the proxy frame is an `Exec` from the machine `A'`'s `CALL` enters
with, it settles to its halted machine `post4C`, and `post4C`'s shadows are `A'`'s at its `CALL`
together with frame 5's.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree (proxy_at_delegatecall)

attribute [local irreducible] callCfgC cp0C e1C cp2C e2C cfg339C e3C cc3C aCallC cp4C e4C cp5C e5C post5C

variable {g : Fork}

/-- The proxy resumed from a settled child `d`. -/
def d4C (d : Devm) : Devm := (resumeCallB cp5C.p cp5C.oi cp5C.os (.ok d)).getD default

/-- The proxy at its `RETURN` (pc 44). -/
def e4C44 (d : Devm) : Evm := (stepN 10 ⟨32, e4C.sta, d4C d⟩).getD default

/-- The proxy's halted machine. -/
def post4CF (d : Devm) : Devm :=
  match Evm.step (e4C44 d) with
  | .halt (.ok d') => d'
  | _ => default

/-- Frame 5's settled machine as the proxy's child, its observed parts as literals. -/
abbrev obsChild5C (d : Devm) : Devm := childObsX gas5C (word 106) refund5 d

theorem resume4C_eq : ∀ d : Devm,
    resumeCallB cp5C.p cp5C.oi cp5C.os (.ok (obsChild5C d)) = some (d4C (obsChild5C d)) := by
  kernel_forall_rfl

theorem tail4C_eq : ∀ d : Devm, stepN 10 ⟨32, e4C.sta, d4C (obsChild5C d)⟩ = some (e4C44 (obsChild5C d)) := by
  kernel_forall_rfl

theorem return4C_eq : ∀ d : Devm,
    Evm.step (e4C44 (obsChild5C d)) = .halt (.ok (post4CF (obsChild5C d))) := by
  kernel_forall_rfl

/-- The proxy frame's gas at its `RETURN`, and its return data (the child's). -/
def gas4C : Nat := 14890357

theorem post4C_obs : ∀ d : Devm,
    ((post4CF (obsChild5C d)).gasLeft, (post4CF (obsChild5C d)).output.map UInt8.toNat,
      (post4CF (obsChild5C d)).error.isNone, (post4CF (obsChild5C d)).refundCounter,
      (post4CF (obsChild5C d)).accountsToDelete) =
    (gas4C, (word 106).map UInt8.toNat, true, refund4, .emptyWithCapacity) := by
  kernel_forall_rfl

theorem post4C_keep : ∀ d : Devm,
    ((post4CF (obsChild5C d)).accessedAddresses, (post4CF (obsChild5C d)).accessedStorageKeys,
      (post4CF (obsChild5C d)).state) =
    ((d4C (obsChild5C d)).accessedAddresses, (d4C (obsChild5C d)).accessedStorageKeys,
      (d4C (obsChild5C d)).state) := by
  kernel_forall_rfl

/-- The proxy frame's settled machine. -/
def post4C : Devm := post4CF post5C

theorem obsChild5_post5C : obsChild5C post5C = post5C := by
  obtain ⟨-, hg, ho, he, -, -, -, -, hr, ha⟩ := r5C_facts
  exact childObsX_eq hg ho he hr ha

theorem e4C_code : e4C.sta.code = proxyCode := by kernel_rfl

/-- The shadows frame 4 hands back to `A'`: its own (`A'`'s at its `CALL`) and frame 5's; frame
5's storage and accounts (`storAT`, `acsAT`) pass through. -/
def keysH4C : List (Adr × B256) := aCallC.keys ++ keys5T
def adrsH4C : List Adr := cp5C.adrs ++ adrs5C

/-- **Frame 4 (the proxy) as `A'`'s child, under any covered fork.** -/
theorem frame4C_child_at (hg : CoveredFork g) :
    ChildOk (e3C.withFork g).sta aCallC post4C ∧
      ChildAgree post4C keysH4C adrsH4C storAT acsAT ∧
      post4C.gasLeft = gas4C ∧ post4C.output = word 106 ∧ post4C.error = none ∧
      post4C.refundCounter = refund4 ∧ post4C.accountsToDelete = .emptyWithCapacity := by
  obtain ⟨hx4, hs4, ha4⟩ := frame5C_child_at hg
  obtain ⟨hstep4, hpa, hpk, -, -, -, -, hst4, -⟩ := cp5C_spec_at hg
  obtain ⟨-, -, -, hcr3, -, -, hsg3, -⟩ := cp4C_spec_at hg
  have hr := resume4C_eq post5C
  have ht := tail4C_eq post5C
  have hh := return4C_eq post5C
  have ho := post4C_obs post5C
  have hk := post4C_keep post5C
  rw [obsChild5_post5C] at hr ht hh ho hk
  simp only [Prod.mk.injEq] at ho hk
  obtain ⟨hgas, hout, he, hrf, hatd⟩ := ho
  obtain ⟨hka, hkk, hks⟩ := hk
  have herr : post4C.error = none := Option.isNone_iff_eq_none.mp he
  -- the proxy frame's `Exec`
  have hspawn : Evm.step (e4C31.withFork g) =
      .spawn (cp5C.withFork g).f (.call cp5C.p cp5C.oi cp5C.os) 32 := by
    have hat : Ninst.At (e4C31.withFork g).sta.code 31 (.exec .delegatecall) := by
      show Ninst.At e4C.sta.code 31 (.exec .delegatecall)
      rw [e4C_code]; exact proxy_at_delegatecall
    show Evm.step ⟨31, (e4C31.withFork g).sta, e4C31.dyna⟩ = _
    rw [Evm.step_next hat, Ninst.step_exec, hstep4]
    rfl
  have henter : (cp5C.withFork g).f.enter = .run (e5C.withFork g) := by
    rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [hst4]; exact e4C_world.2)]; exact e5C_at hg
  have hsettle : Resume.run (.call cp5C.p cp5C.oi cp5C.os)
      ((cp5C.withFork g).f.settle (.ok post5C)) = .ok (d4C post5C) := by
    rw [hs4]; exact resumeCallB_sound hr
  have hsta : (e4C44 post5C).sta = e4C.sta := stepN_sta (evm := ⟨32, e4C.sta, d4C post5C⟩) ht
  have hstep_halt : Evm.step ((e4C44 post5C).withFork g) = .halt (.ok (post4CF post5C)) := by
    have hp : (e4C44 post5C).sta.benvStat.fork = .prague := by rw [hsta]; exact e4C_block.1
    have hx : (e4C44 post5C).sta.benvStat.excessBlobGas = 0 := by rw [hsta]; exact e4C_block.2
    rw [show Evm.step ((e4C44 post5C).withFork g) = (Evm.step (e4C44 post5C)).withFork g from
      evm_step_withFork_prague hp hx hg (by rw [hh]; intro ee; nofun), hh]
    rfl
  have hx3 : Nonempty (Exec (e4C.withFork g).pc (e4C.withFork g).sta (e4C.withFork g).dyna
      (.ok post4C)) :=
    exec_of_stepN_spawn_runOk (prefix4C_at hg) hspawn henter hx4 hsettle
      (exec_of_stepN_halt (stepN_withFork hg (e := ⟨32, e4C.sta, d4C post5C⟩) e4C_block.1
        e4C_block.2 ht) hstep_halt)
  -- the proxy frame's shadows
  have hacc := resumeCallB_acc hr
  have hpe : post5C.error.isSome = false := by rw [r5C_facts.2.2.2.1]; rfl
  refine ⟨fun cp cevm hp he' => ?_, ⟨fun a => ?_, fun x => ?_, fun a k => ?_, fun a => ?_⟩,
    hgas, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout, herr, hrf, hatd⟩
  · rw [cp4C_at hg] at hp; cases hp
    rw [e4C_at hg] at he'; cases he'
    exact ⟨.ok post4C, hx3, frame_settle_ok hcr3 hsg3 herr⟩
  · show a ∈ post4C.accessedAddresses ↔ _
    rw [show post4C = post4CF post5C from rfl, hka, (hacc.1 a), hpe, hpa a, ha4.1 a]
    simp [adrsH4C]
  · show x ∈ post4C.accessedStorageKeys ↔ _
    rw [show post4C = post4CF post5C from rfl, hkk, (hacc.2 x), hpe, hpk, ha4.2.1 x]
    simp only [true_and, keysH4C, List.mem_append]
    rw [show e4C31.dyna.accessedStorageKeys = e4C.dyna.accessedStorageKeys from rfl, e4C_keys x]
  · show storOf post4C.state a k = _
    rw [show post4C = post4CF post5C from rfl, hks, resumeCallB_state hr]; exact ha4.2.2.1 a k
  · show acctView (post4C.state.get a) = _
    rw [show post4C = post4CF post5C from rfl, hks, resumeCallB_state hr]; exact ha4.2.2.2 a

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
