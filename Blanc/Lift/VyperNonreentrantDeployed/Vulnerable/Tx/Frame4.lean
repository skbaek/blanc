import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5Child
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame3

/-!
V- as an admitted transaction, frame 4: the proxy `P` (45 bytes) called by `A'`'s callback with
value 100 (`add_liquidity`).  Its eleven childless steps (`stepN`, `prefix4T`), its `DELEGATECALL`
spawning frame 5 (`dcallPrep_spec`), frame 5 as its child (`frame5_child`), the resume, and its
ten-step tail to `RETURN` (the child's 32 return bytes copied out).  The resume and the tail are
kernel checks over a free child with frame 5's gas and output (`childObs`): frame 5's run is not
re-evaluated.  The result: the proxy frame is an `Exec` from the machine `A'`'s `CALL` enters
with, it settles to its halted machine `post4T`, and `post4T`'s shadows are `A'`'s at its `CALL`
together with frame 5's.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree (proxy_at_delegatecall)

attribute [local irreducible] callCfg cp0 e1T cp2T e2T cfg339T e3T cc3T aCallT cp4T e4T cp5T e5T post5T

/-- The proxy resumed from a settled child `d`. -/
def d4T (d : Devm) : Devm := (resumeCallB cp5T.p cp5T.oi cp5T.os (.ok d)).getD default

/-- The proxy at its `RETURN` (pc 44). -/
def e4T44 (d : Devm) : Evm := (stepN 10 ⟨32, e4T.sta, d4T d⟩).getD default

/-- The proxy's halted machine. -/
def post4TF (d : Devm) : Devm :=
  match Evm.step (e4T44 d) with
  | .halt (.ok d') => d'
  | _ => default

/-- Frame 5's settled machine as the proxy's child, its observed parts as literals. -/
abbrev obsChild5 (d : Devm) : Devm := childObs gas5T (word 106) d

theorem resume4T_eq : ∀ d : Devm,
    resumeCallB cp5T.p cp5T.oi cp5T.os (.ok (obsChild5 d)) = some (d4T (obsChild5 d)) := by
  kernel_forall_rfl

theorem tail4T_eq : ∀ d : Devm, stepN 10 ⟨32, e4T.sta, d4T (obsChild5 d)⟩ = some (e4T44 (obsChild5 d)) := by
  kernel_forall_rfl

theorem return4T_eq : ∀ d : Devm,
    Evm.step (e4T44 (obsChild5 d)) = .halt (.ok (post4TF (obsChild5 d))) := by
  kernel_forall_rfl

/-- The proxy frame's gas at its `RETURN`, and its return data (the child's). -/
def gas4T : Nat := 28057683

theorem post4T_obs : ∀ d : Devm,
    ((post4TF (obsChild5 d)).gasLeft, (post4TF (obsChild5 d)).output.map UInt8.toNat,
      (post4TF (obsChild5 d)).error.isNone) = (gas4T, (word 106).map UInt8.toNat, true) := by
  kernel_forall_rfl

theorem post4T_keep : ∀ d : Devm,
    ((post4TF (obsChild5 d)).accessedAddresses, (post4TF (obsChild5 d)).accessedStorageKeys,
      (post4TF (obsChild5 d)).state) =
    ((d4T (obsChild5 d)).accessedAddresses, (d4T (obsChild5 d)).accessedStorageKeys,
      (d4T (obsChild5 d)).state) := by
  kernel_forall_rfl

/-- The proxy frame's settled machine. -/
def post4T : Devm := post4TF post5T

theorem obsChild5_post5T : obsChild5 post5T = post5T := by
  obtain ⟨-, hg, ho, he, -⟩ := r5_facts
  exact childObs_eq hg ho he

theorem e4T_code : e4T.sta.code = proxyCode := by kernel_rfl

/-- The shadows frame 4 hands back to `A'`: its own (`A'`'s at its `CALL`) and frame 5's; frame
5's storage and accounts (`storAT`, `acsAT`) pass through. -/
def keysH4T : List (Adr × B256) := aCallT.keys ++ keys5T
def adrsH4T : List Adr := cp5T.adrs ++ adrs5T

/-- **Frame 4 (the proxy) as `A'`'s child.** -/
theorem frame4_child : ChildOk e3T.sta aCallT post4T ∧ ChildAgree post4T keysH4T adrsH4T storAT acsAT ∧
    post4T.gasLeft = gas4T ∧ post4T.output = word 106 ∧ post4T.error = none := by
  obtain ⟨hx4, hs4, ha4⟩ := frame5_child
  obtain ⟨hstep4, hpa, hpk, -, -, -, -, hst4, -⟩ := cp5T_spec
  obtain ⟨-, -, -, hcr3, -, -, hsg3, -⟩ := cp4T_spec
  have hr := resume4T_eq post5T
  have ht := tail4T_eq post5T
  have hh := return4T_eq post5T
  have ho := post4T_obs post5T
  have hk := post4T_keep post5T
  rw [obsChild5_post5T] at hr ht hh ho hk
  simp only [Prod.mk.injEq] at ho hk
  obtain ⟨hg, hout, he⟩ := ho
  obtain ⟨hka, hkk, hks⟩ := hk
  have herr : post4T.error = none := Option.isNone_iff_eq_none.mp he
  -- the proxy frame's `Exec`
  have hspawn : Evm.step e4T31 = .spawn cp5T.f (.call cp5T.p cp5T.oi cp5T.os) 32 := by
    have hat : Ninst.At e4T31.sta.code 31 (.exec .delegatecall) := by
      rw [show e4T31.sta = e4T.sta from rfl, e4T_code]; exact proxy_at_delegatecall
    show Evm.step ⟨31, e4T31.sta, e4T31.dyna⟩ = _
    rw [Evm.step_next hat, Ninst.step_exec, hstep4]
    rfl
  have henter : cp5T.f.enter = .run e5T := by
    rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [hst4]; exact e4T_world.2)]; exact e5T_eq
  have hsettle : Resume.run (.call cp5T.p cp5T.oi cp5T.os) (cp5T.f.settle (.ok post5T)) =
      .ok (d4T post5T) := by
    rw [hs4]; exact resumeCallB_sound hr
  have hx3 : Nonempty (Exec e4T.pc e4T.sta e4T.dyna (.ok post4T)) :=
    exec_of_stepN_spawn_runOk prefix4T hspawn henter hx4 hsettle
      (exec_of_stepN_halt ht hh)
  -- the proxy frame's shadows
  have hacc := resumeCallB_acc hr
  have hpe : post5T.error.isSome = false := by rw [r5_facts.2.2.2.1]; rfl
  refine ⟨fun cp cevm hp he' => ?_, ⟨fun a => ?_, fun x => ?_, fun a k => ?_, fun a => ?_⟩,
    hg, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout, herr⟩
  · rw [cp4T_eq] at hp; cases hp
    rw [e4T_eq] at he'; cases he'
    exact ⟨.ok post4T, hx3, frame_settle_ok hcr3 hsg3 herr⟩
  · show a ∈ post4T.accessedAddresses ↔ _
    rw [show post4T = post4TF post5T from rfl, hka, (hacc.1 a), hpe, hpa a, ha4.1 a]
    simp [adrsH4T]
  · show x ∈ post4T.accessedStorageKeys ↔ _
    rw [show post4T = post4TF post5T from rfl, hkk, (hacc.2 x), hpe, hpk, ha4.2.1 x]
    simp only [true_and, keysH4T, List.mem_append]
    rw [show e4T31.dyna.accessedStorageKeys = e4T.dyna.accessedStorageKeys from rfl, e4T_keys x]
  · show storOf post4T.state a k = _
    rw [show post4T = post4TF post5T from rfl, hks, resumeCallB_state hr]; exact ha4.2.2.1 a k
  · show acctView (post4T.state.get a) = _
    rw [show post4T = post4TF post5T from rfl, hks, resumeCallB_state hr]; exact ha4.2.2.2 a

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
