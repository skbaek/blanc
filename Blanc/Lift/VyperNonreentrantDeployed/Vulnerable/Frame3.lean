import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Child

/-!
V- witness, frame 3: the proxy `P` (45 bytes) called by the attacker with value 100.  Its
eleven childless steps (`stepN`, `prefix3`), its `DELEGATECALL` spawning frame 4
(`dcallPrep_spec`), frame 4 as its child (`frame4_child`), the resume, and its ten-step
tail to `RETURN` (the child's 32 return bytes copied out).  The resume and the tail are
kernel checks over a free child with frame 4's gas and output (`childObs`): frame 4's
run is not re-evaluated.  The result: the proxy frame is an `Exec` from the machine the
attacker's `CALL` enters with, it settles to its halted machine `post3`, and `post3`'s
shadows are the attacker's at its `CALL` together with frame 4's.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

attribute [local irreducible] cfg339 e2 cc2 aCall cp3 e3 cp4 e4 post4

/-- The proxy resumed from a settled child `d`. -/
def d32 (d : Devm) : Devm := (resumeCallB cp4.p cp4.oi cp4.os (.ok d)).getD default

/-- The proxy at its `RETURN` (pc 44). -/
def e44 (d : Devm) : Evm := (stepN 10 ⟨32, e3.sta, d32 d⟩).getD default

/-- The proxy's halted machine. -/
def post3F (d : Devm) : Devm :=
  match Evm.step (e44 d) with
  | .halt (.ok d') => d'
  | _ => default

/-- Frame 4's settled machine as the proxy's child, its observed parts as literals. -/
abbrev obsChild4 (d : Devm) : Devm := childObs gas4 (word 106) d

theorem resume3_eq : ∀ d : Devm,
    resumeCallB cp4.p cp4.oi cp4.os (.ok (obsChild4 d)) = some (d32 (obsChild4 d)) := by
  kernel_forall_rfl

theorem tail3_eq : ∀ d : Devm, stepN 10 ⟨32, e3.sta, d32 (obsChild4 d)⟩ = some (e44 (obsChild4 d)) := by
  kernel_forall_rfl

theorem return3_eq : ∀ d : Devm,
    Evm.step (e44 (obsChild4 d)) = .halt (.ok (post3F (obsChild4 d))) := by
  kernel_forall_rfl

/-- The proxy frame's gas at its `RETURN`, and its return data (the child's). -/
def gas3 : Nat := 28500077

theorem post3_obs : ∀ d : Devm,
    ((post3F (obsChild4 d)).gasLeft, (post3F (obsChild4 d)).output.map UInt8.toNat,
      (post3F (obsChild4 d)).error.isNone) = (gas3, (word 106).map UInt8.toNat, true) := by
  kernel_forall_rfl

theorem post3_keep : ∀ d : Devm,
    ((post3F (obsChild4 d)).accessedAddresses, (post3F (obsChild4 d)).accessedStorageKeys,
      (post3F (obsChild4 d)).state) =
    ((d32 (obsChild4 d)).accessedAddresses, (d32 (obsChild4 d)).accessedStorageKeys,
      (d32 (obsChild4 d)).state) := by
  kernel_forall_rfl

/-- The proxy frame's settled machine. -/
def post3 : Devm := post3F post4

theorem obsChild4_post4 : obsChild4 post4 = post4 := by
  obtain ⟨-, hg, ho, he, -⟩ := r4_facts
  exact childObs_eq hg ho he

theorem e3_code : e3.sta.code = proxyCode := by kernel_rfl

theorem proxy_at_delegatecall : Xinst.At proxyCode 31 .delegatecall := by rfl

/-- **Frame 3 (the proxy) as the attacker's child.** -/
theorem frame3_child : ChildOk e2.sta aCall post3 ∧ ChildAgree post3 keys3 adrs3' storA acsA ∧
    post3.gasLeft = gas3 ∧ post3.output = word 106 ∧ post3.error = none := by
  obtain ⟨hx4, hs4, ha4⟩ := frame4_child
  obtain ⟨hstep4, hpa, hpk, -, -, -, -, hst4, -⟩ := cp4_spec
  obtain ⟨-, -, -, hcr3, -, -, hsg3, -⟩ := cp3_spec
  have hr := resume3_eq post4
  have ht := tail3_eq post4
  have hh := return3_eq post4
  have ho := post3_obs post4
  have hk := post3_keep post4
  rw [obsChild4_post4] at hr ht hh ho hk
  simp only [Prod.mk.injEq] at ho hk
  obtain ⟨hg, hout, he⟩ := ho
  obtain ⟨hka, hkk, hks⟩ := hk
  have herr : post3.error = none := Option.isNone_iff_eq_none.mp he
  -- the proxy frame's `Exec`
  have hspawn : Evm.step e31 = .spawn cp4.f (.call cp4.p cp4.oi cp4.os) 32 := by
    have hat : Ninst.At e31.sta.code 31 (.exec .delegatecall) := by
      rw [show e31.sta = e3.sta from rfl, e3_code]; exact proxy_at_delegatecall
    show Evm.step ⟨31, e31.sta, e31.dyna⟩ = _
    rw [Evm.step_next hat, Ninst.step_exec, hstep4]
    rfl
  have henter : cp4.f.enter = .run e4 := by
    rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [hst4]; exact e3_world.2)]; exact e4_eq
  have hsettle : Resume.run (.call cp4.p cp4.oi cp4.os) (cp4.f.settle (.ok post4)) =
      .ok (d32 post4) := by
    rw [hs4]; exact resumeCallB_sound hr
  have hx3 : Nonempty (Exec e3.pc e3.sta e3.dyna (.ok post3)) :=
    exec_of_stepN_spawn_runOk prefix3 hspawn henter hx4 hsettle
      (exec_of_stepN_halt ht hh)
  -- the proxy frame's shadows
  have hacc := resumeCallB_acc hr
  have hpe : post4.error.isSome = false := by rw [r4_facts.2.2.2.1]; rfl
  refine ⟨fun cp cevm hp he' => ?_, ⟨fun a => ?_, fun x => ?_, fun a k => ?_, fun a => ?_⟩,
    hg, List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout, herr⟩
  · rw [cp3_eq] at hp; cases hp
    rw [e3_eq] at he'; cases he'
    exact ⟨.ok post3, hx3, frame_settle_ok hcr3 hsg3 herr⟩
  · show a ∈ post3.accessedAddresses ↔ _
    rw [show post3 = post3F post4 from rfl, hka, (hacc.1 a), hpe, hpa a, ha4.1 a]
    simp only [true_and, adrs3', List.mem_append]
  · show x ∈ post3.accessedStorageKeys ↔ _
    rw [show post3 = post3F post4 from rfl, hkk, (hacc.2 x), hpe, hpk, ha4.2.1 x]
    simp only [true_and, keys3, List.mem_append]
    rw [show e31.dyna.accessedStorageKeys = e3.dyna.accessedStorageKeys from rfl, e3_keys x]
  · show storOf post3.state a k = _
    rw [show post3 = post3F post4 from rfl, hks, resumeCallB_state hr]; exact ha4.2.2.1 a k
  · show acctView (post3.state.get a) = _
    rw [show post3 = post3F post4 from rfl, hks, resumeCallB_state hr]; exact ha4.2.2.2 a

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
