import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame3
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame2Full

/-!
V- as an admitted transaction, frame 1: the proxy `P` (45 bytes) called by `A'` with value 0
(`remove_liquidity(200, [0, 0], A')`).  Its eleven childless steps (`stepN`, `prefix1T`), its
`DELEGATECALL` spawning frame 2 (`dcallPrep_spec`), frame 2 as its child (`frame2_child`, with the
callback subtree `callback_child` discharging its callback child), the resume, and its ten-step
tail to `RETURN` (the child's 64 return bytes copied out).  The resume and the tail are kernel
checks over a free child with frame 2's gas and output (`childObs`): frame 2's run is not
re-evaluated.  The result is exactly the hypothesis of `Tx.tx_message_of_child`: the proxy frame
is `A'`'s `CALL` child (`ChildOk` at `TxTop.callCfg`), with the tx trace's gas, return data and
success and world shadows, and its storage shadow holds the corruption.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree (proxy_at_delegatecall)

attribute [local irreducible] callCfg cp0 e1T cp2T e2T cfg339T

/-- The proxy resumed from a settled child `d`. -/
def d2T (d : Devm) : Devm := (resumeCallB cp2T.p cp2T.oi cp2T.os (.ok d)).getD default

/-- The proxy at its `RETURN` (pc 44). -/
def e1T44 (d : Devm) : Evm := (stepN 10 ⟨32, e1T.sta, d2T d⟩).getD default

/-- The proxy's halted machine. -/
def post1TF (d : Devm) : Devm :=
  match Evm.step (e1T44 d) with
  | .halt (.ok d') => d'
  | _ => default

/-- Frame 2's settled machine as the proxy's child, its observed parts as literals. -/
abbrev obsChild2 (d : Devm) : Devm := childObsX 28916293 childOut refund2 d

theorem resume1T_eq : ∀ d : Devm,
    resumeCallB cp2T.p cp2T.oi cp2T.os (.ok (obsChild2 d)) = some (d2T (obsChild2 d)) := by
  kernel_forall_rfl

theorem tail1T_eq : ∀ d : Devm,
    stepN 10 ⟨32, e1T.sta, d2T (obsChild2 d)⟩ = some (e1T44 (obsChild2 d)) := by
  kernel_forall_rfl

theorem return1T_eq : ∀ d : Devm,
    Evm.step (e1T44 (obsChild2 d)) = .halt (.ok (post1TF (obsChild2 d))) := by
  kernel_forall_rfl

theorem post1T_obs : ∀ d : Devm,
    ((post1TF (obsChild2 d)).gasLeft, (post1TF (obsChild2 d)).output.map UInt8.toNat,
      (post1TF (obsChild2 d)).error.isNone, (post1TF (obsChild2 d)).refundCounter,
      (post1TF (obsChild2 d)).accountsToDelete) =
    (childGas, childOut.map UInt8.toNat, true, refund1, .emptyWithCapacity) := by
  kernel_forall_rfl

theorem post1T_keep : ∀ d : Devm,
    ((post1TF (obsChild2 d)).accessedAddresses, (post1TF (obsChild2 d)).accessedStorageKeys,
      (post1TF (obsChild2 d)).state) =
    ((d2T (obsChild2 d)).accessedAddresses, (d2T (obsChild2 d)).accessedStorageKeys,
      (d2T (obsChild2 d)).state) := by
  kernel_forall_rfl

theorem e1T_code : e1T.sta.code = proxyCode := by kernel_rfl

/-- **Frame 1 (the proxy) as `A'`'s child**, with the corruption in its world: there are a
settled machine `d1` and shadows for it such that `d1` is `A'`'s `CALL` child (`ChildOk` at
`TxTop.callCfg`) with the tx trace's gas, return data and success, and its storage shadow has
`totalSupply = 1800 < 1906 = balanceOf[A']`. -/
theorem frame1_child : ∃ (d1 : Devm) (ck : List (Adr × B256)) (ca : List Adr) (cs : StorShadow)
    (cc : AcctShadow), d1.gasLeft = childGas ∧ d1.output = childOut ∧ d1.error = none ∧
      ChildOk e0tx.sta callCfg d1 ∧ ChildAgree d1 ck ca cs cc ∧
      (lookupS cs proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (lookupS cs proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
      d1.refundCounter = refund0 ∧ d1.accountsToDelete = .emptyWithCapacity := by
  obtain ⟨k3, a3, g3, o3, e3', r3, t3⟩ := callback_child
  obtain ⟨post2, cl, hx2, hs2, ha2, hg2, ho2, he2, h26, hA, -, hr2, ht2⟩ :=
    frame2_child post3T g3 o3 e3' r3 t3 k3 a3
  have hobs : obsChild2 post2 = post2 := childObsX_eq hg2 (by rw [ho2]; rfl) he2 hr2 ht2
  have hr := resume1T_eq post2
  have ht := tail1T_eq post2
  have hh := return1T_eq post2
  have ho := post1T_obs post2
  have hk := post1T_keep post2
  rw [hobs] at hr ht hh ho hk
  simp only [Prod.mk.injEq] at ho hk
  obtain ⟨hg, hout, he, hrf, hatd⟩ := ho
  obtain ⟨hka, hkk, hks⟩ := hk
  have herr : (post1TF post2).error = none := Option.isNone_iff_eq_none.mp he
  obtain ⟨hstep2, hpa, hpk, -, -, -, -, hst2, -⟩ := cp2T_spec
  obtain ⟨-, -, -, hcr1, -, -, hsg1, -⟩ := cp0_spec
  -- the proxy frame's `Exec`
  have hspawn : Evm.step e1T31 = .spawn cp2T.f (.call cp2T.p cp2T.oi cp2T.os) 32 := by
    have hat : Ninst.At e1T31.sta.code 31 (.exec .delegatecall) := by
      rw [show e1T31.sta = e1T.sta from rfl, e1T_code]; exact proxy_at_delegatecall
    show Evm.step ⟨31, e1T31.sta, e1T31.dyna⟩ = _
    rw [Evm.step_next hat, Ninst.step_exec, hstep2]
    rfl
  have henter : cp2T.f.enter = .run e2T := by
    rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [hst2]; exact e1T_world.2)]; exact e2T_eq
  have hsettle : Resume.run (.call cp2T.p cp2T.oi cp2T.os) (cp2T.f.settle (.ok post2)) =
      .ok (d2T post2) := by
    rw [hs2]; exact resumeCallB_sound hr
  have hx1 : Nonempty (Exec e1T.pc e1T.sta e1T.dyna (.ok (post1TF post2))) :=
    exec_of_stepN_spawn_runOk prefix1T hspawn henter hx2 hsettle (exec_of_stepN_halt ht hh)
  -- the proxy frame's shadows
  have hacc := resumeCallB_acc hr
  have hpe : post2.error.isSome = false := by rw [he2]; rfl
  refine ⟨post1TF post2, callCfg.keys ++ cl.keys, cp2T.adrs ++ cl.adrs, cl.stor, cl.acs, hg,
    List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout, herr, ?_,
    ⟨fun a => ?_, fun x => ?_, fun a k => ?_, fun a => ?_⟩, h26, hA, hrf, hatd⟩
  · intro cp cevm hp he'
    rw [cp0_eq] at hp; cases hp
    rw [e1T_eq] at he'; cases he'
    exact ⟨.ok (post1TF post2), hx1, frame_settle_ok hcr1 hsg1 herr⟩
  · rw [hka, (hacc.1 a), hpe, hpa a, ha2.1 a]
    simp
  · rw [hkk, (hacc.2 x), hpe, hpk, ha2.2.1 x]
    simp only [true_and, List.mem_append]
    rw [show e1T31.dyna.accessedStorageKeys = e1T.dyna.accessedStorageKeys from rfl, e1T_keys x]
  · rw [hks, resumeCallB_state hr]; exact ha2.2.2.1 a k
  · rw [hks, resumeCallB_state hr]; exact ha2.2.2.2 a

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
