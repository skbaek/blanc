import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame3
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame2Full
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame1

/-!
V- as an admitted transaction, frame 1: the proxy `P` (45 bytes) called by `A'` with value 0
(`remove_liquidity(200, [0, 0], A')`).  Its eleven childless steps (`stepN`, `prefix1C`), its
`DELEGATECALL` spawning frame 2 (`dcallPrep_spec`), frame 2 as its child (`frame2C_child`, with the
callback subtree `callbackC_child` discharging its callback child), the resume, and its ten-step
tail to `RETURN` (the child's 64 return bytes copied out).  The resume and the tail are kernel
checks over a free child with frame 2's gas and output (`childObs`): frame 2's run is not
re-evaluated.  The result is exactly the hypothesis of `Tx.tx_message_of_child`: the proxy frame
is `A'`'s `CALL` child (`ChildOk` at `callCfgC`), with the tx trace's gas, return data and
success and world shadows, and its storage shadow holds the corruption.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree (proxy_at_delegatecall)

attribute [local irreducible] callCfgC cp0C e1C cp2C e2C cfg339C

variable {g : Fork}

/-- The proxy resumed from a settled child `d`. -/
def d2C (d : Devm) : Devm := (resumeCallB cp2C.p cp2C.oi cp2C.os (.ok d)).getD default

/-- The proxy at its `RETURN` (pc 44). -/
def e1C44 (d : Devm) : Evm := (stepN 10 ⟨32, e1C.sta, d2C d⟩).getD default

/-- The proxy's halted machine. -/
def post1CF (d : Devm) : Devm :=
  match Evm.step (e1C44 d) with
  | .halt (.ok d') => d'
  | _ => default

/-- Frame 2's settled machine as the proxy's child, its observed parts as literals. -/
abbrev obsChild2C (d : Devm) : Devm := childObsX 15327639 childOut refund2 d

theorem resume1C_eq : ∀ d : Devm,
    resumeCallB cp2C.p cp2C.oi cp2C.os (.ok (obsChild2C d)) = some (d2C (obsChild2C d)) := by
  kernel_forall_rfl

theorem tail1C_eq : ∀ d : Devm,
    stepN 10 ⟨32, e1C.sta, d2C (obsChild2C d)⟩ = some (e1C44 (obsChild2C d)) := by
  kernel_forall_rfl

theorem return1C_eq : ∀ d : Devm,
    Evm.step (e1C44 (obsChild2C d)) = .halt (.ok (post1CF (obsChild2C d))) := by
  kernel_forall_rfl

theorem post1C_obs : ∀ d : Devm,
    ((post1CF (obsChild2C d)).gasLeft, (post1CF (obsChild2C d)).output.map UInt8.toNat,
      (post1CF (obsChild2C d)).error.isNone, (post1CF (obsChild2C d)).refundCounter,
      (post1CF (obsChild2C d)).accountsToDelete) =
    (childGasC, childOut.map UInt8.toNat, true, refund1, .emptyWithCapacity) := by
  kernel_forall_rfl

theorem post1C_keep : ∀ d : Devm,
    ((post1CF (obsChild2C d)).accessedAddresses, (post1CF (obsChild2C d)).accessedStorageKeys,
      (post1CF (obsChild2C d)).state) =
    ((d2C (obsChild2C d)).accessedAddresses, (d2C (obsChild2C d)).accessedStorageKeys,
      (d2C (obsChild2C d)).state) := by
  kernel_forall_rfl

theorem e1C_code : e1C.sta.code = proxyCode := by kernel_rfl

/-- **Frame 1 (the proxy) as `A'`'s child, under any covered fork**, with the corruption in its
world: there are a settled machine `d1` and shadows for it such that `d1` is `A'`'s `CALL` child
(`ChildOk` at `callCfgC`) with the tx trace's gas, return data and success, and its storage shadow
has `totalSupply = 1800 < 1906 = balanceOf[A']`. -/
theorem frame1C_child_at (hg : CoveredFork g) :
    ∃ (d1 : Devm) (ck : List (Adr × B256)) (ca : List Adr) (cs : StorShadow)
      (cc : AcctShadow), d1.gasLeft = childGasC ∧ d1.output = childOut ∧ d1.error = none ∧
      ChildOk (e0C.withFork g).sta callCfgC d1 ∧ ChildAgree d1 ck ca cs cc ∧
      (lookupS cs proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (lookupS cs proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
      d1.refundCounter = refund0 ∧ d1.accountsToDelete = .emptyWithCapacity := by
  obtain ⟨k3, a3, g3, o3, e3', r3, t3⟩ := callbackC_child_at hg
  obtain ⟨post2, cl, hx2, hs2, ha2, hg2, ho2, he2, h26, hA, -, hr2, ht2⟩ :=
    frame2C_child_at hg post3C g3 o3 e3' r3 t3 k3 a3
  have hobs : obsChild2C post2 = post2 := childObsX_eq hg2 (by rw [ho2]; rfl) he2 hr2 ht2
  have hr := resume1C_eq post2
  have ht := tail1C_eq post2
  have hh := return1C_eq post2
  have ho := post1C_obs post2
  have hk := post1C_keep post2
  rw [hobs] at hr ht hh ho hk
  simp only [Prod.mk.injEq] at ho hk
  obtain ⟨hgas, hout, he, hrf, hatd⟩ := ho
  obtain ⟨hka, hkk, hks⟩ := hk
  have herr : (post1CF post2).error = none := Option.isNone_iff_eq_none.mp he
  obtain ⟨hstep2, hpa, hpk, -, -, -, -, hst2, -⟩ := cp2C_spec_at hg
  obtain ⟨-, -, -, hcr1, -, -, hsg1, -⟩ := cp0C_spec_at hg
  -- the proxy frame's `Exec`
  have hspawn : Evm.step (e1C31.withFork g) =
      .spawn (cp2C.withFork g).f (.call cp2C.p cp2C.oi cp2C.os) 32 := by
    have hat : Ninst.At (e1C31.withFork g).sta.code 31 (.exec .delegatecall) := by
      show Ninst.At e1C.sta.code 31 (.exec .delegatecall)
      rw [e1C_code]; exact proxy_at_delegatecall
    show Evm.step ⟨31, (e1C31.withFork g).sta, e1C31.dyna⟩ = _
    rw [Evm.step_next hat, Ninst.step_exec, hstep2]
    rfl
  have henter : (cp2C.withFork g).f.enter = .run (e2C.withFork g) := by
    rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [hst2]; exact e1C_world.2)]; exact e2C_at hg
  have hsettle : Resume.run (.call cp2C.p cp2C.oi cp2C.os)
      ((cp2C.withFork g).f.settle (.ok post2)) = .ok (d2C post2) := by
    rw [hs2]; exact resumeCallB_sound hr
  have hsta : (e1C44 post2).sta = e1C.sta := stepN_sta (evm := ⟨32, e1C.sta, d2C post2⟩) ht
  have hstep_halt : Evm.step ((e1C44 post2).withFork g) = .halt (.ok (post1CF post2)) := by
    have hp : (e1C44 post2).sta.benvStat.fork = .prague := by rw [hsta]; exact e1C_block.1
    have hx : (e1C44 post2).sta.benvStat.excessBlobGas = 0 := by rw [hsta]; exact e1C_block.2
    rw [show Evm.step ((e1C44 post2).withFork g) = (Evm.step (e1C44 post2)).withFork g from
      evm_step_withFork_prague hp hx hg (by rw [hh]; intro ee; nofun), hh]
    rfl
  have hx1 : Nonempty (Exec (e1C.withFork g).pc (e1C.withFork g).sta (e1C.withFork g).dyna
      (.ok (post1CF post2))) :=
    exec_of_stepN_spawn_runOk (prefix1C_at hg) hspawn henter hx2 hsettle
      (exec_of_stepN_halt (stepN_withFork hg (e := ⟨32, e1C.sta, d2C post2⟩) e1C_block.1
        e1C_block.2 ht) hstep_halt)
  -- the proxy frame's shadows
  have hacc := resumeCallB_acc hr
  have hpe : post2.error.isSome = false := by rw [he2]; rfl
  refine ⟨post1CF post2, callCfgC.keys ++ cl.keys, cp2C.adrs ++ cl.adrs, cl.stor, cl.acs, hgas,
    List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout, herr, ?_,
    ⟨fun a => ?_, fun x => ?_, fun a k => ?_, fun a => ?_⟩, h26, hA, hrf, hatd⟩
  · intro cp cevm hp he'
    rw [cp0C_at hg] at hp; cases hp
    rw [e1C_at hg] at he'; cases he'
    exact ⟨.ok (post1CF post2), hx1, frame_settle_ok hcr1 hsg1 herr⟩
  · rw [hka, (hacc.1 a), hpe, hpa a, ha2.1 a]
    simp only [true_and, List.mem_append]
  · rw [hkk, (hacc.2 x), hpe, hpk, ha2.2.1 x]
    simp only [true_and, List.mem_append]
    rw [show e1C31.dyna.accessedStorageKeys = e1C.dyna.accessedStorageKeys from rfl, e1C_keys x]
  · rw [hks, resumeCallB_state hr]; exact ha2.2.2.1 a k
  · rw [hks, resumeCallB_state hr]; exact ha2.2.2.2 a

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
