import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolTopRun
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveSpec
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Locks

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable (cert t_0000_c0 cert_checkM cert_jumpsOkM)
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top (remove_guard_bytes add_guard_bytes)
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init

theorem capstone_of_violation (hV : ViolationStmt) : CapstoneStmt := by
  intro fork hfork
  obtain ⟨postI, postP, postC, tokenPost, attackerPost, approvePost, addPost,
    h1, e1, h2, e2, h3, e3, h4, e4, h5, e5, h6, e6, h7, e7, hsound, hcheckpoint⟩ :=
    setup_reaches_checkpoint fork hfork
  obtain ⟨post, hpost⟩ := hV fork hfork addPost.state hcheckpoint
  exact ⟨postI, postP, postC, tokenPost, attackerPost, approvePost, addPost, post,
    h1, e1, h2, e2, h3, e3, h4, e4, h5, e5, h6, e6, h7, e7, hsound, hcheckpoint, hpost⟩

theorem root_child_agree (W : State) (m : Meta) (w : World) (post2 : Devm)
    (hAgreeR : Agree (cR W (storTailOf W) (acctTailOf W) m w))
    (hA4 : ∀ a, a ∈ (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.accessedAddresses ↔
      a ∈ (cpR W (storTailOf W) (acctTailOf W) m w).adrs)
    (hC4' : AcctAgree (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.state
      (acs1R W (storTailOf W) (acctTailOf W) m w))
    (hchildRm : ChildAgree post2 keysRm adrsRm (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W)) :
    ChildAgree (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m w post2))
      keysRm ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
        (acsRm ++ acctTailOf W) := by
  obtain ⟨-, hpaF2, hpkF2, -, -, -, hsgF2, -, -⟩ :=
    dcallPrep_spec (cpF2_eq W (storTailOf W) (acctTailOf W) m w) hA4 hC4'
  have hcpF2adrs : (cpF2 W (storTailOf W) (acctTailOf W) m w).adrs =
      [implAddr, proxyAddr] := of_decide_eq_true (cpF2_adrs W _ _ _ _)
  have hpaF2' : ∀ a, a ∈ (cpF2 W (storTailOf W) (acctTailOf W) m w).p.accessedAddresses ↔
      a ∈ ([implAddr, proxyAddr] : List Adr) := by
    intro a
    rw [hpaF2, hcpF2adrs]
  have hpkF2' : ∀ x, x ∈ (cpF2 W (storTailOf W) (acctTailOf W) m w).p.accessedStorageKeys ↔ False := by
    intro x
    rw [hpkF2, e1'11_keys, e1_entry_keys]
    obtain ⟨-, -, cpk, -, -, cik, -, -⟩ :=
      callPrep_spec (cpR_eq W (storTailOf W) (acctTailOf W) m w)
        hAgreeR.2.1 hAgreeR.2.2.2
    rw [cik, cpk, hAgreeR.1, cR_keys]
    simp only [List.not_mem_nil]
  have hchild1 : ChildAgree (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m w post2))
      keysRm ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W) := by
    have hres := resumeF1raw_eq W (storTailOf W) (acctTailOf W) m w post2
    have hkeep := postF1raw_keep W (storTailOf W) (acctTailOf W) m w post2
    simp only [Prod.mk.injEq] at hkeep
    have hca := resumeCallB_acc hres
    have hce : (obsChildF1raw post2).error.isSome = false := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      rw [obsChildF1_acc, hkeep.1, hca.1 a, hce, hpaF2', obsChildF1raw_acc,
        hchildRm.1 a, List.mem_append]
      simp only [true_and]
    · intro x
      rw [obsChildF1_keys, hkeep.2.1, hca.2 x, hce, hpkF2', obsChildF1raw_keys,
        hchildRm.2.1 x]
      simp only [true_and, false_or]
    · intro a k
      rw [obsChildF1_state, hkeep.2.2, resumeCallB_state hres,
        obsChildF1raw_state, hchildRm.2.2.1 a k]
    · rw [obsChildF1_state, hkeep.2.2, resumeCallB_state hres, obsChildF1raw_state]
      exact hchildRm.2.2.2
  exact hchild1

theorem root_exec_call_core (g : Fork) (W : State) (m : Meta) (w : World)
    (post2 : Devm)
    (hprefix : stepN 11 ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g) =
      some ((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g))
    (htail : stepN 10
      ((⟨32, (e1 W (storTailOf W) (acctTailOf W) m w).sta,
        d1Rraw W (storTailOf W) (acctTailOf W) m w post2⟩ : Evm).withFork g) =
      some ((e1tailraw W (storTailOf W) (acctTailOf W) m w post2).withFork g))
    (hstepF : Evm.step ((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g) =
      .spawn ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f
        (.call ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).p
          ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).oi
          ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).os) 32)
    (henterF : (((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f).enter =
      .run ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g))
    (hexec2 : Nonempty (Exec ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g).pc
      ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna (.ok post2)))
    (hsettleF2 : Resume.run
      (.call ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).p
        ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).oi
        ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).os)
      (((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f.settle (.ok post2)) =
      .ok (d1Rraw W (storTailOf W) (acctTailOf W) m w post2))
    (hhaltF1Fork : Evm.step ((e1tailraw W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
      .halt (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2))) :
    Nonempty (Exec ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).pc
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna
      (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2))) := by
  have hstaR : ((((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).sta)) =
      (((⟨32, ((e1 W (storTailOf W) (acctTailOf W) m w).sta),
        (d1Rraw W (storTailOf W) (acctTailOf W) m w post2)⟩ : Evm).withFork g).sta) := by
    rw [e1_sta_fork g W (storTailOf W) (acctTailOf W) m w,
      mkEvm_sta_fork g 32 ((e1 W (storTailOf W) (acctTailOf W) m w).sta)
        (d1Rraw W (storTailOf W) (acctTailOf W) m w post2)]
  have hrest : Nonempty (Exec 32
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      (d1Rraw W (storTailOf W) (acctTailOf W) m w post2)
      (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2))) := by
    have h := exec_of_stepN_halt htail hhaltF1Fork
    rw [← hstaR, mkEvm_pc_fork, mkEvm_dyna_fork] at h
    exact h
  exact exec_of_stepN_spawn_runOk hprefix hstepF henterF hexec2 hsettleF2 hrest

theorem root_f1_exec_call (g : Fork) (W : State) (m : Meta) (w : World)
    (hg : CoveredFork g)
    (hspawnF2 : SpawnedBy (((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g).sta)
      (((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna) .delegatecall
      ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g))
    (hA4 : ∀ a, a ∈ (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.accessedAddresses ↔
      a ∈ (cpR W (storTailOf W) (acctTailOf W) m w).adrs)
    (hC4' : AcctAgree (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.state
      (acs1R W (storTailOf W) (acctTailOf W) m w))
    (post2 : Devm) (hexec2 : Nonempty (Exec 0 ((sRm.withOrig W).withFork g)
      (Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
        (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
        (c2 W (storTailOf W) (acctTailOf W) m w).devm.world).devm (.ok post2)))
    (hsettleF2 : Resume.run
      (.call ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).p
        ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).oi
        ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).os)
      (((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f.settle
        (.ok post2)) =
      .ok (d1Rraw W (storTailOf W) (acctTailOf W) m w post2))
    (hhaltF1Fork : Evm.step ((e1tailraw W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
      .halt (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2))) :
    Nonempty (Exec ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).pc
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna
      (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2))) := by
  have hprefix := e1'11_at g W (storTailOf W) (acctTailOf W) m w hg
  have htail := tailF1raw_fork g W (storTailOf W) (acctTailOf W) m w post2 hg
  have hcp := cpF2_e2_at g W (storTailOf W) (acctTailOf W) m w hg
  have hspec := dcallPrep_spec hcp.1 hA4 hC4'
  obtain ⟨hstep, -, -, -, -, -, -, hst8, -⟩ := hspec
  have hAgreeEnterF : AcctAgree
      ((((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f).inner.benv.state)
      (acs1R W (storTailOf W) (acctTailOf W) m w) := by
    rw [hst8]
    exact hC4'
  have henterF : ((((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f).enter) =
      .run ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g) := by
    rw [frame_enter_eq_B, frameEnterB_eq_S hAgreeEnterF]
    exact hcp.2
  have hstepF : Evm.step ((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g) =
      .spawn ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f
        (.call ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).p
          ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).oi
          ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).os) 32 := by
    rw [e1'11_fork_shape]
    have hat' : Ninst.At ((e1'11 W (storTailOf W) (acctTailOf W) m w).sta.withFork g).code
        31 (.exec .delegatecall) := by
      rw [e1'11_fork_code]
      exact fwd_at_delegatecall
    rw [Evm.step_next hat', Ninst.step_exec, hstep]
    rfl
  have hcfg2 : Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
      (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
      (c2 W (storTailOf W) (acctTailOf W) m w).devm.world =
      c2 W (storTailOf W) (acctTailOf W) m w :=
    (Boundary.cfg_of_obsDT (c2_obs W (storTailOf W) (acctTailOf W) m w)).symm
  have hexec2' : Nonempty (Exec ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g).pc
      ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna (.ok post2)) := by
    rw [e2_pc_fork, e2_sta_fork, e2_sta_eq, e2_dyna_fork, e2_dyna_c2, ← hcfg2]
    exact hexec2
  have hcall : Nonempty (Exec ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).pc
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna
      (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2))) :=
    root_exec_call_core g W m w post2 hprefix htail hstepF henterF
      hexec2' hsettleF2 hhaltF1Fork
  exact hcall

theorem root_f1_raw_halt (g : Fork) (W : State) (m : Meta) (w : World)
    (hg : CoveredFork g) (post2 : Devm) :
    Evm.step ((e1tailraw W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
      .halt (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2)) := by
  have htailSta : (e1tailraw W (storTailOf W) (acctTailOf W) m w post2).sta.benvStat.fork =
      .prague := by
    rw [stepN_sta (tailF1raw_eq W (storTailOf W) (acctTailOf W) m w post2)]
    exact (e1_fork W (storTailOf W) (acctTailOf W) m w).1
  have hne : ∀ ee, Evm.step (e1tailraw W (storTailOf W) (acctTailOf W) m w post2) ≠
      .halt (.error ee) := by
    intro ee he
    rw [returnF1raw_eq W (storTailOf W) (acctTailOf W) m w post2] at he
    cases he
  have htailHx : (e1tailraw W (storTailOf W) (acctTailOf W) m w post2).sta.benvStat.excessBlobGas =
      0 := by
    rw [stepN_sta (tailF1raw_eq W (storTailOf W) (acctTailOf W) m w post2)]
    exact (e1_fork W (storTailOf W) (acctTailOf W) m w).2
  rw [show Evm.step ((e1tailraw W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
      (Evm.step (e1tailraw W (storTailOf W) (acctTailOf W) m w post2)).withFork g from
    evm_step_withFork_prague htailSta htailHx hg hne]
  rw [returnF1raw_eq]
  rfl

theorem root_f1_settle_raw (g : Fork) (W : State) (m : Meta) (w : World)
    (hg : CoveredFork g)
    (hA4 : ∀ a, a ∈ (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.accessedAddresses ↔
      a ∈ (cpR W (storTailOf W) (acctTailOf W) m w).adrs)
    (hC4' : AcctAgree (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.state
      (acs1R W (storTailOf W) (acctTailOf W) m w))
    (post2 : Devm)
    (hgasRm : post2.gasLeft = gasRm) (houtRm : post2.output = outRm)
    (herrRm : post2.error = none) :
    Resume.run
      (.call ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).p
        ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).oi
        ((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).os)
      (((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f.settle
        (.ok post2)) =
      .ok (d1Rraw W (storTailOf W) (acctTailOf W) m w post2) := by
  obtain ⟨-, -, -, hcrF2, -, -, hsgF2, -, -⟩ :=
    dcallPrep_spec (cpF2_eq W (storTailOf W) (acctTailOf W) m w) hA4 hC4'
  have hsettleRaw : (((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f).settle
      (.ok post2) = .ok post2 := by
    change ((cpF2 W (storTailOf W) (acctTailOf W) m w).f.withFork g).settle
      (.ok post2) = .ok post2
    rw [settle_withFork_of_stat
      (by rw [stepN_sta (e1'11_eq W (storTailOf W) (acctTailOf W) m w),
        (e1_fork W (storTailOf W) (acctTailOf W) m w).1]; exact CoveredFork.prague)
      hg (dcallPrep_stat (cpF2_eq W (storTailOf W) (acctTailOf W) m w))]
    exact frame_settle_ok hcrF2 hsgF2 herrRm
  have hobRaw : obsChildF1raw post2 = post2 :=
    childObs_eq hgasRm houtRm herrRm
  have hresumeRaw : resumeCallB
      ((cpF2 W (storTailOf W) (acctTailOf W) m w).p)
      ((cpF2 W (storTailOf W) (acctTailOf W) m w).oi)
      ((cpF2 W (storTailOf W) (acctTailOf W) m w).os) (.ok post2) =
      some (d1Rraw W (storTailOf W) (acctTailOf W) m w post2) := by
    have h := resumeF1raw_eq W (storTailOf W) (acctTailOf W) m w post2
    rw [hobRaw] at h
    exact h
  rw [hsettleRaw, cpF2_p_fork, cpF2_oi_fork, cpF2_os_fork]
  exact resumeCallB_sound hresumeRaw

theorem root_f1_resume (g : Fork) (W : State) (m : Meta) (w : World)
    (hg : CoveredFork g) (hspawnF2 : SpawnedBy (((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g).sta)
      (((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna) .delegatecall
      ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g))
    (hA4 : ∀ a, a ∈ (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.accessedAddresses ↔
      a ∈ (cpR W (storTailOf W) (acctTailOf W) m w).adrs)
    (hC4' : AcctAgree (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.state
      (acs1R W (storTailOf W) (acctTailOf W) m w))
    (post2 : Devm) (hexec2 : Nonempty (Exec 0 ((sRm.withOrig W).withFork g)
      (Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
        (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
        (c2 W (storTailOf W) (acctTailOf W) m w).devm.world).devm (.ok post2)))
    (hgasRm : post2.gasLeft = gasRm) (houtRm : post2.output = outRm)
    (herrRm : post2.error = none) :
    Nonempty (Exec ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).pc
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna
      (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2))) := by
  have hhaltF1rawFork : Evm.step
      ((e1tailraw W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
      .halt (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2)) :=
    root_f1_raw_halt g W m w hg post2
  have hsettleRun := root_f1_settle_raw g W m w hg hA4 hC4' post2
    hgasRm houtRm herrRm
  exact root_f1_exec_call g W m w hg hspawnF2 hA4 hC4' post2 hexec2
    hsettleRun hhaltF1rawFork

theorem root_f1_exec (g : Fork) (W : State) (m : Meta) (w : World)
    (hg : CoveredFork g) (hAgreeR : Agree (cR W (storTailOf W) (acctTailOf W) m w))
    (hspawnF2 : SpawnedBy (((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g).sta)
      (((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna) .delegatecall
      ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g))
    (hA4 : ∀ a, a ∈ (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.accessedAddresses ↔
      a ∈ (cpR W (storTailOf W) (acctTailOf W) m w).adrs)
    (hC4' : AcctAgree (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.state
      (acs1R W (storTailOf W) (acctTailOf W) m w))
    (post2 : Devm) (hexec2 : Nonempty (Exec 0 ((sRm.withOrig W).withFork g)
      (Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
        (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
        (c2 W (storTailOf W) (acctTailOf W) m w).devm.world).devm (.ok post2)))
    (hgasRm : post2.gasLeft = gasRm) (houtRm : post2.output = outRm)
    (herrRm : post2.error = none)
    (hchild1 : ChildAgree (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m w post2))
      keysRm ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
        (acsRm ++ acctTailOf W)) :
    ChildOk ((sR.withOrig W).withFork g) (cR W (storTailOf W) (acctTailOf W) m w)
      (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m w post2)) := by
  have hFroot : CoveredFork (sR.withOrig W).benvStat.fork := by
    rw [sR_orig_fork W]
    exact CoveredFork.prague
  have hexecF1 := root_f1_resume g W m w hg hspawnF2 hA4 hC4' post2 hexec2
    hgasRm houtRm herrRm
  obtain ⟨-, -, -, hcrR, -, -, hsgR, -⟩ :=
    callPrep_spec (cpR_eq W (storTailOf W) (acctTailOf W) m w) hAgreeR.2.1 hAgreeR.2.2.2
  have hpo := postF1raw_obs W (storTailOf W) (acctTailOf W) m w post2
  simp only [Prod.mk.injEq] at hpo
  obtain ⟨houtMap, herrB⟩ := hpo
  have herrF1raw : (postF1raw W (storTailOf W) (acctTailOf W) m w post2).error = none :=
    Option.isNone_iff_eq_none.mp herrB
  have houtF1raw : (postF1raw W (storTailOf W) (acctTailOf W) m w post2).output = outRm :=
    List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) houtMap
  have hobsF1 : obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m w post2) =
      (postF1raw W (storTailOf W) (acctTailOf W) m w post2) :=
    childObs_eq (postF1raw_gas W (storTailOf W) (acctTailOf W) m w post2)
      houtF1raw herrF1raw
  have hsettleR : (((cpR W (storTailOf W) (acctTailOf W) m w).withFork g).f).settle
      (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2)) =
      .ok (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m w post2)) := by
    change ((cpR W (storTailOf W) (acctTailOf W) m w).f.withFork g).settle
      (.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2)) = _
    rw [settle_withFork_of_stat hFroot hg
      (callPrep_stat (cpR_eq W (storTailOf W) (acctTailOf W) m w))]
    rw [frame_settle_ok hcrR hsgR herrF1raw, hobsF1]
  intro cp cevm hp he
  rw [cpR_at g W (storTailOf W) (acctTailOf W) m w hg] at hp
  obtain rfl := Option.some_inj.mp hp
  rw [e1R_at g W (storTailOf W) (acctTailOf W) m w hg] at he
  cases he
  exact ⟨.ok (postF1raw W (storTailOf W) (acctTailOf W) m w post2),
    hexecF1, hsettleR⟩
  /-
  have hFroot : CoveredFork (sR.withOrig W).benvStat.fork := by
    rw [sR_orig_fork W]
    exact CoveredFork.prague
  obtain ⟨-, hpaF2, hpkF2, hcrF2, -, -, hsgF2, -, -⟩ :=
    dcallPrep_spec (cpF2_eq W (storTailOf W) (acctTailOf W) m w) hA4 hC4'
  have hsettleF2 : (((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f).settle
      (.ok (obsChildF1 post2)) = .ok (obsChildF1 post2) := by
    have hfstat : CoveredFork (e1'11 W (storTailOf W) (acctTailOf W) m w).sta.benvStat.fork := by
      rw [stepN_sta (e1'11_eq W (storTailOf W) (acctTailOf W) m w),
        (e1_fork W (storTailOf W) (acctTailOf W) m w).1]
      exact CoveredFork.prague
    change ((cpF2 W (storTailOf W) (acctTailOf W) m w).f.withFork g).settle
      (.ok (obsChildF1 post2)) = _
    rw [settle_withFork_of_stat hfstat hg
      (dcallPrep_stat (cpF2_eq W (storTailOf W) (acctTailOf W) m w))]
    exact frame_settle_ok hcrF2 hsgF2 (show (obsChildF1 post2).error = none from rfl)
  have htailF1Fork : stepN 10
      ((⟨32, (e1 W (storTailOf W) (acctTailOf W) m w).sta,
        d1R W (storTailOf W) (acctTailOf W) m w post2⟩ : Evm).withFork g) =
      some ((e1tail W (storTailOf W) (acctTailOf W) m w post2).withFork g) :=
    tailF1_fork g W (storTailOf W) (acctTailOf W) m w post2 hg
  have hhaltF1Fork : Evm.step ((e1tail W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
      .halt (.ok (postF1 W (storTailOf W) (acctTailOf W) m w post2)) := by
    have htailSta : (e1tail W (storTailOf W) (acctTailOf W) m w post2).sta.benvStat.fork = .prague := by
      rw [stepN_sta (tailF1_eq W (storTailOf W) (acctTailOf W) m w post2)]
      exact (e1_fork W (storTailOf W) (acctTailOf W) m w).1
    have hne : ∀ ee, Evm.step (e1tail W (storTailOf W) (acctTailOf W) m w post2) ≠
        .halt (.error ee) := by
      intro ee he
      rw [returnF1_eq W (storTailOf W) (acctTailOf W) m w post2] at he
      cases he
    have htailHx : (e1tail W (storTailOf W) (acctTailOf W) m w post2).sta.benvStat.excessBlobGas = 0 := by
      rw [stepN_sta (tailF1_eq W (storTailOf W) (acctTailOf W) m w post2)]
      exact (e1_fork W (storTailOf W) (acctTailOf W) m w).2
    rw [show Evm.step ((e1tail W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
        (Evm.step (e1tail W (storTailOf W) (acctTailOf W) m w post2)).withFork g from
      evm_step_withFork_prague htailSta htailHx hg hne]
    rw [returnF1_eq]
    rfl
  have hexecF1 : Nonempty (Exec 0 ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna
      (.ok (postF1 W (storTailOf W) (acctTailOf W) m w post2))) :=
    root_f1_resume g W m w hg hspawnF2 hA4 hC4' post2 hexec2
      hgasRm houtRm herrRm
  obtain ⟨-, -, -, hcrR, -, -, hsgR, -, -⟩ :=
    callPrep_spec (cpR_eq W (storTailOf W) (acctTailOf W) m w) hAgreeR.2.1 hAgreeR.2.2.2
  have hsettleR : (((cpR W (storTailOf W) (acctTailOf W) m w).withFork g).f).settle
      (.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2))) =
      .ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2)) := by
    change ((cpR W (storTailOf W) (acctTailOf W) m w).f.withFork g).settle
      (.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2))) = _
    rw [settle_withFork_of_stat hFroot hg
      (callPrep_stat (cpR_eq W (storTailOf W) (acctTailOf W) m w))]
    exact frame_settle_ok hcrR hsgR
      (show (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2)).error = none from rfl)
  intro cp cevm hp he
  rw [cpR_at g W (storTailOf W) (acctTailOf W) m w hg] at hp
  obtain rfl := Option.some_inj.mp hp
  rw [e1R_at g W (storTailOf W) (acctTailOf W) m w hg] at he
  cases he
  exact ⟨.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2)),
    hexecF1, hsettleR⟩
  -/

theorem root_f1_facts (hRm : RemoveFrame) (g : Fork) (W : State) (m : Meta) (w : World)
    (hg : CoveredFork g) (hRead : ∀ e ∈ readStor, storOf W e.1.1 e.1.2 = e.2)
    (hAgreeR : Agree (cR W (storTailOf W) (acctTailOf W) m w))
    (hspawnF2 : SpawnedBy (((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g).sta)
      (((e1'11 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna) .delegatecall
      ((e2 W (storTailOf W) (acctTailOf W) m w).withFork g))
    (hA4 : ∀ a, a ∈ (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.accessedAddresses ↔
      a ∈ (cpR W (storTailOf W) (acctTailOf W) m w).adrs)
    (hC4' : AcctAgree (e1'11 W (storTailOf W) (acctTailOf W) m w).dyna.state
      (acs1R W (storTailOf W) (acctTailOf W) m w))
    (hAgreeRm : Agree (Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
      (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
      (c2 W (storTailOf W) (acctTailOf W) m w).devm.world)) :
    ∃ post2, Nonempty (Exec 0 ((sRm.withOrig W).withFork g)
      (Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
        (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
        (c2 W (storTailOf W) (acctTailOf W) m w).devm.world).devm (.ok post2)) ∧
      post2.error = none ∧ RemoveFacts ((sRm.withOrig W).withFork g)
        (Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
          (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
          (c2 W (storTailOf W) (acctTailOf W) m w).devm.world) post2 ∧
      ChildAgree (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m w post2))
        keysRm ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
          (acsRm ++ acctTailOf W) ∧
      ChildOk ((sR.withOrig W).withFork g)
        (cR W (storTailOf W) (acctTailOf W) m w)
        (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m w post2)) := by
  have hFroot : CoveredFork (sR.withOrig W).benvStat.fork := by
    rw [sR_orig_fork W]
    exact CoveredFork.prague
  have hcfg2 : Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
      (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
      (c2 W (storTailOf W) (acctTailOf W) m w).devm.world =
      c2 W (storTailOf W) (acctTailOf W) m w := c2_cfg W _ _ _ _
  obtain ⟨post2, hexec2, hgasRm, houtRm, herrRm, hchildRm, -, hFacts⟩ :=
    hRm g W (storTailOf W) (acctTailOf W)
      (c2 W (storTailOf W) (acctTailOf W) m w).devm.meta
      (c2 W (storTailOf W) (acctTailOf W) m w).devm.world hg hRead hAgreeRm
  obtain ⟨-, hpaF2, hpkF2, hcrF2, hiaF2, hikF2, hsgF2, hstF2, -⟩ :=
    dcallPrep_spec (cpF2_eq W (storTailOf W) (acctTailOf W) m w) hA4 hC4'
  have hcpF2adrs : (cpF2 W (storTailOf W) (acctTailOf W) m w).adrs =
      [implAddr, proxyAddr] := of_decide_eq_true (cpF2_adrs W _ _ _ _)
  have hpaF2' : ∀ a, a ∈ (cpF2 W (storTailOf W) (acctTailOf W) m w).p.accessedAddresses ↔
      a ∈ ([implAddr, proxyAddr] : List Adr) := by
    intro a
    rw [hpaF2, hcpF2adrs]
  have hpkF2' : ∀ x, x ∈ (cpF2 W (storTailOf W) (acctTailOf W) m w).p.accessedStorageKeys ↔ False := by
    intro x
    rw [hpkF2, e1'11_keys, e1_entry_keys]
    obtain ⟨-, -, cpk, -, -, cik, -, -⟩ :=
      callPrep_spec (cpR_eq W _ _ _ _) hAgreeR.2.1 hAgreeR.2.2.2
    rw [cik, cpk, hAgreeR.1, cR_keys]
    simp only [List.not_mem_nil]
  /-
  have hchild1 : ChildAgree (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2))
      keysRm ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W) := by
    have hres := resumeF1_eq W (storTailOf W) (acctTailOf W) m w post2
    have hkeep := postF1_keep W (storTailOf W) (acctTailOf W) m w post2
    simp only [Prod.mk.injEq] at hkeep
    have hca := resumeCallB_acc hres
    have hce : (obsChildF1 post2).error.isSome = false := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      rw [obsChildF1_acc, hkeep.1, hca.1 a, hce, hpaF2', obsChildF1_acc,
        hchildRm.1 a, List.mem_append]
      simp only [true_and]
    · intro x
      rw [obsChildF1_keys, hkeep.2.1, hca.2 x, hce, hpkF2', obsChildF1_keys,
        hchildRm.2.1 x]
      simp only [true_and, false_or]
    · intro a k
      rw [obsChildF1_state, hkeep.2.2, resumeCallB_state hres,
        obsChildF1_state, hchildRm.2.2.1 a k]
    · rw [obsChildF1_state, hkeep.2.2, resumeCallB_state hres, obsChildF1_state]
      exact hchildRm.2.2.2
  -/
  have hchild1 := root_child_agree W m w post2 hAgreeR hA4 hC4' hchildRm
  /-
  have hsettleF2 : (((cpF2 W (storTailOf W) (acctTailOf W) m w).withFork g).f).settle (.ok (obsChildF1 post2)) =
      .ok (obsChildF1 post2) := by
    have hfstat : CoveredFork (e1'11 W (storTailOf W) (acctTailOf W) m w).sta.benvStat.fork := by
      rw [stepN_sta (e1'11_eq W (storTailOf W) (acctTailOf W) m w),
        (e1_fork W (storTailOf W) (acctTailOf W) m w).1]
      exact CoveredFork.prague
    change ((cpF2 W (storTailOf W) (acctTailOf W) m w).f.withFork g).settle
      (.ok (obsChildF1 post2)) = _
    rw [settle_withFork_of_stat hfstat hg
      (dcallPrep_stat (cpF2_eq W (storTailOf W) (acctTailOf W) m w))]
    exact frame_settle_ok hcrF2 hsgF2 (show (obsChildF1 post2).error = none from rfl)
  have htailF1Fork : stepN 10
      ((⟨32, (e1 W (storTailOf W) (acctTailOf W) m w).sta,
        d1R W (storTailOf W) (acctTailOf W) m w post2⟩ : Evm).withFork g) =
      some ((e1tail W (storTailOf W) (acctTailOf W) m w post2).withFork g) :=
    tailF1_fork g W (storTailOf W) (acctTailOf W) m w post2 hg
  have hhaltF1Fork : Evm.step ((e1tail W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
      .halt (.ok (postF1 W (storTailOf W) (acctTailOf W) m w post2)) := by
    have htailSta : (e1tail W (storTailOf W) (acctTailOf W) m w post2).sta.benvStat.fork = .prague := by
      rw [stepN_sta (tailF1_eq W (storTailOf W) (acctTailOf W) m w post2)]
      exact (e1_fork W (storTailOf W) (acctTailOf W) m w).1
    have hne : ∀ ee, Evm.step (e1tail W (storTailOf W) (acctTailOf W) m w post2) ≠ .halt (.error ee) := by
      intro ee he
      rw [returnF1_eq W (storTailOf W) (acctTailOf W) m w post2] at he
      cases he
    have htailHx : (e1tail W (storTailOf W) (acctTailOf W) m w post2).sta.benvStat.excessBlobGas = 0 := by
      rw [stepN_sta (tailF1_eq W (storTailOf W) (acctTailOf W) m w post2)]
      exact (e1_fork W (storTailOf W) (acctTailOf W) m w).2
    rw [show Evm.step ((e1tail W (storTailOf W) (acctTailOf W) m w post2).withFork g) =
        (Evm.step (e1tail W (storTailOf W) (acctTailOf W) m w post2)).withFork g from
      evm_step_withFork_prague htailSta htailHx hg hne]
    rw [returnF1_eq]
    rfl
  obtain ⟨spawnF, rsmF, hstepF, henterF⟩ := hspawnF2
  have hexecF1 : Nonempty (Exec 0 ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).sta
      ((e1 W (storTailOf W) (acctTailOf W) m w).withFork g).dyna
      (.ok (postF1 W (storTailOf W) (acctTailOf W) m w post2))) :=
    exec_of_stepN_spawn_runOk
      (e1'11_at g W (storTailOf W) (acctTailOf W) m w hg) hstepF henterF hexec2
      hsettleF2 (exec_of_stepN_halt htailF1Fork hhaltF1Fork)
  have hpostObs := postF1_obs W (storTailOf W) (acctTailOf W) m w post2
  simp only [Prod.mk.injEq] at hpostObs
  have herrF1 : (postF1 W (storTailOf W) (acctTailOf W) m w post2).error = none :=
    Option.isNone_iff_eq_none.mp hpostObs.2
  obtain ⟨-, -, -, hcrR, -, -, hsgR, -, -⟩ :=
    callPrep_spec (cpR_eq W (storTailOf W) (acctTailOf W) m w) hAgreeR.2.1 hAgreeR.2.2.2
  have hsettleR : (((cpR W (storTailOf W) (acctTailOf W) m w).withFork g).f).settle
      (.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2))) =
      .ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2)) := by
    change ((cpR W (storTailOf W) (acctTailOf W) m w).f.withFork g).settle
      (.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2))) = _
    rw [settle_withFork_of_stat hFroot hg
      (callPrep_stat (cpR_eq W (storTailOf W) (acctTailOf W) m w))]
    exact frame_settle_ok hcrR hsgR
      (show (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2)).error = none from rfl)
  have hchildOkR : ChildOk ((sR.withOrig W).withFork g)
      (cR W (storTailOf W) (acctTailOf W) m w)
      (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2)) := by
    intro cp cevm hp he
    rw [cpR_at g W (storTailOf W) (acctTailOf W) m w hg] at hp
    obtain rfl := Option.some_inj.mp hp
    rw [e1R_at g W (storTailOf W) (acctTailOf W) m w hg] at he
    cases he
    exact ⟨.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m w post2)),
      hexecF1, hsettleR⟩
  -/
  have hchildOkR := root_f1_exec g W m w hg hAgreeR hspawnF2 hA4 hC4' post2 hexec2
    hgasRm houtRm herrRm hchild1
  exact ⟨post2, hexec2, herrRm, hFacts, hchild1, hchildOkR⟩

theorem root_frame (hRm : RemoveFrame) : RootFrame := by
  intro g hg W hW
  generalize hm0 : (rootCfg W).devm.meta = m0
  generalize hw0 : (rootCfg W).devm.world = w0
  have hRead : ∀ e ∈ readStor, storOf W e.1.1 e.1.2 = e.2 := hW.1
  have hOrig : OrigAgreeOn O0 W keysV :=
    origAgreeOn_O0 hRead keys_sub_readKeys.2.2.2
  have hroot := root_entry W
  have hcfg : Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W)
      m0 w0 = rootCfg W := by
    symm
    simpa only [hm0, hw0] using Boundary.cfg_of_obsDT hroot.2.2.2
  have hAgree0 : Agree (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W)
      m0 w0) := by
    rw [hcfg]
    exact frameStart_agree AttackerR.t_0000_c0 hroot.1
      mem_emptyWithCapacity_keys mem_emptyWithCapacity_adrs
      (checkpoint_worldShadow hW).1 (checkpoint_worldShadow hW).2
  have hFroot : CoveredFork (sR.withOrig W).benvStat.fork := by
    rw [sR_orig_fork W]
    exact CoveredFork.prague
  have hSroot : ∀ n c, wrun fsA ((sR.withOrig W).withFork g) n c =
      wrun fsA (sR.withOrig W) n c :=
    fun n c => wrun_withFork hFroot hg (sR_orig_hx W) fsA n c
  have hrun33 : wrun fsA ((sR.withOrig W).withFork g) 33
      (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0) =
      .cont (cR W (storTailOf W) (acctTailOf W) m0 w0) := by
    rw [hSroot]
    exact cR_eq W (storTailOf W) (acctTailOf W) m0 w0
  have hAgreeR : Agree (cR W (storTailOf W) (acctTailOf W) m0 w0) :=
    (wrun_cont hrun33).1 hAgree0
  have hspawnR : SpawnedBy ((sR.withOrig W).withFork g)
      (cR W (storTailOf W) (acctTailOf W) m0 w0).devm .call
      ((e1 W (storTailOf W) (acctTailOf W) m0 w0).withFork g) :=
    spawnedBy_of_callPrep hAgreeR
      (cpR_at g W (storTailOf W) (acctTailOf W) m0 w0 hg)
      (e1R_at g W (storTailOf W) (acctTailOf W) m0 w0 hg)
  have hAgree2 := c2R_agree W (storTailOf W) (acctTailOf W) m0 w0 hAgreeR
  obtain ⟨hA4, hC4'⟩ := chain1_of W (storTailOf W) (acctTailOf W) m0 w0 hAgreeR
  have hspawnF2 : SpawnedBy (((e1'11 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta)
      (((e1'11 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).dyna) .delegatecall
      ((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g) := by
    have hsta := e1'11_sta_fork g W (storTailOf W) (acctTailOf W) m0 w0
    have hdyna := e1'11_dyna_fork g W (storTailOf W) (acctTailOf W) m0 w0
    rw [hsta, hdyna]
    exact spawnedBy_of_dcallPrep (cpF2_e2_at g W (storTailOf W) (acctTailOf W)
      m0 w0 hg).1 hA4 hC4' (cpF2_e2_at g W (storTailOf W) (acctTailOf W)
      m0 w0 hg).2
  have hcfg2 : Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
      (c2 W (storTailOf W) (acctTailOf W) m0 w0).devm.meta
      (c2 W (storTailOf W) (acctTailOf W) m0 w0).devm.world =
      c2 W (storTailOf W) (acctTailOf W) m0 w0 := by
    exact c2_cfg W (storTailOf W) (acctTailOf W) m0 w0
  have hAgreeRm : Agree (Boundary.cfgOfT bRm0 (storTailOf W) (acctTailOf W)
      (c2 W (storTailOf W) (acctTailOf W) m0 w0).devm.meta
      (c2 W (storTailOf W) (acctTailOf W) m0 w0).devm.world) := by
    rw [hcfg2]
    exact hAgree2
  /-
  obtain ⟨post2, hexec2, hgasRm, houtRm, herrRm, hchildRm, hslotRm,
    ⟨c339, e3, c3, hrun339, hAgree339, hslot339, hSupply339, hspawn3,
      he3target, he3code, he3value, hc3dyna, hc3f, hc3K, hAgree3, hreentry,
      hpost26, hpostLP, hpost2slot⟩⟩ :=
    hRm g W (storTailOf W) (acctTailOf W)
      (c2 W (storTailOf W) (acctTailOf W) m0 w0).devm.meta
      (c2 W (storTailOf W) (acctTailOf W) m0 w0).devm.world hg hRead hAgreeRm
  obtain ⟨-, hpaF2, hpkF2, hcrF2, hiaF2, hikF2, hsgF2, hstF2, -⟩ :=
    dcallPrep_spec (cpF2_eq W (storTailOf W) (acctTailOf W) m0 w0) hA4 hC4'
  have hcpF2adrs : (cpF2 W (storTailOf W) (acctTailOf W) m0 w0).adrs =
      [implAddr, proxyAddr] :=
    of_decide_eq_true (cpF2_adrs W (storTailOf W) (acctTailOf W) m0 w0)
  have hpaF2' : ∀ a, a ∈ (cpF2 W (storTailOf W) (acctTailOf W) m0 w0).p.accessedAddresses ↔
      a ∈ ([implAddr, proxyAddr] : List Adr) := by
    intro a
    rw [hpaF2, hcpF2adrs]
  have hpkF2' : ∀ x, x ∈ (cpF2 W (storTailOf W) (acctTailOf W) m0 w0).p.accessedStorageKeys ↔ False := by
    intro x
    rw [hpkF2, e1'11_keys, e1_entry_keys]
    obtain ⟨-, -, cpk, -, -, cik, -, -⟩ :=
      callPrep_spec (cpR_eq W (storTailOf W) (acctTailOf W) m0 w0)
        hAgreeR.2.1 hAgreeR.2.2.2
    rw [cik, cpk, hAgreeR.1, cR_keys]
    simp
  have hchild1 : ChildAgree (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W)
      m0 w0 post2)) keysRm
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W) := by
    let p1 := postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2
    let ch1 := obsChildF1 p1
    have hres := resumeF1_eq W (storTailOf W) (acctTailOf W) m0 w0 post2
    have hkeep := postF1_keep W (storTailOf W) (acctTailOf W) m0 w0 post2
    simp only [Prod.mk.injEq] at hkeep
    have hca := resumeCallB_acc hres
    have hce : (obsChildF1 post2).error.isSome = false := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      rw [obsChildF1_acc, hkeep.1, hca.1 a, hce, hpaF2',
        obsChildF1_acc, hchildRm.1 a, List.mem_append]
      simp only [true_and]
    · intro x
      rw [obsChildF1_keys, hkeep.2.1, hca.2 x, hce, hpkF2',
        obsChildF1_keys, hchildRm.2.1 x]
      simp only [true_and, false_or]
    · intro a k
      rw [obsChildF1_state, hkeep.2.2, resumeCallB_state hres,
        obsChildF1_state, hchildRm.2.2.1 a k]
    · rw [obsChildF1_state, hkeep.2.2, resumeCallB_state hres,
        obsChildF1_state]
      exact hchildRm.2.2.2
  have hsettleF2 : (((cpF2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).f).settle
      (.ok (obsChildF1 post2)) = .ok (obsChildF1 post2) := by
    have hfstat : CoveredFork (e1'11 W (storTailOf W) (acctTailOf W) m0 w0).sta.benvStat.fork := by
      rw [stepN_sta (e1'11_eq W (storTailOf W) (acctTailOf W) m0 w0),
        (e1_fork W (storTailOf W) (acctTailOf W) m0 w0).1]
      exact CoveredFork.prague
    change ((cpF2 W (storTailOf W) (acctTailOf W) m0 w0).f.withFork g).settle
      (.ok (obsChildF1 post2)) = .ok (obsChildF1 post2)
    rw [settle_withFork_of_stat hfstat hg
      (dcallPrep_stat (cpF2_eq W (storTailOf W) (acctTailOf W) m0 w0))]
    exact frame_settle_ok hcrF2 hsgF2 (show (obsChildF1 post2).error = none from rfl)
  have hresF1Fork : resumeCallB (((cpF2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).p)
      (((cpF2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).oi)
      (((cpF2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).os)
      (.ok (obsChildF1 post2)) = some (d1R W (storTailOf W) (acctTailOf W) m0 w0 post2) := by
    rw [cpF2_p_fork, cpF2_oi_fork, cpF2_os_fork]
    exact resumeF1_eq W (storTailOf W) (acctTailOf W) m0 w0 post2
  have htailF1Fork : stepN 10
      ((⟨32, (e1 W (storTailOf W) (acctTailOf W) m0 w0).sta,
        d1R W (storTailOf W) (acctTailOf W) m0 w0 post2⟩ : Evm).withFork g) =
      some ((e1tail W (storTailOf W) (acctTailOf W) m0 w0 post2).withFork g) := by
    exact tailF1_fork g W (storTailOf W) (acctTailOf W) m0 w0 post2 hg
  have hhaltF1Fork : Evm.step ((e1tail W (storTailOf W) (acctTailOf W) m0 w0 post2).withFork g) =
      .halt (.ok (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2)) := by
    have htailSta : (e1tail W (storTailOf W) (acctTailOf W) m0 w0 post2).sta.benvStat.fork =
        .prague := by
      rw [stepN_sta (tailF1_eq W (storTailOf W) (acctTailOf W) m0 w0 post2)]
      exact (e1_fork W (storTailOf W) (acctTailOf W) m0 w0).1
    have hne : ∀ ee, Evm.step (e1tail W (storTailOf W) (acctTailOf W) m0 w0 post2) ≠
        .halt (.error ee) := by
      intro ee he
      rw [returnF1_eq W (storTailOf W) (acctTailOf W) m0 w0 post2] at he
      cases he
    have htailHx : (e1tail W (storTailOf W) (acctTailOf W) m0 w0 post2).sta.benvStat.excessBlobGas = 0 := by
      rw [stepN_sta (tailF1_eq W (storTailOf W) (acctTailOf W) m0 w0 post2)]
      exact (e1_fork W (storTailOf W) (acctTailOf W) m0 w0).2
    rw [show Evm.step ((e1tail W (storTailOf W) (acctTailOf W) m0 w0 post2).withFork g) =
        (Evm.step (e1tail W (storTailOf W) (acctTailOf W) m0 w0 post2)).withFork g from
      evm_step_withFork_prague htailSta htailHx hg hne]
    rw [returnF1_eq]
    rfl
  have hexecF1 : Nonempty (Exec 0
      (((e1 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta)
      (((e1 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).dyna)
      (.ok (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2))) :=
    root_f1_resume g W m0 w0 hg hspawnF2 hA4 hC4' post2 hexec2
      hgasRm houtRm herrRm
  have hpostObs := postF1_obs W (storTailOf W) (acctTailOf W) m0 w0 post2
  simp only [Prod.mk.injEq] at hpostObs
  have houtF1 : (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2).output = outRm :=
    List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hpostObs.1
  have herrF1 : (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2).error = none :=
    Option.isNone_iff_eq_none.mp hpostObs.2
  obtain ⟨-, -, -, hcrR, -, -, hsgR, -, -⟩ :=
    callPrep_spec (cpR_eq W (storTailOf W) (acctTailOf W) m0 w0)
      hAgreeR.2.1 hAgreeR.2.2.2
  have hsettleR : (((cpR W (storTailOf W) (acctTailOf W) m0 w0).withFork g).f).settle
      (.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2))) =
      .ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2)) := by
    change ((cpR W (storTailOf W) (acctTailOf W) m0 w0).f.withFork g).settle
      (.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2))) = _
    rw [settle_withFork_of_stat hFroot hg
      (callPrep_stat (cpR_eq W (storTailOf W) (acctTailOf W) m0 w0))]
    exact frame_settle_ok hcrR hsgR (show (obsChildF1
      (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2)).error = none from rfl)
  have hchildOkR : ChildOk ((sR.withOrig W).withFork g)
      (cR W (storTailOf W) (acctTailOf W) m0 w0)
      (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2)) := by
    intro cp cevm hp he
    rw [cpR_at g W (storTailOf W) (acctTailOf W) m0 w0 hg] at hp
    obtain rfl := Option.some_inj.mp hp
    rw [e1R_at g W (storTailOf W) (acctTailOf W) m0 w0 hg] at he
    cases he
    exact ⟨.ok (obsChildF1 (postF1 W (storTailOf W) (acctTailOf W) m0 w0 post2)),
      hexecF1, hsettleR⟩
  -/
  obtain ⟨post2, hexec2, herrRm, hFacts, hchild1, hchildOkR⟩ :=
    root_f1_facts hRm g W m0 w0 hg hRead hAgreeR hspawnF2 hA4 hC4' hAgreeRm
  obtain ⟨c339, e3, c3, hrun339, hAgree339, hslot339, hSupply339, hspawn3,
    he3target, he3code, he3value, hc3dyna, hc3f, hc3K, hAgree3, hreentry,
    hpost26, hpostLP, hpost2slot⟩ := hFacts
  have hbaseExists : ∃ c1, callResume (sR.withOrig W)
      (cR W (storTailOf W) (acctTailOf W) m0 w0)
      (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m0 w0 post2))
      ((cR W (storTailOf W) (acctTailOf W) m0 w0).keys ++ keysRm)
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W) = some c1 := by
    cases hr : callResume (sR.withOrig W)
        (cR W (storTailOf W) (acctTailOf W) m0 w0)
        (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m0 w0 post2))
        ((cR W (storTailOf W) (acctTailOf W) m0 w0).keys ++ keysRm)
        ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
        (acsRm ++ acctTailOf W) with
    | some c1 => exact ⟨c1, rfl⟩
    | none =>
      exfalso
      have hv := v_kernel_raw W (storTailOf W) (acctTailOf W) m0 w0 post2
      unfold runVraw at hv
      rw [hr] at hv
      simp only [obsV, reduceCtorEq] at hv
  obtain ⟨c1, hbase⟩ := hbaseExists
  have hchild1' : ChildAgree (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m0 w0 post2))
      ((cR W (storTailOf W) (acctTailOf W) m0 w0).keys ++ keysRm)
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W) := by
    rw [cR_keys]
    exact hchild1
  have htrans : callResume (sR.withOrig W)
      (cR W (storTailOf W) (acctTailOf W) m0 w0)
      (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m0 w0 post2))
      ((cR W (storTailOf W) (acctTailOf W) m0 w0).keys ++ keysRm)
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W) =
    callResume ((sR.withOrig W).withFork g)
      (cR W (storTailOf W) (acctTailOf W) m0 w0)
      (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m0 w0 post2))
      ((cR W (storTailOf W) (acctTailOf W) m0 w0).keys ++ keysRm)
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W) :=
    (callResume_withFork hFroot hg (cR W (storTailOf W) (acctTailOf W) m0 w0)
      (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m0 w0 post2))
      ((cR W (storTailOf W) (acctTailOf W) m0 w0).keys ++ keysRm)
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W) (acsRm ++ acctTailOf W)).symm
  have hfork : callResume ((sR.withOrig W).withFork g)
      (cR W (storTailOf W) (acctTailOf W) m0 w0)
      (obsChildF1 (postF1raw W (storTailOf W) (acctTailOf W) m0 w0 post2))
      ((cR W (storTailOf W) (acctTailOf W) m0 w0).keys ++ keysRm)
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ storTailOf W)
      (acsRm ++ acctTailOf W) = some c1 := by
    rw [← htrans]
    exact hbase
  have hdecode : ∃ (p : Devm) (cl : Cfg),
      wrun fsA (sR.withOrig W) 2 c1 = .done (.halted p) cl ∧
      p.gasLeft = gasV ∧ p.output = [] ∧ p.error = none ∧
      cl.stor.take storV.length = storV ∧ cl.stor.drop storV.length = storTailOf W ∧
      cl.keys = keysV := by
    have hv := v_kernel_raw W (storTailOf W) (acctTailOf W) m0 w0 post2
    unfold runVraw at hv
    simp only [hbase] at hv
    cases hr : wrun fsA (sR.withOrig W) 2 c1 with
    | stuck =>
      rw [hr] at hv
      simp only [obsV, reduceCtorEq] at hv
    | cont c =>
      rw [hr] at hv
      simp only [obsV, reduceCtorEq] at hv
    | done o cl =>
      rw [hr] at hv
      cases o with
      | returned d => simp only [obsV, reduceCtorEq] at hv
      | halted d =>
        simp only [obsV, Option.some.injEq, Prod.mk.injEq,
          Bool.and_eq_true, decide_eq_true_eq] at hv
        rcases hv with ⟨hgas, hout, ⟨⟨⟨herr, hkeys⟩, hadrs⟩, htake⟩,
          hdropS, hdropA⟩
        refine ⟨d, cl, rfl, hgas, ?_, ?_, ?_, ?_, ?_⟩
        · exact List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout
        · exact Option.isNone_iff_eq_none.mp herr
        · exact htake
        · rw [← List.take_append_drop storV.length cl.stor, htake, hdropS]
          exact List.drop_left
        · exact hkeys
  obtain ⟨p, cl, hwrBase, hgasV, houtV, herrV, htakeV, hdropV, hkeys⟩ := hdecode
  have hstepRootOrig : StepOk fsA ((sR.withOrig W).withFork g)
      (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0) c1 := by
    exact (wrun_cont hrun33).trans
      (callResume_cont hfork hchildOkR hchild1')
  have hAgree1 : Agree c1 := hstepRootOrig.1 hAgree0
  have hwrForked : wrun fsA ((sR.withOrig W).withFork g) 2 c1 =
      .done (.halted p) cl := by
    rw [hSroot]
    exact hwrBase
  have hdone := wrun_done hwrForked hAgree1
  have hrunK : RunK fsA ((sR.withOrig W).withFork g)
      (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0).devm
      (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0).f
      (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0).K (.halted p) :=
    hstepRootOrig.2 _ hAgree0 hdone.1
  have hrunExact : SProg.RunExact (Cert.prog AttackerR.cert) ((sR.withOrig W).withFork g)
      (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0).devm p :=
    ⟨AttackerR.t_0000_c0, fsA_zero, hrunK⟩
  have hjumpsR : Cert.jumpsOk AttackerR.code AttackerR.cert = true := by
    decide +kernel
  have hcodeR : ((sR.withOrig W).withFork g).code = AttackerR.code := by rfl
  have hsta0 : (((rootEvm W).re g W).sta) = ((sR.withOrig W).withFork g) := by
    show ((((rootEvm W).sta.withFork g).withOrig W)) = _
    rw [hroot.2.2.1]
    rfl
  have hpc0 : (((rootEvm W).re g W).pc) = 0 := by
    show (rootEvm W).pc = 0
    exact hroot.2.1
  have hdyna0 : (((rootEvm W).re g W).dyna) = (rootEvm W).dyna := rfl
  have hc0devm : (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) (m0) (w0)).devm =
      (((rootEvm W).re g W).dyna) := by
    rw [hcfg, hdyna0]
    rfl
  have hexecRoot : Nonempty (Exec (((rootEvm W).re g W).pc)
      (((rootEvm W).re g W).sta) (((rootEvm W).re g W).dyna) (.ok p)) := by
    have hx := lift_exact AttackerR.cert_check hjumpsR hcodeR hg hrunExact
    rw [hpc0, hsta0, ← hc0devm]
    exact hx
  have hAcctB : AcctAgree ((Frame.ofCall (rootMsgK W)).inner.benv.state) (acsW W) :=
    (checkpoint_worldShadow hW).2
  have hB : (Frame.ofCall (rootMsgK W)).enter = .run (rootEvm W) := by
    rw [frame_enter_eq_B, frameEnterB_eq_S hAcctB]
    exact hroot.1
  have hfork0 : CoveredFork (Frame.ofCall (rootMsgK W)).outer.benv.stat.fork :=
    CoveredFork.prague
  have hfork1 : CoveredFork (Frame.ofCall (rootMsgK W)).inner.benv.stat.fork :=
    CoveredFork.prague
  have hpneu : (Frame.ofCall (rootMsgK W)).PrecompNeutral :=
    Frame.precompNeutral_of_codeAddress (a := attackerAddr) rfl (by decide) (by decide)
  have hFrame : Frame.ofCall (violMsg g W) =
      (((Frame.ofCall (rootMsgK W)).withFork g).withOrig W) := rfl
  have hentRoot : (Frame.ofCall (violMsg g W)).enter =
      .run ((rootEvm W).re g W) := by
    rw [hFrame]
    exact frame_enter_re hfork0 hfork1 hg hpneu hB
  have hproc : processMessage (violMsg g W) = .ok p := by
    rw [MessageExecution.processMessage_eq_settle_exec_of_enter _ _ hentRoot]
    have hexec : exec ((rootEvm W).re g W) = .ok p :=
      (exec_iff_exec_eq _ _ _ _).mp hexecRoot
    rw [hexec]
    exact frame_settle_ok rfl
      (CoveredFork.rules_stateGas_none (s := (Frame.ofCall (violMsg g W)).inner.benv.stat) hg)
      herrV
  have hstorV : cl.stor = storV ++ storTailOf W := by
    rw [← List.take_append_drop storV.length cl.stor, htakeV, hdropV]
  have hstate : p.state = cl.devm.state := hdone.2.2 p rfl
  have hAgreeCl : Agree cl := hdone.2.1
  obtain ⟨hRm0, hRe2, hRe0, hRe26, hBody0, hBody2, hRe26', hReLP', hRe0',
    hRe2', hRm26, hRmLP, hRm2, hV26, hVLP, hV2⟩ := boundary_values
  have h26 : storOf p.state proxyAddr 26 = 1800 := by
    rw [hstate, hAgreeCl.2.2.1, hstorV]
    exact hV26
  have hLP : storOf p.state proxyAddr lpSlotA = 1906 := by
    rw [hstate, hAgreeCl.2.2.1, hstorV]
    exact hVLP
  have h2 : storOf p.state proxyAddr 2 = 0 := by
    rw [hstate, hAgreeCl.2.2.1, hstorV]
    exact hV2
  have he0caller : (((rootEvm W).re g W).sta.caller) = creator := by
    rw [hsta0]
    exact sRw_caller W g
  have he0target : (((rootEvm W).re g W).sta.currentTarget) = attackerAddr := by
    rw [hsta0]
    exact sRw_target W g
  have he0code : (((rootEvm W).re g W).sta.code) = AttackerR.code := by
    rw [hsta0]
    exact sRw_code W g
  have hrun33' : wrun fsA (((rootEvm W).re g W).sta) 33
      (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0) = .cont
        (cR W (storTailOf W) (acctTailOf W) m0 w0) := by
    rw [hsta0]
    exact hrun33
  have hspawnR' : SpawnedBy (((rootEvm W).re g W).sta)
      (cR W (storTailOf W) (acctTailOf W) m0 w0).devm .call
      ((e1 W (storTailOf W) (acctTailOf W) m0 w0).withFork g) := by
    rw [hsta0]
    exact hspawnR
  have he1target : (((e1 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta.currentTarget) =
      proxyAddr := e1_target_fork g W (storTailOf W) (acctTailOf W) m0 w0
  have he1code : (((e1 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta.code) =
      fwdCode := e1_code_fork g W (storTailOf W) (acctTailOf W) m0 w0
  have hstep11 : stepN 11 ((e1 W (storTailOf W) (acctTailOf W) m0 w0).withFork g) =
      some ((e1'11 W (storTailOf W) (acctTailOf W) m0 w0).withFork g) :=
    e1'11_at g W (storTailOf W) (acctTailOf W) m0 w0 hg
  have he2target : (((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta.currentTarget) =
      proxyAddr := e2_target_fork g W (storTailOf W) (acctTailOf W) m0 w0
  have he2code : (((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta.code) =
      Vulnerable.code := e2_code_fork g W (storTailOf W) (acctTailOf W) m0 w0
  have he2data : (((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta.data) =
      removeCallR := e2_data_fork g W (storTailOf W) (acctTailOf W) m0 w0
  have he2slot2 : storOf
      (((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).dyna.state)
      proxyAddr 2 = 0 := by
    rw [e2_dyna_fork, e2_dyna_c2, hAgree2.2.2.1 _ _,
      c2_stor2 W (storTailOf W) (acctTailOf W) m0 w0]
  have hspawn3' : SpawnedBy (((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta)
      c339.devm .call e3 := by
    rw [e2_sta_fork, e2_sta_eq]
    exact hspawn3
  have he2exec : Nonempty (Exec ((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).pc
      ((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta
      ((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).dyna (.ok post2)) := by
    rw [e2_pc_fork, e2_sta_fork, e2_sta_eq, e2_dyna_fork, e2_dyna_c2, ← hcfg2]
    exact hexec2
  have hc2devm : (c2 W (storTailOf W) (acctTailOf W) m0 w0).devm =
      ((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).dyna := by
    rw [e2_dyna_fork, e2_dyna_c2]
  have hrun339' : wrun fsI ((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g).sta 339
      (c2 W (storTailOf W) (acctTailOf W) m0 w0) = .cont c339 := by
    rw [e2_sta_fork, e2_sta_eq, ← hcfg2]
    exact hrun339
  have hguardRm :
      Vulnerable.code.getInst 6900 = some (.next (.push [0x02] (by decide))) ∧
      Vulnerable.code.getInst 6902 = some (.next (.reg .sload)) ∧
      Vulnerable.code.getInst 6911 = some (.next (.reg .sstore)) := by
    constructor
    · kernel_rfl
    constructor
    · kernel_rfl
    · kernel_rfl
  have hguardAdd :
      Vulnerable.code.getInst 88 = some (.next (.push [0x00] (by decide))) ∧
      Vulnerable.code.getInst 90 = some (.next (.reg .sload)) ∧
      Vulnerable.code.getInst 99 = some (.next (.reg .sstore)) := by
    constructor
    · kernel_rfl
    constructor
    · kernel_rfl
    · kernel_rfl
  have hc0f : (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0).f =
      AttackerR.t_0000_c0 := bR0_cfg_f _ _ _ _
  have hc0K : (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0).K = [] :=
    bR0_cfg_K _ _ _ _
  have hc2f : (c2 W (storTailOf W) (acctTailOf W) m0 w0).f =
      Vulnerable.t_0000_c0 := c2_f _ _ _ _ _
  have hc2K : (c2 W (storTailOf W) (acctTailOf W) m0 w0).K = [] :=
    c2_K _ _ _ _ _
  obtain ⟨cA, e4, e4', e5, c5, cB, post5, hrun32, hAgreeA, hspawnA,
    he4target, he4code, he4value, hstep11_4, hspawn5, he5target, he5code,
    he5data, he5slot2, he5slot0, hexec5, herr5, hc5dyna, hc5f, hc5K,
    hAgree5, hrun2625, hAgreeB, hcBf, hcB0, hcB2, hpost5_26, hpost5_LP,
    hpost5_0, hpost5_2⟩ := hreentry
  refine ⟨p, hproc, herrV, hgasV, h26, hLP, ?_, h2, ?_⟩
  · rw [h26, hLP]
    decide
  · refine ⟨((rootEvm W).re g W),
      ((e1 W (storTailOf W) (acctTailOf W) m0 w0).withFork g),
      ((e1'11 W (storTailOf W) (acctTailOf W) m0 w0).withFork g),
      ((e2 W (storTailOf W) (acctTailOf W) m0 w0).withFork g), e3, e4, e4', e5,
      (Boundary.cfgOfT bR0 (storTailOf W) (acctTailOf W) m0 w0),
      (cR W (storTailOf W) (acctTailOf W) m0 w0),
      (c2 W (storTailOf W) (acctTailOf W) m0 w0), c339, c3, cA, c5, cB,
      post2, post5, ?_⟩
    exact ⟨hentRoot, hexecRoot, he0caller, he0target, he0code,
      hc0devm, hc0f, hc0K, hAgree0, hrun33', hAgreeR, hspawnR',
      he1target, he1code, hstep11, hspawnF2, he2target, he2code, he2data,
      he2exec, herrRm, he2slot2, hc2devm, hc2f, hc2K, hAgree2,
      hrun339', hAgree339, hslot339, hSupply339, hspawn3',
      he3target, he3code, he3value, hc3dyna, hc3f, hc3K, hAgree3,
      hrun32, hAgreeA, hspawnA, he4target, he4code, he4value,
      hstep11_4, hspawn5, he5target, he5code, he5data,
      he5slot2, he5slot0, hexec5, herr5, hc5dyna, hc5f, hc5K,
      hAgree5, hrun2625, hAgreeB, hcBf, hcB0, hcB2,
      hpost5_26, hpost5_LP, hpost5_0, hpost5_2,
      hguardRm, hguardAdd, hpost26, hpostLP, hpost2slot⟩


end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
