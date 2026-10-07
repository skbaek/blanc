import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.InitRun
import Blanc.Lift.WitnessShadow
import Blanc.Lift.WitnessFork
import Blanc.Lift.NodeWalkFork

/-! # V− setup, message 3: `initialize` through the proxy, under every covered fork

From exactly the world the two creations settle to, the root call of `initialize` through the
clone succeeds on every covered fork with exact gas, and its settled world is determined: the
proxy's storage is exactly the initializer's twelve writes (`initWrites`; eleven nonzero
configuration slots and `fee := 0`), the implementation keeps `fee = 31337`, and no account's
nonce, balance or code changes. The Prague kernel facts of `InitRun.lean` transport to every
covered fork (the run executes no `CLZ`, reads no blob price on a block without excess blob
gas, and its frames enter neither `MODEXP` nor `P256VERIFY`); nothing is re-evaluated. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable (cert t_0000_c0 cert_checkM cert_jumpsOkM)

attribute [local irreducible] e3 e3_31 cpI eI

variable {g : Fork}

/-! ### The forwarder frame's entry -/

/-- The forwarder frame's start: no accessed key or address, the world's storage and the
transferred accounts. -/
theorem e3_agree : Agree ⟨e3.dyna, .undefined, [], [], [], stor2, acs3⟩ := by
  refine frameStart_agree .undefined e3_eq (fun x => ?_) (fun a => ?_) (fun a k => ?_) ?_
  · show x ∈ (Std.HashSet.emptyWithCapacity : Std.HashSet (Adr × B256)) ↔
      x ∈ ([] : List (Adr × B256))
    simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]
  · show a ∈ (Std.HashSet.emptyWithCapacity : AdrSet) ↔ a ∈ ([] : List Adr)
    simp only [Std.HashSet.not_mem_emptyWithCapacity, List.not_mem_nil]
  · exact storAgree2 a k
  · exact acctAgree2

theorem e3_keys : ∀ x, x ∈ e3_31.dyna.accessedStorageKeys ↔ x ∈ ([] : List (Adr × B256)) := by
  rw [static3.2.2.2.2.2.1]; exact e3_agree.1

theorem e3_adrs : ∀ a, a ∈ e3_31.dyna.accessedAddresses ↔ a ∈ ([] : List Adr) := by
  rw [static3.2.2.2.2.1]; exact e3_agree.2.1

theorem e3_world : AcctAgree e3_31.dyna.state acs3 ∧
    ∀ a k, storOf e3_31.dyna.state a k = lookupS stor2 a k := by
  rw [static3.2.2.2.1]; exact ⟨e3_agree.2.2.2, e3_agree.2.2.1⟩

theorem e3_block : e3.sta.benvStat.fork = .prague ∧ e3.sta.benvStat.excessBlobGas = 0 := by
  have h := static3.1
  simp only [Prod.mk.injEq] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

theorem e3_fork : CoveredFork e3_31.sta.benvStat.fork := by
  rw [static3.2.2.1, e3_block.1]; exact CoveredFork.prague

theorem cpI_neutral : cpI.f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress static3.2.2.2.2.2.2.2.1 (by decide) (by decide)

theorem frame3_neutral : frame3.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (a := proxyAddr) rfl (by decide) (by decide)

theorem frame3_enter : frame3.enter = .run e3 := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (acs := acs2) acctAgree2]; exact e3_eq

theorem frame3_enter_at (hg : CoveredFork g) : (frame3.withFork g).enter = .run (e3.withFork g) := by
  rw [frame_enter_withFork CoveredFork.prague CoveredFork.prague hg frame3_neutral, frame3_enter]
  rfl

theorem prefix3_at (hg : CoveredFork g) : stepN 11 (e3.withFork g) = some (e3_31.withFork g) :=
  stepN_withFork hg e3_block.1 e3_block.2 prefix3

theorem cpI_at (hg : CoveredFork g) :
    dcallPrep (e3_31.withFork g).sta e3_31.dyna [] acs3 = some (cpI.withFork g) := by
  show dcallPrep (e3_31.sta.withFork g) e3_31.dyna [] acs3 = _
  rw [dcallPrep_withFork e3_fork hg, cpI_eq]; rfl

theorem eI_at (hg : CoveredFork g) : frameEnterS (cpI.withFork g).f acs3 = .run (eI.withFork g) := by
  show frameEnterS (cpI.f.withFork g) acs3 = _
  rw [frameEnterS_withFork_of_stat e3_fork hg (dcallPrep_stat cpI_eq) cpI_neutral, eI_eq]
  rfl

theorem cpI_spec_at (hg : CoveredFork g) :
    Xinst.step (e3_31.withFork g).sta e3_31.dyna .delegatecall =
        .spawn (cpI.withFork g).f (.call cpI.p cpI.oi cpI.os) ∧
      (∀ a, a ∈ cpI.p.accessedAddresses ↔ a ∈ cpI.adrs) ∧
      cpI.p.accessedStorageKeys = e3_31.dyna.accessedStorageKeys ∧
      (cpI.withFork g).f.isCreate = false ∧
      (cpI.withFork g).f.inner.accessedAddresses = cpI.p.accessedAddresses ∧
      (cpI.withFork g).f.inner.accessedStorageKeys = cpI.p.accessedStorageKeys ∧
      (cpI.withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      (cpI.withFork g).f.inner.benv.state = e3_31.dyna.state ∧ cpI.p.state = e3_31.dyna.state :=
  dcallPrep_spec (cpI_at hg) e3_adrs e3_world.1

theorem spawn3_at (hg : CoveredFork g) :
    Evm.step (e3_31.withFork g) = .spawn (cpI.withFork g).f (.call cpI.p cpI.oi cpI.os) 32 := by
  have hat : Ninst.At (e3_31.withFork g).sta.code 31 (.exec .delegatecall) := by
    show Ninst.At e3_31.sta.code 31 (.exec .delegatecall)
    rw [static3.2.2.1]
    have h := static3.1
    simp only [Prod.mk.injEq] at h
    rw [h.2.1]
    rfl
  rw [show e3_31.withFork g = ⟨31, (e3_31.withFork g).sta, e3_31.dyna⟩ by
    rw [← static3.2.1]; rfl]
  rw [Evm.step_next hat, Ninst.step_exec, (cpI_spec_at hg).1]
  rfl

theorem enterI_at (hg : CoveredFork g) : (cpI.withFork g).f.enter = .run (eI.withFork g) := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [(cpI_spec_at hg).2.2.2.2.2.2.2.1]; exact e3_world.1)]
  exact eI_at hg

/-! ### The implementation frame -/

theorem fsI_zero : fsI[0]? = some t_0000_c0 := by kernel_rfl

theorem cI0_agree : Agree cI0 := by
  obtain ⟨-, hpa, hpk, -, hia, hik, -, hst, -⟩ := dcallPrep_spec cpI_eq e3_adrs e3_world.1
  exact frameStart_agree t_0000_c0 eI_eq
    (fun x => by rw [hik, hpk]; exact e3_keys x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst]; exact e3_world.2 a k) (by rw [hst]; exact e3_world.1)

/-- **The implementation frame, under any covered fork**: an `Exec` of the registered runtime
from the machine the forwarder's `DELEGATECALL` enters, ending with 729,444 gas, no output and
no error, its world's storage the initializer's writes over the start storage, and its
accounts those of the start. -/
theorem frameI_at (hg : CoveredFork g) :
    ∃ dI : Devm, Nonempty (Exec (eI.withFork g).pc (eI.withFork g).sta (eI.withFork g).dyna
        (.ok dI)) ∧ dI.gasLeft = 729444 ∧ dI.output = [] ∧ dI.error = none ∧
      (∀ a k, storOf dI.state a k = lookupS (initWrites ++ stor2) a k) ∧
      AcctAgree dI.state (precompAcs ++ acs3) := by
  have h6 := static3.2.2.2.2.2.2.1
  simp only [Prod.mk.injEq] at h6
  obtain ⟨hpc, hcode, -⟩ := h6
  have hfI : CoveredFork eI.sta.benvStat.fork := by
    rw [(frameEnterS_stat eI_eq).trans (dcallPrep_stat cpI_eq).2, static3.2.2.1, e3_block.1]
    exact CoveredFork.prague
  have hxI : eI.sta.benvStat.excessBlobGas = 0 := by
    rw [(frameEnterS_stat eI_eq).trans (dcallPrep_stat cpI_eq).2, static3.2.2.1, e3_block.2]
  have hk := runI
  rw [← wrun_withFork hfI hg hxI fsI 663 cI0] at hk
  generalize hr : wrun fsI (eI.sta.withFork g) 663 cI0 = r at hk
  cases r with
  | cont c => simp only [obsI, reduceCtorEq] at hk
  | stuck => simp only [obsI, reduceCtorEq] at hk
  | done o cl =>
    cases o with
    | returned d => simp only [obsI, reduceCtorEq] at hk
    | halted d =>
      simp only [obsI, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨hgas, hout, herr, -, hstor, hacs⟩ := hk
      obtain ⟨run, hcl, hst⟩ := wrun_done hr cI0_agree
      have hrun : SProg.RunExact (Cert.prog cert) (eI.sta.withFork g) eI.dyna d :=
        ⟨t_0000_c0, fsI_zero, run⟩
      have hx := lift_exactM (sevm := eI.sta.withFork g) cert_checkM cert_jumpsOkM hcode hg hrun
      refine ⟨d, ?_, hgas, ?_, Option.isNone_iff_eq_none.mp herr, fun a k => ?_, fun a => ?_⟩
      · show Nonempty (Exec eI.pc (eI.sta.withFork g) eI.dyna (.ok d))
        rw [hpc]; exact hx
      · exact List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) hout
      · rw [hst d rfl, hcl.2.2.1, hstor]
      · rw [hst d rfl, hcl.2.2.2 a, hacs]

/-! ### Message 3 -/

/-- Message 3 over `world2` on fork `g` is the Prague message with its fork changed. -/
theorem initMsg_world2 (g : Fork) : initMsg g world2 = msg3.withFork g := rfl

/-- **Message 3, under any covered fork.** The root call of `initialize` through the clone,
over the world the creations settle to, succeeds with 744,993 of its 1,000,000 gas left and
no return data; its settled world's storage is the initializer's writes over the start
storage, and every account keeps its nonce, balance and code. -/
theorem init_message_at (hg : CoveredFork g) :
    ∃ post : Devm, processMessage (initMsg g world2) = .ok post ∧ post.error = none ∧
      post.gasLeft = 744993 ∧ post.output = [] ∧
      (∀ a k, storOf post.state a k = lookupS (initWrites ++ stor2) a k) ∧
      AcctAgree post.state (precompAcs ++ acs3) := by
  obtain ⟨dI, hx1, hg1, ho1, he1, hstor, hacs⟩ := frameI_at hg
  have hobs : obsChildI dI = dI := childObs_eq hg1 ho1 he1
  have hr := resumeI_eq dI
  have ht := tailI_eq dI
  have hh := returnI_eq dI
  have hob := post3_obs dI
  have hk := post3_keep dI
  rw [hobs] at hr ht hh hob hk
  simp only [Prod.mk.injEq] at hob
  obtain ⟨hg0, ho0, he0⟩ := hob
  have he0' : (post3F dI).error = none := Option.isNone_iff_eq_none.mp he0
  obtain ⟨-, -, -, hcr, -, -, hsg, -, -⟩ := cpI_spec_at hg
  have hsettle : Resume.run (.call cpI.p cpI.oi cpI.os) ((cpI.withFork g).f.settle (.ok dI)) =
      .ok (dP2 dI) := by
    rw [frame_settle_ok hcr hsg he1]; exact resumeCallB_sound hr
  have hsta : (e3_44 dI).sta = e3.sta := stepN_sta (evm := ⟨32, e3.sta, dP2 dI⟩) ht
  have hstep_halt : Evm.step ((e3_44 dI).withFork g) = .halt (.ok (post3F dI)) := by
    have hp : (e3_44 dI).sta.benvStat.fork = .prague := by rw [hsta]; exact e3_block.1
    have hx : (e3_44 dI).sta.benvStat.excessBlobGas = 0 := by rw [hsta]; exact e3_block.2
    rw [show Evm.step ((e3_44 dI).withFork g) = (Evm.step (e3_44 dI)).withFork g from
      evm_step_withFork_prague hp hx hg (by rw [hh]; intro ee; nofun), hh]
    rfl
  have hx0 : Nonempty (Exec (e3.withFork g).pc (e3.withFork g).sta (e3.withFork g).dyna
      (.ok (post3F dI))) :=
    exec_of_stepN_spawn_runOk (prefix3_at hg) (spawn3_at hg) (enterI_at hg) hx1 hsettle
      (exec_of_stepN_halt (stepN_withFork hg (e := ⟨32, e3.sta, dP2 dI⟩) e3_block.1
        e3_block.2 ht) hstep_halt)
  have hex := (exec_iff_exec_eq _ _ _ _).mp hx0
  have hstate : (post3F dI).state = dI.state := hk.trans (resumeCallB_state hr)
  refine ⟨post3F dI, ?_, he0', hg0,
    List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h) ho0,
    fun a k => by rw [hstate]; exact hstor a k, by rw [hstate]; exact hacs⟩
  have hsg0 : (frame3.withFork g).inner.benv.stat.rules.stateGas = none :=
    CoveredFork.rules_stateGas_none (s := (frame3.withFork g).inner.benv.stat) hg
  rw [initMsg_world2]
  show runFrame (frame3.withFork g) = _
  unfold runFrame
  rw [frame3_enter_at hg]
  show (frame3.withFork g).settle (exec ⟨(e3.withFork g).pc, (e3.withFork g).sta,
    (e3.withFork g).dyna⟩) = _
  rw [hex]
  exact frame_settle_ok rfl hsg0 he0'

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
