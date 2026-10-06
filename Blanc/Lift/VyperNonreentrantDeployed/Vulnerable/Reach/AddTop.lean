import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.AddRun
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.InitTop
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init.Proxy

/-! # V− setup, message 7: the first `add_liquidity` succeeds, under every covered fork

From **any** world `W` the shadows `acs6`/`stor6` describe (the world `approve` settles to is
one), the root call of `add_liquidity([1000, 1000], 0, attacker)` with value 1000 through the
clone succeeds on every covered fork with 826,595 of its 1,000,000 gas left, returns the minted
amount 2000, and settles to a world whose storage is exactly `storAdd` (shadow lookups) and whose
accounts are `acs7` (the 1000 wei moved from the creator to the clone).  The token's
`transferFrom` runs as an actual child of the pool's `CALL`, by the token's own certificate.

Nothing is evaluated here: the Prague kernel facts of `AddRun.lean` (whose `SSTORE` charges read
the closed original state `world6`) transport to the actual message, whose original state is `W`
itself (`wrun_withOrig`, `childRun_withOrig`, `callResume_withOrig`: `W` has `world6`'s storage),
and to every covered fork. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable (cert t_0000_c0 cert_checkM cert_jumpsOkM)
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init (WorldIs mem_emptyWithCapacity_keys
  mem_emptyWithCapacity_adrs)

attribute [local irreducible] eA eA31 cpA eB

variable {g : Fork} {W : State}

/-! ### Static facts -/

theorem addStatic1 : ∀ W : State,
    ((eA W).pc, (eA W).sta.code, (eA W).sta.currentTarget) = (0, fwdCode, proxyAddr) := by
  kernel_forall_rfl
theorem addStatic2 : ∀ W : State, (eA31 W).pc = 31 := by kernel_forall_rfl
theorem addStatic3 : ∀ W : State, (eA31 W).sta = (eA W).sta := by kernel_forall_rfl
theorem addStatic4 : ∀ W : State,
    (eA31 W).dyna.accessedAddresses = (eA W).dyna.accessedAddresses := by kernel_forall_rfl
theorem addStatic5 : ∀ W : State,
    (eA31 W).dyna.accessedStorageKeys = (eA W).dyna.accessedStorageKeys := by kernel_forall_rfl
theorem addStatic6 : ∀ W : State, ((eB W).pc, (eB W).sta.code, (eB W).sta.currentTarget) =
      (0, Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code, proxyAddr) := by kernel_forall_rfl
theorem addStatic7' : ∀ W : State, decide ((cpA W).f.inner.codeAddress = some implAddr) = true := by
  kernel_forall_rfl

theorem addStatic7 (W : State) : (cpA W).f.inner.codeAddress = some implAddr :=
  of_decide_eq_true (addStatic7' W)

theorem eA31_state : ∀ W : State, (eA31 W).dyna.state = (eA W).dyna.state := by
  kernel_forall_rfl

theorem eA_stat (W : State) : (eA W).sta.benvStat = (frameA W).inner.benv.stat :=
  frameEnterS_stat (addFacts0 W).1

theorem eB_stat (W : State) : (eB W).sta.benvStat = (frameA W).inner.benv.stat := by
  rw [(frameEnterS_stat (addFacts0 W).2.2.2.1).trans (dcallPrep_stat (addFacts0 W).2.2.1).2,
    (addStatic3 W), eA_stat]

theorem eA_fork (W : State) : (eA W).sta.benvStat.fork = .prague ∧
    (eA W).sta.benvStat.excessBlobGas = 0 := by
  rw [eA_stat]; exact ⟨rfl, rfl⟩

theorem eB_kok (W : State) : CoveredFork (eB W).sta.benvStat.fork ∧
    (eB W).sta.benvStat.excessBlobGas = 0 ∧ (eB W).sta.benvStat.origState = W := by
  rw [eB_stat]; exact ⟨CoveredFork.prague, rfl, rfl⟩

/-! ### The forwarder frame's entry -/

theorem frameA_inner_state (W : State) : (frameA W).inner.benv.state = W := rfl

theorem acsTransfer_frameA (W : State) : acsTransfer (frameA W).inner acs6 = acsA := rfl

theorem eA_agree (hW : WorldIs W acs6 stor6) : Agree ⟨(eA W).dyna, .undefined, [], [], [], stor6, acsA⟩ := by
  have h := frameStart_agree (f := frameA W) (keys := []) (adrs := []) .undefined (addFacts0 W).1
    mem_emptyWithCapacity_keys mem_emptyWithCapacity_adrs hW.2 hW.1
  rwa [acsTransfer_frameA] at h

theorem eA31_adrs (hW : WorldIs W acs6 stor6) :
    ∀ a, a ∈ (eA31 W).dyna.accessedAddresses ↔ a ∈ ([] : List Adr) := by
  rw [(addStatic4 W)]; exact (eA_agree hW).2.1

theorem eA31_keys (hW : WorldIs W acs6 stor6) :
    ∀ x, x ∈ (eA31 W).dyna.accessedStorageKeys ↔ x ∈ ([] : List (Adr × B256)) := by
  rw [(addStatic5 W)]; exact (eA_agree hW).1

theorem eA31_world (hW : WorldIs W acs6 stor6) : AcctAgree (eA31 W).dyna.state acsA ∧
    ∀ a k, storOf (eA31 W).dyna.state a k = lookupS stor6 a k := by
  rw [eA31_state]; exact ⟨(eA_agree hW).2.2.2, (eA_agree hW).2.2.1⟩

theorem cpA_neutral (W : State) : (cpA W).f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (addStatic7 W) (by decide) (by decide)

theorem frameA_neutral (W : State) : (frameA W).PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (a := proxyAddr) rfl (by decide) (by decide)

theorem frameA_enter (hW : WorldIs W acs6 stor6) : (frameA W).enter = .run (eA W) := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (acs := acs6) hW.1]; exact (addFacts0 W).1

theorem addMsg_withFork (g : Fork) (W : State) : addMsg g W = (msgA W).withFork g := rfl

theorem frameA_enter_at (hg : CoveredFork g) (hW : WorldIs W acs6 stor6) :
    ((frameA W).withFork g).enter = .run ((eA W).withFork g) := by
  rw [frame_enter_withFork CoveredFork.prague CoveredFork.prague hg (frameA_neutral W),
    frameA_enter hW]
  rfl

theorem prefixA_at (hg : CoveredFork g) :
    stepN 11 ((eA W).withFork g) = some ((eA31 W).withFork g) :=
  stepN_withFork hg (eA_fork W).1 (eA_fork W).2 (addFacts0 W).2.1

theorem eA31_fork (W : State) : CoveredFork (eA31 W).sta.benvStat.fork := by
  rw [(addStatic3 W), (eA_fork W).1]; exact CoveredFork.prague

theorem cpA_at (hg : CoveredFork g) :
    dcallPrep ((eA31 W).withFork g).sta (eA31 W).dyna [] acsA = some ((cpA W).withFork g) := by
  show dcallPrep ((eA31 W).sta.withFork g) (eA31 W).dyna [] acsA = _
  rw [dcallPrep_withFork (eA31_fork W) hg, (addFacts0 W).2.2.1]; rfl

theorem eB_at (hg : CoveredFork g) :
    frameEnterS ((cpA W).withFork g).f acsA = .run ((eB W).withFork g) := by
  show frameEnterS ((cpA W).f.withFork g) acsA = _
  rw [frameEnterS_withFork_of_stat (eA31_fork W) hg (dcallPrep_stat (addFacts0 W).2.2.1)
    (cpA_neutral W), (addFacts0 W).2.2.2.1]
  rfl

theorem cpA_spec_at (hg : CoveredFork g) (hW : WorldIs W acs6 stor6) :
    Xinst.step ((eA31 W).withFork g).sta (eA31 W).dyna .delegatecall =
        .spawn ((cpA W).withFork g).f (.call (cpA W).p (cpA W).oi (cpA W).os) ∧
      (∀ a, a ∈ (cpA W).p.accessedAddresses ↔ a ∈ (cpA W).adrs) ∧
      (cpA W).p.accessedStorageKeys = (eA31 W).dyna.accessedStorageKeys ∧
      ((cpA W).withFork g).f.isCreate = false ∧
      ((cpA W).withFork g).f.inner.accessedAddresses = (cpA W).p.accessedAddresses ∧
      ((cpA W).withFork g).f.inner.accessedStorageKeys = (cpA W).p.accessedStorageKeys ∧
      ((cpA W).withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      ((cpA W).withFork g).f.inner.benv.state = (eA31 W).dyna.state ∧
      (cpA W).p.state = (eA31 W).dyna.state :=
  dcallPrep_spec (cpA_at hg) (eA31_adrs hW) (eA31_world hW).1

theorem spawnA_at (hg : CoveredFork g) (hW : WorldIs W acs6 stor6) :
    Evm.step ((eA31 W).withFork g) =
      .spawn ((cpA W).withFork g).f (.call (cpA W).p (cpA W).oi (cpA W).os) 32 := by
  have hat : Ninst.At ((eA31 W).withFork g).sta.code 31 (.exec .delegatecall) := by
    show Ninst.At (eA31 W).sta.code 31 (.exec .delegatecall)
    have h := (addStatic1 W)
    simp only [Prod.mk.injEq] at h
    rw [(addStatic3 W), h.2.1]
    rfl
  rw [show (eA31 W).withFork g = ⟨31, ((eA31 W).withFork g).sta, (eA31 W).dyna⟩ by
    rw [← (addStatic2 W)]; rfl]
  rw [Evm.step_next hat, Ninst.step_exec, (cpA_spec_at hg hW).1]
  rfl

theorem enterB_at (hg : CoveredFork g) (hW : WorldIs W acs6 stor6) :
    ((cpA W).withFork g).f.enter = .run ((eB W).withFork g) := by
  rw [frame_enter_eq_B, frameEnterB_eq_S (by
    rw [(cpA_spec_at hg hW).2.2.2.2.2.2.2.1]; exact (eA31_world hW).1)]
  exact eB_at hg

/-! ### The implementation frame -/

theorem fsI_zero' : fsI[0]? = some t_0000_c0 := by kernel_rfl

theorem cB0_agree (hW : WorldIs W acs6 stor6) : Agree (cB0 W) := by
  obtain ⟨-, hpa, hpk, -, hia, hik, -, hst, -⟩ := dcallPrep_spec (addFacts0 W).2.2.1
    (eA31_adrs hW) (eA31_world hW).1
  exact frameStart_agree t_0000_c0 (addFacts0 W).2.2.2.1
    (fun x => by rw [hik, hpk]; exact eA31_keys hW x) (fun a => by rw [hia]; exact hpa a)
    (fun a k => by rw [hst]; exact (eA31_world hW).2 a k) (by rw [hst]; exact (eA31_world hW).1)

/-- The actual implementation frame's machine (original state `W`) is the kernel's with its
original state changed back to `W`. -/
theorem sB_withOrig (W : State) : (sB W).withOrig W = (eB W).sta := by
  calc ((eB W).sta.withOrig world6).withOrig W = (eB W).sta.withOrig W := rfl
    _ = (eB W).sta.withOrig (eB W).sta.benvStat.origState := by rw [(eB_kok W).2.2]
    _ = (eB W).sta := sevm_withOrig_self _

/-- What `callEnd` does when its halt is decided: the 125 steps to the token `CALL`, the token
child halting without error, the resume, and the 186 steps to the frame's halt, with the
observations `obsB` decides. -/
theorem callEnd_spec {sta : Sevm} {c : Cfg} (h : obsB (callEnd sta c) = true)
    (hr : restB (callEnd sta c) = Boundary.restsOf acsB) :
    ∃ c3 d2 cl c4 d cl', wrun fsI sta 125 c = .cont c3 ∧
      childRun Token20.prog Token20.code sta 200 c3 = .done (.halted d2) cl ∧
      d2.error = none ∧
      callResume sta c3 d2 cl.keys cl.adrs cl.stor cl.acs = some c4 ∧
      wrun fsI sta 186 c4 = .done (.halted d) cl' ∧
      d.gasLeft = 811048 ∧ d.output = abiWord 2000 ∧ d.error = none ∧
      canonS cl'.stor = storAdd ∧ cl'.acs = acsB := by
  unfold callEnd at h hr
  split at h
  · rename_i c3 h3
    split at h
    · rename_i d2 cl hT
      split at h
      · rename_i hE
        split at h
        · rename_i c4 hR
          simp only [hT, hE, ↓reduceIte, hR, h3] at hr
          generalize h4 : wrun fsI sta 186 c4 = r at h hr
          rcases r with _ | ⟨d | d, cl'⟩ | _
          · simp only [obsB, Bool.false_eq_true] at h
          · simp only [obsB, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
            obtain ⟨⟨⟨⟨hg, ho⟩, he⟩, hs⟩, hk⟩ := h
            simp only [restB] at hr
            exact ⟨c3, d2, cl, c4, d, cl', h3, hT, Option.isNone_iff_eq_none.mp hE, hR, h4, hg, ho,
              he, hs, Boundary.acs_eq_of_views hk (hr.trans (Boundary.restsOf_eq acsB))⟩
          · simp only [obsB, Bool.false_eq_true] at h
          · simp only [obsB, Bool.false_eq_true] at h
        · simp only [obsB, Bool.false_eq_true] at h
      · simp only [obsB, Bool.false_eq_true] at h
    · simp only [obsB, Bool.false_eq_true] at h
  · simp only [obsB, Bool.false_eq_true] at h

/-- **The implementation frame, under any covered fork**: an `Exec` of the registered runtime
from the machine the forwarder's `DELEGATECALL` enters, with the token child a real child of
its `CALL`, ending with 811,048 gas, the word 2000, no error, and the final shadows. -/
theorem frameB_at (hg : CoveredFork g) (hW : WorldIs W acs6 stor6) :
    ∃ d : Devm, Nonempty (Exec ((eB W).withFork g).pc ((eB W).withFork g).sta
        ((eB W).withFork g).dyna (.ok d)) ∧
      d.gasLeft = 811048 ∧ d.output = abiWord 2000 ∧ d.error = none ∧
      (∀ a k, storOf d.state a k = lookupS storAdd a k) ∧ AcctAgree d.state acsB := by
  obtain ⟨hfB, hxB, -⟩ := eB_kok W
  have hO : OrigAgree W (sB W).benvStat.origState := (origAgree6 hW.2).symm
  have hsB : sB W = sBc := (addFacts0 W).2.2.2.2.2
  set S := (eB W).sta.withFork g with hSdef
  have hS : ∀ n c, wrun fsI S n c = wrun fsI sBc n c := fun n c => by
    rw [hSdef, wrun_withFork hfB hg hxB, ← sB_withOrig W, wrun_withOrig hO, hsB]
  have hST : ∀ n c, childRun Token20.prog Token20.code S n c =
      childRun Token20.prog Token20.code sBc n c := fun n c => by
    rw [hSdef, childRun_withFork hfB hg hxB, ← sB_withOrig W, childRun_withOrig hO, hsB]
  have hSR : ∀ c d ck ca cs cacc, callResume S c d ck ca cs cacc =
      callResume sBc c d ck ca cs cacc := fun c d ck ca cs cacc => by
    rw [hSdef, callResume_withFork hfB hg, ← sB_withOrig W, callResume_withOrig, hsB]
  -- the boundaries
  have e0 := Boundary.cfg_of_obsD1 (addFacts0 W).2.2.2.2.1
  obtain ⟨m1, w1, e1⟩ := Boundary.obsD1_cont (addChunk1 (cB0 W).devm.meta (cB0 W).devm.world)
  rw [← e0] at e1
  obtain ⟨m2, w2, e2⟩ := Boundary.obsD1_cont (addChunk2 m1 w1)
  obtain ⟨c3, d2, cl, c4, d, cl', h3, hT, hE, hR, h4, hgas, hout, herr, hcanon, hacs⟩ :=
    callEnd_spec (addChunk3 m2 w2).1 (addChunk3 m2 w2).2
  -- the runs at the actual machine
  have hag0 := cB0_agree hW
  have s1 := wrun_cont (sevm := S) ((hS _ _).trans e1)
  have s2 := wrun_cont (sevm := S) ((hS _ _).trans e2)
  have s3 := wrun_cont (sevm := S) ((hS _ _).trans h3)
  have s123 := (s1.trans s2).trans s3
  obtain ⟨k2, a2⟩ := childOk_of_childRun
    (fun hcode hfork hrun => lift_exact Token20.cert_check Token20.cert_jumpsOk hcode hfork hrun)
    (s123.1 hag0) ((hST _ _).trans hT) hE
  have s := s123.trans (callResume_cont ((hSR _ _ _ _ _ _).trans hR) k2 a2)
  obtain ⟨run, hcl, hst⟩ := wrun_done ((hS _ _).trans h4) (s.1 hag0)
  have hcode : S.code = Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code := by
    have h := (addStatic6 W)
    simp only [Prod.mk.injEq] at h
    exact h.2.1
  have hrun : SProg.RunExact (Cert.prog cert) S (eB W).dyna d := ⟨t_0000_c0, fsI_zero', s.2 _ hag0 run⟩
  have hx := lift_exactM cert_checkM cert_jumpsOkM hcode hg hrun
  refine ⟨d, ?_, hgas, hout, herr, fun a k => ?_, fun a => ?_⟩
  · have hpc : (eB W).pc = 0 := by
      have h := (addStatic6 W)
      simp only [Prod.mk.injEq] at h
      exact h.1
    show Nonempty (Exec (eB W).pc S (eB W).dyna (.ok d))
    rw [hpc]; exact hx
  · rw [hst _ rfl, hcl.2.2.1, ← lookupS_canonS, hcanon]
  · rw [hst _ rfl, hcl.2.2.2 a, hacs]

/-! ### Message 7 -/

/-- **Message 7, the first `add_liquidity`, under any covered fork, from any world the shadows
`acs6`/`stor6` describe.** The root call from the code-free creator, value 1000, succeeds with
826,595 of its 1,000,000 gas left and returns the minted amount 2000; its settled world's
storage is `storAdd` and its accounts are `acsB` (the 1000 wei moved to the clone). -/
theorem add_message_at (hg : CoveredFork g) (hW : WorldIs W acs6 stor6) :
    ∃ post : Devm, processMessage (addMsg g W) = .ok post ∧ post.error = none ∧
      post.gasLeft = 826595 ∧ post.output = abiWord 2000 ∧
      (∀ a k, storOf post.state a k = lookupS storAdd a k) ∧ AcctAgree post.state acsB := by
  obtain ⟨dI, hx1, hg1, ho1, he1, hstor, hacs⟩ := frameB_at hg hW
  have hobs : obsChildB dI = dI := childObs_eq hg1 ho1 he1
  have hr := (addFactsC W dI).1
  have ht := (addFactsC W dI).2.1
  have hh := (addFactsC W dI).2.2
  have hob := addFactsD W dI
  have hk := addFactsE W dI
  rw [hobs] at hr ht hh hob hk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hob
  obtain ⟨⟨hg0, ho0⟩, he0⟩ := hob
  have he0' : (postA W dI).error = none := Option.isNone_iff_eq_none.mp he0
  obtain ⟨-, -, -, hcr, -, -, hsg, -, -⟩ := cpA_spec_at hg hW
  have hsettle : Resume.run (.call (cpA W).p (cpA W).oi (cpA W).os)
      (((cpA W).withFork g).f.settle (.ok dI)) = .ok (dA2 W dI) := by
    rw [frame_settle_ok hcr hsg he1]; exact resumeCallB_sound hr
  have hsta : (eA44 W dI).sta = (eA W).sta := stepN_sta (evm := ⟨32, (eA W).sta, dA2 W dI⟩) ht
  have hstep_halt : Evm.step ((eA44 W dI).withFork g) = .halt (.ok (postA W dI)) := by
    have hp : (eA44 W dI).sta.benvStat.fork = .prague := by rw [hsta]; exact (eA_fork W).1
    have hx : (eA44 W dI).sta.benvStat.excessBlobGas = 0 := by rw [hsta]; exact (eA_fork W).2
    rw [show Evm.step ((eA44 W dI).withFork g) = (Evm.step (eA44 W dI)).withFork g from
      evm_step_withFork_prague hp hx hg (by rw [hh]; intro ee; nofun), hh]
    rfl
  have hx0 : Nonempty (Exec ((eA W).withFork g).pc ((eA W).withFork g).sta ((eA W).withFork g).dyna
      (.ok (postA W dI))) :=
    exec_of_stepN_spawn_runOk (prefixA_at hg) (spawnA_at hg hW) (enterB_at hg hW) hx1 hsettle
      (exec_of_stepN_halt (stepN_withFork hg (e := ⟨32, (eA W).sta, dA2 W dI⟩) (eA_fork W).1
        (eA_fork W).2 ht) hstep_halt)
  have hex := (exec_iff_exec_eq _ _ _ _).mp hx0
  have hstate : (postA W dI).state = dI.state := hk.trans (resumeCallB_state hr)
  refine ⟨postA W dI, ?_, he0', hg0, ho0,
    fun a k => by rw [hstate]; exact hstor a k, by rw [hstate]; exact hacs⟩
  have hsg0 : ((frameA W).withFork g).inner.benv.stat.rules.stateGas = none :=
    CoveredFork.rules_stateGas_none (s := ((frameA W).withFork g).inner.benv.stat) hg
  rw [addMsg_withFork]
  show runFrame ((frameA W).withFork g) = _
  unfold runFrame
  rw [frameA_enter_at hg hW]
  show ((frameA W).withFork g).settle (exec ⟨((eA W).withFork g).pc, ((eA W).withFork g).sta,
    ((eA W).withFork g).dyna⟩) = _
  rw [hex]
  exact frame_settle_ok rfl hsg0 he0'

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
