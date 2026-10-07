import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolCallbackRun

/-!
# V− P2, F3 (with F4 as its child and F5 by `ReAddFrame`): the callback frame

`callback_frame : ReAddFrame → CallbackFrame`: from the callback entry boundary `bCb0`
(with free tails), the 32-step run to the `CALL`, the forwarder child (whose settled
machine comes from `ReAddFrame` via F5), and the resume to the halt with `gasCb`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-! ## P2-internal statements (frozen §5.3, verbatim) -/

/-- The re-entry as seen from the callback frame's start configuration `c3` (static machine
`S`): the callback's `CALL` (step 32), the clone's forwarder, its `DELEGATECALL` into F5, and
F5's facts (the `ViolationAt` sub-block). -/
def ReentryFacts (S : Sevm) (c3 : Cfg) : Prop :=
  ∃ (cA : Cfg) (e4 e4' e5 : Evm) (c5 cB : Cfg) (post5 : Devm),
    wrun fsA S 32 c3 = .cont cA ∧ Agree cA ∧ SpawnedBy S cA.devm .call e4 ∧
    e4.sta.currentTarget = proxyAddr ∧ e4.sta.code = fwdCode ∧ e4.sta.value = 100 ∧
    stepN 11 e4 = some e4' ∧ SpawnedBy e4'.sta e4'.dyna .delegatecall e5 ∧
    e5.sta.currentTarget = proxyAddr ∧ e5.sta.code = Vulnerable.code ∧ e5.sta.data = reAddCall ∧
    storOf e5.dyna.state proxyAddr 2 = 1 ∧ storOf e5.dyna.state proxyAddr 0 = 0 ∧
    Nonempty (Exec e5.pc e5.sta e5.dyna (.ok post5)) ∧ post5.error = none ∧
    c5.devm = e5.dyna ∧ c5.f = Vulnerable.t_0000_c0 ∧ c5.K = [] ∧ Agree c5 ∧
    wrun fsI e5.sta 2625 c5 = .cont cB ∧ Agree cB ∧ cB.f = Vulnerable.t_0370_c63 ∧
    storOf cB.devm.state proxyAddr 0 = 1 ∧ storOf cB.devm.state proxyAddr 2 = 1 ∧
    storOf post5.state proxyAddr 26 = 2106 ∧ storOf post5.state proxyAddr lpSlotA = 2106 ∧
    storOf post5.state proxyAddr 0 = 0 ∧ storOf post5.state proxyAddr 2 = 1

/-- **P2, F3 (with F4 as its child and F5 by `ReAddFrame`)**: the callback frame from its
entry boundary `bCb0`, as the certificate interpreter's run (what `childOk_of_start` takes at
F2's `CALL`): the run to the `CALL` (32 steps) and the resume from F4 as one step `StepOk` to `c1`, then `POP` and `STOP` (`wrun … 2`). -/
def CallbackFrame : Prop :=
  ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    CoveredFork g → (∀ e ∈ readStor, storOf O e.1.1 e.1.2 = e.2) →
    Agree (Boundary.cfgOfT bCb0 tS tA m w) →
    ∃ (c1 cl : Cfg) (post : Devm),
      StepOk fsA ((sCb.withOrig O).withFork g) (Boundary.cfgOfT bCb0 tS tA m w) c1 ∧
      wrun fsA ((sCb.withOrig O).withFork g) 2 c1 = .done (.halted post) cl ∧
      post.gasLeft = gasCb ∧ post.output = [] ∧ post.error = none ∧
      cl.keys = keysCb ∧ cl.adrs = adrsCb ∧ cl.stor = storCb ++ tS ∧ cl.acs = acsCb ++ tA ∧
      ReentryFacts ((sCb.withOrig O).withFork g) (Boundary.cfgOfT bCb0 tS tA m w)

/-! ## Static facts -/

theorem sCb_fork : sCb.benvStat.fork = .prague ∧ sCb.benvStat.excessBlobGas = 0 := by
  decide +kernel

/-! ## F3/F4 entry-agreement probes (kernel batch 1 for `callback_frame`) -/

/-- F4's entered accessed addresses come from F3's `CALL` prep frame. -/
theorem e4Cb_entry_acc : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e4Cb O tS tA m w).dyna.accessedAddresses =
      (cpCb O tS tA m w).f.inner.accessedAddresses := by
  kernel_forall_rfl

/-- F4's entered accessed keys come from F3's `CALL` prep frame. -/
theorem e4Cb_entry_keys : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (e4Cb O tS tA m w).dyna.accessedStorageKeys =
      (cpCb O tS tA m w).f.inner.accessedStorageKeys := by
  kernel_forall_rfl

/-- F3's 32-step run never touches the storage shadow. -/
theorem cACb_stor : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (cACb O tS tA m w).stor = Boundary.storOf1 bCb0 ++ tS := by
  kernel_forall_rfl

/-- F5's start configuration shares F3's storage shadow (a projection). -/
theorem c5Cb_stor : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (c5Cb O tS tA m w).stor = (cACb O tS tA m w).stor := by
  kernel_forall_rfl

/-- Pushing a fork through F5's entered frame lands in its state (kernel form). -/
theorem e5Cb_sta_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e5Cb O tS tA m w).withFork g).sta) =
      ((e5Cb O tS tA m w).sta.withFork g) := by
  kernel_forall_rfl

/-- F5's pushed dynamic machine is F5's start configuration's machine. -/
theorem e5Cb_dyna_c5 : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e5Cb O tS tA m w).withFork g).dyna) = ((c5Cb O tS tA m w).devm) := by
  kernel_forall_rfl

/-- Callback-entry storage literals: slot 2 holds 1, slot 0 holds 0. -/
theorem slot2Cb : ∀ (tS : StorShadow),
    lookupS (Boundary.storOf1 bCb0 ++ tS) proxyAddr 2 = 1 := by
  kernel_forall_rfl

theorem slot0Cb : ∀ (tS : StorShadow),
    lookupS (Boundary.storOf1 bCb0 ++ tS) proxyAddr 0 = 0 := by
  kernel_forall_rfl

/-- F5's start configuration runs the entry node with no halt keys. -/
theorem c5Cb_f : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (c5Cb O tS tA m w).f = Vulnerable.t_0000_c0 := by
  kernel_forall_rfl

theorem c5Cb_K : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (c5Cb O tS tA m w).K = [] := by
  kernel_forall_rfl

/-- F5's settled storage literals over the re-entry shadow. -/
theorem post26Re : ∀ (tS : StorShadow),
    lookupS (storRe ++ tS) proxyAddr 26 = 2106 := by
  kernel_forall_rfl

theorem postLPRe : ∀ (tS : StorShadow),
    lookupS (storRe ++ tS) proxyAddr lpSlotA = 2106 := by
  kernel_forall_rfl

theorem post0Re : ∀ (tS : StorShadow),
    lookupS (storRe ++ tS) proxyAddr 0 = 0 := by
  kernel_forall_rfl

theorem post2Re : ∀ (tS : StorShadow),
    lookupS (storRe ++ tS) proxyAddr 2 = 1 := by
  kernel_forall_rfl

theorem obsChild5Cb_state : ∀ (post : Devm),
    ((obsChild5Cb post).state) = post.state := by
  kernel_forall_rfl

/-- Pushing a fork through F4-at-31 lands in its state / preserves its machine. -/
theorem e4Cb31_sta_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((e4Cb31 O tS tA m w).withFork g).sta)) =
      (((e4Cb31 O tS tA m w).sta.withFork g)) := by
  kernel_forall_rfl

/-- Pushing a fork through entered F4 lands in its state. -/
theorem e4Cb_sta_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((e4Cb O tS tA m w).withFork g).sta)) =
      (((e4Cb O tS tA m w).sta.withFork g)) := by
  kernel_forall_rfl

/-- Pushing a fork through F3's call preserves create flag, keys, addresses. -/
theorem cpCb_f_isCreate_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpCb O tS tA m w).withFork g).f)).isCreate =
      ((((cpCb O tS tA m w).f)).isCreate) := by
  kernel_forall_rfl

theorem cpCb5_p_keys_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpCb5 O tS tA m w).withFork g).p).accessedStorageKeys) =
      (((cpCb5 O tS tA m w).p).accessedStorageKeys) := by
  kernel_forall_rfl

theorem cpCb5_p_acc_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpCb5 O tS tA m w).withFork g).p).accessedAddresses) =
      (((cpCb5 O tS tA m w).p).accessedAddresses) := by
  kernel_forall_rfl

theorem cpCb5_adrs_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpCb5 O tS tA m w).withFork g).adrs)) =
      (((cpCb5 O tS tA m w).adrs)) := by
  kernel_forall_rfl

theorem cpCb5_p_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpCb5 O tS tA m w).withFork g).p)) =
      (((cpCb5 O tS tA m w).p)) := by
  kernel_forall_rfl

theorem cpCb5_oi_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpCb5 O tS tA m w).withFork g).oi)) =
      (((cpCb5 O tS tA m w).oi)) := by
  kernel_forall_rfl

theorem cpCb5_os_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((cpCb5 O tS tA m w).withFork g).os)) =
      (((cpCb5 O tS tA m w).os)) := by
  kernel_forall_rfl

theorem e5Cb_pc_fork : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    ((((e5Cb O tS tA m w).withFork g).pc)) =
      (((e5Cb O tS tA m w).pc)) := by
  kernel_forall_rfl

theorem e4Cb31_dyna_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((e4Cb31 O tS tA m w).withFork g).dyna)) =
      ((e4Cb31 O tS tA m w).dyna) := by
  kernel_forall_rfl

/-- Pushing a fork through a literal entered frame lands in its state. -/
theorem mkEvm_sta_fork : ∀ (g : Fork) (pc : Nat) (s : Sevm) (d : Devm),
    ((((Evm.mk pc s d).withFork g).sta)) = ((s.withFork g)) := by
  kernel_forall_rfl

/-- Pushing a fork through a literal frame preserves pc and machine. -/
theorem mkEvm_pc_fork : ∀ (g : Fork) (pc : Nat) (s : Sevm) (d : Devm),
    ((((Evm.mk pc s d).withFork g).pc)) = pc := by
  kernel_forall_rfl

theorem mkEvm_dyna_fork : ∀ (g : Fork) (pc : Nat) (s : Sevm) (d : Devm),
    ((((Evm.mk pc s d).withFork g).dyna)) = d := by
  kernel_forall_rfl

/-- The forwarder issues `DELEGATECALL` at pc 31 (mirrors `proxy_at_delegatecall`). -/
theorem fwd_at_delegatecall : Xinst.At fwdCode 31 .delegatecall := by rfl

/-- F5's entered static gas is the frozen machine's (whatever literal it is). -/
theorem e5Cb_sta_gas' : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), decide ((e5Cb O tS tA m w).sta.gas = (sRe.withOrig O).gas) = true := by
  kernel_forall_rfl

/-- F5's entered code address is the frozen machine's. -/
theorem e5Cb_sta_codeAddress' : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    decide ((e5Cb O tS tA m w).sta.codeAddress = (sRe.withOrig O).codeAddress) = true := by
  kernel_forall_rfl

/-- F5's entered static machine is the frozen one, at the actual original state. -/
theorem e5Cb_sta_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e5Cb O tS tA m w).sta = sRe.withOrig O := by
  intro O tS tA m w
  have hc := e5Cb_caller O tS tA m w
  have ht := e5Cb_target O tS tA m w
  have hct := (e5Cb_facts O tS tA m w).1
  have hg := of_decide_eq_true (e5Cb_sta_gas' O tS tA m w)
  have hv := e5Cb_value O tS tA m w
  have hd := (e5Cb_facts O tS tA m w).2.2
  have hca := of_decide_eq_true (e5Cb_sta_codeAddress' O tS tA m w)
  have hco := (e5Cb_facts O tS tA m w).2.1
  have hdep := e5Cb_depth O tS tA m w
  obtain ⟨hstv, hst, hdp⟩ := e5Cb_flags O tS tA m w
  have hbs := e5Cb_sta_benvStat O tS tA m w
  have hts := e5Cb_sta_tenv O tS tA m w
  cases h : (e5Cb O tS tA m w).sta with
  | mk c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 =>
    simp only [h] at hc ht hct hg hv hd hca hco hdep hstv hst hdp hbs hts
    subst hc ht hct hg hv hd hca hco hdep hstv hst hdp hbs hts
    rfl

/-! ## Fork transport of the F3/F4/F5 spawn chain -/

/-- `sCb`'s fork survives `withOrig`. -/
theorem sCb_orig_fork : ∀ O : State, (sCb.withOrig O).benvStat.fork = .prague := by
  intro O
  simp only [Sevm.withOrig, BenvStat.withOrig]
  exact sCb_fork.1

/-- `sCb`'s blob-gas absence survives `withOrig`. -/
theorem sCb_orig_hx : ∀ O : State, (sCb.withOrig O).benvStat.excessBlobGas = 0 := by
  intro O
  simp only [Sevm.withOrig, BenvStat.withOrig]
  exact sCb_fork.2

/-- F3's `CALL` prep enters no fork-sensitive precompile. -/
theorem cpCb_neutral : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (cpCb O tS tA m w).f.PrecompNeutral :=
  fun O tS tA m w =>
    Frame.precompNeutral_of_codeAddress (cpCb_codeAddr O tS tA m w) (by decide)
      (by decide)

/-- The forwarder's block facts, from the prep specs. -/
theorem e4Cb_fork : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e4Cb O tS tA m w).sta.benvStat.fork = .prague ∧
      (e4Cb O tS tA m w).sta.benvStat.excessBlobGas = 0 := by
  intro O tS tA m w
  have hst := callPrep_stat (cpCb_eq O tS tA m w)
  have he := frameEnterS_stat (e4Cb_eq O tS tA m w)
  rw [he, hst.2]
  exact ⟨sCb_orig_fork O, sCb_orig_hx O⟩

/-- F3's `CALL` prep under any covered fork. -/
theorem cpCb_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    callPrep ((sCb.withOrig O).withFork g) (cACb O tS tA m w) =
      some ((cpCb O tS tA m w).withFork g) := by
  intro g O tS tA m w hg
  have hF : CoveredFork (sCb.withOrig O).benvStat.fork := by
    rw [sCb_orig_fork O]
    exact CoveredFork.prague
  show callPrep ((sCb.withOrig O).withFork g) _ = _
  rw [callPrep_withFork hF hg, cpCb_eq O tS tA m w]
  rfl

/-- The forwarder's entry under any covered fork. -/
theorem e4Cb_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    frameEnterS (((cpCb O tS tA m w).withFork g).f) (cACb O tS tA m w).acs =
      .run ((e4Cb O tS tA m w).withFork g) := by
  intro g O tS tA m w hg
  have hF : CoveredFork (sCb.withOrig O).benvStat.fork := by
    rw [sCb_orig_fork O]
    exact CoveredFork.prague
  show frameEnterS ((cpCb O tS tA m w).f.withFork g) _ = _
  rw [frameEnterS_withFork_of_stat hF hg (callPrep_stat (cpCb_eq O tS tA m w))
    (cpCb_neutral O tS tA m w), e4Cb_eq O tS tA m w]
  rfl

/-- The forwarder's 11-step prefix under any covered fork. -/
theorem e4Cb31_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    stepN 11 ((e4Cb O tS tA m w).withFork g) =
      some ((e4Cb31 O tS tA m w).withFork g) := by
  intro _ O tS tA m w hg
  exact stepN_withFork hg (e4Cb_fork O tS tA m w).1 (e4Cb_fork O tS tA m w).2
    (e4Cb31_eq O tS tA m w)

/-- F4's `DELEGATECALL` prep and F5's entry under any covered fork. -/
theorem cpCb5_e5_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), CoveredFork g →
    dcallPrep ((e4Cb31 O tS tA m w).sta.withFork g)
        ((e4Cb31 O tS tA m w).dyna) (cpCb O tS tA m w).adrs
        (acs4Cb O tS tA m w) = some ((cpCb5 O tS tA m w).withFork g) ∧
      frameEnterS (((cpCb5 O tS tA m w).withFork g).f) (acs4Cb O tS tA m w) =
        .run ((e5Cb O tS tA m w).withFork g) := by
  intro g O tS tA m w hg
  have hF : CoveredFork (e4Cb31 O tS tA m w).sta.benvStat.fork := by
    rw [stepN_sta (e4Cb31_eq O tS tA m w), (e4Cb_fork O tS tA m w).1]
    exact CoveredFork.prague
  exact dcallSpawn_withFork hF hg (cpCb5_eq O tS tA m w) (cpCb5_neutral O tS tA m w)
    (e5Cb_eq O tS tA m w)

/-! ## F5's start configuration agrees -/

/-- The forwarder reaches its `DELEGATECALL` at pc 31. -/
theorem e4Cb31_pc : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e4Cb31 O tS tA m w).pc = 31 := by
  kernel_forall_rfl

/-! ## F5's start configuration agrees -/

/-- F5's start configuration agrees, from F3's `CALL` agreement: keys and addresses
by the prep specs, storage and accounts across F4's value transfer
(`benvAfterTransfer_eq_S`, `benvAfterTransferB_stor`, `acctAgree_transfer`). -/
theorem c5Cb_agree : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), Agree (cACb O tS tA m w) → Agree (c5Cb O tS tA m w) := by
  intro O tS tA m w hA
  have hcsC := callPrep_spec (cpCb_eq O tS tA m w) hA.2.1 hA.2.2.2
  obtain ⟨cstep, cpa, cpk, ccr, cia, cik, csg, cst8⟩ := hcsC
  obtain ⟨benv4, hb4, he4⟩ := frameEnterS_run (e4Cb_eq O tS tA m w)
  have hC4pre : AcctAgree (cpCb O tS tA m w).f.inner.benv.state
      (cACb O tS tA m w).acs := by
    rw [cst8]
    exact hA.2.2.2
  have hC4 : AcctAgree benv4.state (acs4Cb O tS tA m w) :=
    acctAgree_transfer hC4pre hb4
  have hA4 : ∀ a, a ∈ (e4Cb31 O tS tA m w).dyna.accessedAddresses ↔
      a ∈ (cpCb O tS tA m w).adrs := by
    intro a
    rw [e4Cb31_acc O tS tA m w, e4Cb_entry_acc O tS tA m w, cia, cpa]
  have hC4' : AcctAgree (e4Cb31 O tS tA m w).dyna.state (acs4Cb O tS tA m w) := by
    rw [e4Cb31_state O tS tA m w, he4]
    exact hC4
  have hdc := dcallPrep_spec (cpCb5_eq O tS tA m w) hA4 hC4'
  obtain ⟨dstep, dpa, dpk, dcr, dia, dik, dsg, dst8, dst9⟩ := hdc
  refine frameStart_agree (Vulnerable.t_0000_c0) (e5Cb_eq O tS tA m w) ?hK ?hA' ?hS ?hC
  · intro x
    rw [dik, dpk, e4Cb31_keys O tS tA m w, e4Cb_entry_keys O tS tA m w, cik, cpk]
    exact hA.1 x
  · intro a
    rw [dia, dpa]
  · intro a k
    rw [dst8, e4Cb31_state O tS tA m w, he4]
    show storOf benv4.state a k = lookupS (cACb O tS tA m w).stor a k
    have hB : benvAfterTransferB (cpCb O tS tA m w).f.inner = .ok benv4 := by
      rw [benvAfterTransfer_eq_S hC4pre]
      exact hb4
    have hstor := benvAfterTransferB_stor hB a k
    rw [hstor, cst8]
    exact hA.2.2.1 a k
  · rw [dst8, e4Cb31_state O tS tA m w, he4]
    exact hC4

/-! ## F3-close shadow literals (kernel batch 2 for `callback_frame`) -/

/-- F3's `CALL` needs no fork check, under any covered fork. -/
theorem cpCb_forkfree_at : ∀ (g : Fork) (O : State) (tS : StorShadow)
    (tA : AcctShadow) (m : Meta) (w : World),
    frameEntryForkFree (((cpCb O tS tA m w).withFork g).f) = true := by
  kernel_forall_rfl

/-- F3's `CALL` parent/result-window fields ignore the fork. -/
theorem cpCb_p_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((cpCb O tS tA m w).withFork g).p)) = ((cpCb O tS tA m w).p) := by
  kernel_forall_rfl

theorem cpCb_oi_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((cpCb O tS tA m w).withFork g).oi)) = ((cpCb O tS tA m w).oi) := by
  kernel_forall_rfl

theorem cpCb_os_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((cpCb O tS tA m w).withFork g).os)) = ((cpCb O tS tA m w).os) := by
  kernel_forall_rfl

/-- F3's keys at its `CALL`. -/
theorem cACb_keys : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (cACb O tS tA m w).keys =
      [(proxyAddr, (8 : Nat).toB256), (proxyAddr, (26 : Nat).toB256),
        (proxyAddr, (2 : Nat).toB256)] := by
  kernel_forall_rfl

/-- F3's `CALL` prep addresses. -/
theorem cpCb_adrs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (cpCb O tS tA m w).adrs =
      [proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr] := by
  kernel_forall_rfl

/-- F4's `DELEGATECALL` prep addresses. -/
theorem cpCb5_adrs' : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    decide ((cpCb5 O tS tA m w).adrs =
      [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr]) = true := by
  kernel_forall_rfl

theorem cpCb5_adrs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (cpCb5 O tS tA m w).adrs =
      [implAddr, proxyAddr, attackerAddr, (4 : Adr), implAddr, proxyAddr] :=
  fun O tS tA m w => of_decide_eq_true (cpCb5_adrs' O tS tA m w)

/-- Whether a node is a `CALL` step (kernel-decided on use). -/
def isCallNode : SFunc → Bool
  | .next (.exec .call) _ => true
  | _ => false

/-- F3's `CALL` node shape, as a kernel fact. -/
theorem cACb_fshape : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), isCallNode (cACb O tS tA m w).f = true := by
  kernel_forall_rfl

/-- F4's post-resume output is the re-entrant output. -/
theorem post4Cb_out : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (d : Devm), (post4Cb O tS tA m w d).output = outRe := by
  kernel_forall_rfl

/-- The callback's continuation after its `CALL` (kernel-normalized on use). -/
def cAg0 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) : SFunc :=
  match (cACb O tS tA m w).f with
  | .next _ g => g
  | f => f

/-! ## The resumed configuration, as data -/

/-- The callback frame after its `CALL` settles the forwarder `post`: the resume
result with the forwarder shadows. -/
def C1 (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post : Devm) : Cfg :=
  ⟨(resumeCallB (cpCb O tS tA m w).p (cpCb O tS tA m w).oi (cpCb O tS tA m w).os
      (.ok (obsChild4Cb (post4Cb O tS tA m w post)))).getD
      (post4Cb O tS tA m w post),
    cAg0 O tS tA m w, (cACb O tS tA m w).K,
    (cACb O tS tA m w).keys ++ ((cACb O tS tA m w).keys ++ keysRe),
    (cpCb O tS tA m w).adrs ++ ((cpCb5 O tS tA m w).adrs ++ adrsRe),
    storRe ++ tS, acsRe ++ tA⟩

/-- Two more steps halt with the pinned gas, no output, no error, and the pinned
shadows followed by the tails. -/
theorem halt2_shadows : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post : Devm),
    (match wrun fsA (sCb.withOrig O) 2 (C1 O tS tA m w post) with
      | .done (.halted p) cl =>
        (p.gasLeft, p.output, p.error.isSome, cl.keys, cl.adrs, cl.stor, cl.acs)
      | _ => (0, [], true, [], [], [], [])) =
      (gasCb, [], false, keysCb, adrsCb, storCb ++ tS, acsCb ++ tA) := by
  simp only [C1, cACb_keys, cpCb_adrs, cpCb5_adrs]
  kernel_forall_rfl

/-! ## The halt decoder -/

/-! ## Callback-frame helpers (split for heartbeat budget) -/

/-- F4's value under any covered fork (kernel form; avoids an `OfNat` diamond). -/
theorem e4Cb_value_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World), ((((e4Cb O tS tA m w).withFork g).sta).value) = 100 := by
  kernel_forall_rfl

/-- F5's entry facts under any covered fork (kernel form; `e5Cb` is a match). -/
theorem e5Cb_facts_at : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((((e5Cb O tS tA m w).withFork g).sta).currentTarget = proxyAddr) ∧
      ((((e5Cb O tS tA m w).withFork g).sta).code = Vulnerable.code) ∧
      ((((e5Cb O tS tA m w).withFork g).sta).data = reAddCall) := by
  kernel_forall_rfl_and

/-- F4's `DELEGATECALL` agreements, from F3's: address/key membership and the
prepared frame's state, step, and key facts. -/
theorem chain4_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g)
    (hAgreeA : Agree (cACb O tS tA m w)) :
    (∀ a, a ∈ (e4Cb31 O tS tA m w).dyna.accessedAddresses ↔
      a ∈ (cpCb O tS tA m w).adrs) ∧
    AcctAgree (e4Cb31 O tS tA m w).dyna.state (acs4Cb O tS tA m w) ∧
    ((((cpCb5 O tS tA m w).withFork g).f).isCreate = false) ∧
    ((((cpCb5 O tS tA m w).withFork g).f).inner.benv.stat.rules.stateGas =
      none) ∧
    ((((cpCb5 O tS tA m w).withFork g).f).inner.benv.state =
      (e4Cb31 O tS tA m w).dyna.state) ∧
    (Xinst.step (((e4Cb31 O tS tA m w).sta.withFork g))
      ((e4Cb31 O tS tA m w).dyna) .delegatecall =
      .spawn ((((cpCb5 O tS tA m w).withFork g).f))
        (.call ((((cpCb5 O tS tA m w).withFork g).p))
          ((((cpCb5 O tS tA m w).withFork g).oi))
          ((((cpCb5 O tS tA m w).withFork g).os)))) ∧
    ((((cpCb5 O tS tA m w).withFork g).p).accessedStorageKeys =
      (e4Cb31 O tS tA m w).dyna.accessedStorageKeys) ∧
    (∀ a, a ∈ ((((cpCb5 O tS tA m w).withFork g).p).accessedAddresses) ↔
      a ∈ ((((cpCb5 O tS tA m w).withFork g).adrs))) := by
  have hcsC := callPrep_spec (cpCb_eq O tS tA m w) hAgreeA.2.1 hAgreeA.2.2.2
  obtain ⟨cstep, cpa, cpk, ccr, cia, cik, csg, cst8⟩ := hcsC
  have hA4 : ∀ a, a ∈ (e4Cb31 O tS tA m w).dyna.accessedAddresses ↔
      a ∈ (cpCb O tS tA m w).adrs := by
    intro a
    rw [e4Cb31_acc O tS tA m w, e4Cb_entry_acc O tS tA m w, cia, cpa]
  obtain ⟨benv4, hb4, he4⟩ := frameEnterS_run (e4Cb_eq O tS tA m w)
  have hC4pre : AcctAgree (cpCb O tS tA m w).f.inner.benv.state
      (cACb O tS tA m w).acs := by
    rw [cst8]
    exact hAgreeA.2.2.2
  have hC4 : AcctAgree benv4.state (acs4Cb O tS tA m w) :=
    acctAgree_transfer hC4pre hb4
  have hC4' : AcctAgree (e4Cb31 O tS tA m w).dyna.state
      (acs4Cb O tS tA m w) := by
    rw [e4Cb31_state O tS tA m w, he4]
    exact hC4
  have hdc := dcallPrep_spec (cpCb5_e5_at g O tS tA m w hg).1 hA4 hC4'
  obtain ⟨dstep, dpa, dpk, dcr, dia, dik, dsg, dst8, dst9⟩ := hdc
  exact ⟨hA4, hC4', dcr, dsg, dst8, dstep, dpk, dpa⟩

/-- The re-entry facts: F3 to its `CALL`, F4 to F5, P1's run, and F4's child. -/
theorem reentry_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g)
    (run32 : wrun fsA ((sCb.withOrig O).withFork g) 32
      (Boundary.cfgOfT bCb0 tS tA m w) = .cont (cACb O tS tA m w))
    (hAgreeA : Agree (cACb O tS tA m w))
    (spawnA : SpawnedBy ((sCb.withOrig O).withFork g) (cACb O tS tA m w).devm
      .call ((e4Cb O tS tA m w).withFork g))
    (spawn5 : SpawnedBy (((e4Cb31 O tS tA m w).withFork g).sta)
      (((e4Cb31 O tS tA m w).withFork g).dyna) .delegatecall
      ((e5Cb O tS tA m w).withFork g))
    (post : Devm)
    (hexec5' : Nonempty (Exec (((e5Cb O tS tA m w).withFork g).pc)
      (((e5Cb O tS tA m w).withFork g).sta)
      (((e5Cb O tS tA m w).withFork g).dyna) (.ok post)))
    (herrRe : post.error = none) (hAgree5 : Agree (c5Cb O tS tA m w))
    (cB : Cfg)
    (run2625' : wrun fsI (((e5Cb O tS tA m w).withFork g).sta)
      2625 (c5Cb O tS tA m w) = .cont cB)
    (hagreeB : Agree cB) (hfB : cB.f = Vulnerable.t_0370_c63)
    (hs0B : storOf cB.devm.state proxyAddr 0 = 1)
    (hs2B : storOf cB.devm.state proxyAddr 2 = 1)
    (hchildRe : ChildAgree post keysRe adrsRe (storRe ++ tS) (acsRe ++ tA)) :
    ReentryFacts ((sCb.withOrig O).withFork g)
      (Boundary.cfgOfT bCb0 tS tA m w) := by
  refine ⟨cACb O tS tA m w, (e4Cb O tS tA m w).withFork g,
    (e4Cb31 O tS tA m w).withFork g, (e5Cb O tS tA m w).withFork g,
    c5Cb O tS tA m w, cB, post, run32, hAgreeA, spawnA, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact (e4Cb_target O tS tA m w).1
  · exact e4Cb_code O tS tA m w
  · exact e4Cb_value_at g O tS tA m w
  · exact stepN_withFork hg (e4Cb_fork O tS tA m w).1
      (e4Cb_fork O tS tA m w).2 (e4Cb31_eq O tS tA m w)
  · exact spawn5
  · exact (e5Cb_facts_at g O tS tA m w).1
  · exact (e5Cb_facts_at g O tS tA m w).2.1
  · exact (e5Cb_facts_at g O tS tA m w).2.2
  · have h2 := hAgree5.2.2.1 proxyAddr 2
    rw [c5Cb_stor O tS tA m w, cACb_stor O tS tA m w, slot2Cb tS,
      ← e5Cb_dyna_c5 g O tS tA m w] at h2
    exact h2
  · have h0 := hAgree5.2.2.1 proxyAddr 0
    rw [c5Cb_stor O tS tA m w, cACb_stor O tS tA m w, slot0Cb tS,
      ← e5Cb_dyna_c5 g O tS tA m w] at h0
    exact h0
  · exact hexec5'
  · exact herrRe
  · exact (e5Cb_dyna_c5 g O tS tA m w).symm
  · exact c5Cb_f O tS tA m w
  · exact c5Cb_K O tS tA m w
  · exact hAgree5
  · exact run2625'
  · exact hagreeB
  · exact hfB
  · exact hs0B
  · exact hs2B
  · have h26 := hchildRe.2.2.1 proxyAddr 26
    rw [post26Re tS] at h26
    exact h26
  · have hLP := hchildRe.2.2.1 proxyAddr lpSlotA
    rw [postLPRe tS] at hLP
    exact hLP
  · have hp0 := hchildRe.2.2.1 proxyAddr 0
    rw [post0Re tS] at hp0
    exact hp0
  · have hp2 := hchildRe.2.2.1 proxyAddr 2
    rw [post2Re tS] at hp2
    exact hp2

/-- F4's `DELEGATECALL` step to its spawn (split from `exec4_of` for budget). -/
theorem step4_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World)
    (dstep : Xinst.step (((e4Cb31 O tS tA m w).sta.withFork g))
      ((e4Cb31 O tS tA m w).dyna) .delegatecall =
      .spawn ((((cpCb5 O tS tA m w).withFork g).f))
        (.call ((((cpCb5 O tS tA m w).withFork g).p))
          ((((cpCb5 O tS tA m w).withFork g).oi))
          ((((cpCb5 O tS tA m w).withFork g).os)))) :
    Evm.step ((e4Cb31 O tS tA m w).withFork g) =
      .spawn (((cpCb5 O tS tA m w).withFork g).f)
        (.call (((cpCb5 O tS tA m w).withFork g).p)
          (((cpCb5 O tS tA m w).withFork g).oi)
          (((cpCb5 O tS tA m w).withFork g).os)) 32 := by
  have hcode31 : ((e4Cb31 O tS tA m w).sta.code) = fwdCode := by
    rw [stepN_sta (e4Cb31_eq O tS tA m w)]
    exact e4Cb_code O tS tA m w
  have e4g31_sta : ((((e4Cb31 O tS tA m w).withFork g).sta)) =
      (((e4Cb31 O tS tA m w).sta.withFork g)) :=
    e4Cb31_sta_fork g O tS tA m w
  have hat4 : Ninst.At ((((e4Cb31 O tS tA m w).withFork g).sta).code) 31
      (.exec .delegatecall) := by
    rw [e4Cb31_sta_fork g O tS tA m w,
      Blanc.ForkUniform.Sevm.withFork_code, hcode31]
    exact fwd_at_delegatecall
  rw [show ((e4Cb31 O tS tA m w).withFork g) =
      ⟨31, (((e4Cb31 O tS tA m w).withFork g).sta),
        ((e4Cb31 O tS tA m w).dyna)⟩ by
    rw [← e4Cb31_pc O tS tA m w]
    rfl]
  rw [Evm.step_next hat4, Ninst.step_exec, e4g31_sta, dstep]
  rfl

/-- F4's tail after F5 settles: resume, ten steps, halt (split for budget). -/
theorem rest4_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (post : Devm) :
    Nonempty (Exec 32 ((((e4Cb O tS tA m w).withFork g).sta))
      (d4Cb O tS tA m w post) (.ok (post4Cb O tS tA m w post))) := by
  have hsta444 : ((((e4Cb31 O tS tA m w).withFork g).sta)) =
      (((⟨32, ((e4Cb O tS tA m w).sta),
        (d4Cb O tS tA m w post)⟩ : Evm).withFork g).sta) := by
    rw [e4Cb31_sta_fork g O tS tA m w,
      mkEvm_sta_fork g 32 ((e4Cb O tS tA m w).sta) (d4Cb O tS tA m w post),
      stepN_sta (e4Cb31_eq O tS tA m w)]
  have htail4 : stepN 10
      (((⟨32, ((e4Cb O tS tA m w).sta),
        (d4Cb O tS tA m w post)⟩ : Evm).withFork g)) =
      some (((e444Cb O tS tA m w post).withFork g)) :=
    stepN_withFork hg (e4Cb_fork O tS tA m w).1 (e4Cb_fork O tS tA m w).2
      (tailCb_eq O tS tA m w post)
  have hsta444b : ((e444Cb O tS tA m w post).sta) =
      ((e4Cb O tS tA m w).sta) := by
    have h := stepN_sta (tailCb_eq O tS tA m w post)
    exact h
  have hhalt4 : Evm.step (((e444Cb O tS tA m w post).withFork g)) =
      .halt (.ok (post4Cb O tS tA m w post)) := by
    rw [show Evm.step (((e444Cb O tS tA m w post).withFork g)) =
        (Evm.step (e444Cb O tS tA m w post)).withFork g from
      evm_step_withFork_prague (by rw [hsta444b]; exact (e4Cb_fork O tS tA m w).1)
        (by rw [hsta444b]; exact (e4Cb_fork O tS tA m w).2) hg
        (by rw [returnCb_eq O tS tA m w post]; intro ee; nofun),
      returnCb_eq O tS tA m w post]
    rfl
  have hrest4' := exec_of_stepN_halt htail4 hhalt4
  rw [← hsta444, e4Cb31_sta_fork g O tS tA m w,
    stepN_sta (e4Cb31_eq O tS tA m w), ← e4Cb_sta_fork g O tS tA m w,
    mkEvm_pc_fork, mkEvm_dyna_fork] at hrest4'
  exact hrest4'

/-- F4's entry/settle facts (split from `exec4_of` for budget). -/
theorem mid4_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (post : Devm)
    (hgasRe : post.gasLeft = gasRe) (houtRe : post.output = outRe)
    (herrRe : post.error = none)
    (hC4' : AcctAgree (e4Cb31 O tS tA m w).dyna.state (acs4Cb O tS tA m w))
    (dst8 : ((((cpCb5 O tS tA m w).withFork g).f).inner.benv.state =
      (e4Cb31 O tS tA m w).dyna.state))
    (hsettle4pre : ((((cpCb5 O tS tA m w).withFork g).f).settle (.ok post)) =
      (.ok post)) :
    AcctAgree ((((cpCb5 O tS tA m w).withFork g).f).inner.benv.state)
      (acs4Cb O tS tA m w) ∧
      ((((cpCb5 O tS tA m w).withFork g).f).enter) =
        .run ((e5Cb O tS tA m w).withFork g) ∧
      Resume.run
        (.call (((cpCb5 O tS tA m w).withFork g).p)
          (((cpCb5 O tS tA m w).withFork g).oi)
          (((cpCb5 O tS tA m w).withFork g).os))
        ((((cpCb5 O tS tA m w).withFork g).f).settle (.ok post)) =
        .ok (d4Cb O tS tA m w post) := by
  have hAgreeEnter5 : AcctAgree ((((cpCb5 O tS tA m w).withFork g).f).inner.benv.state)
      (acs4Cb O tS tA m w) := by
    rw [dst8]
    exact hC4'
  have e5enter : ((((cpCb5 O tS tA m w).withFork g).f).enter) =
      .run ((e5Cb O tS tA m w).withFork g) := by
    rw [frame_enter_eq_B, frameEnterB_eq_S hAgreeEnter5]
    exact (cpCb5_e5_at g O tS tA m w hg).2
  have hobs5 : obsChild5Cb post = post := childObs_eq hgasRe houtRe herrRe
  have hresume5 : resumeCallB ((cpCb5 O tS tA m w).p) ((cpCb5 O tS tA m w).oi)
      ((cpCb5 O tS tA m w).os) (.ok post) = some (d4Cb O tS tA m w post) := by
    have hr5 := resumeCb_eq O tS tA m w post
    rw [hobs5] at hr5
    exact hr5
  have hsettle4 : Resume.run
      (.call (((cpCb5 O tS tA m w).withFork g).p)
        (((cpCb5 O tS tA m w).withFork g).oi)
        (((cpCb5 O tS tA m w).withFork g).os))
      ((((cpCb5 O tS tA m w).withFork g).f).settle (.ok post)) =
      .ok (d4Cb O tS tA m w post) := by
    rw [cpCb5_p_fork g O tS tA m w, cpCb5_oi_fork g O tS tA m w,
      cpCb5_os_fork g O tS tA m w, hsettle4pre]
    exact resumeCallB_sound hresume5
  exact ⟨hAgreeEnter5, e5enter, hsettle4⟩

/-- F4's execution assembly from its parts (split from `exec4_of` for budget). -/
theorem end4_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (post : Devm)
    (hstep4 : Evm.step ((e4Cb31 O tS tA m w).withFork g) =
      .spawn (((cpCb5 O tS tA m w).withFork g).f)
        (.call (((cpCb5 O tS tA m w).withFork g).p)
          (((cpCb5 O tS tA m w).withFork g).oi)
          (((cpCb5 O tS tA m w).withFork g).os)) 32)
    (e5enter : ((((cpCb5 O tS tA m w).withFork g).f).enter) =
      .run ((e5Cb O tS tA m w).withFork g))
    (hexec5' : Nonempty (Exec (((e5Cb O tS tA m w).withFork g).pc)
      (((e5Cb O tS tA m w).withFork g).sta)
      (((e5Cb O tS tA m w).withFork g).dyna) (.ok post)))
    (hsettle4 : Resume.run
      (.call (((cpCb5 O tS tA m w).withFork g).p)
        (((cpCb5 O tS tA m w).withFork g).oi)
        (((cpCb5 O tS tA m w).withFork g).os))
      ((((cpCb5 O tS tA m w).withFork g).f).settle (.ok post)) =
      .ok (d4Cb O tS tA m w post))
    (hrest4 : Nonempty (Exec 32 ((((e4Cb O tS tA m w).withFork g).sta))
      (d4Cb O tS tA m w post) (.ok (post4Cb O tS tA m w post)))) :
    Nonempty (Exec ((((e4Cb O tS tA m w).withFork g).pc))
      ((((e4Cb O tS tA m w).withFork g).sta))
      ((((e4Cb O tS tA m w).withFork g).dyna))
      (.ok (post4Cb O tS tA m w post))) := by
  exact exec_of_stepN_spawn_runOk (e4Cb31_at g O tS tA m w hg) hstep4 e5enter
    hexec5' hsettle4 hrest4

/-- F4's execution from its `DELEGATECALL` through F5 to its settled machine. -/
theorem exec4_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (post : Devm)
    (hexec5' : Nonempty (Exec (((e5Cb O tS tA m w).withFork g).pc)
      (((e5Cb O tS tA m w).withFork g).sta)
      (((e5Cb O tS tA m w).withFork g).dyna) (.ok post)))
    (hgasRe : post.gasLeft = gasRe) (houtRe : post.output = outRe)
    (herrRe : post.error = none)
    (hsettleRe : ∀ f : Frame, f.isCreate = false →
      f.inner.benv.stat.rules.stateGas = none → f.settle (.ok post) = .ok post)
    (hC4' : AcctAgree (e4Cb31 O tS tA m w).dyna.state (acs4Cb O tS tA m w))
    (dcr : ((((cpCb5 O tS tA m w).withFork g).f).isCreate = false))
    (dsg : (((((cpCb5 O tS tA m w).withFork g).f).inner.benv.stat.rules.stateGas =
      none)))
    (dst8 : ((((cpCb5 O tS tA m w).withFork g).f).inner.benv.state =
      (e4Cb31 O tS tA m w).dyna.state))
    (dstep : Xinst.step (((e4Cb31 O tS tA m w).sta.withFork g))
      ((e4Cb31 O tS tA m w).dyna) .delegatecall =
      .spawn ((((cpCb5 O tS tA m w).withFork g).f))
        (.call ((((cpCb5 O tS tA m w).withFork g).p))
          ((((cpCb5 O tS tA m w).withFork g).oi))
          ((((cpCb5 O tS tA m w).withFork g).os)))) :
    Nonempty (Exec ((((e4Cb O tS tA m w).withFork g).pc))
      ((((e4Cb O tS tA m w).withFork g).sta))
      ((((e4Cb O tS tA m w).withFork g).dyna))
      (.ok (post4Cb O tS tA m w post))) := by
  have hstep4 := step4_of g O tS tA m w dstep
  have hsettle4pre := hsettleRe _ dcr dsg
  obtain ⟨hAgreeEnter5, e5enter, hsettle4⟩ :=
    mid4_of g O tS tA m w hg post hgasRe houtRe herrRe hC4' dst8 hsettle4pre
  have hrest4 := rest4_of g O tS tA m w hg post
  exact end4_of g O tS tA m w hg post hstep4 e5enter hexec5' hsettle4 hrest4

/-- F4's child: the settled forwarder machine and its agreements. -/
theorem child4_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (post : Devm)
    (hAgreeA : Agree (cACb O tS tA m w))
    (hgasRe : post.gasLeft = gasRe) (houtRe : post.output = outRe)
    (herrRe : post.error = none)
    (hchildRe : ChildAgree post keysRe adrsRe (storRe ++ tS) (acsRe ++ tA))
    (hexec4 : Nonempty (Exec ((((e4Cb O tS tA m w).withFork g).pc))
      ((((e4Cb O tS tA m w).withFork g).sta))
      ((((e4Cb O tS tA m w).withFork g).dyna))
      (.ok (post4Cb O tS tA m w post))))
    (_dcr : ((((cpCb5 O tS tA m w).withFork g).f).isCreate = false))
    (_dsg : (((((cpCb5 O tS tA m w).withFork g).f).inner.benv.stat.rules.stateGas =
      none)))
    (dpk : ((((cpCb5 O tS tA m w).withFork g).p).accessedStorageKeys =
      (e4Cb31 O tS tA m w).dyna.accessedStorageKeys))
    (dpa : (∀ a, a ∈ ((((cpCb5 O tS tA m w).withFork g).p).accessedAddresses) ↔
      a ∈ ((((cpCb5 O tS tA m w).withFork g).adrs)))) :
    ChildOk (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
      (obsChild4Cb (post4Cb O tS tA m w post)) ∧
      ChildAgree (obsChild4Cb (post4Cb O tS tA m w post))
        ((cACb O tS tA m w).keys ++ keysRe)
        ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) := by
  obtain ⟨_, cpa, cpk, ccr, cia, cik, csg, _⟩ :=
    callPrep_spec (cpCb_eq O tS tA m w) hAgreeA.2.1 hAgreeA.2.2.2
  have hpo := post4Cb_obs O tS tA m w post
  simp only [Prod.mk.injEq] at hpo
  obtain ⟨hgas4, _, herr4b⟩ := hpo
  have herr4 : (post4Cb O tS tA m w post).error = none :=
    Option.isNone_iff_eq_none.mp herr4b
  have hobs4 : obsChild4Cb (post4Cb O tS tA m w post) =
      (post4Cb O tS tA m w post) :=
    childObs_eq hgas4 (post4Cb_out O tS tA m w post) herr4
  have hobs5 : obsChild5Cb post = post := childObs_eq hgasRe houtRe herrRe
  have hkeys4 := congrArg Devm.accessedStorageKeys hobs4
  have hacc4 := congrArg Devm.accessedAddresses hobs4
  have hst4 := congrArg Devm.state hobs4
  have hkeep := post4Cb_keep O tS tA m w post
  simp only [Prod.mk.injEq] at hkeep
  have hcrF3 : ((((cpCb O tS tA m w).withFork g).f)).isCreate = false := by
    rw [cpCb_f_isCreate_fork g O tS tA m w]
    exact ccr
  have hsgF3 : ((((cpCb O tS tA m w).withFork g).f).inner.benv.stat.rules.stateGas) =
      none :=
    CoveredFork.rules_stateGas_none
      (s := ((((cpCb O tS tA m w).withFork g).f).inner.benv.stat)) hg
  have hsetF3 : ((((cpCb O tS tA m w).withFork g).f)).settle
      (.ok (post4Cb O tS tA m w post)) =
      .ok (obsChild4Cb (post4Cb O tS tA m w post)) := by
    rw [frame_settle_ok hcrF3 hsgF3 herr4, hobs4]
  have hk : ChildOk (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
      (obsChild4Cb (post4Cb O tS tA m w post)) := by
    intro cp cevm hp he
    rw [cpCb_at g O tS tA m w hg] at hp
    obtain rfl := Option.some_inj.mp hp
    rw [e4Cb_at g O tS tA m w hg] at he
    cases he
    exact ⟨.ok (post4Cb O tS tA m w post), hexec4, hsetF3⟩
  have hdpk5 : (((cpCb5 O tS tA m w).p).accessedStorageKeys) =
      ((((cpCb5 O tS tA m w).withFork g).p).accessedStorageKeys) :=
    (cpCb5_p_keys_fork g O tS tA m w).symm
  have hdpa5 : (((cpCb5 O tS tA m w).p).accessedAddresses) =
      ((((cpCb5 O tS tA m w).withFork g).p).accessedAddresses) :=
    (cpCb5_p_acc_fork g O tS tA m w).symm
  have hAdrs5 : ((((cpCb5 O tS tA m w).withFork g).adrs)) =
      ((cpCb5 O tS tA m w).adrs) :=
    cpCb5_adrs_fork g O tS tA m w
  have haK : ∀ x, x ∈ (obsChild4Cb (post4Cb O tS tA m w post)).accessedStorageKeys ↔
      x ∈ ((cACb O tS tA m w).keys ++ keysRe) := by
    intro x
    rw [hkeys4,
      hkeep.2.1,
      ((resumeCallB_acc (resumeCb_eq O tS tA m w post)).2 x), hobs5, hdpk5, dpk,
      e4Cb31_keys O tS tA m w, e4Cb_entry_keys O tS tA m w, cik, cpk,
      hAgreeA.1 x, hchildRe.2.1 x, List.mem_append]
    simp only [herrRe, Option.isSome_none, true_and]
  have haA : ∀ a, a ∈ (obsChild4Cb (post4Cb O tS tA m w post)).accessedAddresses ↔
      a ∈ ((cpCb5 O tS tA m w).adrs ++ adrsRe) := by
    intro a
    rw [hacc4,
      hkeep.1,
      ((resumeCallB_acc (resumeCb_eq O tS tA m w post)).1 a), hobs5, hdpa5, dpa,
      hAdrs5, hchildRe.1 a, List.mem_append]
    simp only [herrRe, Option.isSome_none, true_and]
  have haS : ∀ a k, storOf (obsChild4Cb (post4Cb O tS tA m w post)).state a k =
      lookupS (storRe ++ tS) a k := by
    intro a k
    rw [hst4,
      hkeep.2.2,
      resumeCallB_state (resumeCb_eq O tS tA m w post),
      obsChild5Cb_state post]
    exact hchildRe.2.2.1 a k
  have haC : AcctAgree (obsChild4Cb (post4Cb O tS tA m w post)).state
      (acsRe ++ tA) := by
    rw [hst4,
      hkeep.2.2,
      resumeCallB_state (resumeCb_eq O tS tA m w post),
      obsChild5Cb_state post]
    exact hchildRe.2.2.2
  exact ⟨hk, haA, haK, haS, haC⟩
/-- F3's `CALL` shape: continuation tag and its forwarder facts. -/
theorem callshape_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) :
    (∃ g0, (cACb O tS tA m w).f = .next (.exec .call) g0 ∧
      cAg0 O tS tA m w = g0) ∧
    frameEntryForkFree ((((cpCb O tS tA m w).withFork g).f)) = true ∧
    ((((cpCb O tS tA m w).withFork g).adrs)) =
      ((cpCb O tS tA m w).adrs) := by
  have hd := cACb_fshape O tS tA m w
  obtain ⟨g0, hg0eq, hcAg0⟩ : ∃ g0, (cACb O tS tA m w).f =
      .next (.exec .call) g0 ∧ cAg0 O tS tA m w = g0 := by
    cases hf : (cACb O tS tA m w).f with
    | next n g0 =>
      cases n with
      | exec x =>
        cases x with
        | call =>
          have hc : cAg0 O tS tA m w = g0 := by
            unfold cAg0
            rw [hf]
          exact ⟨g0, rfl, hc⟩
        | _ => simp only [hf, isCallNode, reduceCtorEq] at hd
      | _ => simp only [hf, isCallNode, reduceCtorEq] at hd
    | _ => simp only [hf, isCallNode, reduceCtorEq] at hd
  exact ⟨⟨g0, hg0eq, hcAg0⟩, cpCb_forkfree_at g O tS tA m w, rfl⟩
/-- The `CALL` resume value exists: inexistence would contradict the kernel run. -/
theorem resumeV_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (post : Devm) (g0 : SFunc)
    (hg0eq : (cACb O tS tA m w).f = .next (.exec .call) g0)
    (hforkfree : frameEntryForkFree ((((cpCb O tS tA m w).withFork g).f)) =
      true)
    (hcrS : callResume (sCb.withOrig O) (cACb O tS tA m w)
        (obsChild4Cb (post4Cb O tS tA m w post))
        ((cACb O tS tA m w).keys ++ keysRe)
        ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) =
        callResume (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
          (obsChild4Cb (post4Cb O tS tA m w post))
          ((cACb O tS tA m w).keys ++ keysRe)
          ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA)) :
    ∃ V, resumeCallB (((cpCb O tS tA m w).withFork g).p)
      (((cpCb O tS tA m w).withFork g).oi)
      (((cpCb O tS tA m w).withFork g).os)
      (.ok (obsChild4Cb (post4Cb O tS tA m w post))) = some V := by
  have hchildErr : (obsChild4Cb (post4Cb O tS tA m w post)).error.isSome =
      false := rfl
  cases hr : resumeCallB (((cpCb O tS tA m w).withFork g).p)
      (((cpCb O tS tA m w).withFork g).oi)
      (((cpCb O tS tA m w).withFork g).os)
      (.ok (obsChild4Cb (post4Cb O tS tA m w post))) with
  | some V => exact ⟨V, rfl⟩
  | none =>
    exfalso
    have hnone : callResume (((sCb.withOrig O).withFork g))
        (cACb O tS tA m w) (obsChild4Cb (post4Cb O tS tA m w post))
        ((cACb O tS tA m w).keys ++ keysRe)
        ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS)
        (acsRe ++ tA) = none := by
      simp only [callResume, hg0eq, cpCb_at g O tS tA m w hg,
        e4Cb_at g O tS tA m w hg, hchildErr, hforkfree, hr, and_self,
        ite_true]
    have hstuck : runCb O tS tA m w
        (obsChild4Cb (post4Cb O tS tA m w post)) = .stuck := by
      unfold runCb
      rw [hcrS, hnone]
    have hcon := cb_kernel O tS tA m w (post4Cb O tS tA m w post)
    rw [hstuck] at hcon
    simp only [obsCb, reduceCtorEq] at hcon
/-- The resumed configuration is the pinned `C1`. -/
theorem resumeC1_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (post : Devm) (g0 : SFunc)
    (hg0eq : (cACb O tS tA m w).f = .next (.exec .call) g0)
    (hcAg0 : cAg0 O tS tA m w = g0)
    (hforkfree : frameEntryForkFree ((((cpCb O tS tA m w).withFork g).f)) =
      true)
    (hAdrsF : ((((cpCb O tS tA m w).withFork g).adrs)) =
      ((cpCb O tS tA m w).adrs))
    (V : Devm)
    (hresumeV : resumeCallB (((cpCb O tS tA m w).withFork g).p)
      (((cpCb O tS tA m w).withFork g).oi)
      (((cpCb O tS tA m w).withFork g).os)
      (.ok (obsChild4Cb (post4Cb O tS tA m w post))) = some V)
    (hresumeV0 : resumeCallB ((cpCb O tS tA m w).p)
      (((cpCb O tS tA m w).oi)) (((cpCb O tS tA m w).os))
      (.ok (obsChild4Cb (post4Cb O tS tA m w post))) = some V)
    (c1' : Cfg)
    (hc1' : callResume (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
      (obsChild4Cb (post4Cb O tS tA m w post))
      ((cACb O tS tA m w).keys ++ keysRe)
      ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) =
      some c1') :
    c1' = C1 O tS tA m w post := by
  have hchildErr : (obsChild4Cb (post4Cb O tS tA m w post)).error.isSome =
      false := rfl
  have hC1 : callResume (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
      (obsChild4Cb (post4Cb O tS tA m w post))
      ((cACb O tS tA m w).keys ++ keysRe)
      ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) =
      some (C1 O tS tA m w post) := by
    simp only [callResume, hg0eq, cpCb_at g O tS tA m w hg,
      e4Cb_at g O tS tA m w hg, hchildErr, hforkfree, hresumeV, hresumeV0, C1,
      Option.getD_some, hcAg0, hAdrsF, and_self, ite_true]
  exact (Option.some_inj.mp (by rw [hC1] at hc1'; exact hc1')).symm
/-- The resumed configuration exists: inexistence would contradict the kernel run. -/
theorem c1ex_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (_hg : CoveredFork g) (post : Devm)
    (hcrS : callResume (sCb.withOrig O) (cACb O tS tA m w)
        (obsChild4Cb (post4Cb O tS tA m w post))
        ((cACb O tS tA m w).keys ++ keysRe)
        ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) =
        callResume (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
          (obsChild4Cb (post4Cb O tS tA m w post))
          ((cACb O tS tA m w).keys ++ keysRe)
          ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA)) :
    ∃ c', callResume (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
      (obsChild4Cb (post4Cb O tS tA m w post))
      ((cACb O tS tA m w).keys ++ keysRe)
      ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) =
      some c' := by
  cases hr : callResume (((sCb.withOrig O).withFork g))
      (cACb O tS tA m w) (obsChild4Cb (post4Cb O tS tA m w post))
      ((cACb O tS tA m w).keys ++ keysRe)
      ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS)
      (acsRe ++ tA) with
  | some c' => exact ⟨c', rfl⟩
  | none =>
    exfalso
    have hstuck : runCb O tS tA m w
        (obsChild4Cb (post4Cb O tS tA m w post)) = .stuck := by
      unfold runCb
      rw [hcrS, hr]
    have hcon := cb_kernel O tS tA m w (post4Cb O tS tA m w post)
    rw [hstuck] at hcon
    simp only [obsCb, reduceCtorEq] at hcon
/-- The `CALL` resumes to the pinned configuration: the resume value exists and
the resumed configuration is `C1`. -/
theorem resume1_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (post : Devm) :
    ∃ c1', callResume (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
      (obsChild4Cb (post4Cb O tS tA m w post))
      ((cACb O tS tA m w).keys ++ keysRe)
      ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) =
      some c1' ∧ c1' = C1 O tS tA m w post := by
  have hF : CoveredFork (sCb.withOrig O).benvStat.fork := by
    rw [sCb_orig_fork O]
    exact CoveredFork.prague
  have hcrS : callResume (sCb.withOrig O) (cACb O tS tA m w)
      (obsChild4Cb (post4Cb O tS tA m w post))
      ((cACb O tS tA m w).keys ++ keysRe)
      ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) =
      callResume (((sCb.withOrig O).withFork g)) (cACb O tS tA m w)
        (obsChild4Cb (post4Cb O tS tA m w post))
        ((cACb O tS tA m w).keys ++ keysRe)
        ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA) :=
    (callResume_withFork hF hg (cACb O tS tA m w)
      (obsChild4Cb (post4Cb O tS tA m w post))
      ((cACb O tS tA m w).keys ++ keysRe)
      ((cpCb5 O tS tA m w).adrs ++ adrsRe) (storRe ++ tS) (acsRe ++ tA)).symm
  obtain ⟨⟨g0, hg0eq, hcAg0⟩, hforkfree, hAdrsF⟩ :=
    callshape_of g O tS tA m w
  obtain ⟨V, hresumeV⟩ :=
    resumeV_of g O tS tA m w hg post g0 hg0eq hforkfree hcrS
  have hresumeV0 : resumeCallB ((cpCb O tS tA m w).p)
      (((cpCb O tS tA m w).oi)) (((cpCb O tS tA m w).os))
      (.ok (obsChild4Cb (post4Cb O tS tA m w post))) = some V := by
    rw [← cpCb_p_at g O tS tA m w, ← cpCb_oi_at g O tS tA m w,
      ← cpCb_os_at g O tS tA m w]
    exact hresumeV
  obtain ⟨c1', hc1'⟩ := c1ex_of g O tS tA m w hg post hcrS
  have hc1C1 : c1' = C1 O tS tA m w post :=
    resumeC1_of g O tS tA m w hg post g0 hg0eq hcAg0 hforkfree hAdrsF V
      hresumeV hresumeV0 c1' hc1'
  exact ⟨c1', hc1', hc1C1⟩
/-- Error-absence from observation-absence: `isSome = false` gives `= none`. -/
theorem herrN_of (p : Devm) (herrB : p.error.isSome = false) :
    p.error = none := by
  match he : p.error with
  | none => rfl
  | some _ =>
    simp only [he, Option.isSome_some] at herrB
    exact Bool.noConfusion herrB

/-- The callback frame's closing existential from its halted 2-step run. -/
theorem closeCb_of (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (hg : CoveredFork g) (c1' : Cfg)
    {p : Devm} {cl' : Cfg}
    (s12 : StepOk fsA (((sCb.withOrig O).withFork g))
      (Boundary.cfgOfT bCb0 tS tA m w) c1')
    (hwr : wrun fsA (sCb.withOrig O) 2 c1' =
      Res.done (Outcome.halted p) cl')
    (hgas : p.gasLeft = gasCb) (hout : p.output = [])
    (herrN : p.error = none)
    (hkeys : cl'.keys = keysCb) (hadrs : cl'.adrs = adrsCb)
    (hstor : cl'.stor = storCb ++ tS) (hacs : cl'.acs = acsCb ++ tA)
    (reentry : ReentryFacts ((sCb.withOrig O).withFork g)
      (Boundary.cfgOfT bCb0 tS tA m w)) :
    ∃ c1 cl post, StepOk fsA ((sCb.withOrig O).withFork g)
      (Boundary.cfgOfT bCb0 tS tA m w) c1 ∧
      wrun fsA ((sCb.withOrig O).withFork g) 2 c1 =
        Res.done (Outcome.halted post) cl ∧
      post.gasLeft = gasCb ∧ post.output = [] ∧ post.error = none ∧
      cl.keys = keysCb ∧ cl.adrs = adrsCb ∧ cl.stor = storCb ++ tS ∧
      cl.acs = acsCb ++ tA ∧
      ReentryFacts (((sCb.withOrig O).withFork g))
        (Boundary.cfgOfT bCb0 tS tA m w) := by
  have hF : CoveredFork (sCb.withOrig O).benvStat.fork := by
    rw [sCb_orig_fork O]
    exact CoveredFork.prague
  have hS : ∀ n c, wrun fsA ((sCb.withOrig O).withFork g) n c =
      wrun fsA (sCb.withOrig O) n c :=
    fun n c => wrun_withFork hF hg (sCb_orig_hx O) fsA n c
  exact ⟨c1', cl', p, s12, by rw [hS]; exact hwr, hgas, hout, herrN, hkeys,
    hadrs, hstor, hacs, reentry⟩

/-! ## The callback frame -/

/-- The callback frame: F3 runs to its `CALL`, F4 forwards to F5, F5 is P1's
re-entrant run, F4 settles and F3 closes. -/
theorem callback_frame (hRe : ReAddFrame) : CallbackFrame := by
  intro g O tS tA m w hg hRead hAgree
  have hF : CoveredFork (sCb.withOrig O).benvStat.fork := by
    rw [sCb_orig_fork O]
    exact CoveredFork.prague
  have hS : ∀ n c, wrun fsA ((sCb.withOrig O).withFork g) n c =
      wrun fsA (sCb.withOrig O) n c :=
    fun n c => wrun_withFork hF hg (sCb_orig_hx O) fsA n c
  have run32 : wrun fsA ((sCb.withOrig O).withFork g) 32
      (Boundary.cfgOfT bCb0 tS tA m w) = .cont (cACb O tS tA m w) := by
    rw [hS]
    exact cACb_eq O tS tA m w
  have s32 := wrun_cont run32
  have hAgreeA : Agree (cACb O tS tA m w) := s32.1 hAgree
  have hAgree5 := c5Cb_agree O tS tA m w hAgreeA
  have heq5 := Boundary.cfg_of_obsDT (c5Cb_obs O tS tA m w)
  have agreeRe : Agree (Boundary.cfgOfT bRe0 tS tA (c5Cb O tS tA m w).devm.meta
      (c5Cb O tS tA m w).devm.world) := by
    rw [← heq5]
    exact hAgree5
  obtain ⟨post, hexec5, hgasRe, houtRe, herrRe, hchildRe,
    ⟨cB, hrun5, hagreeB, hfB, hs0B, hs2B⟩, hsettleRe⟩ :=
    hRe g O tS tA _ _ hg hRead agreeRe
  -- F5's entered frame is P1's initial frame.
  have he5sta : (((e5Cb O tS tA m w).withFork g).sta) =
      (((sRe.withOrig O).withFork g)) := by
    rw [e5Cb_sta_fork g O tS tA m w, e5Cb_sta_eq O tS tA m w]
  have hdyna5 : (((e5Cb O tS tA m w).withFork g).dyna) =
      (Boundary.cfgOfT bRe0 tS tA (c5Cb O tS tA m w).devm.meta
        (c5Cb O tS tA m w).devm.world).devm := by
    rw [e5Cb_dyna_c5 g O tS tA m w]
    exact congrArg Cfg.devm heq5
  have hpc0 : (((e5Cb O tS tA m w).withFork g).pc) = 0 := by
    rw [e5Cb_pc_fork g O tS tA m w, e5Cb_pc O tS tA m w]
  have hexec5' : Nonempty (Exec (((e5Cb O tS tA m w).withFork g).pc)
      (((e5Cb O tS tA m w).withFork g).sta) (((e5Cb O tS tA m w).withFork g).dyna)
      (.ok post)) := by
    rw [hpc0, he5sta, hdyna5]
    exact hexec5
  have run2625' : wrun fsI (((e5Cb O tS tA m w).withFork g).sta)
      2625 (c5Cb O tS tA m w) = .cont cB := by
    rw [he5sta, heq5]
    exact hrun5
  -- F3's `CALL` spawns the forwarder.
  have spawnA : SpawnedBy ((sCb.withOrig O).withFork g) (cACb O tS tA m w).devm
      .call ((e4Cb O tS tA m w).withFork g) :=
    spawnedBy_of_callPrep hAgreeA (cpCb_at g O tS tA m w hg)
      (e4Cb_at g O tS tA m w hg)
  have chain := chain4_of g O tS tA m w hg hAgreeA
  obtain ⟨hA4, hC4', dcr4, dsg4, dst84, dstep4, dpk4, dpa4⟩ := chain
  have spawn5 : SpawnedBy (((e4Cb31 O tS tA m w).withFork g).sta)
      (((e4Cb31 O tS tA m w).withFork g).dyna) .delegatecall
      ((e5Cb O tS tA m w).withFork g) := by
    have e4g_sta : ((((e4Cb31 O tS tA m w).withFork g).sta)) =
        (((e4Cb31 O tS tA m w).sta.withFork g)) :=
      e4Cb31_sta_fork g O tS tA m w
    have e4g_dyna : ((((e4Cb31 O tS tA m w).withFork g).dyna)) =
        ((e4Cb31 O tS tA m w).dyna) :=
      e4Cb31_dyna_fork g O tS tA m w
    rw [e4g_sta, e4g_dyna]
    exact spawnedBy_of_dcallPrep (cpCb5_e5_at g O tS tA m w hg).1 hA4 hC4'
      (cpCb5_e5_at g O tS tA m w hg).2
  have reentry := reentry_of g O tS tA m w hg run32 hAgreeA spawnA spawn5
    post hexec5' herrRe hAgree5 cB run2625' hagreeB hfB hs0B hs2B hchildRe
  have hexec4 := exec4_of g O tS tA m w hg post hexec5' hgasRe houtRe
    herrRe hsettleRe hC4' dcr4 dsg4 dst84 dstep4
  have hchild4 := child4_of g O tS tA m w hg post hAgreeA hgasRe houtRe
    herrRe hchildRe hexec4 dcr4 dsg4 dpk4 dpa4
  obtain ⟨hk, ha⟩ := hchild4
  obtain ⟨c1', hc1', hc1C1⟩ := resume1_of g O tS tA m w hg post
  have sRes : StepOk fsA (((sCb.withOrig O).withFork g)) (cACb O tS tA m w) c1' :=
    callResume_cont hc1' hk ha
  have s12 : StepOk fsA (((sCb.withOrig O).withFork g))
      (Boundary.cfgOfT bCb0 tS tA m w) c1' :=
    (wrun_cont run32).trans sRes
  -- F4's child: settled forwarder machine.
  have htup := halt2_shadows O tS tA m w post
  rw [← hc1C1] at htup
  match hwr : wrun fsA (sCb.withOrig O) 2 c1' with
  | .done (.halted p) cl =>
    rw [hwr] at htup
    dsimp only at htup
    simp only [Prod.mk.injEq] at htup
    obtain ⟨hgas, hout, herrB, hkeys, hadrs, hstor, hacs⟩ := htup
    have herrN : p.error = none := herrN_of _ herrB
    exact closeCb_of g O tS tA m w hg c1' s12 hwr hgas hout herrN
      hkeys hadrs hstor hacs reentry
  | _ =>
    rw [hwr] at htup
    split at htup <;> try simp only [Prod.mk.injEq, reduceCtorEq] at htup
    obtain ⟨hgas, hout, herrB, hkeys, hadrs, hstor, hacs⟩ := htup
    have herrN := herrN_of _ herrB
    exact closeCb_of g O tS tA m w hg c1' s12 hwr hgas hout herrN
      hkeys hadrs hstor hacs reentry
    exact htup.2.2.1.elim

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
