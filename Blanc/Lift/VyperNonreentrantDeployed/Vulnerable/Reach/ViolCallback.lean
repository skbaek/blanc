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

theorem fsCb_zero : fsA[0]? = some AttackerR.t_0000_c0 := by kernel_rfl

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

/-- F3's 32-step run never touches the account shadow. -/
theorem cACb_acs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World),
    (cACb O tS tA m w).acs = Boundary.acsOf1 bCb0 ++ tA := by
  kernel_forall_rfl

/-- The forwarder enters at pc 0. -/
theorem e4Cb_pc : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (e4Cb O tS tA m w).pc = 0 := by
  kernel_forall_rfl

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

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
