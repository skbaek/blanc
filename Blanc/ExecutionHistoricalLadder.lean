import Blanc.ExecutionHistoricalAdmission
import Blanc.ContractAdmissionSem
import Blanc.HistoricalFork

/-!
# Historical frame ladder

The modern trace-admitted frame ladder (`ContractSpecSem.preserves_lift_admitted_sem`,
`ContractSpecSem.preserves_inv_admitted`) quantifies `CoveredFork` at every frame. Its fork use
is confined to four step lemmas: the executable-instruction shape (`Xinst.step_shapeCovered`, a
wrapper of the `stateGas = none` shape `Xinst.step_shapeNoStateGas`), the child fork transport
(`Xinst.Run.some_child_fork`), and the selfdestruct case of `Linst.inv_postcond`, which also
reads the modern access, presence and EIP-6780 deletion rules.

This module is the additive historical counterpart over a selected fork domain `F`:

* the step twins take only `sevm.benvStat.rules.stateGas = none`; the selfdestruct twin handles
  both access regimes (`flat`/`eip2929`), both beneficiary-credit regimes (presence-preserving
  before Paris, erasing from Paris) and both deletion regimes (every selfdestruct schedules
  before Cancun, only created accounts from Cancun), reading each from the actual fork rules;
* the child transport is `F`-agnostic: an entered child has the parent's block environment;
* `preserves_lift_admitted_semIn` and `preserves_inv_admittedIn` produce
  `PreservesAdmittedIn F` from `SoundAdmittedIn F` given `∀ f, F f → f.ruleSet.stateGas = none`;
  `HistFork` instantiates this through `HistFork.stateGas_none`.
-/

namespace Blanc

open Jaune

/-- An actually entered child frame stays in any fork domain the parent is in. -/
lemma Xinst.Run.some_child_forkIn {F : Fork → Prop} {sevm : Sevm} {pre : Devm} {x : Xinst}
    {evm' : Evm} {exn' : Execution} {out : Execution}
    (h : Xinst.Run sevm pre x (.some ⟨evm', exn'⟩) out)
    (hF : F sevm.benvStat.fork) :
    F evm'.sta.benvStat.fork := by
  rw [Xinst.Run.some_child_benvStat h]
  exact hF

namespace ContractSpecSem

variable {c : ContractSpecSem}

/-- `stateGas = none` twin of `Xinst.none_preserves_precond`. -/
lemma Xinst.none_preserves_precond_noStateGas {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {x : Xinst}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h_run : Xinst.Run sevm devm x .none (.ok inter))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa sevm inter := by
  unfold Xinst.Run at h_run
  rcases Xinst.step_shapeNoStateGas sevm devm x hsg with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, hcal, -, hs⟩ <;> rw [hs] at h_run
  · obtain ⟨-, hex⟩ := h_run
    rw [← hex] at hframe
    have hif : Devm.InstructionFrame devm inter := hframe
    exact h_pc.state_eq hif.state.symm
  · exact GenericCreate.none_preserves_precond h_run (h_pc.state_eq hf.state.symm)
  · refine GenericCall.none_preserves_precond h_run ?_ (h_pc.state_eq hf.state.symm)
    rintro hstv
    rcases hcal with ⟨-, rfl⟩ | ⟨hsf, -⟩
    · exact h_ne
    · rw [hsf] at hstv; cases hstv

/-- `stateGas = none` twin of `Xinst.some_preserves_precond`. -/
lemma Xinst.some_preserves_precond_noStateGas {wa : Adr} {sevm : Sevm} {devm inter : Devm}
    {x : Xinst} {evm' : Evm} {exn' : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h_run : Xinst.Run sevm devm x (.some ⟨evm', exn'⟩) (.ok inter))
    (ex_sub : Exec evm'.pc evm'.sta evm'.dyna exn')
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm devm) :
    c.Pre wa evm'.sta evm'.dyna ∧
      (ifOk (c.Post wa evm'.sta) exn' → c.Pre wa sevm inter) := by
  unfold Xinst.Run at h_run
  rcases Xinst.step_shapeNoStateGas sevm devm x hsg with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hfr, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hfr, -, hcal, -, hs⟩ <;> rw [hs] at h_run
  · cases h_run.1
  · exact GenericCreate.some_preserves_precond h_run ex_sub h_ne
      (h_pc.state_eq hfr.state.symm)
  · refine GenericCall.some_preserves_precond h_run ex_sub h_ne ?_ ?_
      (h_pc.state_eq hfr.state.symm)
    · rintro hstv
      rcases hcal with ⟨-, rfl⟩ | ⟨hsf, -⟩
      · exact h_ne
      · rw [hsf] at hstv; cases hstv
    · rintro hsf ht
      rcases hcal with ⟨hst, -⟩ | ⟨-, rfl⟩
      · rw [hsf] at hst; cases hst
      · exact absurd ht h_ne

/-- `stateGas = none` twin of `Linst.inv_postcond`. The selfdestruct case reads the actual
access, beneficiary-credit and deletion rules of the fork instead of their modern values. -/
lemma Linst.inv_postcond_noStateGas {wa : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (h_run : Linst.Run sevm pre l (.ok post))
    (h_ne : sevm.currentTarget ≠ wa)
    (h_pc : c.Pre wa sevm pre) :
    c.Post wa sevm post := by
  cases l
  case stop =>
    dsimp only [Linst.Run, Linst.run] at h_run
    injection h_run with h_eq; subst h_eq
    exact post_of_pre h_pc
  case return_ =>
    have h_bal : pre.getBal = post.getBal :=
      ((inferInstance : Linst.Hinv Devm.getBal Devm.getBal Linst.return_)).inv h_run
    have h_stor : Devm.getStor pre = Devm.getStor post :=
      ((inferInstance : Linst.Hinv Devm.getStor Devm.getStor Linst.return_)).inv h_run
    constructor
    · rw [← h_bal]; exact h_pc.side
    · show c.Inv (Devm.getStor post wa) 0 (post.getBal wa)
      have hb : post.getBal wa = pre.getBal wa := (congr_fun h_bal wa).symm
      have hs : Devm.getStor post wa = Devm.getStor pre wa := (congr_fun h_stor wa).symm
      rw [hb, hs]
      exact h_pc.inv.right h_ne
  case revert =>
    dsimp only [Linst.Run, Linst.run, Lean.Elab.WF.paramLet] at h_run
    rcases Except.bind_eq_ok h_run with ⟨_, _, h2⟩
    rcases Except.bind_eq_ok h2 with ⟨_, _, h4⟩
    rcases Except.bind_eq_ok h4 with ⟨_, _, h6⟩
    contradiction
  case selfdestruct =>
    have hbal : sevm.benvStat.rules.bal = none :=
      BenvStat.bal_none_of_stateGas_none hsg
    dsimp only [Linst.Run, Linst.run, ne_eq, Except.bind_ok, ite_not, Lean.Elab.WF.paramLet,
      Devm.balReadAccount_accessedAddresses, Devm.balReadAccount_getAcct] at h_run
    rw [hsg] at h_run
    simp only [Devm.balReadAccount_of_bal_none hbal] at h_run
    rcases Except.bind_eq_ok h_run with ⟨⟨dest_a, devm1⟩, h_pop, h_run1⟩
    dsimp only at h_run1
    have h_pc1 : c.Pre wa sevm devm1 := by
      apply Pre.of_eqs h_pc
      · exact Devm.popToAdr_getCode_eq h_pop wa
      · ext a; exact Devm.popToAdr_getBal_eq h_pop a
      · exact congr_fun (Devm.popToAdr_getStor_eq h_pop).symm wa
    -- The access pricing (flat before Berlin, EIP-2929 after) changes no world state.
    have h_acc : (match sevm.benvStat.rules.access with
        | AccessSchedule.eip2929 =>
          if dest_a ∉ devm1.accessedAddresses then
            (addAccessedAddress devm1 dest_a,
              gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess)
          else (devm1, gasSelfDestruct)
        | AccessSchedule.flat _ => (devm1, gasSelfDestruct)).1.state = devm1.state := by
      cases sevm.benvStat.rules.access with
      | eip2929 => dsimp only; split <;> rfl
      | flat _ => rfl
    rcases Except.bind_eq_ok h_run1 with ⟨devm2, h_charge, h_run2⟩
    have h_pc2 : c.Pre wa sevm devm2 :=
      Pre.state_eq (Pre.state_eq h_pc1 h_acc)
        ((chargeGas_worldEq_of_ok h_charge).1.symm)
    rcases Except.bind_eq_ok h_run2 with ⟨_, _, h_run3⟩
    rcases Except.bind_eq_ok h_run3 with ⟨devm3, h_sub, h_run4⟩
    have h_sub_some : devm2.subBal sevm.currentTarget
        (devm1.getAcct sevm.currentTarget).bal = some devm3 := by
      cases eq : devm2.subBal sevm.currentTarget (devm1.getAcct sevm.currentTarget).bal
      · rw [eq] at h_sub; contradiction
      · rw [eq] at h_sub; injection h_sub with h; subst h; rfl
    have h_sub_st : devm2.state.subBal sevm.currentTarget
        (devm1.getAcct sevm.currentTarget).bal = some devm3.state := by
      dsimp only [Devm.subBal, Option.bind_eq_bind, Option.bind] at h_sub_some
      cases h : devm2.state.subBal sevm.currentTarget (devm1.getAcct sevm.currentTarget).bal
      · rw [h] at h_sub_some; contradiction
      · rw [h] at h_sub_some; injection h_sub_some with h2; subst h2; rfl
    have h_pcY : c.Pre wa sevm
        (devm3.addBal dest_a (devm1.getAcct sevm.currentTarget).bal) :=
      Pre.transfer_state h_pc2 h_ne h_sub_st rfl
    -- The beneficiary credit in either presence regime agrees with `addBal` on every
    -- precondition field.
    have h_prot : State.Protected devm3.state wa := by
      apply State.Protected.of_image (sem := c.sem)
      have := h_pcY.code
      rwa [show (devm3.addBal dest_a (devm1.getAcct sevm.currentTarget).bal).getCode wa =
        devm3.getCode wa from State.addBal_getCode _ _ _ _] at this
    have h_pcX : c.Pre wa sevm (devm3.creditBeneficiary sevm.benvStat.rules dest_a
        (devm1.getAcct sevm.currentTarget).bal) := by
      refine Pre.of_eqs h_pcY ?_ (Devm.creditBeneficiary_getBal _ _ _ _) ?_
      · rw [Devm.creditBeneficiary_getCode]
        exact (State.addBal_getCode _ _ _ _).symm
      · rw [Devm.creditBeneficiary_getStor_of_protected _ _ _ _ _ h_prot]
        exact (State.setBal_get_stor_of_protected h_prot).symm
    by_cases hdel : sevm.currentTarget ∈ (devm3.creditBeneficiary sevm.benvStat.rules dest_a
        (devm1.getAcct sevm.currentTarget).bal).createdAccounts ∨
        sevm.benvStat.rules.settle.selfdestructOnlyCreated = false
    · simp only [hdel, ↓reduceIte, Except.ok.injEq] at h_run4
      rw [← h_run4]
      exact Post.of_state_eq (Post.selfdestruct_delete h_ne h_pcX)
        (creditSelfdestructRefund_state _ _ _)
    · simp only [hdel, ↓reduceIte, Except.ok.injEq] at h_run4
      rw [← h_run4]
      exact post_of_pre h_pcX

/-- **Historical frame ladder.** The `F`-domain counterpart of `preserves_lift_admitted_sem`:
every frame position carries `F` instead of `CoveredFork`, and the step obligations need only
`stateGas = none`, supplied by `hF` (for `HistFork`, `HistFork.stateGas_none`). -/
theorem preserves_lift_admitted_semIn (F : Fork → Prop)
    (hF : ∀ {f : Fork}, F f → f.ruleSet.stateGas = none)
    (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (σ : Sevm → Devm → Prop)
    (σ_pre : ∀ {e : Sevm} {d : Devm}, σ e d → c.Pre ca e d)
    (σ_of_ne : ∀ {e : Sevm} {d : Devm},
      e.currentTarget ≠ ca → c.Pre ca e d → σ e d)
    (σ_of_wf : ∀ {e : Sevm} {d : Devm},
      Mem.Wf d.memory → c.Pre ca e d → σ e d)
    (body :
      ∀ {sevm pre post},
        F sevm.benvStat.fork →
        (execution : Exec 0 sevm pre (.ok post)) →
        c.sem.Run sevm pre post →
        sevm.currentTarget = ca →
        Exec.FrameAdmitted ca entry execution →
        (∀ pc' sevm' pre' post'
            (child : Exec pc' sevm' pre' (.ok post')),
          sevm'.depth < sevm.depth →
          c.sem.At ca pc' sevm' pre' →
          F sevm'.benvStat.fork →
          Exec.FrameAdmitted ca entry child →
          σ sevm' pre' →
          c.Post ca sevm' post') →
        σ sevm pre →
        c.Post ca sevm post) :
    ∀ sevm pre post,
      F sevm.benvStat.fork →
      (execution : Exec 0 sevm pre (.ok post)) →
      Exec.FrameAdmitted ca entry execution →
      (sevm.currentTarget = ca → some sevm.code.toList = c.sem.image) →
      σ sevm pre →
      c.Post ca sevm post := by
  intro sevm devm post hfork execution admitted h_code hσ
  refine lift_inv_admitted_sem entry ca c.sem
    (fun e d => σ e d ∧ F e.benvStat.fork) (c.Post ca) ?_
    ?_ ?_ ?_ ?_ 0 sevm devm post execution ?_ admitted ⟨hσ, hfork⟩
  · intro sevm' pre' post' run hprog target admitted ih hσ'
    exact body hσ'.2 run hprog target admitted
      (fun pc'' sevm'' pre'' post'' child depth childAt hfork' childAdmitted hpre' =>
        ih pc'' sevm'' pre'' post'' child depth childAt childAdmitted ⟨hpre', hfork'⟩)
      hσ'.1
  · intro pc' sevm' pre' n' inter' h_at' h_run' h_ne' h_pc'
    obtain ⟨hσ', hfork'⟩ := h_pc'
    refine ⟨σ_of_ne h_ne' ?_, hfork'⟩
    replace hσ' := σ_pre hσ'
    cases n' with
    | push xs le =>
      have frame := Ninst.push_instructionFrame_effectRec
        (xl := .none) trivial h_run'
      exact hσ'.state_eq frame.state.symm
    | dupn imm =>
      have frame := Ninst.dupn_instructionFrame_effectRec
        (xl := .none) trivial h_run'
      exact hσ'.state_eq frame.state.symm
    | swapn imm =>
      have frame := Ninst.swapn_instructionFrame_effectRec
        (xl := .none) trivial h_run'
      exact hσ'.state_eq frame.state.symm
    | exchange imm =>
      have frame := Ninst.exchange_instructionFrame_effectRec
        (xl := .none) trivial h_run'
      exact hσ'.state_eq frame.state.symm
    | reg r =>
      have h_reg : Rinst.run ⟨pc', sevm', pre'⟩ r = .ok inter' := by
        exact ((Step.run_ofExecution (xl := (.none : Xlot))).mp h_run').2.symm
      by_cases h_ss : r = Rinst.sstore
      · subst h_ss
        have h_frame := Rinst.sstore_run_stateWriteFrame pc' pre' sevm'
        rw [h_reg] at h_frame
        refine Pre.of_eqs hσ' (h_frame.getCode_eq ca).symm ?_
          (sstore_preserves_getStor_ne h_reg h_ne')
        funext b
        exact (h_frame.getBal_eq b).symm
      · exact Pre.of_eqs hσ' (Rinst.preserves_getCode h_reg ca)
          (Rinst.preserves_bal h_reg).symm
          (congr_fun (Rinst.preserves_stor h_ss h_reg) ca).symm
    | exec x =>
      refine Xinst.none_preserves_precond_noStateGas (x := x) (hF hfork') ?_ h_ne' hσ'
      exact XStep.run_toStep.mp h_run'
  · intro pc' sevm' pre' n' evm'' exn'' inter' h_at' h_run' ex_sub' h_ne' h_pc'
    obtain ⟨hσ', hfork'⟩ := h_pc'
    cases n' with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push] at h_run'
      split at h_run' <;> cases (Step.run_ofExecution.mp h_run').1
    | dupn imm =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | swapn imm =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | exchange imm =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | reg r =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
    | exec x =>
      have hx : Xinst.Run sevm' pre' x (.some ⟨evm'', exn''⟩) (.ok inter') := by
        exact XStep.run_toStep.mp h_run'
      have hfork_c := Xinst.Run.some_child_forkIn hx hfork'
      obtain ⟨h_child, h_back⟩ :=
        Xinst.some_preserves_precond_noStateGas (x := x) (hF hfork') hx ex_sub' h_ne' (σ_pre hσ')
      exact ⟨⟨σ_of_wf (Xinst.some_child_wf hx) h_child, hfork_c⟩,
        fun h_if => ⟨σ_of_ne h_ne' (h_back h_if), hfork'⟩⟩
  · intro pc' sevm' pre' j' pc'' inter' h_at' h_run' h_ne' h_pc'
    obtain ⟨hσ', hfork'⟩ := h_pc'
    exact ⟨σ_of_ne h_ne'
      (Pre.state_eq (σ_pre hσ') (Jinst.preserves_state h_run')), hfork'⟩
  · intro pc' sevm' pre' l' post' h_at' h_run' h_ne' h_pc'
    obtain ⟨hσ', hfork'⟩ := h_pc'
    exact Linst.inv_postcond_noStateGas (hF hfork') h_run' h_ne' (σ_pre hσ')
  · exact ⟨(σ_pre hσ).1, fun target => ⟨h_code target, rfl⟩⟩



/-- **Memory-carrying historical frame theorem**: `SoundAdmittedIn F` gives `PreservesAdmittedIn F`
for any fork domain whose members disable state gas. -/
theorem preserves_inv_admittedIn (F : Fork → Prop)
    (hF : ∀ {f : Fork}, F f → f.ruleSet.stateGas = none)
    (c : ContractSpecSem) (ca : Adr) (entry : Sevm → Devm → Prop)
    (body : c.SoundAdmittedIn F ca entry) :
    c.PreservesAdmittedIn F ca entry := by
  intro sevm pre post hfork execution admitted h_code h_wf h_pre
  refine preserves_lift_admitted_semIn F hF c ca entry (c.PreWf ca)
    (fun h => h.pre)
    (fun h_ne h => ⟨h, fun target => (h_ne target).elim⟩)
    (fun h_wf' h => ⟨h, fun _ => h_wf'⟩) ?_
    sevm pre post hfork execution admitted h_code ⟨h_pre, h_wf⟩
  intro sevm' pre' post' hfork' run h_prog h_target h_admitted ih h_pre'
  exact body hfork' run h_prog h_target h_admitted
    (fun pc'' sevm'' pre'' post'' child depth childAt hfork'' childAdmitted h_childPre =>
      ih pc'' sevm'' pre'' post'' child depth childAt hfork'' childAdmitted h_childPre)
    (h_pre'.wf h_target) h_pre'.pre

/-- The historical frame theorem at the accepted historical domain `HistFork`. -/
theorem preserves_inv_admitted_histFork (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop) (body : c.SoundAdmittedIn HistFork ca entry) :
    c.PreservesAdmittedIn HistFork ca entry :=
  preserves_inv_admittedIn HistFork HistFork.stateGas_none c ca entry body

/-- The modern frame theorem is the `CoveredFork` instance of the historical one. -/
theorem preserves_inv_admitted_viaIn (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop) (body : c.SoundAdmitted ca entry) :
    c.PreservesAdmitted ca entry :=
  preserves_inv_admittedIn CoveredFork (fun h => h.histFork.stateGas_none) c ca entry body

end ContractSpecSem

namespace ContractSpec

/-- `ContractSpec` form of the historical frame theorem. -/
theorem preserves_inv_admittedIn (F : Fork → Prop)
    (hF : ∀ {f : Fork}, F f → f.ruleSet.stateGas = none)
    (c : ContractSpec) (ca : Adr) (entry : Sevm → Devm → Prop)
    (body : c.SoundAdmittedIn F ca entry) :
    c.PreservesAdmittedIn F ca entry :=
  preservesAdmittedIn_ofSem c ca entry
    (ContractSpecSem.preserves_inv_admittedIn F hF c.toSem ca entry
      (soundAdmittedIn_toSem c ca entry body))

/-- `ContractSpec` form at `HistFork`. -/
theorem preserves_inv_admitted_histFork (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop) (body : c.SoundAdmittedIn HistFork ca entry) :
    c.PreservesAdmittedIn HistFork ca entry :=
  preserves_inv_admittedIn HistFork HistFork.stateGas_none c ca entry body

end ContractSpec

end Blanc
