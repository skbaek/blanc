import Blanc.LadderSem
import Blanc.ExecutionAdmissionSem

/-!
# Contract preservation with trace-local frame admission

This module extends the ordinary `ContractSpec` ladder with positive entry
conditions attached to the concrete execution's actual target-frame roots.
The admission is not a result premise and does not weaken the contract's
postcondition.
-/

namespace Blanc

open Jaune

namespace ContractSpecSem

/-- Contract soundness relative to a trace-local condition at every actually
entered target-frame root. The condition is about entry state only; the
execution result and poststate remain conclusions. -/
def SoundAdmitted (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ {sevm pre post},
    CoveredFork sevm.benvStat.fork →
    (execution : Exec 0 sevm pre (.ok post)) →
    c.sem.Run sevm pre post →
    sevm.currentTarget = ca →
    Exec.FrameAdmitted ca entry execution →
    (∀ pc' sevm' pre' post'
        (child : Exec pc' sevm' pre' (.ok post')),
      sevm'.depth < sevm.depth →
      c.sem.At ca pc' sevm' pre' →
      CoveredFork sevm'.benvStat.fork →
      Exec.FrameAdmitted ca entry child →
      c.PreWf ca sevm' pre' →
      c.Post ca sevm' post') →
    Mem.Wf pre.memory →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- Frame preservation with positive evidence about the concrete execution's
actual target-frame roots. This is the trace-admitted analogue of
`ContractSpec.Preserves`. -/
def PreservesAdmitted (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ sevm pre post,
    CoveredFork sevm.benvStat.fork →
    (execution : Exec 0 sevm pre (.ok post)) →
    Exec.FrameAdmitted ca entry execution →
    (sevm.currentTarget = ca → some sevm.code.toList = c.sem.image) →
    (sevm.currentTarget = ca → Mem.Wf pre.memory) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- Generic frame ladder for trace-admitted contract soundness. The ordinary
precondition transport is unchanged; the concrete admission proof is threaded
only through actual target-frame roots by `lift_inv_admitted_sem`. -/
theorem preserves_lift_admitted_sem (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (σ : Sevm → Devm → Prop)
    (σ_pre : ∀ {e : Sevm} {d : Devm}, σ e d → c.Pre ca e d)
    (σ_of_ne : ∀ {e : Sevm} {d : Devm},
      e.currentTarget ≠ ca → c.Pre ca e d → σ e d)
    (σ_of_wf : ∀ {e : Sevm} {d : Devm},
      Mem.Wf d.memory → c.Pre ca e d → σ e d)
    (body :
      ∀ {sevm pre post},
        CoveredFork sevm.benvStat.fork →
        (execution : Exec 0 sevm pre (.ok post)) →
        c.sem.Run sevm pre post →
        sevm.currentTarget = ca →
        Exec.FrameAdmitted ca entry execution →
        (∀ pc' sevm' pre' post'
            (child : Exec pc' sevm' pre' (.ok post')),
          sevm'.depth < sevm.depth →
          c.sem.At ca pc' sevm' pre' →
          CoveredFork sevm'.benvStat.fork →
          Exec.FrameAdmitted ca entry child →
          σ sevm' pre' →
          c.Post ca sevm' post') →
        σ sevm pre →
        c.Post ca sevm post) :
    ∀ sevm pre post,
      CoveredFork sevm.benvStat.fork →
      (execution : Exec 0 sevm pre (.ok post)) →
      Exec.FrameAdmitted ca entry execution →
      (sevm.currentTarget = ca → some sevm.code.toList = c.sem.image) →
      σ sevm pre →
      c.Post ca sevm post := by
  intro sevm devm post hfork execution admitted h_code hσ
  refine lift_inv_admitted_sem entry ca c.sem
    (fun e d => σ e d ∧ CoveredFork e.benvStat.fork) (c.Post ca) ?_
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
      have hrun := (Step.run_ofExecution (xl := (.none : Xlot))).mp h_run'
      rcases Except.bind_eq_ok hrun.2.symm with ⟨devm1, h_charge, h_push⟩
      exact hσ'.state_eq
        (((Devm.burn_of_chargeGas h_charge).state).trans
          ((Devm.push_of_push h_push).state)).symm
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
      refine Xinst.none_preserves_precond (x := x) hfork' ?_ h_ne' hσ'
      exact XStep.run_toStep.mp h_run'
  · intro pc' sevm' pre' n' evm'' exn'' inter' h_at' h_run' ex_sub' h_ne' h_pc'
    obtain ⟨hσ', hfork'⟩ := h_pc'
    cases n' with
    | push xs le =>
      have hrun := (Step.run_ofExecution
        (xl := (.some ⟨evm'', exn''⟩ : Xlot))).mp h_run'
      cases hrun.1
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
      have hfork_c := Xinst.Run.some_child_fork hx hfork'
      obtain ⟨h_child, h_back⟩ :=
        Xinst.some_preserves_precond (x := x) hfork' hx ex_sub' h_ne' (σ_pre hσ')
      exact ⟨⟨σ_of_wf (Xinst.some_child_wf hx) h_child, hfork_c⟩,
        fun h_if => ⟨σ_of_ne h_ne' (h_back h_if), hfork'⟩⟩
  · intro pc' sevm' pre' j' pc'' inter' h_at' h_run' h_ne' h_pc'
    obtain ⟨hσ', hfork'⟩ := h_pc'
    exact ⟨σ_of_ne h_ne'
      (Pre.state_eq (σ_pre hσ') (Jinst.preserves_state h_run')), hfork'⟩
  · intro pc' sevm' pre' l' post' h_at' h_run' h_ne' h_pc'
    obtain ⟨hσ', hfork'⟩ := h_pc'
    exact Linst.inv_postcond hfork' h_run' h_ne' (σ_pre hσ')
  · exact ⟨(σ_pre hσ).1, fun target => ⟨h_code target, rfl⟩⟩

/-- The memory-carrying trace-admitted frame theorem. -/
theorem preserves_inv_admitted (c : ContractSpecSem) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (body : c.SoundAdmitted ca entry) :
    c.PreservesAdmitted ca entry := by
  intro sevm pre post hfork execution admitted h_code h_wf h_pre
  refine preserves_lift_admitted_sem c ca entry (c.PreWf ca)
    (fun h => h.pre)
    (fun h_ne h => ⟨h, fun target => (h_ne target).elim⟩)
    (fun h_wf' h => ⟨h, fun _ => h_wf'⟩) ?_
    sevm pre post hfork execution admitted h_code ⟨h_pre, h_wf⟩
  intro sevm' pre' post' hfork' run h_prog h_target h_admitted ih h_pre'
  exact body hfork' run h_prog h_target h_admitted
    (fun pc'' sevm'' pre'' post'' child depth childAt hfork'' childAdmitted h_childPre =>
      ih pc'' sevm'' pre'' post'' child depth childAt hfork'' childAdmitted h_childPre)
    (h_pre'.wf h_target) h_pre'.pre

end ContractSpecSem

end Blanc

