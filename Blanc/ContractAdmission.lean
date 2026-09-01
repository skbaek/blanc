import Blanc.Ladder
import Blanc.ExecutionAdmission

/-!
# Contract preservation with trace-local frame admission

This module extends the ordinary `ContractSpec` ladder with positive entry
conditions attached to the concrete execution's actual target-frame roots.
The admission is not a result premise and does not weaken the contract's
postcondition.
-/

namespace Blanc

open Jaune

namespace ContractSpec

/-- Contract soundness relative to a trace-local condition at every actually
entered target-frame root. The condition is about entry state only; the
execution result and poststate remain conclusions. -/
def SoundAdmitted (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ {sevm pre post} (execution : Exec 0 sevm pre (.ok post)),
    Prog.Run sevm pre c.prog post →
    sevm.currentTarget = ca →
    Exec.FrameAdmitted ca entry execution →
    (∀ pc' sevm' pre' post'
        (child : Exec pc' sevm' pre' (.ok post')),
      sevm'.depth < sevm.depth →
      Prog.At c.prog ca pc' sevm' pre' →
      Exec.FrameAdmitted ca entry child →
      c.PreWf ca sevm' pre' →
      c.Post ca sevm' post') →
    Mem.Wf pre.memory →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- Frame preservation with positive evidence about the concrete execution's
actual target-frame roots. This is the trace-admitted analogue of
`ContractSpec.Preserves`. -/
def PreservesAdmitted (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ sevm pre post (execution : Exec 0 sevm pre (.ok post)),
    Exec.FrameAdmitted ca entry execution →
    (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
    (sevm.currentTarget = ca → Mem.Wf pre.memory) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

/-- Generic frame ladder for trace-admitted contract soundness. The ordinary
precondition transport is unchanged; the concrete admission proof is threaded
only through actual target-frame roots by `lift_inv_admitted`. -/
theorem preserves_lift_admitted (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (σ : Sevm → Devm → Prop)
    (σ_pre : ∀ {e : Sevm} {d : Devm}, σ e d → c.Pre ca e d)
    (σ_of_ne : ∀ {e : Sevm} {d : Devm},
      e.currentTarget ≠ ca → c.Pre ca e d → σ e d)
    (σ_of_wf : ∀ {e : Sevm} {d : Devm},
      Mem.Wf d.memory → c.Pre ca e d → σ e d)
    (body :
      ∀ {sevm pre post} (execution : Exec 0 sevm pre (.ok post)),
        Prog.Run sevm pre c.prog post →
        sevm.currentTarget = ca →
        Exec.FrameAdmitted ca entry execution →
        (∀ pc' sevm' pre' post'
            (child : Exec pc' sevm' pre' (.ok post')),
          sevm'.depth < sevm.depth →
          Prog.At c.prog ca pc' sevm' pre' →
          Exec.FrameAdmitted ca entry child →
          σ sevm' pre' →
          c.Post ca sevm' post') →
        σ sevm pre →
        c.Post ca sevm post) :
    ∀ sevm pre post (execution : Exec 0 sevm pre (.ok post)),
      Exec.FrameAdmitted ca entry execution →
      (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
      σ sevm pre →
      c.Post ca sevm post := by
  intro sevm pre post execution admitted h_code hσ
  refine lift_inv_admitted entry ca c.prog σ (c.Post ca) body
    ?_ ?_ ?_ ?_ 0 sevm pre post execution ?_ admitted hσ
  · intro pc' sevm' pre' n' inter' h_at' h_run' h_ne' hσ'
    refine σ_of_ne h_ne' ?_
    replace hσ' := σ_pre hσ'
    cases n' with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run'
      rcases Except.bind_eq_ok h_run'.2.symm with ⟨devm1, h_charge, h_push⟩
      exact hσ'.state_eq
        (((Devm.burn_of_chargeGas h_charge).state).trans
          ((Devm.push_of_push h_push).state)).symm
    | reg r =>
      have h_reg : Rinst.run ⟨pc', sevm', pre'⟩ r = .ok inter' := by
        simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_run'
        exact h_run'.2.symm
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
      refine Xinst.none_preserves_precond (x := x) ?_ h_ne' hσ'
      simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run]
        using h_run'
  · intro pc' sevm' pre' n' evm'' out'' inter' h_at' h_run' child h_ne' hσ'
    cases n' with
    | push xs le =>
      simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_run'
      cases h_run'.1
    | reg r =>
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_run'
      cases h_run'.1
    | exec x =>
      have hx : Xinst.Run sevm' pre' x (.some ⟨evm'', out''⟩) (.ok inter') := by
        simpa only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.Run]
          using h_run'
      obtain ⟨h_child, h_back⟩ :=
        Xinst.some_preserves_precond (x := x) hx child h_ne' (σ_pre hσ')
      exact ⟨σ_of_wf (Xinst.some_child_wf hx) h_child,
        fun h_if => σ_of_ne h_ne' (h_back h_if)⟩
  · intro pc' sevm' pre' j' pc'' inter' h_at' h_run' h_ne' hσ'
    exact σ_of_ne h_ne'
      (Pre.state_eq (σ_pre hσ') (Jinst.preserves_state h_run'))
  · intro pc' sevm' pre' l' post' h_at' h_run' h_ne' hσ'
    exact Linst.inv_postcond h_run' h_ne' (σ_pre hσ')
  · exact ⟨(σ_pre hσ).1, fun target => ⟨h_code target, rfl⟩⟩

/-- The memory-carrying trace-admitted frame theorem. -/
theorem preserves_inv_admitted (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (body : c.SoundAdmitted ca entry) :
    c.PreservesAdmitted ca entry := by
  intro sevm pre post execution admitted h_code h_wf h_pre
  refine preserves_lift_admitted c ca entry (c.PreWf ca)
    (fun h => h.pre)
    (fun h_ne h => ⟨h, fun target => (h_ne target).elim⟩)
    (fun h_wf' h => ⟨h, fun _ => h_wf'⟩) ?_
    sevm pre post execution admitted h_code ⟨h_pre, h_wf⟩
  intro sevm' pre' post' run h_prog h_target h_admitted ih h_pre'
  exact body run h_prog h_target h_admitted
    (fun pc'' sevm'' pre'' post'' child depth childAt childAdmitted h_childPre =>
      ih pc'' sevm'' pre'' post'' child depth childAt childAdmitted h_childPre)
    (h_pre'.wf h_target) h_pre'.pre

end ContractSpec

end Blanc
