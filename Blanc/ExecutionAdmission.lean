import Blanc.CommonProofs
import Blanc.ExecutionFrames

/-!
# Execution induction with trace-local frame admission

These eliminators preserve a concrete execution derivation in the induction
motive, allowing positive entry evidence to be restricted to each actual
child frame without changing the ordinary execution semantics.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

/-- Depth induction over successful target frames whose concrete execution
derivations satisfy a trace-local entry condition. -/
def ForallSubExecAdmitted (k : Nat) (ca : Adr) (p : Prog)
    (entry : Sevm → Devm → Prop)
    (R : Sevm → Devm → Devm → Prop) : Prop :=
  ∀ pc sevm devm post (run : Exec pc sevm devm (.ok post)),
    sevm.depth < k →
    p.At ca pc sevm devm →
    Exec.FrameAdmitted ca entry run →
    R sevm devm post

/-- The target-frame case of `lift_admitted`: the concrete derivation supplies
the selected root's entry condition, while lower-depth executions retain their
own trace-local admission premises. -/
private lemma lift_admitted.atTarget
    {entry : Sevm → Devm → Prop}
    {R : Sevm → Devm → Devm → Prop}
    {ca : Adr} {p : Prog}
    (depth_ind :
      ∀ {sevm pre post} (run : Exec 0 sevm pre (.ok post)),
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        Exec.FrameAdmitted ca entry run →
        ForallSubExecAdmitted sevm.depth ca p entry R →
        R sevm pre post)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h_fa : ForallDeeperAt sevm.depth ca p
      (fun _ sevm' pre' out' run' =>
        Exec.FrameAdmitted ca entry run' → ifOk (R sevm' pre') out'))
    (h_at : p.At ca pc sevm pre)
    (target : sevm.currentTarget = ca) :
    Exec.FrameAdmitted ca entry run → ifOk (R sevm pre) out := by
  cases out with
  | error error => intro; exact trivial
  | ok post =>
      intro admitted
      have h_pc : pc = 0 := (h_at.right target).right
      subst h_pc
      refine depth_ind run
        (correct sevm pre p post run (h_at.right target).left)
        target admitted ?_
      intro pc' sevm' pre' post' child depth childAt childAdmitted
      exact h_fa pc' sevm' pre' (.ok post') child depth childAt childAdmitted

/-- Trace-admitted counterpart of `lift`. It preserves the existing driver
decomposition, but keeps the concrete execution proof in the induction motive
so an entry premise can be restricted to actual child-frame roots. -/
lemma lift_admitted
    (entry : Sevm → Devm → Prop)
    (R : Sevm → Devm → Devm → Prop)
    (ca : Adr) (p : Prog)
    (depth_ind :
      ∀ {sevm pre post} (run : Exec 0 sevm pre (.ok post)),
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        Exec.FrameAdmitted ca entry run →
        ForallSubExecAdmitted sevm.depth ca p entry R →
        R sevm pre post)
    (nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post)
    (nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'}
        {out' : Execution} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n
          (.some ⟨evm', out'⟩) (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna out' →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        ifOk (R evm'.sta evm'.dyna) out' →
        R sevm inter post →
        R sevm pre post)
    (jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter} {post},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        Exec pc' sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post)
    (last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm pre post) :
    ∀ pc sevm pre post (run : Exec pc sevm pre (.ok post)),
      Prog.At p ca pc sevm pre →
      Exec.FrameAdmitted ca entry run →
      R sevm pre post := by
  have all : Exec.Fa
      (Exec.Wkn ca p (fun _ sevm pre out run =>
        Exec.FrameAdmitted ca entry run → ifOk (R sevm pre) out)) := by
    apply Exec.strong_rec
    apply @Exec.rec (Fortify
      (Exec.Wkn ca p (fun _ sevm pre out run =>
        Exec.FrameAdmitted ca entry run → ifOk (R sevm pre) out)))
    -- halt
    · intro pc sevm pre out hstep h_fa h_at admitted
      rcases em (sevm.currentTarget = ca) with target | targetNe
      · exact lift_admitted.atTarget depth_ind (.halt hstep) h_fa h_at target admitted
      · cases out with
        | error error => exact trivial
        | ok post =>
            rcases hgi : Evm.getInst ⟨pc, sevm, pre⟩ with _ | instruction
            · rw [Evm.step_invOp hgi] at hstep
              cases hstep
            · cases instruction with
              | next n =>
                  have hns : Ninst.step ⟨pc, sevm, pre⟩ n = .halt (.ok post) := by
                    rw [← Evm.step_next (n := n) hgi]
                    exact hstep
                  exact absurd hns Ninst.step_ne_halt_ok
              | jump j =>
                  rw [Evm.step_jump (j := j) hgi] at hstep
                  rcases hj : j.run ⟨pc, sevm, pre⟩ with error | ⟨pc', inter⟩ <;>
                    rw [hj] at hstep <;> simp only [Step.ofJump] at hstep
                  · cases hstep
                  · cases hstep
              | last l =>
                  rw [Evm.step_last (l := l) hgi] at hstep
                  injection hstep with hrun
                  exact last hgi hrun targetNe
    -- cont
    · intro pc sevm pre pc' inter out hstep next ih h_fa h_at admitted
      rcases em (sevm.currentTarget = ca) with target | targetNe
      · exact lift_admitted.atTarget depth_ind (.cont hstep next)
          h_fa h_at target admitted
      · have h_ne_code : (pre.getCode ca).toList ≠ [] := fun empty =>
          Prog.compile_ne_nil (Eq.trans h_at.left.symm (congrArg some empty))
        have hcode : inter.getCode ca = pre.getCode ca :=
          lift_core.stepCode (xl := .none) trivial
            (by rw [hstep]; exact ⟨rfl, rfl⟩) ca h_ne_code
        have h_at' : p.At ca pc' sevm inter :=
          ⟨by rw [hcode]; exact h_at.left, fun equal => (targetNe equal).elim⟩
        cases out with
        | error error => exact trivial
        | ok post =>
            rcases hgi : Evm.getInst ⟨pc, sevm, pre⟩ with _ | instruction
            · rw [Evm.step_invOp hgi] at hstep
              cases hstep
            · cases instruction with
              | next n =>
                  have hns : Ninst.step ⟨pc, sevm, pre⟩ n = .cont pc' inter := by
                    rw [← Evm.step_next (n := n) hgi]
                    exact hstep
                  have hpc : pc' = pc + n.size := Ninst.step_cont_pc hns
                  subst hpc
                  have hrun : Ninst.StepRun pc sevm pre n .none (.ok inter) := by
                    unfold Ninst.StepRun
                    rw [hns]
                    exact ⟨rfl, rfl⟩
                  exact nextNone hgi hrun next targetNe
                    (ih h_fa h_at' (admitted.cont_of_ne targetNe))
              | jump j =>
                  rw [Evm.step_jump (j := j) hgi] at hstep
                  exact jump hgi (Step.ofJump_cont hstep) next targetNe
                    (ih h_fa h_at' (admitted.cont_of_ne targetNe))
              | last l =>
                  rw [Evm.step_last (l := l) hgi] at hstep
                  cases hstep
    -- doneErr
    · intro pc sevm pre frame resume pc' result error hstep henter hresume
        h_fa h_at admitted
      rcases em (sevm.currentTarget = ca) with target | targetNe
      · exact lift_admitted.atTarget depth_ind
          (.doneErr hstep henter hresume) h_fa h_at target admitted
      · exact trivial
    -- doneOk
    · intro pc sevm pre frame resume pc' result inter out hstep henter hresume
        next ih h_fa h_at admitted
      rcases em (sevm.currentTarget = ca) with target | targetNe
      · exact lift_admitted.atTarget depth_ind
          (.doneOk hstep henter hresume next) h_fa h_at target admitted
      · cases out with
        | error error => exact trivial
        | ok post =>
            obtain ⟨x, hxat, -, hpc'⟩ := Evm.step_spawn_inv hstep
            subst hpc'
            have h_ne_code : (pre.getCode ca).toList ≠ [] := fun empty =>
              Prog.compile_ne_nil (Eq.trans h_at.left.symm (congrArg some empty))
            have hrun : Ninst.StepRun pc sevm pre (.exec x) .none (.ok inter) := by
              unfold Ninst.StepRun
              rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
              exact ⟨result, RunFrame.of_done henter, hresume.symm⟩
            have hcode : inter.getCode ca = pre.getCode ca :=
              lift_core.stepCode (xl := .none) trivial
                (by rw [hstep]; exact ⟨result, RunFrame.of_done henter, hresume.symm⟩)
                ca h_ne_code
            have h_at' : p.At ca (pc + 1) sevm inter :=
              ⟨by rw [hcode]; exact h_at.left,
                fun equal => (targetNe equal).elim⟩
            exact nextNone hxat hrun next targetNe
              (ih h_fa h_at' (admitted.doneOk_of_ne targetNe))
    -- runErr
    · intro pc sevm pre frame resume pc' childEvm raw error hstep henter child
        hresume ihc h_fa h_at admitted
      rcases em (sevm.currentTarget = ca) with target | targetNe
      · exact lift_admitted.atTarget depth_ind
          (.runErr hstep henter child hresume) h_fa h_at target admitted
      · exact trivial
    -- runOk
    · intro pc sevm pre frame resume pc' childEvm raw inter out hstep henter child
        hresume next ihc ih h_fa h_at admitted
      rcases em (sevm.currentTarget = ca) with target | targetNe
      · exact lift_admitted.atTarget depth_ind
          (.runOk hstep henter child hresume next) h_fa h_at target admitted
      · cases out with
        | error error => exact trivial
        | ok post =>
            obtain ⟨x, hxat, -, hpc'⟩ := Evm.step_spawn_inv hstep
            subst hpc'
            obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
            have hdepth : childEvm.sta.depth < sevm.depth := by
              rw [Frame.enter_run_depth henter]
              exact Step.spawn_depth_lt hstep
            have h_ne_code : (pre.getCode ca).toList ≠ [] := fun empty =>
              Prog.compile_ne_nil (Eq.trans h_at.left.symm (congrArg some empty))
            have h_at_child : p.At ca childEvm.pc childEvm.sta childEvm.dyna := by
              refine ⟨by rw [hgc ca]; exact h_at.left, fun childTarget => ⟨?_, hpc0⟩⟩
              have targetsNe : sevm.currentTarget ≠ childEvm.sta.currentTarget := by
                rw [childTarget]
                exact targetNe
              have hcode := hsrc targetsNe
                (by rw [childTarget]; exact not_empty_of_compile h_at.left)
                (by rw [childTarget]; exact not_delegation_of_compile h_at.left)
              rw [hcode, childTarget]
              exact h_at.left
            have hchild : Xlot.Rel Devm.CodePreserve (.some ⟨childEvm, raw⟩) :=
              Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
                Ninst.codePreserve_effectRec Jinst.codePreserve_effect
                Linst.codePreserve_effect child
            have hrun : Ninst.StepRun pc sevm pre (.exec x)
                (.some ⟨childEvm, raw⟩) (.ok inter) := by
              unfold Ninst.StepRun
              rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
              exact ⟨frame.settle raw, RunFrame.of_run henter, hresume.symm⟩
            have hcode : inter.getCode ca = pre.getCode ca :=
              lift_core.stepCode (xl := .some ⟨childEvm, raw⟩) hchild
                (by rw [hstep]
                    exact ⟨frame.settle raw, RunFrame.of_run henter, hresume.symm⟩)
                ca h_ne_code
            have h_at' : p.At ca (pc + 1) sevm inter :=
              ⟨by rw [hcode]; exact h_at.left,
                fun equal => (targetNe equal).elim⟩
            exact nextSome hxat hrun child next targetNe
              (h_fa childEvm.pc childEvm.sta childEvm.dyna raw child
                hdepth h_at_child admitted.runOk_child)
              (ih h_fa h_at' (admitted.runOk_next_of_ne targetNe))
  intro pc sevm pre post run h_at admitted
  exact all pc sevm pre (.ok post) run h_at admitted

/-- Trace-admitted counterpart of `lift_inv`. The invariant transport outside
the target is unchanged; only target-frame entry and recursive target frames
carry the concrete admission evidence. -/
lemma lift_inv_admitted
    (entry : Sevm → Devm → Prop)
    (ca : Adr) (p : Prog)
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    (with_depth_ind :
      ∀ {sevm pre post} (run : Exec 0 sevm pre (.ok post)),
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        Exec.FrameAdmitted ca entry run →
        (∀ pc' sevm' pre' post'
            (child : Exec pc' sevm' pre' (.ok post')),
          sevm'.depth < sevm.depth →
          Prog.At p ca pc' sevm' pre' →
          Exec.FrameAdmitted ca entry child →
          σ sevm' pre' →
          ρ sevm' post') →
        σ sevm pre →
        ρ sevm post)
    (nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter)
    (nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'} {out'} {inter},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n (.some ⟨evm', out'⟩) (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna out' →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ evm'.sta evm'.dyna ∧
          (ifOk (ρ evm'.sta) out' → σ sevm inter))
    (jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter)
    (last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        ρ sevm post) :
    ∀ pc sevm pre post (run : Exec pc sevm pre (.ok post)),
      Prog.At p ca pc sevm pre →
      Exec.FrameAdmitted ca entry run →
      σ sevm pre →
      ρ sevm post := by
  apply @lift_admitted entry (fun sevm pre post => σ sevm pre → ρ sevm post)
    ca p
  · intro sevm pre post run hprog target admitted ih hσ
    exact with_depth_ind run hprog target admitted
      (fun pc' sevm' pre' post' child depth childAt childAdmitted hσ' =>
        ih pc' sevm' pre' post' child depth childAt childAdmitted hσ') hσ
  · intro pc sevm pre n inter post h_at h_run _ targetNe ih hσ
    exact ih (nextNone h_at h_run targetNe hσ)
  · intro pc sevm pre n evm' out' inter post h_at h_run child _ targetNe
      childResult ih hσ
    rcases nextSome h_at h_run child targetNe hσ with ⟨hσChild, resume⟩
    apply ih
    apply resume
    cases out' with
    | error error => exact trivial
    | ok childPost => exact childResult hσChild
  · intro pc sevm pre j pc' inter post h_at h_run _ targetNe ih hσ
    exact ih (jump h_at h_run targetNe hσ)
  · intro pc sevm pre l post h_at h_run targetNe hσ
    exact last h_at h_run targetNe hσ

end Blanc

