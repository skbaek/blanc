import Blanc.Ladder
import Blanc.ExecutionAdmission
import Blanc.ContractAdmissionSem

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
  ∀ {sevm pre post},
    CoveredFork sevm.benvStat.fork →
    (execution : Exec 0 sevm pre (.ok post)) →
    Prog.Run sevm pre c.prog post →
    sevm.currentTarget = ca →
    Exec.FrameAdmitted ca entry execution →
    (∀ pc' sevm' pre' post'
        (child : Exec pc' sevm' pre' (.ok post')),
      sevm'.depth < sevm.depth →
      Prog.At c.prog ca pc' sevm' pre' →
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
def PreservesAdmitted (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop) : Prop :=
  ∀ sevm pre post,
    CoveredFork sevm.benvStat.fork →
    (execution : Exec 0 sevm pre (.ok post)) →
    Exec.FrameAdmitted ca entry execution →
    (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
    (sevm.currentTarget = ca → Mem.Wf pre.memory) →
    c.Pre ca sevm pre →
    c.Post ca sevm post

def soundAdmitted_toSem (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (h : c.SoundAdmitted ca entry) : c.toSem.SoundAdmitted ca entry := by
  intro sevm pre post hfork execution hrun target admitted body hwf hpre
  apply post_toSem
  apply h hfork execution (by simpa [ContractSpec.toSem, Prog.codeSem] using hrun)
    target admitted
  · intro pc' sevm' pre' post' child depth childAt hfork' childAdmitted hpre'
    exact post_ofSem (body (pc' := pc') (sevm' := sevm') (pre' := pre')
      (post' := post') (child := child) depth
      (by simpa [ContractSpec.toSem, Prog.codeSem, CodeSem.At, Prog.At] using childAt)
      hfork' childAdmitted (preWf_toSem hpre'))
  · exact hwf
  · exact pre_ofSem hpre

def preservesAdmitted_ofSem (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (h : c.toSem.PreservesAdmitted ca entry) : c.PreservesAdmitted ca entry := by
  intro sevm pre post hfork execution admitted h_code h_wf hpre
  apply post_ofSem
  apply h sevm pre post hfork execution admitted
    (fun target => by simpa [ContractSpec.toSem, Prog.codeSem] using h_code target)
    h_wf (pre_toSem hpre)

def preservesAdmitted_toSem (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (h : c.PreservesAdmitted ca entry) : c.toSem.PreservesAdmitted ca entry := by
  intro sevm pre post hfork execution admitted h_code h_wf hpre
  apply post_toSem
  apply h sevm pre post hfork execution admitted
    (fun target => by simpa [ContractSpec.toSem, Prog.codeSem] using h_code target)
    h_wf (pre_ofSem hpre)

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
      ∀ {sevm pre post},
        CoveredFork sevm.benvStat.fork →
        (execution : Exec 0 sevm pre (.ok post)) →
        Prog.Run sevm pre c.prog post →
        sevm.currentTarget = ca →
        Exec.FrameAdmitted ca entry execution →
        (∀ pc' sevm' pre' post'
            (child : Exec pc' sevm' pre' (.ok post')),
          sevm'.depth < sevm.depth →
          Prog.At c.prog ca pc' sevm' pre' →
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
      (sevm.currentTarget = ca → some sevm.code.toList = Prog.compile c.prog) →
      σ sevm pre →
      c.Post ca sevm post := by
  intro sevm pre post hfork execution admitted h_code hσ
  refine post_ofSem (ContractSpecSem.preserves_lift_admitted_sem c.toSem ca entry σ
    ?_ ?_ ?_ ?_ sevm pre post hfork execution admitted
    (fun target => by simpa [ContractSpec.toSem, Prog.codeSem] using h_code target) hσ)
  · intro e d h
    exact pre_toSem (σ_pre h)
  · intro e d h_ne h
    exact σ_of_ne h_ne (pre_ofSem h)
  · intro e d h_wf h
    exact σ_of_wf h_wf (pre_ofSem h)
  · intro sevm pre post hfork execution hrun target admitted ih hσ
    apply post_toSem
    apply body hfork execution (by simpa [ContractSpec.toSem, Prog.codeSem] using hrun)
      target admitted
    · intro pc' sevm' pre' post' child depth childAt hfork' childAdmitted hσ'
      exact post_ofSem (ih pc' sevm' pre' post' child depth
        (by simpa [ContractSpec.toSem, Prog.codeSem, CodeSem.At, Prog.At] using childAt)
        hfork' childAdmitted hσ')
    · exact hσ
/-- The memory-carrying trace-admitted frame theorem. -/
theorem preserves_inv_admitted (c : ContractSpec) (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (body : c.SoundAdmitted ca entry) :
    c.PreservesAdmitted ca entry := by
  exact preservesAdmitted_ofSem c ca entry
    (ContractSpecSem.preserves_inv_admitted c.toSem ca entry
      (soundAdmitted_toSem c ca entry body))
end ContractSpec

end Blanc
