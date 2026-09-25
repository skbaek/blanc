import Blanc.CommonProofs
import Blanc.ExecutionFrames
import Blanc.ExecutionAdmissionSem

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
  ForallSubExecAdmittedSem k ca p.codeSem entry R

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
  simpa [Prog.codeSem, CodeSem.At, Prog.At, ForallDeeperAtSem, ForallDeeperAt,
    ForallSubExecAdmittedSem, ForallSubExecAdmitted] using
    (lift_admitted_sem.atTarget (sem := p.codeSem) depth_ind run h_fa h_at target)

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
  simpa [Prog.codeSem, CodeSem.At, Prog.At, ForallDeeperAtSem, ForallDeeperAt,
    ForallSubExecAdmittedSem, ForallSubExecAdmitted] using
    (lift_admitted_sem entry R ca p.codeSem depth_ind nextNone nextSome jump last)
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
  simpa [Prog.codeSem, CodeSem.At, Prog.At, ForallDeeperAtSem, ForallDeeperAt,
    ForallSubExecAdmittedSem, ForallSubExecAdmitted] using
    (lift_inv_admitted_sem entry ca p.codeSem σ ρ with_depth_ind nextNone nextSome jump last)
end Blanc
