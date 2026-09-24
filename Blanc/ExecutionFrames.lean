import Blanc.CommonCore
import Blanc.ExecutionSettlement

/-!
# Raw execution-frame roots and trace-local admission

This module retains every actually entered code-frame root, independently of
settlement or commitment filtering.  `Exec.FrameAdmitted` attaches a positive
entry condition only to roots executing at one selected address and provides
the restriction lemmas needed by execution induction.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-- The root derivation bundled by a retained frame. -/
def Exec.Frame.rootDeriv (frame : Exec.Frame) : Exec.Deriv :=
  ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩

/-- Roots of actually entered child code frames, in execution order. Same-frame
continuations contribute only the child frames that they later enter. -/
def Exec.rawFrameDescendants {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Deriv :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.rawFrameDescendants next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.rawFrameDescendants next
  | .runErr _ _ child _ =>
      ⟨_, _, _, _, child⟩ :: Exec.rawFrameDescendants child
  | .runOk _ _ child _ next =>
      ⟨_, _, _, _, child⟩ ::
        (Exec.rawFrameDescendants child ++ Exec.rawFrameDescendants next)
termination_by sizeOf run

/-- The all-outcome code-frame traversal: the selected outer root followed by
every actually entered child root, with child descendants before roots reached
after the parent resumes. No commitment or settlement filter is applied. -/
def Exec.rawFrameRoots {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Deriv :=
  ⟨pc, sevm, pre, out, run⟩ :: Exec.rawFrameDescendants run

/-- Every committed descendant frame came from an actually entered raw child
root.  The result is deliberately a membership bridge: it does not say that
the committed projection retains same-frame prefixes or resumed continuations. -/
theorem Exec.mem_rawFrameDescendants_of_mem_descendantFrames :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out) (frame : Exec.Frame),
      frame ∈ Exec.descendantFrames run →
        (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ Exec.rawFrameDescendants run := by
  intro pc sevm pre out run
  induction run with
  | halt hstep => simp [Exec.descendantFrames, Exec.rawFrameDescendants]
  | cont hstep next ih =>
      simpa [Exec.descendantFrames, Exec.rawFrameDescendants] using ih
  | doneErr hstep henter hresume =>
      simp [Exec.descendantFrames, Exec.rawFrameDescendants]
  | doneOk hstep henter hresume next ih =>
      simpa [Exec.descendantFrames, Exec.rawFrameDescendants] using ih
  | runErr hstep henter child hresume =>
      simp [Exec.descendantFrames, Exec.rawFrameDescendants]
  | runOk hstep henter child hresume next childIh nextIh =>
      intro frame member
      simp only [Exec.descendantFrames, Exec.rawFrameDescendants] at member ⊢
      split at member
      next childSettles =>
        simp only [List.mem_append, List.mem_cons] at member ⊢
        rcases member with (rfl | childMember) | nextMember
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (childIh _ childMember))
        · exact Or.inr (Or.inr (nextIh _ nextMember))
      next childDoesNotSettle =>
        simp only [List.nil_append] at member
        simp only [List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr (nextIh _ member))

/-- A committed frame root is among the all-outcome roots of the execution
that retained it.  This preserves invocation-root membership only; callers
needing full storage chronology must also retain parent prefix and suffix
steps around spawned children. -/
theorem Exec.mem_rawFrameRoots_of_mem_committedFrames
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (frame : Exec.Frame)
    (member : frame ∈ Exec.committedFrames run) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ Exec.rawFrameRoots run := by
  unfold Exec.committedFrames at member
  split at member
  next committed =>
    simp only [List.mem_cons] at member
    rcases member with rfl | descendant
    · change (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) ∈ Exec.rawFrameRoots run
      simp [Exec.rawFrameRoots]
    · simp only [Exec.rawFrameRoots, List.mem_cons]
      exact Or.inr
        (Exec.mem_rawFrameDescendants_of_mem_descendantFrames run frame descendant)
  next notCommitted => simp at member

/-- The selected outer execution always heads its raw-frame traversal. -/
theorem Exec.mem_rawFrameRoots_self
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) ∈
      Exec.rawFrameRoots run := by
  simp [Exec.rawFrameRoots]

/-- A failed parent resume still retains the entered child and all of its raw
descendant frame roots. -/
@[simp] theorem Exec.rawFrameRoots_runErr
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw : Execution} {error : EvmError × Devm}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .error error) :
    Exec.rawFrameRoots (.runErr hstep henter child hresume) =
      ⟨pc, sevm, pre, .error error,
        Exec.runErr hstep henter child hresume⟩ ::
        Exec.rawFrameRoots child := by
  simp [Exec.rawFrameRoots, Exec.rawFrameDescendants]

/-- On a successful parent resume, the child's complete raw-frame segment
precedes every child frame entered later by the resumed parent. -/
@[simp] theorem Exec.rawFrameRoots_runOk
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok post)
    (next : Exec pc' sevm post out) :
    Exec.rawFrameRoots (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Exec.runOk hstep henter child hresume next⟩ ::
        (Exec.rawFrameRoots child ++ Exec.rawFrameDescendants next) := by
  simp [Exec.rawFrameRoots, Exec.rawFrameDescendants]

/-- A trace-local entry condition for every actually entered frame executing
at `ca`. Frames at unrelated targets impose no condition. -/
def Exec.FrameAdmitted
    (ca : Adr) (entry : Sevm → Devm → Prop)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Prop :=
  ∀ root ∈ Exec.rawFrameRoots run,
    root.sevm.currentTarget = ca → entry root.sevm root.devm

/-- A frame-root admission immediately supplies the entry condition at the
selected outer root. -/
theorem Exec.FrameAdmitted.root
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (admitted : Exec.FrameAdmitted ca entry run)
    (target : sevm.currentTarget = ca) : entry sevm pre := by
  exact admitted ⟨pc, sevm, pre, out, run⟩
    (Exec.mem_rawFrameRoots_self run) target

/-- Admission restricts along inclusion of raw frame-root traversals. -/
theorem Exec.FrameAdmitted.mono
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc pc' : Nat} {sevm sevm' : Sevm} {pre pre' : Devm}
    {out out' : Execution}
    {run : Exec pc sevm pre out} {subrun : Exec pc' sevm' pre' out'}
    (admitted : Exec.FrameAdmitted ca entry run)
    (subset : ∀ root, root ∈ Exec.rawFrameRoots subrun →
      root ∈ Exec.rawFrameRoots run) :
    Exec.FrameAdmitted ca entry subrun := by
  intro root member target
  exact admitted root (subset root member) target

/-- A same-frame continuation at a foreign target needs admission only for
the child-frame descendants it may enter later. -/
theorem Exec.FrameAdmitted.of_descendants_of_ne
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc pc' : Nat} {sevm : Sevm} {pre pre' : Devm}
    {out out' : Execution}
    {run : Exec pc sevm pre out} {next : Exec pc' sevm pre' out'}
    (admitted : Exec.FrameAdmitted ca entry run)
    (targetNe : sevm.currentTarget ≠ ca)
    (subset : ∀ root, root ∈ Exec.rawFrameDescendants next →
      root ∈ Exec.rawFrameDescendants run) :
    Exec.FrameAdmitted ca entry next := by
  intro root member target
  simp only [Exec.rawFrameRoots, List.mem_cons] at member
  rcases member with rfl | descendant
  · exact (targetNe target).elim
  · exact admitted root (by
      simp only [Exec.rawFrameRoots, List.mem_cons]
      exact Or.inr (subset root descendant)) target

theorem Exec.FrameAdmitted.cont_of_ne
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {out : Execution}
    {hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post}
    {next : Exec pc' sevm post out}
    (admitted : Exec.FrameAdmitted ca entry (.cont hstep next))
    (targetNe : sevm.currentTarget ≠ ca) :
    Exec.FrameAdmitted ca entry next :=
  admitted.of_descendants_of_ne targetNe (by
    intro root member
    simpa only [Exec.rawFrameDescendants] using member)

theorem Exec.FrameAdmitted.doneOk_of_ne
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume} {result}
    {out : Execution}
    {hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
    {henter : frame.enter = .done result}
    {hresume : resume.run result = .ok post}
    {next : Exec pc' sevm post out}
    (admitted : Exec.FrameAdmitted ca entry
      (.doneOk hstep henter hresume next))
    (targetNe : sevm.currentTarget ≠ ca) :
    Exec.FrameAdmitted ca entry next :=
  admitted.of_descendants_of_ne targetNe (by
    intro root member
    simpa only [Exec.rawFrameDescendants] using member)

theorem Exec.FrameAdmitted.runErr_child
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw : Execution} {error : EvmError × Devm}
    {hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
    {henter : frame.enter = .run childEvm}
    {child : Exec childEvm.pc childEvm.sta childEvm.dyna raw}
    {hresume : resume.run (frame.settle raw) = .error error}
    (admitted : Exec.FrameAdmitted ca entry
      (.runErr hstep henter child hresume)) :
    Exec.FrameAdmitted ca entry child :=
  admitted.mono (by
    intro root member
    rw [Exec.rawFrameRoots_runErr]
    exact List.mem_cons_of_mem _ member)

theorem Exec.FrameAdmitted.runOk_child
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw out : Execution}
    {hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
    {henter : frame.enter = .run childEvm}
    {child : Exec childEvm.pc childEvm.sta childEvm.dyna raw}
    {hresume : resume.run (frame.settle raw) = .ok post}
    {next : Exec pc' sevm post out}
    (admitted : Exec.FrameAdmitted ca entry
      (.runOk hstep henter child hresume next)) :
    Exec.FrameAdmitted ca entry child :=
  admitted.mono (by
    intro root member
    rw [Exec.rawFrameRoots_runOk]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ member))

theorem Exec.FrameAdmitted.runOk_next_of_ne
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
    {raw out : Execution}
    {hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
    {henter : frame.enter = .run childEvm}
    {child : Exec childEvm.pc childEvm.sta childEvm.dyna raw}
    {hresume : resume.run (frame.settle raw) = .ok post}
    {next : Exec pc' sevm post out}
    (admitted : Exec.FrameAdmitted ca entry
      (.runOk hstep henter child hresume next))
    (targetNe : sevm.currentTarget ≠ ca) :
    Exec.FrameAdmitted ca entry next :=
  admitted.of_descendants_of_ne targetNe (by
    intro root member
    simp only [Exec.rawFrameDescendants]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ member))

end Blanc
