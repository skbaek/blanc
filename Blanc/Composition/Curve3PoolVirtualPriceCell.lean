import Blanc.Lift.CallerProvenance
import Blanc.ExecutionAccountingPositional
import Blanc.ExecutionNoninterference
import Blanc.Lift.TargetLogEvents
import Blanc.LockExclusion

/-!
# A foreign storage cell across a frame's direct children

A frame's own instructions write only its own target's storage. So a cell of another address with code
moves only through the frame's settled children:

* `cell_upto`: it is unchanged up to the entry of a child when every earlier child keeps it, and up to the
  frame's end when every child does;
* `cell_after`: at the frame's end it is what a child left when every later child keeps it.

Nothing here names a contract.
-/

namespace Blanc.Composition.Curve3PoolVirtualPrice

open Jaune Blanc

/-- A frame keeps a cell. -/
def KeepsCell (a : Adr) (key : B256) (c : Exec.Frame) : Prop :=
  (c.post.getStor a).get key = (c.pre.getStor a).get key

/-- A run's last step, with no child frame, keeps a foreign cell. -/
private theorem halt_cell {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) {a : Adr} (key : B256) (hne : sevm.currentTarget ≠ a)
    (code : (pre.getCode a).toList ≠ []) (nil : Exec.rawFrameDescendants run = []) :
    (Devm.getStor (Execution.committedPost out committed) a).get key = (Devm.getStor pre a).get key :=
  Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas run committed hsg a key code
    (Exec.noRetainedWriteTo_of_frame_owners_ne run a key fun r hr => by
      simp only [Exec.rawFrameRoots, nil, List.mem_singleton] at hr
      subst hr
      exact hne)

/-- **A foreign cell up to a child's entry, or to the frame's end**, when the children before keep it. -/
theorem cell_upto {a : Adr} (key : B256) {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    Execution.commits out = true → sevm.benvStat.rules.stateGas = none → sevm.currentTarget ≠ a →
    (pre.getCode a).toList ≠ [] → ∀ xs ys, Exec.childFrames run = xs ++ ys →
    (∀ c ∈ xs, KeepsCell a key c) →
    (∀ c rest, ys = c :: rest → (c.pre.getStor a).get key = (Devm.getStor pre a).get key) ∧
    (∀ committed : Execution.commits out = true, ys = [] →
      (Devm.getStor (Execution.committedPost out committed) a).get key = (Devm.getStor pre a).get key) := by
  induction run with
  | halt step =>
    intro committed hsg hne code xs ys split _
    simp only [Exec.childFrames] at split
    obtain ⟨-, rfl⟩ := List.append_eq_nil_iff.mp split.symm
    refine ⟨fun _ _ h => (by cases h), fun committed _ => ?_⟩
    exact halt_cell (.halt step) committed hsg key hne code (by simp only [Exec.rawFrameDescendants])
  | cont step next ih =>
    rename_i nextPre _
    intro committed hsg hne code xs ys split keeps
    have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve (.cont step next) a code
    have e := Evm.step_cont_getStor_foreign_noStateGas hsg step hne
    simp only [Exec.childFrames] at split
    obtain ⟨h1, h2⟩ := ih committed hsg hne (by rw [codeEq]; exact code) xs ys split keeps
    rw [e] at h1 h2
    exact ⟨h1, h2⟩
  | doneErr _ _ _ =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resume next ih =>
    intro committed hsg hne code xs ys split keeps
    have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve (.doneOk step enter resume next) a code
    have e := Evm.step_doneOk_getStor_eq step enter resume a (State.Protected.of_code_ne_nil code)
    simp only [Exec.childFrames] at split
    obtain ⟨h1, h2⟩ := ih committed hsg hne (by rw [codeEq]; exact code) xs ys split keeps
    rw [e] at h1 h2
    exact ⟨h1, h2⟩
  | runErr _ _ _ _ =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | runOk step enter child resume next childIh nextIh =>
    rename_i curPre frame _ _ cevm raw nextPre _
    intro committed hsg hne code xs ys split keeps
    have protection := State.Protected.of_code_ne_nil code
    have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve (.runOk step enter child resume next) a code
    have nextNe : (Devm.getCode nextPre a).toList ≠ [] := by rw [codeEq]; exact code
    have entryEq := Evm.step_spawn_enter_getStor_protected_noStateGas hsg step enter a protection
    obtain ⟨seamOk, seamNo⟩ := Exec.spawn_seam_noStateGas hsg step enter child resume
    simp only [Exec.childFrames] at split
    by_cases settles : Frame.settlementCommits frame raw = true
    · rw [dite_eq_left settles] at split
      cases xs with
      | nil =>
        rw [List.nil_append] at split
        subst split
        refine ⟨fun c rest h => ?_, fun _ h => (by cases h)⟩
        rw [List.singleton_append, List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact congrArg (fun σ : Stor => σ.get key) entryEq
      | cons x xs' =>
        rw [List.singleton_append, List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, tail⟩ := split
        have keepHead := keeps _ List.mem_cons_self
        have e : (Devm.getStor nextPre a).get key = (Devm.getStor curPre a).get key := by
          rw [seamOk (Frame.raw_commits_of_settlementCommits settles) settles a key]
          exact keepHead.trans (congrArg (fun σ : Stor => σ.get key) entryEq)
        obtain ⟨h1, h2⟩ := nextIh committed hsg hne nextNe xs' ys tail
          (fun c hc => keeps c (List.mem_cons_of_mem _ hc))
        rw [e] at h1 h2
        exact ⟨h1, h2⟩
    · rw [dite_eq_right settles, List.nil_append] at split
      have e := seamNo settles a key
      obtain ⟨h1, h2⟩ := nextIh committed hsg hne nextNe xs ys split keeps
      rw [e] at h1 h2
      exact ⟨h1, h2⟩

/-- **A foreign cell at the frame's end is what a child left**, when every later child keeps it. -/
theorem cell_after {a : Adr} (key : B256) {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    ∀ committed : Execution.commits out = true, sevm.benvStat.rules.stateGas = none →
    sevm.currentTarget ≠ a → (pre.getCode a).toList ≠ [] →
    ∀ xs (c : Exec.Frame) ys, Exec.childFrames run = xs ++ c :: ys → (∀ c' ∈ ys, KeepsCell a key c') →
    (Devm.getStor (Execution.committedPost out committed) a).get key = (c.post.getStor a).get key := by
  induction run with
  | halt step =>
    intro _ _ _ _ xs c ys split _
    simp only [Exec.childFrames] at split
    cases xs <;> cases split
  | cont step next ih =>
    intro committed hsg hne code xs c ys split keeps
    have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve (.cont step next) a code
    simp only [Exec.childFrames] at split
    exact ih committed hsg hne (by rw [codeEq]; exact code) xs c ys split keeps
  | doneErr _ _ _ =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resume next ih =>
    intro committed hsg hne code xs c ys split keeps
    have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve (.doneOk step enter resume next) a code
    simp only [Exec.childFrames] at split
    exact ih committed hsg hne (by rw [codeEq]; exact code) xs c ys split keeps
  | runErr _ _ _ _ =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | runOk step enter child resume next childIh nextIh =>
    rename_i frame _ _ cevm raw nextPre _
    intro committed hsg hne code xs c ys split keeps
    have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve (.runOk step enter child resume next) a code
    have nextNe : (Devm.getCode nextPre a).toList ≠ [] := by rw [codeEq]; exact code
    obtain ⟨seamOk, -⟩ := Exec.spawn_seam_noStateGas hsg step enter child resume
    simp only [Exec.childFrames] at split
    by_cases settles : Frame.settlementCommits frame raw = true
    · rw [dite_eq_left settles] at split
      cases xs with
      | nil =>
        rw [List.nil_append, List.singleton_append, List.cons.injEq] at split
        obtain ⟨rfl, tail⟩ := split
        have whole := (cell_upto key next committed hsg hne nextNe ys [] (by rw [List.append_nil]; exact tail)
          keeps).2 committed rfl
        rw [whole]
        exact seamOk (Frame.raw_commits_of_settlementCommits settles) settles a key
      | cons x xs' =>
        rw [List.singleton_append, List.cons_append, List.cons.injEq] at split
        exact nextIh committed hsg hne nextNe xs' c ys split.2 keeps
    · rw [dite_eq_right settles, List.nil_append] at split
      exact nextIh committed hsg hne nextNe xs c ys split keeps

end Blanc.Composition.Curve3PoolVirtualPrice
