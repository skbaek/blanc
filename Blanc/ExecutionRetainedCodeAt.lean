import Blanc.ExecutionHistoryInCodeAt
import Blanc.ExecutionCallerExclusion
import Blanc.LockExclusion

/-!
# Code preservation through settlement-retained creations

Creation avoidance is required only for child frames whose complete settlement
commits. A discarded subtree may create at the selected address: rollback
restores its code before the parent resumes. No condition is imposed on that
subtree's internal frames. The initial code value remains arbitrary.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- A committing execution preserves code at `a` when its retained creations
avoid `a`; every retained child starts with the original code at `a`. -/
theorem Exec.codeAt_retained_noStateGas {a : Adr} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (avoid : ∀ root ∈ Exec.descendantFrames run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    (Execution.committedPost out committed).getCode a = pre.getCode a ∧
      ∀ root ∈ Exec.descendantFrames run, root.pre.getCode a = pre.getCode a := by
  induction run with
  | @halt pc sevm pre out step =>
    simp only [Exec.descendantFrames] at avoid ⊢
    have rel := Evm.step_codeAt_noStateGas (a := a) (xl := .none) hsg
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
    refine ⟨?_, fun root member => (List.not_mem_nil member).elim⟩
    cases out with
    | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
    | ok post => exact rel
  | cont step next ih =>
    simp only [Exec.descendantFrames] at avoid ⊢
    have head : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none)
      (out := .ok _) hsg
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h => by rw [step] at h; cases h))
      trivial (by rw [step]; exact ⟨rfl, rfl⟩)
    obtain ⟨last, roots⟩ := ih committed hsg avoid
    exact ⟨last.trans head, fun root member => (roots root member).trans head⟩
  | doneErr step enter resume =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resume next ih =>
    simp only [Exec.descendantFrames] at avoid ⊢
    have head : Devm.CodeAt a _ _ := Evm.step_codeAt_noStateGas (xl := .none)
      (out := .ok _) hsg
      (Xinst.avoidsAt_of_step (fun f rsm pc' cevm h hen => by
        rw [step] at h; cases h; rw [enter] at hen; cases hen))
      trivial (by rw [step]; exact ⟨_, RunFrame.of_done enter, resume.symm⟩)
    obtain ⟨last, roots⟩ := ih committed hsg avoid
    exact ⟨last.trans head, fun root member => (roots root member).trans head⟩
  | runErr step enter child resume ih =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame rsm pc' cevm raw inter out step enter child resume next
      childIH nextIH =>
    by_cases settles : frame.settlementCommits raw = true
    · have childCommit := Frame.raw_commits_of_settlementCommits settles
      have frames := Exec.descendantFrames_runOk_of_settlementCommits
        step enter child resume next settles
      rw [frames] at avoid ⊢
      have childAvoid := avoid (Exec.Frame.ofRun child childCommit)
        (List.mem_append_left _ (List.mem_cons_self ..))
      have childGas : cevm.sta.benvStat.rules.stateGas = none := by
        rw [Evm.step_spawn_child_benvStat step enter]
        exact hsg
      obtain ⟨childLast, childRoots⟩ := childIH childCommit childGas
        (fun root member => avoid root
          (List.mem_append_left _ (List.mem_cons_of_mem _ member)))
      have childRel : Execution.Rel (Devm.CodeAt a) cevm.dyna raw := by
        cases raw with
        | error error => simp only [Execution.commits, Bool.false_eq_true] at childCommit
        | ok post => exact childLast
      obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
      have codeAddress : cevm.sta.codeAddress = frame.inner.codeAddress := by
        obtain ⟨benv, _, eq⟩ := Frame.enter_run_inv enter
        rw [eq]
        rfl
      have head : Devm.CodeAt a pre inter :=
        Evm.step_codeAt_noStateGas (xl := .some ⟨cevm, raw⟩) (out := .ok inter) hsg
          (Xinst.avoidsAt_of_step (fun f rsm' pc'' cevm' h hen create => by
            rw [step] at h; cases h; rw [enter] at hen; cases hen
            rw [← Frame.enter_run_currentTarget enter]
            exact childAvoid (codeAddress.trans
              (Xinst.step_spawn_create_codeAddress_noStateGas hsg spawn create))))
          childRel (by rw [step]; exact ⟨_, RunFrame.of_run enter, resume.symm⟩)
      obtain ⟨last, roots⟩ := nextIH committed hsg
        (fun root member => avoid root (List.mem_append_right _ member))
      refine ⟨last.trans head, ?_⟩
      intro root member
      rcases List.mem_append.mp member with before | after
      · rcases List.mem_cons.mp before with rfl | deeper
        · exact (Evm.step_spawn_child step enter).2.1 a
        · exact (childRoots root deeper).trans ((Evm.step_spawn_child step enter).2.1 a)
      · exact (roots root after).trans head
    · have frames := Exec.descendantFrames_runOk_of_not_settlementCommits
        step enter child resume next settles
      rw [frames] at avoid ⊢
      have head := congrFun
        (Blanc.Evm.step_spawn_rollback_code_stor_noStateGas hsg step enter resume settles).1 a
      obtain ⟨last, roots⟩ := nextIH committed hsg avoid
      exact ⟨last.trans head, fun root member => (roots root member).trans head⟩

/-- The caller fold needs empty code and creation avoidance only at retained
children. Discarded child executions contribute no caller obligation. -/
theorem Exec.descendantFrames_caller_excluded_noStateGas {a : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (caller : sevm.caller ≠ a)
    (targetCode : sevm.currentTarget = a → sevm.code = ByteArray.empty)
    (empty : ∀ root ∈ Exec.descendantFrames run, root.pre.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ Exec.descendantFrames run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ Exec.descendantFrames run,
      root.sevm.caller ≠ a ∧
        (root.sevm.currentTarget = a → root.sevm.code = ByteArray.empty) := by
  induction run with
  | halt step =>
    intro root member
    simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
    simp only [Exec.descendantFrames] at empty avoid ⊢
    exact ih hsg caller targetCode empty avoid
  | doneErr step enter resume =>
    intro root member
    simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
    simp only [Exec.descendantFrames] at empty avoid ⊢
    exact ih hsg caller targetCode empty avoid
  | runErr step enter child resume ih =>
    intro root member
    simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | @runOk pc sevm pre frame resume nextPc child raw post out step enter childRun resumeRun
      next childIH nextIH =>
    by_cases settles : frame.settlementCommits raw = true
    · have frames := Exec.descendantFrames_runOk_of_settlementCommits
        step enter childRun resumeRun next settles
      rw [frames] at empty avoid ⊢
      have childMember := List.mem_append_left (Exec.descendantFrames next)
        (List.mem_cons_self (a := Exec.Frame.ofRun childRun
          (Frame.raw_commits_of_settlementCommits settles)) (l := Exec.descendantFrames childRun))
      obtain ⟨childCaller, childCode⟩ := Blanc.Evm.step_spawn_caller_excluded_noStateGas
        step hsg enter caller targetCode (empty _ childMember) (avoid _ childMember)
      have childRoots := childIH (by rw [Evm.step_spawn_child_benvStat step enter]; exact hsg)
        childCaller childCode
        (fun root member => empty root (List.mem_append_left _ (List.mem_cons_of_mem _ member)))
        (fun root member => avoid root (List.mem_append_left _ (List.mem_cons_of_mem _ member)))
      have laterRoots := nextIH hsg caller targetCode
        (fun root member => empty root (List.mem_append_right _ member))
        (fun root member => avoid root (List.mem_append_right _ member))
      intro root member
      rcases List.mem_append.mp member with before | after
      · rcases List.mem_cons.mp before with rfl | deeper
        · exact ⟨childCaller, childCode⟩
        · exact childRoots root deeper
      · exact laterRoots root after
    · have frames := Exec.descendantFrames_runOk_of_not_settlementCommits
        step enter childRun resumeRun next settles
      rw [frames] at empty avoid ⊢
      exact nextIH hsg caller targetCode empty avoid

/-- Empty initial code and retained creation avoidance give both endpoint
emptiness and caller exclusion throughout the committing frame's retained
forest. There is no premise about creations in discarded subtrees. -/
theorem Exec.codeAt_and_callers_retained_noStateGas {a : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (caller : sevm.caller ≠ a)
    (targetCode : sevm.currentTarget = a → sevm.code = ByteArray.empty)
    (initial : pre.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ Exec.descendantFrames run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    (Execution.committedPost out committed).getCode a = ByteArray.empty ∧
      ∀ root ∈ Exec.committedFrames run, root.sevm.caller ≠ a := by
  obtain ⟨last, code⟩ := Exec.codeAt_retained_noStateGas run committed hsg avoid
  have callers := Exec.descendantFrames_caller_excluded_noStateGas run hsg caller targetCode
    (fun root member => (code root member).trans initial) avoid
  refine ⟨last.trans initial, ?_⟩
  intro root member
  rw [Exec.committedFrames, dite_eq_left committed] at member
  rcases List.mem_cons.mp member with rfl | deeper
  · exact caller
  · exact (callers root deeper).1

end Blanc.ExecutionTrace
