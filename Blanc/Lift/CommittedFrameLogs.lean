import Blanc.Lift.TargetLogEvents

/-!
# Logs of retained committed frames

Every log in a retained frame's committed endpoint survives in the root's
committed endpoint. Retention uses complete frame settlement, including CREATE
code deposit; raw child success alone is insufficient.
-/

namespace Blanc

open Jaune

private theorem Exec.descendantFrame_logs_subset_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (frame : Exec.Frame) (retained : frame ∈ Exec.descendantFrames run) :
    frame.post.logs ⊆ (Execution.committedPost out committed).logs := by
  induction run generalizing frame with
  | halt step =>
      simp only [Exec.descendantFrames, List.not_mem_nil] at retained
  | cont step next ih =>
      simp only [Exec.descendantFrames] at retained
      exact ih committed hsg frame retained
  | doneErr step entered resumed =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step entered resumed next ih =>
      simp only [Exec.descendantFrames] at retained
      exact ih committed hsg frame retained
  | runErr step entered child resumed ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre callee resume pc' childEvm raw inter out
      step entered child resumed next childIH nextIH =>
      by_cases settles : Frame.settlementCommits callee raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits
          step entered child resumed next settles] at retained
        simp only [List.mem_append, List.mem_cons] at retained
        rcases retained with fromChild | later
        · have childStat := Evm.step_spawn_child_benvStat step entered
          have childHsg : childEvm.sta.benvStat.rules.stateGas = none := by
            rw [childStat]
            exact hsg
          have member : frame.post.logs ⊆ (Execution.committedPost raw
              (Frame.raw_commits_of_settlementCommits settles)).logs := by
            rcases fromChild with root | below
            · subst frame
              exact fun _ present => present
            · exact childIH (Frame.raw_commits_of_settlementCommits settles)
                childHsg frame below
          have initialLogs : childEvm.dyna.logs = [] := by
            obtain ⟨benv, transfer, childEq⟩ := Frame.enter_run_inv entered
            rw [childEq] at childHsg ⊢
            exact Lift.initDevm_logs childHsg
          obtain ⟨logs, childLogs, interLogs⟩ :=
            (Exec.runOk_logs_eq_noStateGas hsg rfl rfl
              step entered child resumed next committed).1 settles
          rw [initialLogs, List.nil_append] at childLogs
          intro entry present
          have inChild := member present
          rw [childLogs] at inChild
          rw [Exec.committed_logs_noStateGas next committed hsg rfl rfl, interLogs]
          simp only [List.mem_append]
          exact Or.inl (Or.inr inChild)
        · exact nextIH committed hsg frame later
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits
          step entered child resumed next settles] at retained
        exact nextIH committed hsg frame retained

/-- A retained frame's committed logs occur in the enclosing execution's
committed logs. Complete settlement, rather than raw child success, governs
membership in `Exec.committedFrames`. Delegation and access rules are arbitrary. -/
theorem Exec.committedFrame_logs_subset_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (frame : Exec.Frame) (retained : frame ∈ Exec.committedFrames run) :
    frame.post.logs ⊆ (Execution.committedPost out committed).logs := by
  rw [Exec.committedFrames, dite_eq_left committed] at retained
  rcases List.mem_cons.mp retained with root | below
  · subst frame
    exact fun _ present => present
  · exact Exec.descendantFrame_logs_subset_noStateGas run committed hsg frame below

end Blanc
