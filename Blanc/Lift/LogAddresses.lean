import Blanc.Lift.TargetLogEvents

/-!
# Every committed log comes from a frame of the execution

`Exec.log_addresses`: a log of a committed execution's post is either already in the entry
machine's logs or was emitted at the current target of one of the execution's raw frames
(`Exec.rawFrameRoots`).  Only an actual successful `LOG` instruction emits a log, at its frame's
own target (`Exec.logAt?`); a precompile child adds none; a settled child contributes exactly the
logs it emitted, and a child starts with no log.  Nothing here mentions a contract: a caller that
knows the targets of its raw frames knows the addresses of every log, e.g. that no log comes from
a given non-participating address.
-/

namespace Blanc

open Jaune

theorem Exec.logAt?_address {pc : Nat} {sevm : Sevm} {pre : Devm} {e : Log}
    (h : Exec.logAt? pc sevm pre = some e) : e.address = sevm.currentTarget := by
  unfold Exec.logAt? at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h
      rfl
    · cases h
  · cases h

/-- **The addresses of a committed execution's logs** (see the module note). -/
theorem Exec.log_addresses :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      (committed : Execution.commits out = true), CoveredFork sevm.benvStat.fork →
      ∀ log ∈ (Execution.committedPost out committed).logs,
        log ∈ pre.logs ∨ ∃ r ∈ Exec.rawFrameRoots run, log.address = r.sevm.currentTarget := by
  intro pc sevm pre out run
  induction run with
  | @halt pc sevm pre out step =>
    intro committed fork log hlog
    have whole := Exec.committed_logs_at (.halt step) committed fork [] 0
    simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, List.flatMap_nil,
      Exec.boundaryOwnLogs, Exec.stateBoundary, List.append_nil] at whole
    rw [whole] at hlog
    exact .inl hlog
  | @cont pc sevm pre pc' inter out step next ih =>
    intro committed fork log hlog
    have hinter := Exec.cont_logs_eq fork step next committed
    rcases ih committed fork log hlog with h | ⟨r, hr, ha⟩
    · rw [hinter, List.mem_append] at h
      rcases h with h | h
      · exact .inl h
      · right
        refine ⟨⟨pc, sevm, pre, out, .cont step next⟩, List.mem_cons_self, ?_⟩
        cases hl : Exec.logAt? pc sevm pre with
        | none => rw [hl] at h; cases h
        | some e =>
          rw [hl, Option.toList_some, List.mem_singleton] at h
          rw [h]
          exact Exec.logAt?_address hl
    · right
      rcases List.mem_cons.mp hr with rfl | hd
      · exact ⟨⟨pc, sevm, pre, out, .cont step next⟩, List.mem_cons_self, ha⟩
      · exact ⟨r, List.mem_cons_of_mem _ (by rw [Exec.rawFrameDescendants]; exact hd), ha⟩
  | doneErr step enter resume =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre f rsm pc' r inter out step enter resume next ih =>
    intro committed fork log hlog
    have hinter := Exec.doneOk_logs_eq fork step enter resume next committed
    rcases ih committed fork log hlog with h | ⟨r', hr, ha⟩
    · rw [hinter] at h
      exact .inl h
    · right
      rcases List.mem_cons.mp hr with rfl | hd
      · exact ⟨⟨pc, sevm, pre, out, .doneOk step enter resume next⟩, List.mem_cons_self, ha⟩
      · exact ⟨r', List.mem_cons_of_mem _ (by rw [Exec.rawFrameDescendants]; exact hd), ha⟩
  | runErr step enter child resume =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre f rsm pc' cevm raw inter out step enter child resume next ihc ihn =>
    intro committed fork log hlog
    have hboth := Exec.runOk_logs_eq fork step enter child resume next committed
    have hroot : ∀ r ∈ Exec.rawFrameRoots child,
        r ∈ Exec.rawFrameRoots (Exec.runOk step enter child resume next) := by
      intro r hr
      refine List.mem_cons_of_mem _ ?_
      rw [Exec.rawFrameDescendants]
      rcases List.mem_cons.mp hr with rfl | hd
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hd)
    rcases ihn committed fork log hlog with h | ⟨r', hr, ha⟩
    · by_cases settles : Frame.settlementCommits f raw = true
      · obtain ⟨L, hchild, hinter⟩ := hboth.1 settles
        rw [hinter, List.mem_append] at h
        rcases h with h | h
        · exact .inl h
        · right
          obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv step
          have hnil := Xinst.spawn_child_logs fork hx enter
          have hmem : log ∈ (Execution.committedPost raw
              (Frame.raw_commits_of_settlementCommits settles)).logs := by
            rw [hchild, hnil, List.nil_append]
            exact h
          rcases ihc (Frame.raw_commits_of_settlementCommits settles)
              (Evm.step_spawn_child_fork step enter fork) log hmem with h0 | ⟨r, hr, ha⟩
          · rw [hnil] at h0
            cases h0
          · exact ⟨r, hroot r hr, ha⟩
      · rw [hboth.2 settles] at h
        exact .inl h
    · right
      rcases List.mem_cons.mp hr with rfl | hd
      · exact ⟨⟨pc, sevm, pre, out, .runOk step enter child resume next⟩, List.mem_cons_self, ha⟩
      · refine ⟨r', List.mem_cons_of_mem _ ?_, ha⟩
        rw [Exec.rawFrameDescendants]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hd)

end Blanc
