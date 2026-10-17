import Blanc.ExecutionSettledOwnCode

/-!
# Committed descendants from the spawns of a frame's own chain

`Exec.descendantFrames_of_spawns`: to show a property of every committed descendant frame of a
run, it suffices to show it, at every spawning node of the run's own chain whose child settles,
for that child and for every committed descendant of the child.  The spawning step, the child's
entry and the child's membership among the root's direct children are supplied, so the caller
can read the child's entry facts off its spawn (`Evm.step_spawn_child`,
`Evm.step_spawn_enter_getStor`, …) or off a child-classification theorem stated over
`Exec.childFrames`.

Contract-neutral.
-/

namespace Blanc

open Jaune

/-- **Descendants by spawns.**  If, at every spawning node `N` of the chain of `root` whose child
settles, the child and its committed descendants satisfy `Q`, then every committed descendant of
any suffix of that chain satisfies `Q`. -/
theorem Exec.descendantFrames_of_spawns {root : Exec.Deriv} {Q : Exec.Frame → Prop}
    (spawned : ∀ (N : Exec.Deriv) {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
      {raw : Execution} (child : Exec cevm.pc cevm.sta cevm.dyna raw) (h : raw.commits = true),
      Exec.Deriv.ParentPrefix root N → Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn f rsm pc' →
      f.enter = .run cevm → Exec.Frame.ofRun child h ∈ Exec.childFrames root.exc →
      Q (Exec.Frame.ofRun child h) ∧ ∀ g ∈ Exec.descendantFrames child, Q g) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      (∀ c ∈ Exec.childFrames run, c ∈ Exec.childFrames root.exc) →
      ∀ g ∈ Exec.descendantFrames run, Q g := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ _ g member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro chain children
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.cont step next)) (by simpa only [Exec.childFrames] using children)
  | doneErr _ _ _ =>
      intro _ _ g member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro chain children
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next))
          (by simpa only [Exec.childFrames] using children)
  | runErr _ _ _ _ =>
      intro _ _ g member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro chain children g member
      have nextChildren : ∀ c ∈ Exec.childFrames next, c ∈ Exec.childFrames root.exc :=
        fun c hc => children c (by
          simp only [Exec.childFrames, List.mem_append]
          exact Or.inr hc)
      by_cases settles : Frame.settlementCommits frame raw = true
      · have committed := Frame.raw_commits_of_settlementCommits settles
        have here : Exec.Frame.ofRun child committed ∈ Exec.childFrames root.exc :=
          children _ (by
            simp only [Exec.childFrames, dite_eq_left settles, List.mem_append,
              List.mem_singleton, true_or])
        obtain ⟨atChild, belowChild⟩ := spawned _ child committed chain hstep henter here
        rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next
          settles] at member
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with (rfl | inChild) | inNext
        · exact atChild
        · exact belowChild g inChild
        · exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) nextChildren g inNext
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next
          settles] at member
        exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) nextChildren g member

end Blanc
