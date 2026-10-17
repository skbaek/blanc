import Blanc.ExecutionSettledOwnCode
import Blanc.LockExclusion

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
      (∀ g ∈ Exec.Frame.ofRun child h :: Exec.descendantFrames child,
        g ∈ Exec.descendantFrames root.exc) →
      Q (Exec.Frame.ofRun child h) ∧ ∀ g ∈ Exec.descendantFrames child, Q g) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      (∀ c ∈ Exec.childFrames run, c ∈ Exec.childFrames root.exc) →
      (∀ g ∈ Exec.descendantFrames run, g ∈ Exec.descendantFrames root.exc) →
      ∀ g ∈ Exec.descendantFrames run, Q g := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ _ _ g member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro chain children desc
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.cont step next)) (by simpa only [Exec.childFrames] using children)
          (by simpa only [Exec.descendantFrames] using desc)
  | doneErr _ _ _ =>
      intro _ _ _ g member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro chain children desc
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next))
          (by simpa only [Exec.childFrames] using children)
          (by simpa only [Exec.descendantFrames] using desc)
  | runErr _ _ _ _ =>
      intro _ _ _ g member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro chain children desc g member
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
        rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next
          settles] at member desc
        obtain ⟨atChild, belowChild⟩ := spawned _ child committed chain hstep henter here
          (fun g hg => desc g (by
            simp only [List.mem_cons, List.mem_append] at hg ⊢
            rcases hg with rfl | hg
            · exact Or.inl (Or.inl rfl)
            · exact Or.inl (Or.inr hg)))
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with (rfl | inChild) | inNext
        · exact atChild
        · exact belowChild g inChild
        · exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) nextChildren
            (fun g hg => desc g (List.mem_cons_of_mem _ (List.mem_append_right _ hg))) g inNext
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next
          settles] at member desc
        exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) nextChildren desc g
          member

/-- **The pieces of a filled spawning step.**  A step at an external instruction whose slot holds
an entered child is one driver spawn: the instruction's own spawn, the driver step, the child's
entry and the resumption from the child's settlement. -/
theorem Ninst.StepRun.spawnParts {pc : Nat} {sevm : Sevm} {pre inter : Devm} {x : Xinst}
    {cevm : Evm} {raw : Execution} (hat : Ninst.At sevm.code pc (.exec x))
    (step : Ninst.StepRun pc sevm pre (.exec x) (.some ⟨cevm, raw⟩) (.ok inter)) :
    ∃ (frame : Frame) (resume : Resume), Xinst.step sevm pre x = .spawn frame resume ∧
      frame.enter = .run cevm ∧ resume.run (frame.settle raw) = .ok inter ∧
      Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume (pc + 1) := by
  have hxrun := XStep.run_toStep.mp step
  cases spawnEq : Xinst.step sevm pre x with
  | done execution =>
      simp only [XStep.Run, spawnEq, ExceptT.stM_eq, reduceCtorEq, false_and] at hxrun
  | spawn frame resume =>
      simp only [spawnEq, XStep.Run] at hxrun
      obtain ⟨result, frameRun, resumeRun⟩ := hxrun
      obtain ⟨enter, settle⟩ := RunFrame.some_inv frameRun
      refine ⟨frame, resume, rfl, enter, by rw [← settle]; exact resumeRun.symm, ?_⟩
      rw [Evm.step_next hat]
      simp only [Ninst.step_exec, spawnEq, XStep.toStep]

/-- Admission at a run restricts to any committed descendant's own run. -/
theorem Exec.FrameAdmitted.of_mem_descendantFrames {ca : Adr} {entry : Sevm → Devm → Prop}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} {run : Exec pc sevm pre out}
    (admitted : Exec.FrameAdmitted ca entry run) {g : Exec.Frame}
    (member : g ∈ Exec.descendantFrames run) : Exec.FrameAdmitted ca entry g.run :=
  admitted.mono fun _ inner => Exec.rawFrameRoots_trans
    (List.mem_cons_of_mem _ (Exec.mem_rawFrameDescendants_of_mem_descendantFrames run g member))
    inner

/-- **A spawned child's entry**: it starts at pc `0` on a covered fork one depth lower, with the
parent's code everywhere and the parent's storage at every protected account. -/
theorem Evm.step_spawn_entry {pc pc' : Nat} {sevm : Sevm} {pre : Devm} {f : Frame} {rsm : Resume}
    {cevm : Evm} (fork : CoveredFork sevm.benvStat.fork)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc') (enter : f.enter = .run cevm) :
    cevm.pc = 0 ∧ CoveredFork cevm.sta.benvStat.fork ∧ cevm.sta.depth < sevm.depth ∧
      (∀ a, cevm.dyna.getCode a = pre.getCode a) ∧
      ∀ owner, State.Protected pre.state owner →
        cevm.dyna.state.getStor owner = pre.state.getStor owner := by
  obtain ⟨pcZero, code, -⟩ := Evm.step_spawn_child step enter
  refine ⟨pcZero, Evm.step_spawn_child_fork step enter fork, ?_, code,
    fun owner hp => Evm.step_spawn_enter_getStor fork step enter owner hp⟩
  rw [Frame.enter_run_depth enter]
  exact Step.spawn_depth_lt step

end Blanc
