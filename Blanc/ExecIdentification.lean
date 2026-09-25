import Blanc.ExecutionTraceSettledFrames

/-! # Execution identification

Contract-neutral facts identifying an execution's descendant frames across one
step, proved by `Exec.unique`-style identification. Moved here from the DRIP
modules. -/

namespace Blanc

open Jaune

/-- A nonrecursive instruction's derivation retains its continuation's
descendant frames. -/
theorem Exec.descendantFrames_eq_of_nextNone {pc : Nat} {sevm : Sevm}
    {pre inter : Devm} {n : Ninst} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (run : Exec pc sevm pre out) (next : Exec (pc + n.size) sevm inter out) :
    Exec.descendantFrames run = Exec.descendantFrames next := by
  have hroot : Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ n :=
    Evm.step_next hat
  unfold Ninst.StepRun at step
  cases run with
  | halt hstep =>
      rw [hroot] at hstep
      rw [hstep] at step
      rw [← step.2] at hstep
      exact (Ninst.step_ne_halt_ok hstep).elim
  | cont hstep next' =>
      rw [hroot] at hstep
      have hpc := Ninst.step_cont_pc hstep
      rw [hstep] at step
      cases step.2
      subst hpc
      simp only [Exec.descendantFrames]
      rw [Exec.unique next' next]
  | doneErr hstep henter hresume =>
      rw [hroot] at hstep
      rw [hstep] at step
      obtain ⟨settled, frameRun, result⟩ := step
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      rw [frameRun.2, hresume] at result
      cases result
  | doneOk hstep henter hresume next' =>
      rw [hroot] at hstep
      have hpc := Ninst.step_spawn_pc hstep
      rw [hstep] at step
      obtain ⟨settled, frameRun, result⟩ := step
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      rw [frameRun.2, hresume] at result
      cases result
      subst hpc
      simp only [Exec.descendantFrames]
      rw [Exec.unique next' next]
  | runErr hstep henter child hresume =>
      rw [hroot] at hstep
      rw [hstep] at step
      obtain ⟨settled, frameRun, -⟩ := step
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨raw, slot, -⟩ := frameRun
      cases slot
  | runOk hstep henter child hresume next' =>
      rw [hroot] at hstep
      rw [hstep] at step
      obtain ⟨settled, frameRun, -⟩ := step
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨raw, slot, -⟩ := frameRun
      cases slot

/-- A jump's derivation retains its continuation's descendant frames. -/
theorem Exec.descendantFrames_eq_of_jump {pc pc' : Nat} {sevm : Sevm}
    {pre inter : Devm} {j : Jinst} {out : Execution}
    (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (run : Exec pc sevm pre out) (next : Exec pc' sevm inter out) :
    Exec.descendantFrames run = Exec.descendantFrames next := by
  have hroot : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' inter := by
    rw [Evm.step_jump hat]
    unfold Jinst.Run at step
    rw [step]
    rfl
  cases run with
  | cont hstep next' =>
      cases hroot.symm.trans hstep
      simp only [Exec.descendantFrames]
      rw [Exec.unique next' next]
  | halt hstep => cases hroot.symm.trans hstep
  | doneErr hstep _ _ => cases hroot.symm.trans hstep
  | doneOk hstep _ _ _ => cases hroot.symm.trans hstep
  | runErr hstep _ _ _ => cases hroot.symm.trans hstep
  | runOk hstep _ _ _ _ => cases hroot.symm.trans hstep

/-- A terminal instruction's derivation retains no descendant frame. -/
theorem Exec.descendantFrames_eq_nil_of_last {pc : Nat} {sevm : Sevm}
    {pre : Devm} {l : Linst} {out : Execution}
    (hat : Linst.At sevm.code pc l) (run : Exec pc sevm pre out) :
    Exec.descendantFrames run = [] := by
  have hroot := Evm.step_last (devm := pre) hat
  cases run with
  | halt _ => simp only [Exec.descendantFrames]
  | cont hstep _ => cases hroot.symm.trans hstep
  | doneErr hstep _ _ => cases hroot.symm.trans hstep
  | doneOk hstep _ _ _ => cases hroot.symm.trans hstep
  | runErr hstep _ _ _ => cases hroot.symm.trans hstep
  | runOk hstep _ _ _ _ => cases hroot.symm.trans hstep

/-- A filled spawn's derivation retains the settled child's committed frames,
then its continuation's descendant frames, read through any frame
observation. -/
theorem Exec.descendantFrames_flatMap_of_nextSome {α : Type} (f : Exec.Frame → List α)
    {pc : Nat} {sevm : Sevm} {pre inter settled : Devm} {x : Xinst}
    {frame : Jaune.Frame} {resume : Resume} {cevm : Evm} {raw out : Execution}
    (hat : Ninst.At sevm.code pc (.exec x))
    (spawnEq : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (resumeRun : resume.run (.ok settled) = .ok inter)
    (run : Exec pc sevm pre out) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + 1) sevm inter out) :
    (Exec.descendantFrames run).flatMap f =
      (if Frame.settlementCommits frame raw = true
        then (Exec.committedFrames child).flatMap f else []) ++
      (Exec.descendantFrames next).flatMap f := by
  have hroot : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume (pc + 1) := by
    rw [Evm.step_next hat]
    simp only [Ninst.step_exec, spawnEq, XStep.toStep]
  obtain ⟨henter, hsettle⟩ := RunFrame.some_inv frameRun
  cases run with
  | runOk hstep henter' child' hresume next' =>
      cases hroot.symm.trans hstep
      rw [henter] at henter'
      cases henter'
      have rawEq := Exec.result_unique child child'
      subst rawEq
      rw [Exec.unique child' child]
      rw [← hsettle, resumeRun] at hresume
      cases hresume
      rw [Exec.unique next' next]
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child
          _ next settles, if_pos settles]
        simp [Exec.committedFrames,
          Frame.raw_commits_of_settlementCommits settles]
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter
          child _ next settles, if_neg settles, List.nil_append]
  | halt hstep => cases hroot.symm.trans hstep
  | cont hstep _ => cases hroot.symm.trans hstep
  | doneErr hstep henter' _ =>
      cases hroot.symm.trans hstep
      rw [henter] at henter'
      cases henter'
  | doneOk hstep henter' _ _ =>
      cases hroot.symm.trans hstep
      rw [henter] at henter'
      cases henter'
  | runErr hstep henter' child' hresume =>
      cases hroot.symm.trans hstep
      rw [henter] at henter'
      cases henter'
      have rawEq := Exec.result_unique child child'
      subst rawEq
      rw [← hsettle, resumeRun] at hresume
      cases hresume

/-- One same-frame step whose retained slot is `retained` contributes exactly
that slot's settled frames, provided a spawned child's settlement commits. -/
theorem Exec.Deriv.descendantFrames_eq_of_stepRun {node next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next node) {xl : Xlot}
    (stepRun : Step.Run (Evm.step ⟨node.pc, node.sevm, node.devm⟩) xl
      (.ok next.devm))
    (settles : ∀ (frame : Jaune.Frame) (resume : Resume) (nextPc : Nat)
      (evm : Evm) (raw : Execution),
      Evm.step ⟨node.pc, node.sevm, node.devm⟩ = .spawn frame resume nextPc →
      xl = .some ⟨evm, raw⟩ → Frame.settlementCommits frame raw = true)
    (retained : ExecutionTrace.RetainedXlot xl) :
    Exec.descendantFrames node.exc =
      retained.settledFrames ++ Exec.descendantFrames next.exc := by
  cases edge with
  | cont hstep next =>
      rw [hstep] at stepRun
      obtain ⟨hxl, -⟩ := stepRun
      subst hxl
      cases retained
      simp [Exec.descendantFrames]
  | doneOk hstep henter hresume next =>
      rw [hstep] at stepRun
      obtain ⟨r, frameRun, -⟩ := stepRun
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨hxl, -⟩ := frameRun
      subst hxl
      cases retained
      simp [Exec.descendantFrames]
  | runOk hstep henter child hresume next =>
      have stepRun' := stepRun
      rw [hstep] at stepRun'
      obtain ⟨r, frameRun, -⟩ := stepRun'
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨raw', hxl, -⟩ := frameRun
      have commits := settles _ _ _ _ raw' hstep hxl
      subst hxl
      cases retained with
      | some run =>
          have rawEq := Exec.result_unique run child
          subst rawEq
          have runEq : run = child := Exec.unique _ _
          subst runEq
          have hraw := Frame.raw_commits_of_settlementCommits commits
          simp [commits, Exec.committedFrames, hraw]

end Blanc
