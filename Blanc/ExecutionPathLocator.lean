import Blanc.ExecutionPath

/-!
Forward location of an entered, settlement-retained child from a supplied
instruction occurrence in the committed root frame's own continuation.
-/

namespace Blanc

open Jaune

private theorem Exec.Deriv.ParentPrefix.descendants {root node : Exec.Deriv} (hprefix : Exec.Deriv.ParentPrefix root node) :
    ∀ (path : List Nat) (n : Nat), ∃ k, ∀ child,
      child ∈ Exec.descendantFramePaths path k node.exc →
      child ∈ Exec.descendantFramePaths path n root.exc := by
  induction hprefix with
  | refl => intro path n; exact ⟨n, fun _ h => h⟩
  | step edge rest ih =>
    intro path n
    cases edge with
    | cont step next =>
        simpa only [Exec.descendantFramePaths] using ih path n
    | doneOk step entered resumed next =>
        simpa only [Exec.descendantFramePaths] using ih path (n + 1)
    | runOk step entered child resumed next =>
      obtain ⟨k, members⟩ := ih path (n + 1)
      refine ⟨k, fun selected member => ?_⟩
      have hm := members selected member
      simp only [Exec.descendantFramePaths, List.mem_append]
      exact Or.inr hm

theorem Exec.exists_next_of_run_spawn
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm}
    {out raw : Execution} {frame : Jaune.Frame} {resume : Resume}
    {childEvm : Evm}
    (run : Exec pc sevm pre out)
    (spawn : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc)
    (entered : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post) :
    ∃ next : Exec nextPc sevm post out,
      run = .runOk spawn entered child resumed next := by
  cases run with
  | halt step => rw [spawn] at step; cases step
  | cont step next => rw [spawn] at step; cases step
  | doneErr step entry result =>
      rcases Step.spawn.inj (spawn.symm.trans step) with ⟨rfl, rfl, rfl⟩
      rw [entered] at entry
      cases entry
  | doneOk step entry result next =>
      rcases Step.spawn.inj (spawn.symm.trans step) with ⟨rfl, rfl, rfl⟩
      rw [entered] at entry
      cases entry
  | runErr step entry actual result =>
      rcases Step.spawn.inj (spawn.symm.trans step) with ⟨rfl, rfl, rfl⟩
      cases FrameEntry.run.inj (entered.symm.trans entry)
      cases Exec.result_unique child actual
      rw [resumed] at result
      cases result
  | runOk step entry actual result next =>
      rcases Step.spawn.inj (spawn.symm.trans step) with ⟨rfl, rfl, rfl⟩
      cases FrameEntry.run.inj (entered.symm.trans entry)
      cases Exec.result_unique child actual
      cases Except.ok.inj (resumed.symm.trans result)
      exact ⟨next, Exec.unique _ _⟩


/-- Locate the actual entered child of a successful CALL-shaped step in the
root frame's own continuation.  Root commitment and clean child settlement
are independent premises; an immediate/no-code slot does not satisfy this
statement.  The returned entering witness keeps the supplied occurrence. -/
theorem Exec.NinstOccurrence.exists_root_call_child
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (root : Exec pc sevm pre out)
    (rootCommitted : Execution.commits out = true)
    (occurrence : Exec.NinstOccurrence ⟨pc, sevm, pre, out, root⟩)
    (sameFrame : Exec.Deriv.ParentPrefix
      ⟨pc, sevm, pre, out, root⟩ occurrence.node)
    {msg : Msg} {resume : Resume} {nextPc : Nat}
    {childEvm : Evm} {raw : Execution} {settled post : Devm}
    (slotEq : occurrence.slot = .some ⟨childEvm, raw⟩)
    (spawn : Evm.step
      ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
        .spawn (Frame.ofCall msg) resume nextPc)
    (process : ProcessMessage msg (.some ⟨childEvm, raw⟩) (.ok settled))
    (clean : settled.error.isSome = false)
    (resumed : resume.run (.ok settled) = .ok post) :
    ∃ child : Exec.LocatedFrame,
      child ∈ Exec.committedFramePaths root ∧
      ∃ entering : Exec.LocatedFrame.EnteringOccurrence root child,
        entering.parent = ⟨[], Exec.Frame.ofRun root rootCommitted⟩ ∧
        HEq entering.occurrence occurrence ∧
        child.path = [entering.childIndex] ∧
        occurrence.slot = .some
          ⟨⟨child.frame.pc, child.frame.sevm, child.frame.pre⟩, child.frame.out⟩ := by
  have filled : Xlot.Filled (.some ⟨childEvm, raw⟩) := by
    rw [← slotEq]
    exact occurrence.filled
  obtain ⟨childRun⟩ := filled
  obtain ⟨entered, settledEq⟩ := RunFrame.some_inv process
  have resumeRaw : resume.run ((Frame.ofCall msg).settle raw) = .ok post := by
    rw [← settledEq]
    exact resumed
  have childSettles :=
    ProcessMessage.settlementCommits_of_some_ok_clean process clean
  have childCommitted := Frame.raw_commits_of_settlementCommits childSettles
  obtain ⟨next, nodeEq⟩ := Exec.exists_next_of_run_spawn occurrence.node.exc
    spawn entered childRun resumeRaw
  obtain ⟨index, embedMember⟩ := sameFrame.descendants [] 0
  let child : Exec.LocatedFrame :=
    ⟨[index], Exec.Frame.ofRun childRun childCommitted⟩
  have childMember : child ∈ Exec.committedFramePaths root := by
    have localMember : child ∈ Exec.descendantFramePaths [] index
        occurrence.node.exc := by
      rw [nodeEq]
      simp [Exec.descendantFramePaths, child, childSettles]
    have member := embedMember child localMember
    simp [Exec.committedFramePaths, rootCommitted, member]
  have parentMember :
      ⟨[], Exec.Frame.ofRun root rootCommitted⟩ ∈
        Exec.committedFramePaths root := by
    simp [Exec.committedFramePaths, rootCommitted]
  have retained : occurrence.Retained := by
    apply (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix
      root occurrence.node).mpr
    exact ⟨Exec.Frame.ofRun root rootCommitted,
      by simp [Exec.committedFrames, rootCommitted], sameFrame⟩
  let entering : Exec.LocatedFrame.EnteringOccurrence root child :=
    { parent := ⟨[], Exec.Frame.ofRun root rootCommitted⟩
      parentMember := parentMember
      childIndex := index
      path_eq := rfl
      occurrence := occurrence
      sameFrame := sameFrame
      retained := retained
      slot_eq := slotEq
      spawns := ⟨Frame.ofCall msg, resume, nextPc, post,
        spawn, entered, resumeRaw, next, nodeEq⟩ }
  exact ⟨child, childMember, entering, rfl, HEq.rfl, rfl, slotEq⟩

end Blanc
