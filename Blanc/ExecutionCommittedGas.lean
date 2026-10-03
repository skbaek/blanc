import Blanc.ExecutionFrames

/-! A settled gas budget for retained descendant-frame multiplicity. This
uses the pinned all-fork gas measure and keeps complete child settlement. -/

namespace Blanc

open Jaune

/-- Returned settled gas and every retained descendant share the entry budget.
Locally successful descendants of a failed child are not counted at its parent. -/
theorem Exec.descendantFrames_settledGas {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    ∀ stateGas : Option StateGasRules, ∀ post : Devm,
      executeCode.handleErrorWith stateGas out = .ok post →
      run.descendantFrames.length + post.gasMeasure ≤ pre.gasMeasure := by
  induction run with
  | @halt pc sevm pre out step =>
    intro stateGas post handled
    have bound := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at bound
    simpa only [Exec.descendantFrames, List.length_nil, Nat.zero_add] using
      bound stateGas post handled
  | @cont pc sevm pre pc' inter out step next ih =>
    intro stateGas post handled
    have bound := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at bound
    have tail := ih stateGas post handled
    simp only [Exec.descendantFrames]
    change inter.gasMeasure < pre.gasMeasure at bound
    omega
  | @doneErr pc sevm pre frame resume pc' result error step enter resumed =>
    intro stateGas post handled
    have spawn := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at spawn
    have resumedGas := Resume.run_gasLe (rsm := resume) (m := frame.inner.gas)
      (fun d hd => Frame.enter_done_gasLe enter hd)
    rw [resumed] at resumedGas
    have returned := Execution.settledGasLe_of_gasLe resumedGas stateGas post handled
    simp only [Exec.descendantFrames, List.length_nil, Nat.zero_add]
    change frame.inner.gas + resume.parentGas < pre.gasMeasure ∧ _ at spawn
    omega
  | @doneOk pc sevm pre frame resume pc' result inter out step enter resumed next ih =>
    intro stateGas post handled
    have spawn := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at spawn
    have resumedGas := Resume.run_gasLe (rsm := resume) (m := frame.inner.gas)
      (fun d hd => Frame.enter_done_gasLe enter hd)
    rw [resumed, Execution.gasMeasure_ok] at resumedGas
    have tail := ih stateGas post handled
    simp only [Exec.descendantFrames]
    change frame.inner.gas + resume.parentGas < pre.gasMeasure ∧ _ at spawn
    omega
  | @runErr pc sevm pre frame resume pc' childEvm raw error step enter child resumed ih =>
    intro stateGas post handled
    have spawn := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at spawn
    have childGas : raw.SettledGasLe frame.inner.gas := by
      intro sg d hd
      have budget := ih sg d hd
      rw [Frame.enter_run_gasMeasure enter] at budget
      omega
    have resumedGas := Resume.run_gasLe (rsm := resume) (r := frame.settle raw)
      (m := frame.inner.gas) (fun d hd => Frame.settle_gasLe childGas hd)
    rw [resumed] at resumedGas
    have returned := Execution.settledGasLe_of_gasLe resumedGas stateGas post handled
    simp only [Exec.descendantFrames, List.length_nil, Nat.zero_add]
    change frame.inner.gas + resume.parentGas < pre.gasMeasure ∧ _ at spawn
    omega
  | @runOk pc sevm pre frame resume pc' childEvm raw inter out
      step enter child resumed next childIH nextIH =>
    intro stateGas post handled
    have spawn := Evm.step_gasBound ⟨pc, sevm, pre⟩
    rw [step] at spawn
    change frame.inner.gas + resume.parentGas < pre.gasMeasure ∧ _ at spawn
    have tail := nextIH stateGas post handled
    by_cases committed : frame.settlementCommits raw = true
    · have rawCommitted := Frame.raw_commits_of_settlementCommits committed
      cases raw with
      | error err =>
        simp only [Execution.commits, Bool.false_eq_true] at rawCommitted
      | ok childPost =>
        have childBudget := childIH none childPost rfl
        rw [Frame.enter_run_gasMeasure enter] at childBudget
        have resumedGas := Resume.run_gasLe (rsm := resume) (r := frame.settle (.ok childPost))
          (m := childPost.gasMeasure) (fun d hd => Frame.settle_gasLe
            (Execution.settledGasLe_of_gasLe (ex := .ok childPost)
              (Nat.le_refl childPost.gasMeasure)) hd)
        rw [resumed, Execution.gasMeasure_ok] at resumedGas
        rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resumed next committed,
          List.length_append, List.length_cons]
        omega
    · have childGas : raw.SettledGasLe frame.inner.gas := by
        intro sg d hd
        have budget := childIH sg d hd
        rw [Frame.enter_run_gasMeasure enter] at budget
        omega
      have resumedGas := Resume.run_gasLe (rsm := resume) (r := frame.settle raw)
        (m := frame.inner.gas) (fun d hd => Frame.settle_gasLe childGas hd)
      rw [resumed, Execution.gasMeasure_ok] at resumedGas
      rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resumed next committed]
      omega

/-- The successful raw-result specialization of the settled budget. -/
theorem Exec.descendantFrames_length_gas_le {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (run : Exec pc sevm pre (.ok post)) :
    run.descendantFrames.length + post.gasMeasure ≤ pre.gasMeasure := by
  exact Exec.descendantFrames_settledGas run none post rfl

/-- The root itself has no universal positive cost (STOP may be free), so all
committed frames have one extra root allowance. -/
theorem Exec.committedFrames_length_gas_le {pc : Nat} {sevm : Sevm} {pre post : Devm}
    (run : Exec pc sevm pre (.ok post)) :
    run.committedFrames.length + post.gasMeasure ≤ pre.gasMeasure + 1 := by
  have bound := Exec.descendantFrames_length_gas_le run
  by_cases committed : Execution.commits (.ok post) = true
  · rw [Exec.committedFrames, dite_eq_left committed, List.length_cons]
    omega
  · rw [Exec.committedFrames, dite_eq_right committed, List.length_nil]
    omega

/-- Complete CALL/CREATE settlement can only reduce the returned measure.
The count is an upper bound even when CREATE code deposit discards raw frames. -/
theorem Exec.committedFrames_settle_length_gas_le {pc : Nat} {sevm : Sevm} {pre : Devm}
    {raw : Execution} {frame : Jaune.Frame} {post : Devm}
    (run : Exec pc sevm pre raw) (settled : frame.settle raw = .ok post) :
    run.committedFrames.length + post.gasMeasure ≤ pre.gasMeasure + 1 := by
  cases raw with
  | ok rawPost =>
    have count := Exec.committedFrames_length_gas_le run
    have gas := Frame.settle_gasLe
      (Execution.settledGasLe_of_gasLe (ex := .ok rawPost) (Nat.le_refl rawPost.gasMeasure)) settled
    omega
  | error error =>
    unfold Frame.settle at settled
    obtain ⟨handledPost, handled, gas⟩ := Frame.settleMsg_ok_gasLe settled
    have budget := Exec.descendantFrames_settledGas run _ handledPost handled
    rw [Exec.committedFrames, dite_eq_right
      (by intro impossible; cases impossible), List.length_nil, Nat.zero_add]
    omega

end Blanc
