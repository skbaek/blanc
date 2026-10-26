import Blanc.ExecutionDeletionSafety
import Blanc.ExecutionExistingAccount
import Jaune.ExecChronology

/-!
No-deletion along the actual complete-settlement-retained chronology.
Discarded child settlements preserve the resumed parent's deletion set;
account preservation supplies code and created-account exclusion separately.
-/

namespace Blanc

open Jaune

/-- An ordinary CREATE resuming from a flagged settled child keeps the
saved parent's deletion set. -/
theorem Resume.create_atd_of_error {parent child post : Devm} {address : Adr}
    (failed : child.error.isSome = true)
    (run : (Resume.create parent address).run (.ok child) = .ok post) :
    post.accountsToDelete = parent.accountsToDelete := by
  simp only [Resume.run, liftToExecution, Bind.bind, Except.bind, failed,
    ↓reduceIte] at run
  exact congrArg Prod.fst (Devm.push_delSets_eq run)

/-- An ordinary CALL resuming from a flagged settled child keeps the
saved parent's deletion set, including the status push and output copy. -/
theorem Resume.call_atd_of_error {parent child post : Devm} {oi os : Nat}
    (failed : child.error.isSome = true)
    (run : (Resume.call parent oi os).run (.ok child) = .ok post) :
    post.accountsToDelete = parent.accountsToDelete := by
  simp only [Resume.run, liftToExecution, Bind.bind, Except.bind, failed,
    ↓reduceIte] at run
  cases hp : (incorporateChildOnError parent child child.output).push 0 with
  | error e => simp only [hp, reduceCtorEq] at run
  | ok pushed =>
    simp only [hp, Except.ok.injEq] at run
    subst post
    exact congrArg Prod.fst (Devm.push_delSets_eq hp)

/-- A discarded COMPLETE settlement and successful ordinary-lane resumption
preserve the actual spawning parent's deletion set. Raw child success is not
a settlement-commitment assumption. -/
theorem Evm.step_spawn_resume_atd_of_discarded_noStateGas
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {raw : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (discarded : Frame.settlementCommits frame raw ≠ true)
    (hresume : resume.run (frame.settle raw) = .ok post) :
    post.accountsToDelete = pre.accountsToDelete := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hstep
  rcases Xinst.step_shapeNoStateGas sevm pre x hsg with ⟨ex, hs, -⟩ |
    ⟨d, endowment, address, mi, ms, hf, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isSt, ii, isz,
      oi, osz, code, dp, hf, -, -, -, hs⟩
  · rw [hx] at hs
    cases hs
  · have spawn := hs.symm.trans hx
    obtain ⟨-, rfl⟩ := genericCreate_step_spawn_exact spawn
    cases settled : frame.settle raw with
    | error e =>
      rw [settled] at hresume
      exact False.elim (Resume.create_run_error hresume)
    | ok child =>
      have failed : child.error.isSome = true := by
        simpa only [Frame.settlementCommits, settled, Bool.not_eq_true,
          Option.isNone_eq_false_iff] using discarded
      have atd := Resume.create_atd_of_error failed (settled ▸ hresume)
      exact atd.trans hf.accountsToDelete.symm
  · have spawn := hs.symm.trans hx
    obtain ⟨-, rfl⟩ := genericCall_step_spawn_exact spawn
    cases settled : frame.settle raw with
    | error e =>
      rw [settled] at hresume
      exact False.elim (Resume.call_run_error hresume)
    | ok child =>
      have failed : child.error.isSome = true := by
        simpa only [Frame.settlementCommits, settled, Bool.not_eq_true,
          Option.isNone_eq_false_iff] using discarded
      have atd := Resume.call_atd_of_error failed (settled ▸ hresume)
      exact atd.trans hf.accountsToDelete.symm

/-- A successfully resumed discarded child needs no terminal-safety premise:
its actual account effect and rollback deletion-set law preserve NoDel. -/
theorem Evm.step_spawn_resume_noDel_of_discarded_noStateGas
    {wa : Adr} {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {childEvm : Evm} {raw : Execution}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (discarded : Frame.settlementCommits frame raw ≠ true)
    (hresume : resume.run (frame.settle raw) = .ok post)
    (initial : Devm.NoDel wa pre) : Devm.NoDel wa post := by
  have account : Execution.Rel (Devm.AccountPreserve true) pre (.ok post) :=
    Evm.step_effect (accountPreserve_refl_trans true).1
      (Ninst.accountPreserve_effectRec true) (Jinst.accountPreserve_effect true)
      (Linst.accountPreserve_effect true) (xl := .some ⟨childEvm, raw⟩)
      (Exec.accountPreserve true child)
      (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hresume.symm⟩)
  change Devm.AccountPreserve true pre post at account
  have preserved := account wa initial.code
  refine ⟨?_, preserved.2 rfl initial.ca, ?_⟩
  · rw [Evm.step_spawn_resume_atd_of_discarded_noStateGas hsg hstep discarded hresume]
    exact initial.atd
  · rw [preserved.1]
    exact initial.code

/-- Terminal exclusion only on nodes retained by complete settlement suffices
for no-deletion in a committing execution. Discarded children require no
terminal certificate, and the selected child obligation uses the same run. -/
theorem Exec.inv_noDel_of_retained_terminal_safe
    {wa : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none)
    (safe : ∀ node ∈ Exec.retainedNodes run,
      node.sevm.currentTarget = wa → ¬ Linst.At node.sevm.code node.pc .selfdestruct)
    (initial : Devm.NoDel wa pre) : Execution.NoDel wa out := by
  revert committed hsg safe initial
  induction run with
  | halt hstep =>
    intro committed hsg safe initial
    have safeNode := safe _ (by
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits]
      exact List.mem_cons_self)
    exact Exec.noDel_step_of_safe (slot := .none) hsg initial safeNode trivial
      (by rw [hstep]; exact ⟨rfl, rfl⟩)
  | cont hstep next ih =>
    intro committed hsg safe initial
    have safeNode := safe _ (by
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits]
      exact List.mem_cons_self)
    have mid : Execution.NoDel wa _ :=
      Exec.noDel_step_of_safe (slot := .none) hsg initial safeNode trivial
        (by rw [hstep]; exact ⟨rfl, rfl⟩)
    apply ih committed hsg _ mid
    intro node member
    exact safe node (by
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        ← Exec.retainedNodes_eq_of_commits next committed]
      exact List.mem_cons_of_mem _ member)
  | doneErr hstep henter hr =>
    intro committed
    cases committed
  | doneOk hstep henter hr next ih =>
    intro committed hsg safe initial
    have safeNode := safe _ (by
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits]
      exact List.mem_cons_self)
    have mid : Execution.NoDel wa _ :=
      Exec.noDel_step_of_safe (slot := .none) hsg initial safeNode trivial
        (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
    apply ih committed hsg _ mid
    intro node member
    exact safe node (by
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        ← Exec.retainedNodes_eq_of_commits next committed]
      exact List.mem_cons_of_mem _ member)
  | runErr hstep henter child hr ihc =>
    intro committed
    cases committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out
      hstep henter child hr next ihc ih =>
    intro committed hsg safe initial
    by_cases selected : Frame.settlementCommits frame raw = true
    · have chronology := Exec.retainedNodes_runOk_of_settlementCommits
        hstep henter child hr next committed selected
      have safeNode := safe _ (by rw [chronology]; exact List.mem_cons_self)
      have childCommits := Frame.raw_commits_of_settlementCommits selected
      have childGas := (Evm.step_spawn_child_benvStat hstep henter).symm ▸ hsg
      have safeChild : ∀ node ∈ Exec.retainedNodes child,
          node.sevm.currentTarget = wa →
          ¬ Linst.At node.sevm.code node.pc .selfdestruct := by
        intro node member
        exact safe node (by rw [chronology]; exact
          List.mem_cons_of_mem _ (List.mem_append_left _ member))
      have mid : Execution.NoDel wa _ :=
        Exec.noDel_step_of_safe (slot := .some ⟨_, _⟩) hsg initial safeNode
          (fun input => ihc childCommits childGas safeChild input)
          (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
      apply ih committed hsg _ mid
      intro node member
      exact safe node (by rw [chronology]; exact
        List.mem_cons_of_mem _ (List.mem_append_right _ member))
    · have chronology := Exec.retainedNodes_runOk_of_not_settlementCommits
        hstep henter child hr next committed selected
      have mid := Evm.step_spawn_resume_noDel_of_discarded_noStateGas
        hsg hstep henter child selected hr initial
      apply ih committed hsg _ mid
      intro node member
      exact safe node (by rw [chronology]; exact List.mem_cons_of_mem _ member)

end Blanc
