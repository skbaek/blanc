import Blanc.ExecutionCodeAt
import Blanc.ExecutionFrameEntry
import Blanc.OwnerDiscipline

/-! Caller exclusion for transaction execution around an empty-code address. -/

namespace Blanc

open Jaune

/-- The actual spawn caller is either the parent's target or its inherited caller. -/
theorem Xinst.step_spawn_caller_parent_or_inherited
    {sevm : Sevm} {devm : Devm} {x : Xinst} {frame : Frame} {resume : Resume}
    (spawn : Xinst.step sevm devm x = .spawn frame resume) :
    frame.inner.caller = sevm.currentTarget ∨ frame.inner.caller = sevm.caller := by
  cases x <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at spawn
  all_goals repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | solve | cases spawn
    | obtain ⟨rfl, _⟩ := genericCreate_step_spawn_exact spawn
      exact Or.inl rfl
    | exact Or.inl (genericCreateAmsterdam_step_spawn_caller spawn)
    | obtain ⟨rfl, _⟩ := genericCall_step_spawn_exact spawn
      first | exact Or.inl rfl | exact Or.inr rfl
    | obtain ⟨rfl, _⟩ := genericCallAmsterdam_step_spawn_exact spawn
      first | exact Or.inl rfl | exact Or.inr rfl

theorem Xinst.step_spawn_context_target
    {sevm : Sevm} {devm : Devm} {x : Xinst} {frame : Frame} {resume : Resume}
    (context : x = .callcode ∨ x = .delegatecall)
    (spawn : Xinst.step sevm devm x = .spawn frame resume) :
    frame.inner.currentTarget = sevm.currentTarget := by
  rcases context with rfl | rfl <;>
    simp only [Xinst.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at spawn
  all_goals repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | solve | cases spawn
    | obtain ⟨rfl, _⟩ := genericCall_step_spawn_exact spawn
      rfl
    | obtain ⟨rfl, _⟩ := genericCallAmsterdam_step_spawn_exact spawn
      rfl

theorem Frame.enter_run_caller {frame : Frame} {child : Evm}
    (enter : frame.enter = .run child) : child.sta.caller = frame.inner.caller := by
  obtain ⟨_, _, rfl⟩ := Frame.enter_run_inv enter
  rfl

theorem Xinst.step_create_spawn_codeAddress
    {sevm : Sevm} {devm : Devm} {x : Xinst} {frame : Frame} {resume : Resume}
    (fork : CoveredFork sevm.benvStat.fork) (create : x = .create ∨ x = .create2)
    (spawn : Xinst.step sevm devm x = .spawn frame resume) :
    frame.inner.codeAddress = none := by
  rcases create with rfl | rfl <;>
    simp only [Xinst.step, fork.rules_stateGas_none, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at spawn
  all_goals repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | solve | cases spawn
    | exact genericCreate.step_spawn_codeAddress spawn

theorem Frame.enter_run_codeAddress {frame : Frame} {child : Evm}
    (enter : frame.enter = .run child) : child.sta.codeAddress = frame.inner.codeAddress := by
  obtain ⟨_, _, rfl⟩ := Frame.enter_run_inv enter
  rfl

/-- Empty executing code fetches STOP at every program counter and cannot spawn. -/
theorem Evm.step_empty_code_not_spawn {pc : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume} {nextPc : Nat}
    (empty : sevm.code = ByteArray.empty) :
    Evm.step ⟨pc, sevm, pre⟩ ≠ .spawn frame resume nextPc := by
  have fetch : Evm.getInst ⟨pc, sevm, pre⟩ = some (.last .stop) := by
    change ByteArray.getInst sevm.code pc = _
    rw [empty]
    unfold ByteArray.getInst
    rw [dite_eq_right (by change ¬ pc < 0; omega)]
  rw [Evm.step_last fetch]
  intro eq
  cases eq

/-- One entered child preserves caller exclusion and the empty-target invariant. -/
theorem Evm.step_spawn_caller_excluded {a : Adr} {pc nextPc : Nat}
    {sevm : Sevm} {pre : Devm} {frame : Frame} {resume : Resume} {child : Evm}
    (spawn : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume nextPc)
    (fork : CoveredFork sevm.benvStat.fork)
    (enter : frame.enter = .run child) (caller : sevm.caller ≠ a)
    (targetCode : sevm.currentTarget = a → sevm.code = ByteArray.empty)
    (childEmpty : child.dyna.getCode a = ByteArray.empty)
    (avoid : child.sta.codeAddress = none → child.sta.currentTarget ≠ a) :
    child.sta.caller ≠ a ∧
      (child.sta.currentTarget = a → child.sta.code = ByteArray.empty) := by
  have parentTarget : sevm.currentTarget ≠ a := by
    intro eq
    exact Evm.step_empty_code_not_spawn (targetCode eq) spawn
  obtain ⟨x, _, instruction, _⟩ := Evm.step_spawn_inv spawn
  have childCaller : child.sta.caller ≠ a := by
    rw [Frame.enter_run_caller enter]
    rcases Xinst.step_spawn_caller_parent_or_inherited instruction with parent | inherited
    · rw [parent]
      exact parentTarget
    · rw [inherited]
      exact caller
  refine ⟨childCaller, fun target => ?_⟩
  have emptyAt : pre.getCode a = ByteArray.empty := by
    rw [← (Evm.step_spawn_child spawn enter).2.1 a]
    exact childEmpty
  have frameTarget : frame.inner.currentTarget = a :=
    (Frame.enter_run_currentTarget enter).symm.trans target
  cases x with
  | create =>
    exact False.elim (avoid (by
      rw [Frame.enter_run_codeAddress enter]
      exact Xinst.step_create_spawn_codeAddress fork (Or.inl rfl) instruction) target)
  | create2 =>
    exact False.elim (avoid (by
      rw [Frame.enter_run_codeAddress enter]
      exact Xinst.step_create_spawn_codeAddress fork (Or.inr rfl) instruction) target)
  | call =>
    rw [Frame.enter_run_code enter,
      Xinst.step_directCall_spawn_code (Or.inl rfl) instruction (by
        rw [frameTarget, emptyAt]
        decide), frameTarget, emptyAt]
  | staticcall =>
    rw [Frame.enter_run_code enter,
      Xinst.step_directCall_spawn_code (Or.inr rfl) instruction (by
        rw [frameTarget, emptyAt]
        decide), frameTarget, emptyAt]
  | callcode =>
    exact False.elim (parentTarget ((Xinst.step_spawn_context_target
      (Or.inl rfl) instruction).symm.trans frameTarget))
  | delegatecall =>
    exact False.elim (parentTarget ((Xinst.step_spawn_context_target
      (Or.inr rfl) instruction).symm.trans frameTarget))

private theorem Exec.rawFrameDescendants_caller_excluded {a : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ a)
    (targetCode : sevm.currentTarget = a → sevm.code = ByteArray.empty)
    (empty : ∀ root ∈ Exec.rawFrameDescendants run, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ Exec.rawFrameDescendants run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ Exec.rawFrameDescendants run,
      root.sevm.caller ≠ a ∧
        (root.sevm.currentTarget = a → root.sevm.code = ByteArray.empty) := by
  induction run with
  | halt step =>
    intro root member
    simp only [Exec.rawFrameDescendants, List.not_mem_nil] at member
  | cont step next ih =>
    simpa only [Exec.rawFrameDescendants] using ih fork caller targetCode
      (by simpa only [Exec.rawFrameDescendants] using empty)
      (by simpa only [Exec.rawFrameDescendants] using avoid)
  | doneErr step enter resume =>
    intro root member
    simp only [Exec.rawFrameDescendants, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
    simpa only [Exec.rawFrameDescendants] using ih fork caller targetCode
      (by simpa only [Exec.rawFrameDescendants] using empty)
      (by simpa only [Exec.rawFrameDescendants] using avoid)
  | @runErr pc sevm pre frame resume nextPc child raw error step enter childRun resumeRun ih =>
    simp only [Exec.rawFrameDescendants] at empty avoid
    have childRoot : (⟨child.pc, child.sta, child.dyna, raw, childRun⟩ : Exec.Deriv) ∈
        Exec.rawFrameDescendants (Exec.runErr step enter childRun resumeRun) :=
      by rw [Exec.rawFrameDescendants]; exact List.mem_cons_self
    obtain ⟨childCaller, childCode⟩ := Evm.step_spawn_caller_excluded step fork enter caller
      targetCode (empty _ (by simpa only [Exec.rawFrameDescendants] using childRoot))
      (avoid _ (by simpa only [Exec.rawFrameDescendants] using childRoot))
    have descendants := ih (Evm.step_spawn_child_fork step enter fork) childCaller childCode
      (fun root member => empty root (List.mem_cons_of_mem _ member))
      (fun root member => avoid root (List.mem_cons_of_mem _ member))
    intro root member
    simp only [Exec.rawFrameDescendants, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨childCaller, childCode⟩
    · exact descendants root member
  | @runOk pc sevm pre frame resume nextPc child raw post out step enter childRun resumeRun
      next ihChild ihNext =>
    simp only [Exec.rawFrameDescendants] at empty avoid
    have childRoot : (⟨child.pc, child.sta, child.dyna, raw, childRun⟩ : Exec.Deriv) ∈
        Exec.rawFrameDescendants (Exec.runOk step enter childRun resumeRun next) :=
      by rw [Exec.rawFrameDescendants]; exact List.mem_cons_self
    obtain ⟨childCaller, childCode⟩ := Evm.step_spawn_caller_excluded step fork enter caller
      targetCode (empty _ (by simpa only [Exec.rawFrameDescendants] using childRoot))
      (avoid _ (by simpa only [Exec.rawFrameDescendants] using childRoot))
    have childDescendants := ihChild (Evm.step_spawn_child_fork step enter fork)
      childCaller childCode
      (fun root member => empty root
        (List.mem_cons_of_mem _ (List.mem_append_left _ member)))
      (fun root member => avoid root
        (List.mem_cons_of_mem _ (List.mem_append_left _ member)))
    have nextDescendants := ihNext fork caller targetCode
      (fun root member => empty root
        (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
      (fun root member => avoid root
        (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
    intro root member
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member
    · exact ⟨childCaller, childCode⟩
    · rcases member with childMember | nextMember
      · exact childDescendants root childMember
      · exact nextDescendants root nextMember

/-- Root and descendant callers are excluded using actual empty-code and CREATE witnesses. -/
theorem Exec.rawFrameRoots_caller_excluded {a : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ a)
    (targetCode : sevm.currentTarget = a → sevm.code = ByteArray.empty)
    (empty : ∀ root ∈ Exec.rawFrameRoots run, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ Exec.rawFrameRoots run,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ Exec.rawFrameRoots run,
      root.sevm.caller ≠ a ∧
        (root.sevm.currentTarget = a → root.sevm.code = ByteArray.empty) := by
  simp only [Exec.rawFrameRoots] at empty avoid
  have descendants := Exec.rawFrameDescendants_caller_excluded run fork caller targetCode
    (fun root member => empty root (List.mem_cons_of_mem _ member))
    (fun root member => avoid root (List.mem_cons_of_mem _ member))
  intro root member
  simp only [Exec.rawFrameRoots, List.mem_cons] at member
  rcases member with rfl | member
  · exact ⟨caller, targetCode⟩
  · exact descendants root member

end Blanc
