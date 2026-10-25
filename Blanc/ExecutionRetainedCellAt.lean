import Blanc.ExecutionNoninterference
import Blanc.ExecutionCellProvenance
import Blanc.Lift.TargetLogEvents

/-!
# Persistent cells at actual settlement-retained node entries

Absence of retained writes fixes the cell at every retained entry, including
entries inside completely settled children. Raw nodes of rolled-back children
are deliberately outside the conclusion.
-/

namespace Blanc

open Jaune

private theorem Exec.noRetainedWriteTo_of_retainedNodes_subset
    {pc₁ pc₂ : Nat} {sevm₁ sevm₂ : Sevm} {pre₁ pre₂ : Devm} {out₁ out₂ : Execution}
    {first : Exec pc₁ sevm₁ pre₁ out₁} {second : Exec pc₂ sevm₂ pre₂ out₂}
    {owner : Adr} {key : B256} (noWrite : Exec.NoRetainedWriteTo first owner key)
    (subset : Exec.retainedNodes second ⊆ Exec.retainedNodes first) :
    Exec.NoRetainedWriteTo second owner key := by
  intro write member
  obtain ⟨node, retained, found⟩ := List.mem_filterMap.mp member
  exact noWrite write (List.mem_filterMap.mpr ⟨node, subset retained, found⟩)

/-- A committing invocation with no retained write to the observed cell keeps
that cell at every actual retained node entry. Complete child settlement
governs membership; reverted raw writes are allowed. -/
theorem Exec.retainedNode_cell_eq_of_noRetainedWriteTo_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) (owner : Adr) (key : B256)
    (hcode : (pre.getCode owner).toList ≠ [])
    (noWrite : Exec.NoRetainedWriteTo run owner key)
    {node : Exec.Deriv} (retained : node ∈ Exec.retainedNodes run) :
    (node.devm.getStor owner).get key = (pre.getStor owner).get key := by
  induction run with
  | halt step =>
      simp only [Exec.retainedNodes_eq_of_commits _ committed,
        Exec.retainedNodesOfCommits, List.mem_cons, List.not_mem_nil, or_false] at retained
      subst node
      rfl
  | @cont pc sevm pre pc' post out step next ih =>
      have code := Exec.Deriv.ParentStep.codePreserve (.cont step next) owner hcode
      have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
      have nextNoWrite : Exec.NoRetainedWriteTo next owner key :=
        Exec.noRetainedWriteTo_of_retainedNodes_subset noWrite (by
          intro m member
          simpa only [Exec.retainedNodes_eq_of_commits _ committed,
            Exec.retainedNodesOfCommits, List.mem_cons] using Or.inr member)
      simp only [Exec.retainedNodes_eq_of_commits _ committed,
        Exec.retainedNodesOfCommits, List.mem_cons] at retained
      rcases retained with rfl | retained
      · rfl
      · have nextRetained : node ∈ Exec.retainedNodes next := by
          rw [Exec.retainedNodes_eq_of_commits _ committed]
          exact retained
        have parentCell := Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas
          (.cont step next) committed hsg owner key hcode noWrite
        have nextCell := Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas
          next committed hsg owner key nextCode nextNoWrite
        exact (ih committed hsg nextCode nextNoWrite nextRetained).trans
          (nextCell.symm.trans parentCell)
  | doneErr step enter resume =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre frame resume pc' settled post out step enter resumed next ih =>
      have code := Exec.Deriv.ParentStep.codePreserve
        (.doneOk step enter resumed next) owner hcode
      have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
      have nextNoWrite : Exec.NoRetainedWriteTo next owner key :=
        Exec.noRetainedWriteTo_of_retainedNodes_subset noWrite (by
          intro m member
          simpa only [Exec.retainedNodes_eq_of_commits _ committed,
            Exec.retainedNodesOfCommits, List.mem_cons] using Or.inr member)
      simp only [Exec.retainedNodes_eq_of_commits _ committed,
        Exec.retainedNodesOfCommits, List.mem_cons] at retained
      rcases retained with rfl | retained
      · rfl
      · have nextRetained : node ∈ Exec.retainedNodes next := by
          rw [Exec.retainedNodes_eq_of_commits _ committed]
          exact retained
        rw [ih committed hsg nextCode nextNoWrite nextRetained]
        rw [Evm.step_doneOk_getStor_eq step enter resumed owner
          (State.Protected.of_code_ne_nil hcode)]
  | runErr step enter child resume ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child
      resumed next childIH nextIH =>
      have code := Exec.Deriv.ParentStep.codePreserve
        (.runOk step enter child resumed next) owner hcode
      have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
      have childCode : (childEvm.dyna.getCode owner).toList ≠ [] := by
        rw [(Evm.step_spawn_child step enter).2.1 owner]
        exact hcode
      have childSg := Evm.step_spawn_child_fork_noStateGas step enter hsg
      obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
      have nonempty : pre.getCode owner ≠ .empty := by
        intro empty
        apply hcode
        rw [empty]
        exact ByteArray.toList_empty
      have seam := Xinst.spawn_run_getStor_noStateGas hsg spawn enter child resumed nonempty
      by_cases settles : frame.settlementCommits raw = true
      · have childCommitted := Frame.raw_commits_of_settlementCommits settles
        have childNoWrite : Exec.NoRetainedWriteTo child owner key :=
          Exec.noRetainedWriteTo_of_retainedNodes_subset noWrite (by
            intro m member
            rw [Exec.retainedNodes_runOk_of_settlementCommits _ _ _ _ _ committed settles]
            exact List.mem_cons_of_mem _ (List.mem_append_left _ member))
        have nextNoWrite : Exec.NoRetainedWriteTo next owner key :=
          Exec.noRetainedWriteTo_of_retainedNodes_subset noWrite (by
            intro m member
            rw [Exec.retainedNodes_runOk_of_settlementCommits _ _ _ _ _ committed settles]
            exact List.mem_cons_of_mem _ (List.mem_append_right _ member))
        rw [Exec.retainedNodes_runOk_of_settlementCommits _ _ _ _ _ committed settles]
          at retained
        rcases List.mem_cons.mp retained with rfl | retained
        · rfl
        · rcases List.mem_append.mp retained with inChild | inNext
          · rw [childIH childCommitted childSg childCode childNoWrite inChild,
              Evm.step_spawn_enter_getStor_noStateGas hsg step enter hcode]
          · have childCell := Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas
              child childCommitted childSg owner key childCode childNoWrite
            rw [nextIH committed hsg nextCode nextNoWrite inNext,
              seam.1 settles key, childCell,
              Evm.step_spawn_enter_getStor_noStateGas hsg step enter hcode]
      · have nextNoWrite : Exec.NoRetainedWriteTo next owner key :=
          Exec.noRetainedWriteTo_of_retainedNodes_subset noWrite (by
            intro m member
            rw [Exec.retainedNodes_runOk_of_not_settlementCommits _ _ _ _ _ committed settles]
            exact List.mem_cons_of_mem _ member)
        rw [Exec.retainedNodes_runOk_of_not_settlementCommits _ _ _ _ _ committed settles]
          at retained
        rcases List.mem_cons.mp retained with rfl | retained
        · rfl
        · rw [nextIH committed hsg nextCode nextNoWrite retained, seam.2 settles key]

end Blanc
