import Blanc.ExecutionInRawNodeOrigin

/-!
# Actual positional origin within a settlement-retained execution

The root branch identifies the actual input derivation. Every other node has
a same-frame or spawning witness strictly earlier in this retained prefix.
No own-code fact is assumed about arbitrary delegated frame roots.
-/

namespace Blanc

open Jaune

/-- Every retained node is the actual input root, follows an earlier retained
node of its frame, or is a child root spawned by an earlier retained node.
Complete child settlement controls the chronology; raw-only witnesses from
discarded children cannot occur in the result. -/
theorem Exec.retainedNodes_split_origin
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    {before after : List Exec.Deriv} {n : Exec.Deriv}
    (split : Exec.retainedNodes run = before ++ n :: after) :
    (before = [] ∧ n = ⟨pc, sevm, pre, out, run⟩) ∨
      (∃ m ∈ before, m.sevm = n.sevm) ∨
      ∃ m ∈ before, Exec.Deriv.SpawnedAt m n := by
  induction run generalizing before n after with
  | halt step =>
      simp only [Exec.retainedNodes_eq_of_commits _ committed,
        Exec.retainedNodesOfCommits] at split
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          exact Or.inl ⟨rfl, split.1.symm⟩
      | cons b bs =>
          simp only [List.cons_append, List.cons.injEq] at split
          have length := congrArg List.length split.2
          simp only [List.length_nil, List.length_append, List.length_cons] at length
          omega
  | @cont pc sevm pre pc' post out step next ih =>
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        ← Exec.retainedNodes_eq_of_commits next committed] at split
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          exact Or.inl ⟨rfl, split.1.symm⟩
      | cons b bs =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, remaining⟩ := split
          rcases ih committed remaining with ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨m, member, spawn⟩
          · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
          · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ member, same⟩)
          · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ member, spawn⟩)
  | doneErr step enter resume =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre frame resume pc' settled post out step enter resumed next ih =>
      rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        ← Exec.retainedNodes_eq_of_commits next committed] at split
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          exact Or.inl ⟨rfl, split.1.symm⟩
      | cons b bs =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, remaining⟩ := split
          rcases ih committed remaining with ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨m, member, spawn⟩
          · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
          · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ member, same⟩)
          · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ member, spawn⟩)
  | runErr step enter child resume ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child
      resumed next childIH nextIH =>
      by_cases settles : frame.settlementCommits raw = true
      · rw [Exec.retainedNodes_runOk_of_settlementCommits _ _ _ _ _ committed settles]
          at split
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at split
            exact Or.inl ⟨rfl, split.1.symm⟩
        | cons b bs =>
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨rfl, remaining⟩ := split
            rcases List.split_append_cons remaining with
              ⟨suffix, childSplit, _⟩ | ⟨earlier, beforeEq, nextSplit⟩
            · rcases childIH (Frame.raw_commits_of_settlementCommits settles) childSplit with
                ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨m, member, spawn⟩
              · exact Or.inr (Or.inr ⟨_, List.mem_cons_self,
                  frame, resume, pc', childEvm, step, enter, rfl, rfl, rfl⟩)
              · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ member, same⟩)
              · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ member, spawn⟩)
            · rw [beforeEq]
              rcases nextIH committed nextSplit with
                ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨m, member, spawn⟩
              · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
              · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _
                  (List.mem_append_right _ member), same⟩)
              · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _
                  (List.mem_append_right _ member), spawn⟩)
      · rw [Exec.retainedNodes_runOk_of_not_settlementCommits _ _ _ _ _ committed settles]
          at split
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at split
            exact Or.inl ⟨rfl, split.1.symm⟩
        | cons b bs =>
            simp only [List.cons_append, List.cons.injEq] at split
            obtain ⟨rfl, remaining⟩ := split
            rcases nextIH committed remaining with
              ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨m, member, spawn⟩
            · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
            · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ member, same⟩)
            · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ member, spawn⟩)

end Blanc
