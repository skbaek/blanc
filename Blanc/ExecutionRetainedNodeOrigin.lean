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
node of its frame, or is a child root immediately following its retained spawn.
Complete child settlement controls the chronology; raw-only witnesses from
discarded children cannot occur in the result. -/
theorem Exec.retainedNodes_split_immediate_origin
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    {before after : List Exec.Deriv} {n : Exec.Deriv}
    (split : Exec.retainedNodes run = before ++ n :: after) :
    (before = [] ∧ n = ⟨pc, sevm, pre, out, run⟩) ∨
      (∃ m ∈ before, m.sevm = n.sevm) ∨
      ∃ prior m, before = prior ++ [m] ∧ Exec.Deriv.SpawnedAt m n := by
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
          rcases ih committed remaining with ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨prior, m, last, spawn⟩
          · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
          · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ member, same⟩)
          · exact Or.inr (Or.inr ⟨_ :: prior, m, by rw [last]; rfl, spawn⟩)
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
          rcases ih committed remaining with ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨prior, m, last, spawn⟩
          · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
          · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ member, same⟩)
          · exact Or.inr (Or.inr ⟨_ :: prior, m, by rw [last]; rfl, spawn⟩)
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
                ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨prior, m, last, spawn⟩
              · exact Or.inr (Or.inr ⟨[], _, rfl,
                  frame, resume, pc', childEvm, step, enter, rfl, rfl, rfl⟩)
              · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ member, same⟩)
              · exact Or.inr (Or.inr ⟨_ :: prior, m, by rw [last]; rfl, spawn⟩)
            · rw [beforeEq]
              rcases nextIH committed nextSplit with
                ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨prior, m, last, spawn⟩
              · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
              · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _
                  (List.mem_append_right _ member), same⟩)
              · exact Or.inr (Or.inr ⟨_ :: (Exec.retainedNodes child ++ prior), m, by
                  rw [last]
                  simp only [List.cons_append, List.append_assoc]
                  rfl, spawn⟩)
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
              ⟨rfl, rfl⟩ | ⟨m, member, same⟩ | ⟨prior, m, last, spawn⟩
            · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
            · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ member, same⟩)
            · exact Or.inr (Or.inr ⟨_ :: prior, m, by rw [last]; rfl, spawn⟩)

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
  rcases Exec.retainedNodes_split_immediate_origin run committed split with
    root | same | ⟨prior, m, last, spawn⟩
  · exact Or.inl root
  · exact Or.inr (Or.inl same)
  · exact Or.inr (Or.inr ⟨m, by rw [last]; exact List.mem_append_right _ List.mem_cons_self,
      spawn⟩)


/-- A retained node's remaining execution is one contiguous segment of the
original retained chronology. In particular, its endpoint commits; no node
from a discarded nested execution can supply this witness. -/
theorem Exec.retainedNodes_segment_of_mem
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    {n : Exec.Deriv} (member : n ∈ Exec.retainedNodes run) :
    Execution.commits n.exn = true ∧ ∃ before after,
      Exec.retainedNodes run = before ++ Exec.retainedNodes n.exc ++ after := by
  induction run with
  | halt step =>
      have same : n = ⟨_, _, _, _, Exec.halt step⟩ := by
        simpa only [Exec.retainedNodes_eq_of_commits _ committed,
          Exec.retainedNodesOfCommits, List.mem_singleton] using member
      subst n
      exact ⟨committed, [], [], by simp only [List.nil_append, List.append_nil]⟩
  | cont step next ih =>
      have chronology : Exec.retainedNodes (.cont step next) =
          ⟨_, _, _, _, Exec.cont step next⟩ :: Exec.retainedNodes next := by
        rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
          ← Exec.retainedNodes_eq_of_commits next committed]
      rw [chronology, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨committed, [], [], by simp only [List.nil_append, List.append_nil]⟩
      · obtain ⟨nodeCommits, before, after, segment⟩ := ih committed member
        exact ⟨nodeCommits, _ :: before, after, by
          rw [chronology, segment]
          simp only [List.cons_append]
          rfl⟩
  | doneErr => simp only [Execution.commits, Bool.false_eq_true] at committed
  | doneOk step enter resumed next ih =>
      have chronology : Exec.retainedNodes (.doneOk step enter resumed next) =
          ⟨_, _, _, _, Exec.doneOk step enter resumed next⟩ :: Exec.retainedNodes next := by
        rw [Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
          ← Exec.retainedNodes_eq_of_commits next committed]
      rw [chronology, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨committed, [], [], by simp only [List.nil_append, List.append_nil]⟩
      · obtain ⟨nodeCommits, before, after, segment⟩ := ih committed member
        exact ⟨nodeCommits, _ :: before, after, by
          rw [chronology, segment]
          simp only [List.cons_append]
          rfl⟩
  | runErr => simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child
      resumed next childIH nextIH =>
      by_cases settles : frame.settlementCommits raw = true
      · have chronology := Exec.retainedNodes_runOk_of_settlementCommits
          step enter child resumed next committed settles
        rw [chronology, List.mem_cons] at member
        rcases member with rfl | member
        · exact ⟨committed, [], [], by simp only [List.nil_append, List.append_nil]⟩
        · rcases List.mem_append.mp member with inChild | inNext
          · obtain ⟨nodeCommits, before, after, segment⟩ :=
              childIH (Frame.raw_commits_of_settlementCommits settles) inChild
            refine ⟨nodeCommits, ⟨pc, sevm, pre, out, .runOk step enter child resumed next⟩ :: before, after ++ Exec.retainedNodes next, ?_⟩
            rw [chronology, segment]
            simp only [List.cons_append, List.append_assoc]
          · obtain ⟨nodeCommits, before, after, segment⟩ := nextIH committed inNext
            refine ⟨nodeCommits, ⟨pc, sevm, pre, out, .runOk step enter child resumed next⟩ :: (Exec.retainedNodes child ++ before), after, ?_⟩
            rw [chronology, segment]
            simp only [List.cons_append, List.append_assoc]
      · have chronology := Exec.retainedNodes_runOk_of_not_settlementCommits
          step enter child resumed next committed settles
        rw [chronology, List.mem_cons] at member
        rcases member with rfl | member
        · exact ⟨committed, [], [], by simp only [List.nil_append, List.append_nil]⟩
        · obtain ⟨nodeCommits, before, after, segment⟩ := nextIH committed member
          exact ⟨nodeCommits, _ :: before, after, by
            rw [chronology, segment]
            simp only [List.cons_append]
            rfl⟩

/-- A retained, settling spawn exposes its entire actual child as the segment
immediately after the spawning instruction. The suffix includes the resumed
parent and any later ancestor continuations. -/
theorem Exec.retainedNodes_settled_spawn_segment
    {root : Exec.Deriv} (committed : Execution.commits root.exn = true)
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Frame} {resume : Resume} {childEvm : Evm} {raw out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (next : Exec pc' sevm post out)
    (member : (⟨pc, sevm, pre, out, .runOk step enter child resumed next⟩ : Exec.Deriv)
      ∈ Exec.retainedNodes root.exc)
    (settles : frame.settlementCommits raw = true) :
    ∃ before after, Exec.retainedNodes root.exc = before ++
      ⟨pc, sevm, pre, out, .runOk step enter child resumed next⟩ ::
        (Exec.retainedNodes child ++ (Exec.retainedNodes next ++ after)) := by
  obtain ⟨nodeCommits, before, tail, segment⟩ :=
    Exec.retainedNodes_segment_of_mem root.exc committed member
  rw [Exec.retainedNodes_runOk_of_settlementCommits
    step enter child resumed next nodeCommits settles] at segment
  exact ⟨before, tail, by
    simpa only [List.cons_append, List.append_assoc] using segment⟩

end Blanc
