import Blanc.Lift.CallerProvenance
import Blanc.ExecutionAccountingPositional

/-!
# The settled frames of a history are a pre-order forest

`settledFrames` lists every settled frame followed by its retained descendants, at every depth
(`settledFrames_eq`, `Exec.committedFrames`, `Exec.descendantFrames`).  This module states the two
positional consequences a list-level induction over settled positions needs, contract-neutrally and
without any uniqueness of frames (every occurrence of a frame is produced by its own expansion):

* **contiguity**: at every split `before ++ F :: after`, `after` begins with `F`'s descendants
  (`Exec.descendantFrames_contig`, `ConfiguredHistoryTrace.settledFrames_contig`);
* **positional parent**: a settled frame is a message root, or an earlier frame `G` spawned it as a
  direct child and its position lies inside `G`'s block of descendants
  (`ConfiguredHistoryTrace.settledFrames_parent`).
-/

namespace Blanc

open Jaune

/-- A retained frame's committed frames are the frame itself, then its descendants. -/
theorem Exec.Frame.committedFrames_self (F : Exec.Frame) :
    Exec.committedFrames F.run = F :: Exec.descendantFrames F.run := by
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := F
  simp only [Exec.committedFrames, committed, ↓reduceDIte]
  rfl

/-- `F` is a direct child spawned by a frame with static environment `s`: it receives `s`'s current
target as caller or keeps it as its own target, and it is static when `s` is. -/
def Exec.SpawnedBy (s : Sevm) (F : Exec.Frame) : Prop :=
  (F.sevm.caller = s.currentTarget ∨ F.sevm.currentTarget = s.currentTarget) ∧
    (s.isStatic = true → F.sevm.isStatic = true)

/-- **The descendants of a run are a pre-order forest**: at every split, the rest begins with the
selected frame's descendants, and the selected frame is a direct child of the run or of an earlier
frame whose block of descendants covers its position. -/
theorem Exec.descendantFrames_forest :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      {b : List Exec.Frame} {F : Exec.Frame} {a : List Exec.Frame},
      Exec.descendantFrames run = b ++ F :: a →
      (∃ r, a = Exec.descendantFrames F.run ++ r) ∧
        ((F ∈ Exec.childFrames run ∧ Exec.SpawnedBy sevm F) ∨
          ∃ b₁ G b₂, b = b₁ ++ G :: b₂ ∧ F ∈ Exec.childFrames G.run ∧ Exec.SpawnedBy G.sevm F ∧
            b₂.length < (Exec.descendantFrames G.run).length) := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro b F a split
      simp only [Exec.descendantFrames] at split
      cases b <;> cases split
  | cont _ next ih =>
      intro b F a split
      simp only [Exec.descendantFrames, Exec.childFrames] at split ⊢
      exact ih split
  | doneErr _ _ _ =>
      intro b F a split
      simp only [Exec.descendantFrames] at split
      cases b <;> cases split
  | doneOk _ _ _ next ih =>
      intro b F a split
      simp only [Exec.descendantFrames, Exec.childFrames] at split ⊢
      exact ih split
  | runErr _ _ _ _ =>
      intro b F a split
      simp only [Exec.descendantFrames] at split
      cases b <;> cases split
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro b F a split
      by_cases hs : Frame.settlementCommits frame raw = true
      · have hchildren : Exec.childFrames (Exec.runOk hstep henter child hresume next) =
            Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits hs) ::
              Exec.childFrames next := by
          simp only [Exec.childFrames, dite_eq_left hs, List.singleton_append]
        rw [hchildren]
        rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next hs]
          at split
        have spawned : Exec.SpawnedBy nodeSevm
            (Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits hs)) := by
          obtain ⟨x, -, spawn, -⟩ := Evm.step_spawn_inv hstep
          exact ⟨Evm.step_spawn_child_caller hstep henter, fun static =>
            (Frame.enter_run_isStatic henter).trans (Xinst.step_spawn_isStatic spawn static)⟩
        rcases List.split_append_cons split with ⟨m, head, rfl⟩ | ⟨n, rfl, inNext⟩
        · cases b with
          | nil =>
              obtain ⟨rfl, rfl⟩ := List.cons.inj head
              exact ⟨⟨_, rfl⟩, .inl ⟨List.mem_cons_self, spawned⟩⟩
          | cons x b' =>
              obtain ⟨rfl, inChild⟩ := List.cons.inj head
              obtain ⟨⟨r, rest⟩, parent⟩ := childIh inChild
              refine ⟨⟨r ++ Exec.descendantFrames next, by rw [rest, List.append_assoc]⟩, .inr ?_⟩
              rcases parent with ⟨member, sp⟩ | ⟨b₁, G, b₂, rfl, member, sp, shorter⟩
              · refine ⟨[], _, b', rfl, member, sp, ?_⟩
                change b'.length < (Exec.descendantFrames child).length
                rw [inChild]
                change b'.length < (b' ++ F :: m).length
                rw [List.length_append, List.length_cons]
                omega
              · exact ⟨_ :: b₁, G, b₂, rfl, member, sp, shorter⟩
        · obtain ⟨contig, parent⟩ := nextIh inNext
          refine ⟨contig, ?_⟩
          rcases parent with ⟨member, sp⟩ | ⟨b₁, G, b₂, rfl, member, sp, shorter⟩
          · exact .inl ⟨List.mem_cons_of_mem _ member, sp⟩
          · exact .inr ⟨_ ++ b₁, G, b₂, (by rw [List.append_assoc, List.cons_append]), member, sp,
              shorter⟩
      · have hchildren : Exec.childFrames (Exec.runOk hstep henter child hresume next) =
            Exec.childFrames next := by
          simp only [Exec.childFrames, dite_eq_right hs, List.nil_append]
        rw [hchildren]
        rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next hs]
          at split
        exact nextIh split

/-- **Contiguity of a run's descendants**: at every split, the rest begins with the selected frame's
descendants. -/
theorem Exec.descendantFrames_contig {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) {b : List Exec.Frame} {F : Exec.Frame} {a : List Exec.Frame}
    (split : Exec.descendantFrames run = b ++ F :: a) :
    ∃ r, a = Exec.descendantFrames F.run ++ r :=
  (Exec.descendantFrames_forest run split).1

/-- The forest facts for the committed frames of a list of retained roots. -/
theorem rootFrames_forest {roots : List Exec.Frame} {b : List Exec.Frame} {F : Exec.Frame}
    {a : List Exec.Frame}
    (split : (roots.flatMap fun R => Exec.committedFrames R.run) = b ++ F :: a) :
    (∃ r, a = Exec.descendantFrames F.run ++ r) ∧
      (F ∈ roots ∨ ∃ b₁ G b₂, b = b₁ ++ G :: b₂ ∧ F ∈ Exec.childFrames G.run ∧
        Exec.SpawnedBy G.sevm F ∧ b₂.length < (Exec.descendantFrames G.run).length) := by
  induction roots generalizing b with
  | nil => cases b <;> cases split
  | cons R rest ih =>
      rw [List.flatMap_cons, Exec.Frame.committedFrames_self] at split
      rcases List.split_append_cons split with ⟨m, head, rfl⟩ | ⟨n, rfl, inRest⟩
      · cases b with
        | nil =>
            obtain ⟨rfl, rfl⟩ := List.cons.inj head
            exact ⟨⟨_, rfl⟩, .inl List.mem_cons_self⟩
        | cons x b' =>
            obtain ⟨rfl, inDesc⟩ := List.cons.inj head
            obtain ⟨⟨r, restEq⟩, parent⟩ := Exec.descendantFrames_forest R.run inDesc
            refine ⟨⟨r ++ _, by rw [restEq, List.append_assoc]⟩, .inr ?_⟩
            rcases parent with ⟨member, sp⟩ | ⟨b₁, G, b₂, rfl, member, sp, shorter⟩
            · refine ⟨[], R, b', rfl, member, sp, ?_⟩
              rw [inDesc]
              change b'.length < (b' ++ F :: m).length
              rw [List.length_append, List.length_cons]
              omega
            · exact ⟨R :: b₁, G, b₂, rfl, member, sp, shorter⟩
      · obtain ⟨contig, parent⟩ := ih inRest
        refine ⟨contig, ?_⟩
        rcases parent with member | ⟨b₁, G, b₂, rfl, member, sp, shorter⟩
        · exact .inl (List.mem_cons_of_mem _ member)
        · exact .inr ⟨_ ++ b₁, G, b₂, (by rw [List.append_assoc, List.cons_append]), member, sp,
            shorter⟩

namespace ExecutionTrace

/-- **Contiguity of a history's settled frames**: at every split, the rest begins with the selected
frame's descendants. -/
theorem ConfiguredHistoryTrace.settledFrames_contig {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    {b : List Exec.Frame} {F : Exec.Frame} {a : List Exec.Frame}
    (split : trace.settledFrames = b ++ F :: a) :
    ∃ r, a = Exec.descendantFrames F.run ++ r := by
  rw [trace.settledFrames_eq] at split
  exact (rootFrames_forest split).1

/-- **The positional parent of a settled frame**: it is a settled message root, or an earlier settled
frame `G` spawned it as a direct child and its position lies inside `G`'s block of descendants. -/
theorem ConfiguredHistoryTrace.settledFrames_parent {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future)
    {b : List Exec.Frame} {F : Exec.Frame} {a : List Exec.Frame}
    (split : trace.settledFrames = b ++ F :: a) :
    F ∈ trace.settledRoots ∨ ∃ b₁ G b₂, b = b₁ ++ G :: b₂ ∧ F ∈ Exec.childFrames G.run ∧
      Exec.SpawnedBy G.sevm F ∧ b₂.length < (Exec.descendantFrames G.run).length := by
  rw [trace.settledFrames_eq] at split
  exact (rootFrames_forest split).2

end ExecutionTrace

end Blanc
