import Blanc.ExecutionSettlement

/-!
Contract-neutral call-tree paths for settlement-retained execution frames.
The path index counts every entered or immediately completed child message at
its parent, including children later pruned by settlement, so deleting a
failed sibling cannot silently renumber the surviving execution provenance.
-/

namespace Blanc

open Jaune

/-- A settlement-retained execution frame paired with its call-tree path.  The
selected root has path `[]`; a recursively executed child appends its
zero-based sibling index. -/
structure Exec.LocatedFrame where
  path : List Nat
  frame : Exec.Frame

/-- Settlement-retained descendant frames with call-tree paths.  `nextChild`
counts all child messages already encountered in the current parent. -/
def Exec.descendantFramePaths (parentPath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.LocatedFrame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.descendantFramePaths parentPath nextChild next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next =>
      Exec.descendantFramePaths parentPath (nextChild + 1) next
  | .runErr _ _ _ _ => []
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      let childPath := parentPath ++ [nextChild]
      let childFrames :=
        if h : Blanc.Frame.settlementCommits frame raw = true then
          ⟨childPath, Exec.Frame.ofRun child
            (Blanc.Frame.raw_commits_of_settlementCommits h)⟩ ::
              Exec.descendantFramePaths childPath 0 child
        else []
      childFrames ++
        Exec.descendantFramePaths parentPath (nextChild + 1) next
termination_by sizeOf run

/-- All and only settlement-retained frames, annotated by their stable
call-tree paths. -/
def Exec.committedFramePaths
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.LocatedFrame :=
  if h : Execution.commits out = true then
    ⟨[], Exec.Frame.ofRun run h⟩ :: Exec.descendantFramePaths [] 0 run
  else []

/-- Path annotation is conservative: erasing paths yields the established
settlement-retained frame traversal exactly, with identical order and pruning. -/
private theorem Exec.descendantFramePaths_map_frame
    (parentPath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (Exec.descendantFramePaths parentPath nextChild run).map
        Exec.LocatedFrame.frame =
      Exec.descendantFrames run := by
  induction run generalizing parentPath nextChild with
  | halt =>
      simp [Exec.descendantFramePaths, Exec.descendantFrames]
  | cont hstep next ih =>
      simpa [Exec.descendantFramePaths, Exec.descendantFrames] using
        ih (parentPath := parentPath) (nextChild := nextChild)
  | doneErr =>
      simp [Exec.descendantFramePaths, Exec.descendantFrames]
  | doneOk hstep henter hresume next ih =>
      simpa [Exec.descendantFramePaths, Exec.descendantFrames] using
        ih (parentPath := parentPath) (nextChild := nextChild + 1)
  | runErr =>
      simp [Exec.descendantFramePaths, Exec.descendantFrames]
  | runOk hstep henter child hresume next childIh nextIh =>
      simp only [Exec.descendantFramePaths, Exec.descendantFrames,
        List.map_append]
      split
      next childSettles =>
        simp only [List.map_cons]
        rw [childIh, nextIh]
      next childDoesNotSettle =>
        simp only [List.map_nil, List.nil_append]
        exact nextIh parentPath (nextChild + 1)

/-- Forgetting every path recovers `Exec.committedFrames` definitionally up to
the recursive annotation erasure. -/
theorem Exec.committedFramePaths_map_frame
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (Exec.committedFramePaths run).map Exec.LocatedFrame.frame =
      Exec.committedFrames run := by
  unfold Exec.committedFramePaths Exec.committedFrames
  split
  next committed =>
    simp only [List.map_cons]
    rw [Exec.descendantFramePaths_map_frame]
  next notCommitted =>
    rfl

end Blanc
