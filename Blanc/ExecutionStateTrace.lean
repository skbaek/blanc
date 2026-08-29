import Blanc.ExecutionPath

/-!
Contract-neutral state chronology for settlement-retained execution.

Unlike a pre-order frame list, this trace records both sides of a recursive
message boundary.  A committing child is placed between its entry and
settlement boundaries; a child whose complete settlement rolls back is
pruned as one rollback boundary.  Consequently terminal effects such as
`SELFDESTRUCT` remain in their true execution position, and every emitted
boundary carries the exact committing driver suffix that produced it.
-/

namespace Blanc

open Jaune

/-- The semantic boundary crossed by one retained execution segment. -/
inductive Exec.StateBoundaryKind where
  /-- A non-spawning instruction advanced the current frame. -/
  | instruction
  /-- A child message completed without entering interpreted code. -/
  | childless
  /-- A settlement-committing child entered interpreted code. -/
  | childEntry
  /-- A settlement-committing child returned to its parent. -/
  | childSettlement
  /-- A child subtree was discarded by complete frame settlement. -/
  | childRollback
  /-- The current frame executed its terminal instruction. -/
  | terminal
  deriving DecidableEq

/-- One exact retained state boundary, located within the call tree.  The
committing driver suffix retains the concrete execution proof at the
boundary. -/
structure Exec.StateBoundary where
  framePath : List Nat
  driver : Exec.Frame
  kind : Exec.StateBoundaryKind
  before : State
  after : State

/-- The initial world state indexed by an execution derivation. -/
def Exec.startState {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (_run : Exec pc sevm pre out) : State :=
  pre.state

/-- A list of exact state boundaries forms one continuous state replay. -/
inductive Exec.StateReplay :
    State → List Exec.StateBoundary → State → Prop
  | nil (state : State) : Exec.StateReplay state [] state
  | cons {tail : List Exec.StateBoundary} {post : State}
      (event : Exec.StateBoundary)
      (rest : Exec.StateReplay event.after tail post) :
      Exec.StateReplay event.before (event :: tail) post

theorem Exec.StateReplay.append
    {pre middle post : State}
    {left right : List Exec.StateBoundary}
    (headReplay : Exec.StateReplay pre left middle)
    (tailReplay : Exec.StateReplay middle right post) :
    Exec.StateReplay pre (left ++ right) post := by
  induction headReplay with
  | nil => exact tailReplay
  | cons event rest ih => exact .cons event (ih tailReplay)

/-- Retained state boundaries for a known-committing frame.  `nextChild`
counts every entered or immediately completed child message, including a
later-pruned sibling, exactly as `Exec.descendantFramePaths` does. -/
def Exec.stateBoundariesOfCommits (framePath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) :
    List Exec.StateBoundary :=
  let driver := Exec.Frame.ofRun run committed
  match run with
  | .halt _ =>
      [{ framePath
         driver
         kind := .terminal
         before := pre.state
         after := (Execution.committedPost out committed).state }]
  | .cont _ next =>
      { framePath
        driver
        kind := .instruction
        before := pre.state
        after := Exec.startState next } ::
        Exec.stateBoundariesOfCommits framePath nextChild next committed
  | .doneErr _ _ _ => by simp [Execution.commits] at committed
  | .doneOk _ _ _ next =>
      { framePath
        driver
        kind := .childless
        before := pre.state
        after := Exec.startState next } ::
        Exec.stateBoundariesOfCommits
          framePath (nextChild + 1) next committed
  | .runErr _ _ _ _ => by simp [Execution.commits] at committed
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      let childPath := framePath ++ [nextChild]
      if h : Frame.settlementCommits frame raw = true then
        let childCommitted :=
          Frame.raw_commits_of_settlementCommits h
        { framePath
          driver
          kind := .childEntry
          before := pre.state
          after := Exec.startState child } ::
          (Exec.stateBoundariesOfCommits childPath 0 child childCommitted ++
            { framePath
              driver
              kind := .childSettlement
              before :=
                (Execution.committedPost raw childCommitted).state
              after := Exec.startState next } ::
              Exec.stateBoundariesOfCommits
                framePath (nextChild + 1) next committed)
      else
        { framePath
          driver
          kind := .childRollback
          before := pre.state
          after := Exec.startState next } ::
          Exec.stateBoundariesOfCommits
            framePath (nextChild + 1) next committed
termination_by sizeOf run

/-- Public state chronology, erased wholesale when the selected root does not
commit. -/
def Exec.committedStateBoundaries
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.StateBoundary :=
  if h : Execution.commits out = true then
    Exec.stateBoundariesOfCommits [] 0 run h
  else []

@[simp] theorem Exec.committedStateBoundaries_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (notCommitted : Execution.commits out ≠ true) :
    Exec.committedStateBoundaries run = [] := by
  simp [Exec.committedStateBoundaries, notCommitted]

private theorem Exec.stateReplay_of_commits
    (framePath : List Nat) (nextChild : Nat)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) :
    Exec.StateReplay pre.state
      (Exec.stateBoundariesOfCommits framePath nextChild run committed)
      (Execution.committedPost out committed).state := by
  induction run generalizing framePath nextChild with
  | halt step =>
      simp only [Exec.stateBoundariesOfCommits]
      exact .cons
        { framePath
          driver := Exec.Frame.ofRun (.halt step) committed
          kind := .terminal
          before := Exec.startState (.halt step)
          after := (Execution.committedPost _ committed).state }
        (.nil _)
  | cont step next ih =>
      simp only [Exec.stateBoundariesOfCommits]
      exact .cons
        { framePath
          driver := Exec.Frame.ofRun (.cont step next) committed
          kind := .instruction
          before := Exec.startState (.cont step next)
          after := Exec.startState next }
        (ih framePath nextChild committed)
  | doneErr step enter resume =>
      simp [Execution.commits] at committed
  | doneOk step enter resume next ih =>
      simp only [Exec.stateBoundariesOfCommits]
      exact .cons
        { framePath
          driver := Exec.Frame.ofRun (.doneOk step enter resume next) committed
          kind := .childless
          before := Exec.startState (.doneOk step enter resume next)
          after := Exec.startState next }
        (ih framePath (nextChild + 1) committed)
  | runErr step enter child resume ih =>
      simp [Execution.commits] at committed
  | runOk step enter child resume next childIh nextIh =>
      simp only [Exec.stateBoundariesOfCommits]
      split
      next childSettles =>
        let childCommitted :=
          Frame.raw_commits_of_settlementCommits childSettles
        let entry : Exec.StateBoundary :=
          { framePath
            driver := Exec.Frame.ofRun
              (.runOk step enter child resume next) committed
            kind := .childEntry
            before := Exec.startState
              (.runOk step enter child resume next)
            after := Exec.startState child }
        let settlement : Exec.StateBoundary :=
          { framePath
            driver := Exec.Frame.ofRun
              (.runOk step enter child resume next) committed
            kind := .childSettlement
            before :=
              (Execution.committedPost _ childCommitted).state
            after := Exec.startState next }
        exact .cons entry
          ((childIh (framePath ++ [nextChild]) 0 childCommitted).append
            (.cons settlement
              (nextIh framePath (nextChild + 1) committed)))
      next childDoesNotSettle =>
        let rollback : Exec.StateBoundary :=
          { framePath
            driver := Exec.Frame.ofRun
              (.runOk step enter child resume next) committed
            kind := .childRollback
            before := Exec.startState
              (.runOk step enter child resume next)
            after := Exec.startState next }
        exact .cons rollback
          (nextIh framePath (nextChild + 1) committed)

/-- The retained boundary chronology is continuous from the selected frame's
pre-state to its committed post-state. -/
theorem Exec.committedStateReplay
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) :
    Exec.StateReplay pre.state (Exec.committedStateBoundaries run)
      (Execution.committedPost out committed).state := by
  simpa [Exec.committedStateBoundaries, committed] using
    Exec.stateReplay_of_commits [] 0 run committed

end Blanc
