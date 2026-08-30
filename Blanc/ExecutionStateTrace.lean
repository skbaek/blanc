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

/-- One state-to-state transition carrying an owner-selected exact origin. -/
structure StateTransition (Origin : Type) where
  origin : Origin
  before : State
  after : State

/-- A list of state transitions forms one continuous replay. -/
inductive StateReplay {Origin : Type} :
    State → List (StateTransition Origin) → State → Prop
  | nil (state : State) : StateReplay state [] state
  | cons {tail : List (StateTransition Origin)} {post : State}
      (event : StateTransition Origin)
      (rest : StateReplay event.after tail post) :
      StateReplay event.before (event :: tail) post

theorem StateReplay.append
    {Origin : Type} {pre middle post : State}
    {left right : List (StateTransition Origin)}
    (headReplay : StateReplay pre left middle)
    (tailReplay : StateReplay middle right post) :
    StateReplay pre (left ++ right) post := by
  induction headReplay with
  | nil => exact tailReplay
  | cons event rest ih => exact .cons event (ih tailReplay)

/-- Change only a transition's provenance vocabulary. -/
def StateTransition.mapOrigin {Old New : Type} (f : Old → New)
    (event : StateTransition Old) : StateTransition New :=
  { origin := f event.origin
    before := event.before
    after := event.after }

/-- Provenance relabelling preserves an exact state replay. -/
theorem StateReplay.mapOrigin
    {Old New : Type} (f : Old → New)
    {pre post : State} {events : List (StateTransition Old)}
    (replay : StateReplay pre events post) :
    StateReplay pre (events.map (StateTransition.mapOrigin f)) post := by
  induction replay with
  | nil => exact .nil _
  | cons event rest ih => exact .cons (event.mapOrigin f) ih

/-- Change only the named final state of an already continuous replay. -/
theorem StateReplay.castPost
    {Origin : Type} {pre post post' : State}
    {events : List (StateTransition Origin)}
    (replay : StateReplay pre events post) (eq : post = post') :
    StateReplay pre events post' := by
  subst post'
  exact replay

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

/-- Provenance of one exact retained execution-state boundary.  The committing
driver suffix retains the concrete execution proof at the boundary. -/
structure Exec.StateBoundaryOrigin where
  framePath : List Nat
  driver : Exec.Frame
  kind : Exec.StateBoundaryKind

abbrev Exec.StateBoundary := StateTransition Exec.StateBoundaryOrigin

/-- Build a retained boundary without repeating its provenance wrapper. -/
def Exec.stateBoundary (framePath : List Nat) (driver : Exec.Frame)
    (kind : Exec.StateBoundaryKind) (before after : State) :
    Exec.StateBoundary :=
  { origin := { framePath, driver, kind }
    before
    after }

/-- The initial world state indexed by an execution derivation. -/
def Exec.startState {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (_run : Exec pc sevm pre out) : State :=
  pre.state

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
      [Exec.stateBoundary framePath driver .terminal pre.state
        (Execution.committedPost out committed).state]
  | .cont _ next =>
      Exec.stateBoundary framePath driver .instruction pre.state
          (Exec.startState next) ::
        Exec.stateBoundariesOfCommits framePath nextChild next committed
  | .doneErr _ _ _ => by simp [Execution.commits] at committed
  | .doneOk _ _ _ next =>
      Exec.stateBoundary framePath driver .childless pre.state
          (Exec.startState next) ::
        Exec.stateBoundariesOfCommits
          framePath (nextChild + 1) next committed
  | .runErr _ _ _ _ => by simp [Execution.commits] at committed
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      let childPath := framePath ++ [nextChild]
      if h : Frame.settlementCommits frame raw = true then
        let childCommitted :=
          Frame.raw_commits_of_settlementCommits h
        Exec.stateBoundary framePath driver .childEntry pre.state
            (Exec.startState child) ::
          (Exec.stateBoundariesOfCommits childPath 0 child childCommitted ++
            Exec.stateBoundary framePath driver .childSettlement
                (Execution.committedPost raw childCommitted).state
                (Exec.startState next) ::
              Exec.stateBoundariesOfCommits
                framePath (nextChild + 1) next committed)
      else
        Exec.stateBoundary framePath driver .childRollback pre.state
            (Exec.startState next) ::
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
    StateReplay pre.state
      (Exec.stateBoundariesOfCommits framePath nextChild run committed)
      (Execution.committedPost out committed).state := by
  induction run generalizing framePath nextChild with
  | halt step =>
      simp only [Exec.stateBoundariesOfCommits]
      exact .cons
        (Exec.stateBoundary framePath
          (Exec.Frame.ofRun (.halt step) committed) .terminal
          (Exec.startState (.halt step))
          (Execution.committedPost _ committed).state)
        (.nil _)
  | cont step next ih =>
      simp only [Exec.stateBoundariesOfCommits]
      exact .cons
        (Exec.stateBoundary framePath
          (Exec.Frame.ofRun (.cont step next) committed) .instruction
          (Exec.startState (.cont step next)) (Exec.startState next))
        (ih framePath nextChild committed)
  | doneErr step enter resume =>
      simp [Execution.commits] at committed
  | doneOk step enter resume next ih =>
      simp only [Exec.stateBoundariesOfCommits]
      exact .cons
        (Exec.stateBoundary framePath
          (Exec.Frame.ofRun (.doneOk step enter resume next) committed)
          .childless (Exec.startState (.doneOk step enter resume next))
          (Exec.startState next))
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
          Exec.stateBoundary framePath
            (Exec.Frame.ofRun (.runOk step enter child resume next) committed)
            .childEntry (Exec.startState
              (.runOk step enter child resume next))
            (Exec.startState child)
        let settlement : Exec.StateBoundary :=
          Exec.stateBoundary framePath
            (Exec.Frame.ofRun (.runOk step enter child resume next) committed)
            .childSettlement
            (Execution.committedPost _ childCommitted).state
            (Exec.startState next)
        exact .cons entry
          ((childIh (framePath ++ [nextChild]) 0 childCommitted).append
            (.cons settlement
              (nextIh framePath (nextChild + 1) committed)))
      next childDoesNotSettle =>
        let rollback : Exec.StateBoundary :=
          Exec.stateBoundary framePath
            (Exec.Frame.ofRun (.runOk step enter child resume next) committed)
            .childRollback (Exec.startState
              (.runOk step enter child resume next))
            (Exec.startState next)
        exact .cons rollback
          (nextIh framePath (nextChild + 1) committed)

/-- The retained boundary chronology is continuous from the selected frame's
pre-state to its committed post-state. -/
theorem Exec.committedStateReplay
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) :
    StateReplay pre.state (Exec.committedStateBoundaries run)
      (Execution.committedPost out committed).state := by
  simpa [Exec.committedStateBoundaries, committed] using
    Exec.stateReplay_of_commits [] 0 run committed

end Blanc
