import Blanc.ExecutionStateTrace
import Blanc.ExecutionTrace

/-!
Contract-neutral state chronology for Jaune's settled message-call wrapper.

The raw recursive execution is retained only when the complete CALL or CREATE
settlement commits.  Wrapper preparation is placed before that execution and
settlement after it; a discarded raw subtree is represented by one rollback
boundary.  This is the message-level bridge needed by transaction and block
chronologies without assigning any contract-specific meaning to a balance
change.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Message-wrapper boundaries surrounding the retained recursive execution. -/
inductive MessageStateBoundaryKind where
  | collision
  | childless
  | entry
  | settlement
  | rollback
  deriving DecidableEq

/-- Exact provenance for one retained message-level state boundary. -/
inductive MessageStateBoundaryOrigin where
  | wrapper {msg : Msg} {state : State} {out : MsgCallOutput}
      (trace : MessageCallTrace msg state out)
      (kind : MessageStateBoundaryKind)
  | execution {msg : Msg} {state : State} {out : MsgCallOutput}
      (trace : MessageCallTrace msg state out)
      (origin : Exec.StateBoundaryOrigin)

abbrev MessageStateBoundary := StateTransition MessageStateBoundaryOrigin

/-- Build one wrapper boundary while retaining its complete message trace. -/
def MessageCallTrace.stateBoundary
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (kind : MessageStateBoundaryKind) (before after : State) :
    MessageStateBoundary :=
  { origin := .wrapper trace kind
    before
    after }

/-- Lift one retained raw execution through its complete frame settlement. -/
private def MessageCallTrace.stateBoundariesOfRetained
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (frame : Frame)
    {slot : Xlot} (retained : RetainedXlot slot) :
    List MessageStateBoundary :=
  match retained with
  | .none =>
      [trace.stateBoundary .childless msg.benv.state state]
  | .some (out := raw) run =>
      if h : Frame.settlementCommits frame raw = true then
        let committed := Frame.raw_commits_of_settlementCommits h
        trace.stateBoundary .entry msg.benv.state (Exec.startState run) ::
          ((Exec.committedStateBoundaries run).map
            (StateTransition.mapOrigin
              (MessageStateBoundaryOrigin.execution trace)) ++
            [trace.stateBoundary .settlement
              (Execution.committedPost raw committed).state state])
      else
        [trace.stateBoundary .rollback msg.benv.state state]

/-- Settlement-selected raw boundaries replay exactly from message entry to
the settled wrapper state. -/
private theorem MessageCallTrace.stateReplayOfRetained
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (frame : Frame)
    {slot : Xlot} (retained : RetainedXlot slot) :
    StateReplay msg.benv.state
      (trace.stateBoundariesOfRetained frame retained) state := by
  cases retained with
  | none =>
      exact .cons
        (trace.stateBoundary .childless msg.benv.state state) (.nil _)
  | some run =>
      simp only [MessageCallTrace.stateBoundariesOfRetained]
      split
      next h =>
        let committed := Frame.raw_commits_of_settlementCommits h
        let entry := trace.stateBoundary .entry msg.benv.state
          (Exec.startState run)
        let settlement := trace.stateBoundary .settlement
          (Execution.committedPost _ committed).state state
        have rawReplay := StateReplay.mapOrigin
          (MessageStateBoundaryOrigin.execution trace)
          (Exec.committedStateReplay run committed)
        exact .cons entry
          (rawReplay.append (.cons settlement (.nil _)))
      next _ =>
        exact .cons
          (trace.stateBoundary .rollback msg.benv.state state) (.nil _)

/-- Exact message-level state chronology. -/
def MessageCallTrace.stateBoundaries
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    List MessageStateBoundary :=
  match trace with
  | .createCollision .. =>
      [trace.stateBoundary .collision msg.benv.state state]
  | .createRun _ _ _ _ core _ =>
      trace.stateBoundariesOfRetained (Frame.ofCreate msg) core.retained
  | .callRun _ _ _ _ execMsg _ _ _ core _ =>
      trace.stateBoundariesOfRetained (Frame.ofCall execMsg) core.retained

/-- The retained message chronology is continuous from wrapper entry to its
settled state. -/
theorem MessageCallTrace.stateReplay
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) :
    StateReplay msg.benv.state trace.stateBoundaries state := by
  cases trace with
  | createCollision htarget hcollision hresult =>
      let trace : MessageCallTrace msg state out :=
        .createCollision htarget hcollision hresult
      exact .cons
        (trace.stateBoundary .collision msg.benv.state state) (.nil _)
  | createRun htarget hcollision evm hcore core hresult =>
      let trace : MessageCallTrace msg state out :=
        .createRun htarget hcollision evm hcore core hresult
      exact trace.stateReplayOfRetained (Frame.ofCreate msg) core.retained
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm hcore
      core hresult =>
      let trace : MessageCallTrace msg state out :=
        .callRun htarget delegated refund hdelegation execMsg hexecMsg evm
          hcore core hresult
      exact trace.stateReplayOfRetained (Frame.ofCall execMsg) core.retained

end ExecutionTrace

end Blanc
