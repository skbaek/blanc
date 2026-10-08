import Blanc.Lift.UniswapV2Pair.SourceAdmission
import Blanc.Lift.UniswapV2Pair.MutablePositionalFold

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The actual output belongs to the same recursively admitted child result. -/
def AdmittedChildConsumes (Auth : Exec.Deriv → Entry → Transcript → Prop)
    (root : Exec.Deriv) (segment : SegmentResult) (transcript : Transcript) (out : RunResult) : Prop :=
  AdmittedSourceConsumes Auth root root 0 segment transcript out ∧
    ∀ committed : Execution.commits root.exn = true,
      out.status = .success (Execution.committedPost root.exn committed).output

/-- The fold carries one positional turn proof and admission on that same proof. -/
def AdmittedMutableTurns (Auth : Exec.Deriv → Entry → Transcript → Prop)
    (frame : Frame) (request : Request) (turn : Nat)
    (events : List (Log ⊕ Exec.LocatedFrame)) (transcript : Transcript) (out : TurnsResult) : Prop :=
  ∃ selected : PositionalMutableTurns frame request turn events transcript out,
    MutableAdmission Auth selected

theorem sourceAdmittedMutableTurnRules (Auth : Exec.Deriv → Entry → Transcript → Prop) :
    MutableTurnRules (AdmittedChildConsumes Auth) (AdmittedMutableTurns Auth) := by
  refine ⟨?_, ?_⟩
  · intro frame request turn log events tail out mutable rest
    obtain ⟨selected, admitted⟩ := rest
    exact ⟨.foreignLog mutable selected, .foreignLog mutable selected admitted⟩
  · intro frame request turn located entry events nested tail child out selected rest
    obtain ⟨⟨source, admittedSource⟩, output⟩ := selected
    obtain ⟨tailProof, admittedTail⟩ := rest
    exact ⟨.invoke source (output located.frame.committed) tailProof,
      .invoke source (output located.frame.committed) tailProof admittedSource admittedTail⟩

theorem sourceAdmittedMutableTurns_done (Auth : Exec.Deriv → Entry → Transcript → Prop)
    (frame : Frame) (request : Request) (turn : Nat) :
    AdmittedMutableTurns Auth frame request turn [] .done
      {complete := true, frame := frame, childReturns := []} :=
  ⟨.done frame request turn, .done frame request turn⟩

/-- The original slot walk constructs recursive admission and same-queue entry
authentication together, at the same incoming checkpoint and actual returned state. -/
theorem admitted_source_slot_turns
    {pair : Adr} {Rep : State → Stor → Prop} {Good : Exec.Deriv → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop} {owned : Event → Option Log}
    (supply : PairFrameSupplyWith (AdmittedChildConsumes Auth) pair Rep Good Auth owned)
    (repCongr : ∀ st (s s' : Stor), (∀ k, s'.get k = s.get k) → Rep st s → Rep st s')
    (sem : CodeSem) (image : sem.image = some code.toList)
    {root : Exec.Deriv} {frame : Frame} {request : Request} {reply : ExternalResult} {index : Nat}
    (observed : SourceCallAt root frame request reply index)
    (pairEq : frame.context.pair = pair) (mutable : externalStatic frame request = false)
    (installed : some (observed.call.occurrence.node.devm.getCode pair).toList = sem.image)
    (rep : Rep frame.current.state (observed.call.occurrence.node.devm.getStor pair))
    (time : frame.context.timestamp = observed.call.occurrence.node.sevm.benvStat.time)
    (fork : CoveredFork observed.call.occurrence.node.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = pair → Good F) :
    ∃ (events : List (Log ⊕ Exec.LocatedFrame)) (turns : List MutableTurn)
      (c : Checkpoint) (added : List PendingLog) (rets : List ChildReturn),
      SourceSlotEvents observed.call frame.context.pair index events ∧
      events.filterMap Sum.getRight? = observed.paths ∧
      turns.map MutableTurn.event = events ∧
      AdmittedMutableTurns Auth frame request 0 events (mutableTranscript turns .done)
        {complete := true, frame := {frame with current := c}, childReturns := rets} ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
        Auth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      Rep c.state (observed.call.returned.devm.getStor pair) ∧
      c.logs = frame.current.logs ++ added ∧
      ∃ L : List Log,
        observed.call.returned.devm.logs = observed.call.occurrence.node.devm.logs ++ L ∧
        added.map (PendingLog.rawWith owned) = L.map some := by
  exact mutable_source_slot_turns_with supply (sourceAdmittedMutableTurnRules Auth)
    (sourceAdmittedMutableTurns_done Auth) repCongr sem image observed pairEq mutable
    installed rep time fork good

end Blanc.Lift.UniswapV2Pair
