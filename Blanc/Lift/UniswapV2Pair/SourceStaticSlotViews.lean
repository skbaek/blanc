import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.Lift.UniswapV2Pair.StaticSlotTurns
import Blanc.Lift.CursorOccurrenceRoots

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The actual static occurrence supplies its exact slot queue, complete child
paths, and source views. Root freshness is projected to that same child. -/
theorem CallOccurrenceStep.staticSlotViews {root : Exec.Deriv}
    (call : CallOccurrenceStep root .staticcall) {K : WriterKey → Prop}
    {frame : Frame} {request : Request} (index : Nat)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (call.occurrence.node.devm.getCode frame.context.pair).toList = sem.image)
    (rep : WriterRep K (call.occurrence.node.devm.getStor frame.context.pair) frame.current.state)
    (time : frame.context.timestamp = call.occurrence.node.sevm.benvStat.time)
    (fork : CoveredFork call.occurrence.node.sevm.benvStat.fork)
    (fresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = frame.context.pair →
      WriterFreshKeys K (staticViewDecodedKeys F.sevm)) :
    ∃ (paths : List Exec.LocatedFrame) (views : List StaticViewTurn),
      SourceSlotQueue call frame.context.pair index paths ∧ views.map Prod.fst = paths ∧
      (∀ picked ∈ views, picked.Authentic frame) ∧
      ExactTurns frame request 0 (staticViewTranscript views .done)
        {complete := true, frame := frame,
          childReturns := staticViewChildReturns frame request 0 views} := by
  rcases sync_static_slot_filtered_turns_inv (path := [index]) call.occurrence call.returned
      call.instruction call.result sem image installed rep time fork with none | some
  · obtain ⟨slot, during⟩ := none
    exact ⟨[], [], Or.inl ⟨slot, rfl⟩, rfl,
      (fun _ member => (List.not_mem_nil member).elim), during⟩
  · obtain ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed,
      slot, original, views⟩ := some
    have contained := call.slotFilledWith
    rw [slot] at contained
    obtain ⟨picked, roots⟩ := contained
    have same := Exec.unique picked child
    rw [same] at roots
    have selectedFresh : ∀ located ∈
        (if Jaune.Frame.settlementCommits callee raw = true then
          (Exec.retainedTargetTurnsAt frame.context.pair [index] child).filterMap Sum.getRight?
        else []), WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm) := by
      intro located member
      by_cases commits : Jaune.Frame.settlementCommits callee raw = true
      · rw [ite_eq_left commits, Exec.retainedTargetTurnsAt_filterMap_eq _ _ _
          (Jaune.Frame.raw_commits_of_settlementCommits commits)] at member
        obtain ⟨rootMember, target⟩ := Exec.retainedTargetFramesFromAt_rawFrameRoot
          frame.context.pair child (Jaune.Frame.raw_commits_of_settlementCommits commits) member
        exact fresh (Exec.Frame.rootDeriv located.frame) (roots _ rootMember) target
      · rw [ite_eq_right commits] at member
        exact (List.not_mem_nil member).elim
    obtain ⟨chosen, mapped, authentic, during⟩ := views selectedFresh
    exact ⟨_, chosen, Or.inr ⟨evm, raw, callee, resume, pc, child, next, spawn, enter,
      resumed, slot, original, rfl⟩, mapped, authentic, during⟩

end Blanc.Lift.UniswapV2Pair
