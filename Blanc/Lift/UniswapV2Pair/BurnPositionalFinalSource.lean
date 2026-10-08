import Blanc.Lift.UniswapV2Pair.BurnPositionalFeeSource
import Blanc.Lift.UniswapV2Pair.BurnPositionalFinishSource
import Blanc.Lift.UniswapV2Pair.BurnFinalTurns
import Blanc.Lift.UniswapV2Pair.SourceStaticSlotViews

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The first final query's source views retain the exact sixth slot and the
supplied same-state frame from the second transfer. -/
theorem BurnSevenCalls.final0Views {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K J : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    (r : BurnSevenCalls root sevm b)
    (incoming : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (rep : WriterRep J (r.five.second.returned.devm.getStor sevm.currentTarget) frame.current.state)
    (invocation : List Nat) (context : frame.context = writerContext sevm invocation)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (fresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys J (staticViewDecodedKeys F.sevm)) :
    let request := burnFinalRequest0 frame (r.five.four.sourcePriced current)
    ∃ (observed : SourceCallAt root frame request (feeObservedResult r.final0.out) 5)
      (views : List StaticViewTurn), observed.call = r.final0.call ∧
      PositionalTurns frame request observed.paths (staticViewTranscript views .done)
        {complete := true, frame := frame,
          childReturns := staticViewChildReturns frame request 0 views} ∧
      WriterRep J (r.final0.call.returned.devm.getStor sevm.currentTarget) frame.current.state := by
  let request := burnFinalRequest0 frame (r.five.four.sourcePriced current)
  have pair : frame.context.pair = sevm.currentTarget := by rw [context]; rfl
  have env : r.five.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.five.second.edge).trans r.five.sevm_eq
  have nonempty : (root.devm.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have actualInstalled : some (r.final0.call.occurrence.node.devm.getCode sevm.currentTarget).toList =
      sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode r.final0.call.sameFrame).2
      sevm.currentTarget nonempty]
    exact installed
  have inputStorage : r.final0.call.occurrence.node.devm.getStor sevm.currentTarget =
      r.five.second.returned.devm.getStor sevm.currentTarget := by
    rw [r.final0.input, St_getStor]
    simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
  have returnedStorage : r.final0.call.returned.devm.getStor sevm.currentTarget =
      r.five.second.returned.devm.getStor sevm.currentTarget := by
    rw [r.final0.reply.stor]
    simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
  have actualRep : WriterRep J (r.final0.call.occurrence.node.devm.getStor frame.context.pair)
      frame.current.state := by rw [pair, inputStorage]; exact rep
  obtain ⟨paths, views, queue, mapped, authentic, during⟩ :=
    CallOccurrenceStep.staticSlotViews r.final0.call (frame := frame) (request := request) 5
      sem image (by rw [pair]; exact actualInstalled) actualRep
      (by rw [r.final0.sevm_eq, env, context]; rfl)
      (by rw [r.final0.sevm_eq, env]; exact fork)
      (by intro F member target; exact fresh F member (target.trans pair))
  obtain ⟨observed, same, samePaths⟩ := r.final0SourceCall (frame := frame) incoming pair fork queue
  refine ⟨observed, views, same, ?_, ?_⟩
  · rw [samePaths]
    exact .staticViews views mapped authentic during
  · rw [returnedStorage]
    exact rep

/-- The second final query's views retain the exact seventh slot and the
first final query's full returned state. -/
theorem BurnSevenCalls.final1Views {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K J : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    (r : BurnSevenCalls root sevm b)
    (incoming : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (rep : WriterRep J (r.final0.call.returned.devm.getStor sevm.currentTarget) frame.current.state)
    (invocation : List Nat) (context : frame.context = writerContext sevm invocation)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (fresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys J (staticViewDecodedKeys F.sevm)) :
    let request := burnFinalRequest1 frame (r.five.four.sourcePriced current)
    ∃ (observed : SourceCallAt root frame request (feeObservedResult r.final1.out) 6)
      (views : List StaticViewTurn), observed.call = r.final1.call ∧
      PositionalTurns frame request observed.paths (staticViewTranscript views .done)
        {complete := true, frame := frame,
          childReturns := staticViewChildReturns frame request 0 views} ∧
      WriterRep J (r.final1.call.returned.devm.getStor sevm.currentTarget) frame.current.state := by
  let request := burnFinalRequest1 frame (r.five.four.sourcePriced current)
  have pair : frame.context.pair = sevm.currentTarget := by rw [context]; rfl
  have env : r.final0.call.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.final0.call.edge).trans
      (r.final0.sevm_eq.trans ((Cursor.parentStep_sevm r.five.second.edge).trans r.five.sevm_eq))
  have nonempty : (root.devm.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have actualInstalled : some (r.final1.call.occurrence.node.devm.getCode sevm.currentTarget).toList =
      sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode r.final1.call.sameFrame).2
      sevm.currentTarget nonempty]
    exact installed
  have inputStorage : r.final1.call.occurrence.node.devm.getStor sevm.currentTarget =
      r.final0.call.returned.devm.getStor sevm.currentTarget := by
    rw [r.final1.input, St_getStor]
    simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
  have returnedStorage : r.final1.call.returned.devm.getStor sevm.currentTarget =
      r.final0.call.returned.devm.getStor sevm.currentTarget := by
    rw [r.final1.reply.stor]
    simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
  have actualRep : WriterRep J (r.final1.call.occurrence.node.devm.getStor frame.context.pair)
      frame.current.state := by rw [pair, inputStorage]; exact rep
  obtain ⟨paths, views, queue, mapped, authentic, during⟩ :=
    CallOccurrenceStep.staticSlotViews r.final1.call (frame := frame) (request := request) 6
      sem image (by rw [pair]; exact actualInstalled) actualRep
      (by rw [r.final1.sevm_eq, env, context]; rfl)
      (by rw [r.final1.sevm_eq, env]; exact fork)
      (by intro F member target; exact fresh F member (target.trans pair))
  obtain ⟨observed, same, samePaths⟩ := r.final1SourceCall (frame := frame) incoming pair fork queue
  refine ⟨observed, views, same, ?_, ?_⟩
  · rw [samePaths]
    exact .staticViews views mapped authentic during
  · rw [returnedStorage]
    exact rep


end Blanc.Lift.UniswapV2Pair
