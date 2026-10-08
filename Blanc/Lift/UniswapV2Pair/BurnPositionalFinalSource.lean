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


/-- The same second-transfer source frame consumes both original final slots
and their full view queues, then the actual accepted update/unlock/output tail. -/
theorem BurnSevenCalls.finalSource
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K J : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    (r : BurnSevenCalls root sevm b)
    (incoming : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (rep : WriterRep J (r.five.second.returned.devm.getStor sevm.currentTarget) frame.current.state)
    (invocation : List Nat) (context : frame.context = writerContext sevm invocation)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork)
    (fresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys J (staticViewDecodedKeys F.sevm)) :
    let priced := r.five.four.sourcePriced current
    let request0 := burnFinalRequest0 frame priced
    let frame1 := frame.beginResume request0
    let request1 := burnFinalRequest1 frame1 priced
    let frame2 := frame1.beginResume request1
    let flag := feeOnWord (Bytes.toB256 (r.five.four.three.fee.out.take 32))
    let recipient := (Sevm.dataWord sevm 4).toAdr.toB256
    ∃ (updated : State) (event : Event) (oracle : OracleUpdate) (views0 views1 : List StaticViewTurn),
      let finished := burnFinishedFrame frame2 updated event oracle flag recipient
        priced.amount0 priced.amount1
      AdmittedSourceConsumes Auth root r.five.second.returned 5
        (.suspended frame request0 (.burnFinalBalance0 priced))
        (.next (feeObservedResult r.final0.out) (staticViewTranscript views0 .done)
          (.next (feeObservedResult r.final1.out) (staticViewTranscript views1 .done) .done))
        {status := .success (encodeWords [priced.amount0, priced.amount1]), frame := finished,
          remaining := .done, childReturns := staticViewChildReturns frame request0 0 views0 ++
            staticViewChildReturns frame1 request1 0 views1} ∧
      WriterRep J (post.getStor sevm.currentTarget) finished.current.state ∧
      post.output = encodeWords [priced.amount0, priced.amount1] ∧
      post.logs = r.final1.call.returned.devm.logs ++
        [⟨frame.context.pair, [updateSyncTopic],
          encodeWords [Bytes.toB256 (r.final0.out.take 32), Bytes.toB256 (r.final1.out.take 32)]⟩,
         ⟨frame.context.pair,
          [burnEventTopic, frame.context.sender.toB256, recipient.toAdr.toB256],
          encodeWords [priced.amount0, priced.amount1]⟩] := by
  dsimp only
  let priced := r.five.four.sourcePriced current
  let request0 := burnFinalRequest0 frame priced
  let frame1 := frame.beginResume request0
  let request1 := burnFinalRequest1 frame1 priced
  let frame2 := frame1.beginResume request1
  let flag := feeOnWord (Bytes.toB256 (r.five.four.three.fee.out.take 32))
  let recipient := (Sevm.dataWord sevm 4).toAdr.toB256
  obtain ⟨observed0, views0, same0, during0, rep0⟩ :=
    r.final0Views incoming rep invocation context sem image installed fork fresh
  obtain ⟨observed1, views1, same1, during1, rep1⟩ :=
    r.final1Views (frame := frame1) incoming rep0 invocation context sem image installed fork fresh
  obtain ⟨updated, event, oracle, accepted, _, finalRep, output, logs⟩ :=
    r.finishSource (frame := frame2) incoming rep1
      (by change frame.context.timestamp = _; rw [context]; rfl)
      (by change frame.context.pair = _; rw [context]; rfl)
      (by change frame.context.sender = _; rw [context]; rfl) success fork
  let finished := burnFinishedFrame frame2 updated event oracle flag recipient
    priced.amount0 priced.amount1
  have terminal := AdmittedSourceConsumes.finished (Auth := Auth) (root := root)
    (start := r.final1.call.returned) (index := 7) finished
    (encodeWords [priced.amount0, priced.amount1]) r.suffix
  have fee : priced.feeOn = decide (flag ≠ 0) :=
    feeBranchSourceFee_flag _ _ _ _ _ _
  have recipientEq : recipient.toAdr = priced.observed.locals.recipient := by
    change ((Sevm.dataWord sevm 4).toAdr.toB256).toAdr = (Sevm.dataWord sevm 4).toAdr
    exact toAdr_toB256 _
  have resumed1 := burn_resumeFinalBalance1 (frame := frame1) (priced := priced)
    (out := r.final1.out) r.final1.width fee recipientEq accepted
  change resumeSegment frame1 request1
    (.burnFinalBalance1 priced (Bytes.toB256 (r.final0.out.take 32)))
    (feeObservedResult r.final1.out) =
      .finished finished (encodeWords [priced.amount0, priced.amount1]) at resumed1
  rw [← resumed1] at terminal
  have second := AdmittedSourceConsumes.nextCall (start := r.final0.call.returned)
    (continuation := .burnFinalBalance1 priced (Bytes.toB256 (r.final0.out.take 32))) observed1
    (by rw [same1]; exact r.final1.free)
    (by simp only [burnFinalRequest1, externalStatic, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro impossible; cases impossible) during1
    (by simpa only [same1, feeObservedResult, ite_true] using terminal)
  have resumed0 := burn_resumeFinalBalance0 (frame := frame) (priced := priced) r.final0.width
  change resumeSegment frame request0 (.burnFinalBalance0 priced) (feeObservedResult r.final0.out) =
    .suspended frame1 request1 (.burnFinalBalance1 priced (Bytes.toB256 (r.final0.out.take 32))) at resumed0
  rw [← resumed0] at second
  have first := AdmittedSourceConsumes.nextCall (start := r.five.second.returned)
    (continuation := .burnFinalBalance0 priced) observed0
    (by rw [same0]; exact r.final0.free)
    (by simp only [burnFinalRequest0, externalStatic, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro impossible; cases impossible) during0
    (by simpa only [same0, feeObservedResult, ite_true] using second)
  refine ⟨updated, event, oracle, views0, views1, ?_, finalRep, output, logs⟩
  simpa only [List.append_nil, feeObservedResult, priced, request0, frame1, request1, frame2,
    flag, recipient, finished] using first

end Blanc.Lift.UniswapV2Pair
