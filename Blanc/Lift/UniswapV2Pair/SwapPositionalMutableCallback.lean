import Blanc.Lift.UniswapV2Pair.SwapSourceOccurrenceCallback
import Blanc.Lift.UniswapV2Pair.SwapPositionalSourcePrefix

/-! The guarded callback consumes its own full recursively admitted mutable queue. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The exact guarded callback retains its full events, same admitted children,
checkpoint, finite representation and source/raw log images. -/
structure SwapCallbackMutable {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {q toWord a0 a1 len dataStart : B256} {K : List SFunc}
    (r : SwapCallbackOccurrence root start b L M q toWord a0 a1 len dataStart K)
    (U : WriterKey → Prop) (ctx : Context) (current : Checkpoint) (base : Devm)
    (frame : Frame) (index : Nat) where
  observed : SourceCallAt root frame
    (requestFor .swapCallback toWord.toAdr (.callback start.sevm.caller a0 a1
      (start.sevm.data.sliceD dataStart.toNat len.toNat 0)))
    (swapCallbackReply r.step.returned.devm.returnData) index
  same : observed.call = r.step
  events : List (Log ⊕ Exec.LocatedFrame)
  turns : List MutableTurn
  checkpoint : Checkpoint
  added : List PendingLog
  rets : List ChildReturn
  queue : SourceSlotEvents observed.call frame.context.pair index events
  mappedPaths : events.filterMap Sum.getRight? = observed.paths
  mappedTurns : turns.map MutableTurn.event = events
  during : AdmittedMutableTurns LockedAuth frame
    (requestFor .swapCallback toWord.toAdr (.callback start.sevm.caller a0 a1
      (start.sevm.data.sliceD dataStart.toNat len.toNat 0))) 0 events
    (mutableTranscript turns .done)
    {complete := true, frame := {frame with current := checkpoint}, childReturns := rets}
  authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested
  invariant : SwapFrontState U root.sevm.currentTarget ctx current base
    {frame with current := checkpoint} r.step.returned.devm

/-- The shared locked fold supplies the SAME guarded callback event queue. -/
theorem swap_callback_mutable {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {q toWord a0 a1 len dataStart : B256} {K : List SFunc}
    {U : WriterKey → Prop} {ctx : Context} {current : Checkpoint} {base : Devm} {frame : Frame}
    (r : SwapCallbackOccurrence root start b L M q toWord a0 a1 len dataStart K)
    (index : Nat) (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (base.getCode root.sevm.currentTarget).toList = sem.image)
    (inv : SwapFrontState U root.sevm.currentTarget ctx current base frame b)
    (pair : ctx.pair = root.sevm.currentTarget) (time : ctx.timestamp = root.sevm.benvStat.time)
    (nonstatic : ctx.isStatic = false) (rootNonstatic : root.sevm.isStatic = false)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → LockedGood U F) :
    Nonempty (SwapCallbackMutable r U ctx current base frame index) := by
  have env : start.sevm = root.sevm := r.sevmEq.symm.trans
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.step.sameFrame)
  obtain ⟨observed, same⟩ := r.sourceCall frame index
    (by rw [inv.context, env, nonstatic, rootNonstatic])
    (by rw [inv.context, env]; exact pair) (by rw [env]; exact fork)
  have pairEq : frame.context.pair = root.sevm.currentTarget := inv.context ▸ pair
  have preCode : r.step.occurrence.node.devm.getCode root.sevm.currentTarget =
      base.getCode root.sevm.currentTarget := by
    rw [r.input]
    change (temporalAccountAccessBase b
      (0xffffffffffffffffffffffffffffffffffffffff &&& toWord).toAdr).getCode _ = _
    rw [Blanc.Lift.temporalAccountAccessBase_getCode]
    exact inv.code
  have preRep : LockedRep U frame.current.state
      (r.step.occurrence.node.devm.getStor root.sevm.currentTarget) := by
    rw [r.input]
    change LockedRep U frame.current.state ((temporalAccountAccessBase b
      (0xffffffffffffffffffffffffffffffffffffffff &&& toWord).toAdr).getStor _)
    rw [Blanc.Lift.temporalAccountAccessBase_getStor]
    exact inv.rep
  obtain ⟨events, turns, c, added, rets, queue, mappedPaths, mappedTurns, during,
    authentic, afterRep, sourceLogs, rawLogs⟩ :=
    locked_admitted_mutable_source_slot_turns inj apart sem image observed pairEq
      (by change (frame.context.isStatic || false) = false; rw [inv.context, nonstatic]; rfl)
      (by rw [same, preCode]; exact installed)
      (by rw [same]; exact preRep)
      (by rw [same, r.sevmEq, env, inv.context]; exact time)
      (by rw [same, r.sevmEq, env]; exact fork) good
  rw [same] at afterRep rawLogs
  have nonemptyCode : (r.step.occurrence.node.devm.getCode root.sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (by rw [preCode] at empty; rw [← installed, empty]) rfl
  obtain ⟨oldAdded, oldRaw, oldSource, oldLogs, oldImages⟩ := inv.logs
  obtain ⟨newRaw, newLogs, newImages⟩ := rawLogs
  refine ⟨⟨observed, same, events, turns, c, added, rets, queue, mappedPaths, mappedTurns,
    during, authentic, inv.context, afterRep, ?_, r.output.trans inv.output,
    ⟨oldAdded ++ added, oldRaw ++ newRaw, ?_, ?_, ?_⟩, inv.checkpoint⟩⟩
  · rw [StepIn.codePreserve r.step.toStepIn _ nonemptyCode, preCode]
  · rw [sourceLogs, oldSource, List.append_assoc]
  · rw [newLogs, r.input]
    simp only [St, Devm.setMach_logs, temporalAccountAccessBase_logs]
    rw [oldLogs, List.append_assoc]
  · rw [List.map_append, List.map_append, oldImages, newImages]

def swapCallbackPhaseRequest (frame : Frame) (locals : SwapLocals) : Request :=
  requestFor .swapCallback locals.recipient
    (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)

def swapBalancePhaseStart (frame : Frame) (locals : SwapLocals) : SegmentResult :=
  .suspended frame (requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair))
    (.swapBalance0 locals)

/-- Optional callback admission shares the same selected children and result;
the skipped branch consumes no instruction or source index. -/
theorem swap_optional_callback_admitted {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {q toWord len dataStart : B256} {K : List SFunc}
    {U : WriterKey → Prop} {ctx : Context} {current : Checkpoint} {base : Devm}
    {frame : Frame} {locals : SwapLocals}
    (opt : SwapOptionalCallback root start b L M q toWord locals.amount0Out locals.amount1Out
      len dataStart K)
    (recipientEq : toWord.toAdr = locals.recipient)
    (dataEq : locals.data = start.sevm.data.sliceD dataStart.toNat len.toNat 0)
    (senderEq : ctx.sender = start.sevm.caller)
    (index : Nat) (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (base.getCode root.sevm.currentTarget).toList = sem.image)
    (inv : SwapFrontState U root.sevm.currentTarget ctx current base frame b)
    (pair : ctx.pair = root.sevm.currentTarget) (time : ctx.timestamp = root.sevm.benvStat.time)
    (nonstatic : ctx.isStatic = false) (rootNonstatic : root.sevm.isStatic = false)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → LockedGood U F) :
    ∃ (nextFrame : Frame) (T : Transcript → Transcript) (rets : List ChildReturn),
      SwapFrontState U root.sevm.currentTarget ctx current base nextFrame opt.world ∧
      ∀ tail out,
        AdmittedSourceConsumes LockedAuth root opt.next (index + if len = 0 then 0 else 1)
          (swapBalancePhaseStart nextFrame locals) tail out →
        AdmittedSourceConsumes LockedAuth root start index (frame.afterSwapTransfer1 locals)
          (T tail) {out with childReturns := rets ++ out.childReturns} := by
  have dataLen : locals.data.length = len.toNat := by
    rw [dataEq]
    exact List.length_sliceD _ _ _ _
  rcases opt.choice with ⟨zero, next, world, _⟩ | ⟨actual, nonzero, next, world, _⟩
  · have empty : ¬ locals.data.length > 0 := by rw [dataLen, zero]; decide
    have skip : frame.afterSwapTransfer1 locals = swapBalancePhaseStart frame locals := by
      simp only [Frame.afterSwapTransfer1, empty, ite_false, Frame.suspend, swapBalancePhaseStart]
    refine ⟨frame, id, [], ?_, ?_⟩
    · rw [world]; exact inv
    · intro tail out rest
      rw [next, ite_eq_left zero, Nat.add_zero] at rest
      rw [skip]
      exact rest
  · obtain ⟨selected⟩ := swap_callback_mutable actual index inj apart sem image installed
      inv pair time nonstatic rootNonstatic fork good
    let request := swapCallbackPhaseRequest frame locals
    let nextFrame : Frame := ({frame with current := selected.checkpoint} : Frame).beginResume request
    have callerEq : start.sevm.caller = frame.context.sender := by rw [inv.context, senderEq]
    have requestEq : requestFor .swapCallback toWord.toAdr (.callback start.sevm.caller
        locals.amount0Out locals.amount1Out
        (start.sevm.data.sliceD dataStart.toNat len.toNat 0)) = request := by
      rw [recipientEq, callerEq, ← dataEq]; rfl
    have source : ∃ observed : SourceCallAt root frame request
        (swapCallbackReply actual.step.returned.devm.returnData) index,
        observed.call = actual.step := by
      have packet : ∃ observed : SourceCallAt root frame
          (requestFor .swapCallback toWord.toAdr (.callback start.sevm.caller
            locals.amount0Out locals.amount1Out
            (start.sevm.data.sliceD dataStart.toNat len.toNat 0)))
          (swapCallbackReply actual.step.returned.devm.returnData) index,
          observed.call = actual.step := ⟨selected.observed, selected.same⟩
      rw [recipientEq, callerEq, ← dataEq] at packet
      exact packet
    obtain ⟨observed, obsSame⟩ := source
    have queue : SourceSlotEvents observed.call frame.context.pair index selected.events := by
      rw [obsSame, ← selected.same]; exact selected.queue
    have during := selected.during
    rw [requestEq] at during
    have present : locals.data.length > 0 := by
      rw [dataLen]
      have ne : len.toNat ≠ 0 := fun e => nonzero (B256.toNat_inj _ _ (e.trans rfl))
      omega
    have suspend : frame.afterSwapTransfer1 locals = .suspended frame request (.swapCallback locals) := by
      simp only [Frame.afterSwapTransfer1, present, ite_true, Frame.suspend,
        request, swapCallbackPhaseRequest]
    refine ⟨nextFrame, fun tail => .next (swapCallbackReply actual.step.returned.devm.returnData)
      (mutableTranscript selected.turns .done) tail, selected.rets, ?_, ?_⟩
    · rw [world]; exact selected.invariant.beginResume request
    · intro tail out rest
      rw [next, ite_eq_right nonzero] at rest
      rw [suspend]
      refine AdmittedSourceConsumes.nextMutableCall observed ?_ queue rfl
        (fun impossible => by cases impossible) selected.mappedTurns selected.authentic during ?_
      · rw [obsSame]; exact actual.gap
      · change AdmittedSourceConsumes LockedAuth root observed.call.returned (index + 1)
          (resumeSegment {frame with current := selected.checkpoint} request (.swapCallback locals)
            (swapCallbackReply actual.step.returned.devm.returnData)) tail out
        rw [obsSame]
        have resumed := swap_resume_callback
          (frame := ({frame with current := selected.checkpoint} : Frame)) (locals := locals)
          (out := actual.step.returned.devm.returnData)
        exact Eq.mpr (congrArg (fun segment => AdmittedSourceConsumes LockedAuth root
          actual.step.returned (index + 1) segment tail out) resumed) rest

/-- All optional mutable calls compose from the original source entry, on the
same physical chain and the same evolving admitted source checkpoint. -/
theorem swap_source_callbacks {root : Exec.Deriv} {b : Devm}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (r : SwapCallbacks root root.sevm b)
    (entryFacts : SwapSourcePrefix U current invocation root.sevm b)
    (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode root.sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → LockedGood U F) :
    let locals := swapFrontLocals root.sevm current.state
    let count0 := if swapAmount0Out root.sevm = 0 then 0 else 1
    let count1 := if swapAmount1Out root.sevm = 0 then 0 else 1
    let countC := if swapDataLength root.sevm = 0 then 0 else 1
    ∃ (frame : Frame) (T : Transcript → Transcript) (rets : List ChildReturn),
      SwapFrontState U root.sevm.currentTarget (writerContext root.sevm invocation)
        current b frame r.callback.world ∧
      ∀ tail out,
        AdmittedSourceConsumes LockedAuth root r.callback.next (count0 + count1 + countC)
          (swapBalancePhaseStart frame locals) tail out →
        AdmittedSourceConsumes LockedAuth root root 0
          (startTyped current (writerContext root.sevm invocation) (swapDecodedEntry root.sevm))
          (T tail) {out with childReturns := rets ++ out.childReturns} := by
  intro locals count0 count1 countC
  obtain ⟨F, T, R, inv, reach⟩ := swap_source_transfers r.transfers entryFacts inj apart
    sem image installed fork good
  have env : r.transfers.second.next.sevm = root.sevm :=
    r.transfers.second.sevmEq.trans r.transfers.first.sevmEq
  have recipient : (swapRecipientWord root.sevm).toAdr = locals.recipient := by
    rw [swapRecipientWord_eq, toAdr_toB256]; rfl
  have data : locals.data = r.transfers.second.next.sevm.data.sliceD
      (swapDataStart root.sevm).toNat (swapDataLength root.sevm).toNat 0 := by rw [env]; rfl
  have sender : (writerContext root.sevm invocation).sender = r.transfers.second.next.sevm.caller := by
    rw [env]; rfl
  obtain ⟨FC, TC, RC, invC, reachC⟩ := swap_optional_callback_admitted (locals := locals)
    r.callback recipient data sender (count0 + count1) inj apart sem image installed inv
    rfl rfl entryFacts.nonstatic entryFacts.nonstatic fork good
  refine ⟨FC, fun tail => T (TC tail), R ++ RC, invC, ?_⟩
  intro tail out rest
  have callback := reachC tail out rest
  have prefixRun := reach (TC tail) _ callback
  simpa only [List.append_assoc] using prefixRun

end Blanc.Lift.UniswapV2Pair
