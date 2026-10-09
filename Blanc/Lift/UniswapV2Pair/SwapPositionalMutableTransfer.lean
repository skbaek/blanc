import Blanc.Lift.UniswapV2Pair.SwapSourceOccurrenceTransfer
import Blanc.Lift.UniswapV2Pair.MutablePositionalLockedSupply
import Blanc.Lift.UniswapV2Pair.SourceSlotEventsEmpty
import Blanc.Lift.CursorOccurrenceRoots

/-! The same actual Swap transfer slot supplies recursively admitted mutable turns. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- One exact transfer's full event queue, admitted selected children and resulting
finite source state remain tied to the same physical returned parent. -/
structure SwapTransferMutable {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {p amount toWord token rho : B256}
    {caller : SFunc} {K : List SFunc}
    (r : SwapTransferOccurrence root start b L M p amount toWord token rho caller K)
    (U : WriterKey → Prop) (ctx : Context) (current : Checkpoint) (base : Devm)
    (frame : Frame) (site : CallSite) (index : Nat) where
  observed : SourceCallAt root frame
    (requestFor site token.toAdr (.transfer toWord.toAdr amount))
    (swapObservedTransferReply r.step.returned.devm.returnData r.step.occurrence.slot.isSome) index
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
    (requestFor site token.toAdr (.transfer toWord.toAdr amount)) 0 events
    (mutableTranscript turns .done)
    {complete := true, frame := {frame with current := checkpoint}, childReturns := rets}
  authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested
  invariant : SwapFrontState U root.sevm.currentTarget ctx current base
    {frame with current := checkpoint} r.step.returned.devm

/-- The shared locked supply consumes this transfer's SAME original complete slot,
retaining recursive admission and exact located-entry authentication. -/
theorem swap_transfer_mutable {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {p amount toWord token rho : B256}
    {caller : SFunc} {K : List SFunc} {U : WriterKey → Prop}
    {ctx : Context} {current : Checkpoint} {base : Devm} {frame : Frame}
    (r : SwapTransferOccurrence root start b L M p amount toWord token rho caller K)
    (site : CallSite) (index : Nat) (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (base.getCode root.sevm.currentTarget).toList = sem.image)
    (inv : SwapFrontState U root.sevm.currentTarget ctx current base frame b)
    (pair : ctx.pair = root.sevm.currentTarget) (time : ctx.timestamp = root.sevm.benvStat.time)
    (nonstatic : ctx.isStatic = false) (rootNonstatic : root.sevm.isStatic = false)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → LockedGood U F) :
    Nonempty (SwapTransferMutable r U ctx current base frame site index) := by
  have env : start.sevm = root.sevm := r.sevmEq.symm.trans
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.step.sameFrame)
  obtain ⟨observed, same⟩ := r.sourceCall frame site index
    (by rw [inv.context, env, nonstatic, rootNonstatic])
    (by rw [inv.context, env]; exact pair) (by rw [env]; exact fork)
  have pairEq : frame.context.pair = root.sevm.currentTarget := inv.context ▸ pair
  have preCode : r.step.occurrence.node.devm.getCode root.sevm.currentTarget =
      base.getCode root.sevm.currentTarget := by
    rw [r.input]
    simpa only [St, Devm.getCode_setMach] using inv.code
  have preRep : LockedRep U frame.current.state
      (r.step.occurrence.node.devm.getStor root.sevm.currentTarget) := by
    rw [r.input]
    simpa only [St, Devm.getStor, Devm.getAcct, Devm.setMach_state] using inv.rep
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
    simp only [St, Devm.setMach_logs]
    rw [oldLogs, List.append_assoc]
  · rw [List.map_append, List.map_append, oldImages, newImages]

def swapTransferPhaseRequest (second : Bool) (locals : SwapLocals) : Request :=
  requestFor (if second then .swapTransfer1 else .swapTransfer0)
    (if second then locals.token1 else locals.token0)
    (.transfer locals.recipient (if second then locals.amount1Out else locals.amount0Out))

def swapTransferPhaseStart (second : Bool) (frame : Frame) (locals : SwapLocals) : SegmentResult :=
  if second then frame.afterSwapTransfer0 locals
  else if locals.amount0Out > 0 then
    .suspended frame (swapTransferPhaseRequest false locals) (.swapTransfer0 locals)
  else frame.afterSwapTransfer0 locals

def swapTransferPhaseEnd (second : Bool) (frame : Frame) (locals : SwapLocals) : SegmentResult :=
  if second then frame.afterSwapTransfer1 locals else frame.afterSwapTransfer0 locals

/-- Both optional transfers compose their SAME admitted queue and resumed frame;
only an executed instruction advances the original source index. -/
theorem swap_optional_transfer_admitted {root start : Exec.Deriv} {b : Devm}
    {L : List B256} {M : Mem} {p toWord token rho : B256} {caller : SFunc} {K : List SFunc}
    {U : WriterKey → Prop} {ctx : Context} {current : Checkpoint} {base : Devm} {frame : Frame}
    {locals : SwapLocals} (second : Bool)
    (opt : SwapOptionalTransfer root start b L M p
      (if second then locals.amount1Out else locals.amount0Out) toWord token rho caller K)
    (tokenEq : token.toAdr = if second then locals.token1 else locals.token0)
    (recipientEq : toWord.toAdr = locals.recipient)
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
        AdmittedSourceConsumes LockedAuth root opt.next
          (index + if (if second then locals.amount1Out else locals.amount0Out) = 0 then 0 else 1)
          (swapTransferPhaseEnd second nextFrame locals) tail out →
        AdmittedSourceConsumes LockedAuth root start index
          (swapTransferPhaseStart second frame locals) (T tail)
          {out with childReturns := rets ++ out.childReturns} := by
  rcases opt.choice with ⟨zero, next, world, _, _⟩ |
    ⟨actual, nonzero, next, world, _, _⟩
  · refine ⟨frame, id, [], ?_, ?_⟩
    · rw [world]; exact inv
    · intro tail out rest
      have skip : swapTransferPhaseStart second frame locals =
          swapTransferPhaseEnd second frame locals := by
        cases second with
        | false => simp only [Bool.false_eq_true, ite_false] at zero
                   simp only [swapTransferPhaseStart, swapTransferPhaseEnd, Bool.false_eq_true,
                     ite_false, zero, show ¬ ((0 : B256) > 0) from by decide]
        | true => simp only [ite_true] at zero
                  simp only [swapTransferPhaseStart, swapTransferPhaseEnd, ite_true,
                    Frame.afterSwapTransfer0, zero, show ¬ ((0 : B256) > 0) from by decide, ite_false]
      rw [next, ite_eq_left zero, Nat.add_zero] at rest
      rw [skip]
      exact rest
  · obtain ⟨selected⟩ := swap_transfer_mutable actual
      (if second then .swapTransfer1 else .swapTransfer0) index inj apart sem image installed
      inv pair time nonstatic rootNonstatic fork good
    let request := swapTransferPhaseRequest second locals
    let nextFrame : Frame := ({frame with current := selected.checkpoint} : Frame).beginResume request
    have requestEq : requestFor (if second then .swapTransfer1 else .swapTransfer0)
        token.toAdr (.transfer toWord.toAdr (if second then locals.amount1Out else locals.amount0Out)) =
        request := by rw [tokenEq, recipientEq]; rfl
    have source : ∃ observed : SourceCallAt root frame request
        (swapObservedTransferReply actual.step.returned.devm.returnData actual.step.occurrence.slot.isSome) index,
        observed.call = actual.step := by
      have packet : ∃ observed : SourceCallAt root frame
          (requestFor (if second then .swapTransfer1 else .swapTransfer0) token.toAdr
            (.transfer toWord.toAdr (if second then locals.amount1Out else locals.amount0Out)))
          (swapObservedTransferReply actual.step.returned.devm.returnData actual.step.occurrence.slot.isSome) index,
          observed.call = actual.step := ⟨selected.observed, selected.same⟩
      rw [tokenEq, recipientEq] at packet
      exact packet
    obtain ⟨observed, obsSame⟩ := source
    have queue : SourceSlotEvents observed.call frame.context.pair index selected.events := by
      rw [obsSame, ← selected.same]
      exact selected.queue
    have mapped := selected.mappedTurns
    have during := selected.during
    rw [requestEq] at during
    have suspend : swapTransferPhaseStart second frame locals =
        .suspended frame request (if second then .swapTransfer1 locals else .swapTransfer0 locals) := by
      cases second with
      | false => simp only [Bool.false_eq_true, ite_false] at nonzero
                 simp only [swapTransferPhaseStart, Bool.false_eq_true, ite_false,
                   swap_pos_of_ne nonzero, ite_true, request, swapTransferPhaseRequest]
      | true => simp only [ite_true] at nonzero
                simp only [swapTransferPhaseStart, ite_true, Frame.afterSwapTransfer0,
                  swap_pos_of_ne nonzero, ite_true, Frame.suspend, request, swapTransferPhaseRequest]
    refine ⟨nextFrame, fun tail => .next
      (swapObservedTransferReply actual.step.returned.devm.returnData actual.step.occurrence.slot.isSome)
      (mutableTranscript selected.turns .done) tail, selected.rets, ?_, ?_⟩
    · rw [world]
      exact selected.invariant.beginResume request
    · intro tail out rest
      rw [next, ite_eq_right nonzero] at rest
      rw [suspend]
      refine AdmittedSourceConsumes.nextMutableCall observed ?_ queue
        (by change (false && _) = false; rfl)
        (fun missing => observed.noCodeMutableTranscript rfl queue mapped missing)
        mapped selected.authentic during ?_
      · rw [obsSame]; exact actual.gap
      · change AdmittedSourceConsumes LockedAuth root observed.call.returned (index + 1)
          (resumeSegment {frame with current := selected.checkpoint} request
            (if second then .swapTransfer1 locals else .swapTransfer0 locals)
            (swapObservedTransferReply actual.step.returned.devm.returnData actual.step.occurrence.slot.isSome))
          tail out
        rw [obsSame]
        have resumed := swap_resume_observed_transfer
          (frame := ({frame with current := selected.checkpoint} : Frame))
          (locals := locals) second actual.step.occurrence.slot.isSome actual.accepted
        exact Eq.mpr (congrArg (fun segment => AdmittedSourceConsumes LockedAuth root
          actual.step.returned (index + 1) segment tail out) resumed) rest

end Blanc.Lift.UniswapV2Pair
