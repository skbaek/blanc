import Blanc.Lift.UniswapV2Pair.BurnPositionalFeeSource
import Blanc.Lift.UniswapV2Pair.BurnPositionalTransferSource
import Blanc.Lift.UniswapV2Pair.MutablePositionalLockedSupply
import Blanc.Lift.UniswapV2Pair.BurnTransferTurns
import Blanc.Lift.UniswapV2Pair.SourceSlotEventsEmpty
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueExistence

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The first transfer keeps one full original queue, selected turns and
recursive child admission at its actual returned finite checkpoint. -/
structure BurnFirstMutable {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) (U : WriterKey → Prop)
    (current : Checkpoint) (invocation : List Nat) where
  observed : SourceCallAt root (r.sourceTransferFrame current invocation)
    (burnTransferRequest0 (r.sourcePriced current))
    (burnTransferResult r.transfer.returned.devm.returnData r.transfer.occurrence.slot.isSome) 3
  same : observed.call = r.transfer
  nonstatic : sevm.isStatic = false
  events : List (Log ⊕ Exec.LocatedFrame)
  turns : List MutableTurn
  checkpoint : Checkpoint
  added : List PendingLog
  rets : List ChildReturn
  queue : SourceSlotEvents observed.call sevm.currentTarget 3 events
  mappedPaths : events.filterMap Sum.getRight? = observed.paths
  mappedTurns : turns.map MutableTurn.event = events
  during : AdmittedMutableTurns LockedAuth (r.sourceTransferFrame current invocation)
    (burnTransferRequest0 (r.sourcePriced current)) 0 events (mutableTranscript turns .done)
    {complete := true, frame := {r.sourceTransferFrame current invocation with current := checkpoint},
      childReturns := rets}
  authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested
  rep : LockedRep U checkpoint.state (r.transfer.returned.devm.getStor sevm.currentTarget)
  sourceLogs : checkpoint.logs = (r.sourceTransferFrame current invocation).current.logs ++ added
  rawLogs : ∃ L : List Log,
    r.transfer.returned.devm.logs = r.transfer.occurrence.node.devm.logs ++ L ∧
    added.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L.map some

structure BurnFirstMutableH {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFourCallsH root sevm b w) (U : WriterKey → Prop)
    (current : Checkpoint) (invocation : List Nat) where
  observed : SourceCallAt root (r.sourceTransferFrame current invocation)
    (burnTransferRequest0 (r.sourcePriced current))
    (burnTransferResult r.transfer.returned.devm.returnData r.transfer.occurrence.slot.isSome) 3
  same : observed.call = r.transfer
  nonstatic : sevm.isStatic = false
  events : List (Log ⊕ Exec.LocatedFrame)
  turns : List MutableTurn
  checkpoint : Checkpoint
  added : List PendingLog
  rets : List ChildReturn
  queue : SourceSlotEvents observed.call sevm.currentTarget 3 events
  mappedPaths : events.filterMap Sum.getRight? = observed.paths
  mappedTurns : turns.map MutableTurn.event = events
  during : AdmittedMutableTurns LockedAuthH (r.sourceTransferFrame current invocation)
    (burnTransferRequest0 (r.sourcePriced current)) 0 events (mutableTranscript turns .done)
    {complete := true, frame := {r.sourceTransferFrame current invocation with current := checkpoint},
      childReturns := rets}
  authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuthH (Exec.Frame.rootDeriv located.frame) entry nested
  rep : LockedRep U checkpoint.state (r.transfer.returned.devm.getStor sevm.currentTarget)
  sourceLogs : checkpoint.logs = (r.sourceTransferFrame current invocation).current.logs ++ added
  rawLogs : ∃ L : List Log,
    r.transfer.returned.devm.logs = r.transfer.occurrence.node.devm.logs ++ L ∧
    added.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L.map some

theorem BurnThreeCallsH.root_sevm {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnThreeCallsH root sevm b w) : root.sevm = sevm :=
  (Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.initial.second.sameFrame).symm.trans r.initial.second_sevm

/-- At the modern call worlds and on a covered fork, `BurnFirstMutableH` over `r` gives the modern
`BurnFirstMutable` over `r.toCovered fork`. -/
def BurnFirstMutableH.toCoveredOf {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {r : BurnFourCallsH root sevm b BurnSchedule.modern} {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnFirstMutableH r U current invocation) :
    BurnFirstMutable (r.toCovered fork) U current invocation :=
  have rootFork : CoveredFork root.sevm.benvStat.fork := by
    rw [r.three.root_sevm]; exact fork
  { observed := h.observed,
    same := h.same,
    nonstatic := h.nonstatic,
    events := h.events,
    turns := h.turns,
    checkpoint := h.checkpoint,
    added := h.added,
    rets := h.rets,
    queue := h.queue,
    mappedPaths := h.mappedPaths,
    mappedTurns := h.mappedTurns,
    during := AdmittedMutableTurns.mono_benvStat (P := fun stat => CoveredFork stat.fork)
      (fun _ _ _ covered auth => auth.toCovered covered)
      (h.queue.located_inherits (P := fun stat => CoveredFork stat.fork) rootFork) h.during,
    authentic := h.queue.turns_mono_benvStat (P := fun stat => CoveredFork stat.fork)
      (fun _ _ _ covered auth => auth.toCovered covered) h.mappedTurns rootFork h.authentic,
    rep := h.rep,
    sourceLogs := h.sourceLogs,
    rawLogs := h.rawLogs }

theorem BurnFourCallsH.firstMutable {root : Exec.Deriv} {sevm : Sevm} {b post : Devm} {w : BurnSchedule}
    {K U : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCallsH root sevm b w)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget)) (invocation : List Nat)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys root, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (success : root.exn = .ok post) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      LockedGood U F) : Nonempty (BurnFirstMutableH r U current invocation) := by
  let frame := r.sourceTransferFrame current invocation
  let request := burnTransferRequest0 (r.sourcePriced current)
  obtain ⟨fresh, feeSub⟩ := r.three.feeUniverse current stateGas inj apart sub trace
  have inputRep := (r.payoutSource rep fresh tracked
    (resumed := burnPositionalAfterFeeFrame current invocation sevm) rfl success stateGas bal).2
  have rows := lpMintTouched_rows (sub _ tracked)
  have keysSub := Blanc.SlotFootprint.extendBy_subset feeSub rows
  have locked : frame.current.state.unlocked = 0 := by
    change (r.three.sourceFee current).state.unlocked = 0
    exact feeBranchSourceFee_unlocked {current.state with unlocked := 0} _ _ _ _ _
  have inputLocked : LockedRep U frame.current.state
      (r.transfer.occurrence.node.devm.getStor sevm.currentTarget) :=
    ⟨_, keysSub, inputRep, locked⟩
  have env : r.three.fee.occurrence.call.returned.sevm = sevm :=
    ((Cursor.parentStep_sevm r.three.fee.occurrence.call.edge).trans
      r.three.fee.occurrence.sevm_eq).trans
      ((Cursor.parentStep_sevm r.three.initial.second.edge).trans r.three.initial.second_sevm)
  obtain ⟨_, _, _, _, _, _, _, nonstatic, _⟩ :=
    r.lp_source_result (r.pricingRep rep fresh) (r.pricingFresh rep fresh tracked) success stateGas bal
  rw [env] at nonstatic
  have nonempty : (root.devm.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have inputCode : some (r.transfer.occurrence.node.devm.getCode sevm.currentTarget).toList =
      sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode r.transfer.sameFrame).2
      sevm.currentTarget nonempty]
    exact installed
  obtain ⟨paths, queue⟩ := CallOccurrenceStep.sourceSlotQueue r.transfer sevm.currentTarget 3
  obtain ⟨observed, same, _⟩ := r.transferSourceCall (frame := frame) rep rfl rfl success stateGas queue
  obtain ⟨events, turns, c, added, rets, queue, mappedPaths, mappedTurns, during,
      authentic, afterRep, sourceLogs, rawLogs⟩ :=
    locked_admitted_mutable_source_slot_turnsH inj apart sem image observed rfl
      (by change (sevm.isStatic || false) = false; rw [nonstatic]; rfl)
      (by rw [same]; exact inputCode)
      (by rw [same]; exact inputLocked)
      (by rw [same, r.transfer_sevm]; rfl)
      (by rw [same, r.transfer_sevm]; exact stateGas) (by rw [same, r.transfer_sevm]; exact bal) good
  rw [same] at afterRep rawLogs
  exact ⟨⟨observed, same, nonstatic, events, turns, c, added, rets, queue, mappedPaths, mappedTurns,
    during, authentic, afterRep, sourceLogs, rawLogs⟩⟩


/-- The second transfer starts at the checkpoint produced by the first
original mutable queue, while the priced locals stay cached. -/
def BurnFirstMutable.secondFrame {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {r : BurnFourCalls root sevm b} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (first : BurnFirstMutable r U current invocation) : Frame :=
  {r.sourceTransferFrame current invocation with current := first.checkpoint}.beginResume
    (burnTransferRequest0 (r.sourcePriced current))

def BurnFirstMutableH.secondFrame {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    {r : BurnFourCallsH root sevm b w} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (first : BurnFirstMutableH r U current invocation) : Frame :=
  {r.sourceTransferFrame current invocation with current := first.checkpoint}.beginResume
    (burnTransferRequest0 (r.sourcePriced current))

structure BurnSecondMutable {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat}
    (first : BurnFirstMutable r.four U current invocation) where
  observed : SourceCallAt root first.secondFrame
    (burnTransferRequest1 (r.four.sourcePriced current))
    (burnTransferResult r.second.returned.devm.returnData r.second.occurrence.slot.isSome) 4
  same : observed.call = r.second
  events : List (Log ⊕ Exec.LocatedFrame)
  turns : List MutableTurn
  checkpoint : Checkpoint
  added : List PendingLog
  rets : List ChildReturn
  queue : SourceSlotEvents observed.call sevm.currentTarget 4 events
  mappedPaths : events.filterMap Sum.getRight? = observed.paths
  mappedTurns : turns.map MutableTurn.event = events
  during : AdmittedMutableTurns LockedAuth first.secondFrame
    (burnTransferRequest1 (r.four.sourcePriced current)) 0 events (mutableTranscript turns .done)
    {complete := true, frame := {first.secondFrame with current := checkpoint}, childReturns := rets}
  authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested
  rep : LockedRep U checkpoint.state (r.second.returned.devm.getStor sevm.currentTarget)
  sourceLogs : checkpoint.logs = first.checkpoint.logs ++ added
  rawLogs : ∃ L : List Log,
    r.second.returned.devm.logs = r.second.occurrence.node.devm.logs ++ L ∧
    added.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L.map some

structure BurnSecondMutableH {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFiveCallsH root sevm b w) {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat}
    (first : BurnFirstMutableH r.four U current invocation) where
  observed : SourceCallAt root first.secondFrame
    (burnTransferRequest1 (r.four.sourcePriced current))
    (burnTransferResult r.second.returned.devm.returnData r.second.occurrence.slot.isSome) 4
  same : observed.call = r.second
  events : List (Log ⊕ Exec.LocatedFrame)
  turns : List MutableTurn
  checkpoint : Checkpoint
  added : List PendingLog
  rets : List ChildReturn
  queue : SourceSlotEvents observed.call sevm.currentTarget 4 events
  mappedPaths : events.filterMap Sum.getRight? = observed.paths
  mappedTurns : turns.map MutableTurn.event = events
  during : AdmittedMutableTurns LockedAuthH first.secondFrame
    (burnTransferRequest1 (r.four.sourcePriced current)) 0 events (mutableTranscript turns .done)
    {complete := true, frame := {first.secondFrame with current := checkpoint}, childReturns := rets}
  authentic : ∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuthH (Exec.Frame.rootDeriv located.frame) entry nested
  rep : LockedRep U checkpoint.state (r.second.returned.devm.getStor sevm.currentTarget)
  sourceLogs : checkpoint.logs = first.checkpoint.logs ++ added
  rawLogs : ∃ L : List Log,
    r.second.returned.devm.logs = r.second.occurrence.node.devm.logs ++ L ∧
    added.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L.map some

/-- At the modern call worlds and on a covered fork, `BurnSecondMutableH` over `r` gives the modern
`BurnSecondMutable` over `r.toCovered fork`. -/
def BurnSecondMutableH.toCoveredOf {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {r : BurnFiveCallsH root sevm b BurnSchedule.modern} {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    {first : BurnFirstMutableH r.four U current invocation}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnSecondMutableH r first) :
    BurnSecondMutable (r.toCovered fork) (first.toCoveredOf fork) :=
  have rootFork : CoveredFork root.sevm.benvStat.fork := by
    rw [r.four.three.root_sevm]; exact fork
  { observed := h.observed,
    same := h.same,
    events := h.events,
    turns := h.turns,
    checkpoint := h.checkpoint,
    added := h.added,
    rets := h.rets,
    queue := h.queue,
    mappedPaths := h.mappedPaths,
    mappedTurns := h.mappedTurns,
    during := AdmittedMutableTurns.mono_benvStat (P := fun stat => CoveredFork stat.fork)
      (fun _ _ _ covered auth => auth.toCovered covered)
      (h.queue.located_inherits (P := fun stat => CoveredFork stat.fork) rootFork) h.during,
    authentic := h.queue.turns_mono_benvStat (P := fun stat => CoveredFork stat.fork)
      (fun _ _ _ covered auth => auth.toCovered covered) h.mappedTurns rootFork h.authentic,
    rep := h.rep,
    sourceLogs := h.sourceLogs,
    rawLogs := h.rawLogs }

theorem BurnFiveCallsH.secondMutable {root : Exec.Deriv} {sevm : Sevm} {b post : Devm} {w : BurnSchedule}
    {K U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (r : BurnFiveCallsH root sevm b w) (first : BurnFirstMutableH r.four U current invocation)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (success : root.exn = .ok post) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      LockedGood U F) : Nonempty (BurnSecondMutableH r first) := by
  let frame := first.secondFrame
  have inputRep : LockedRep U frame.current.state
      (r.second.occurrence.node.devm.getStor sevm.currentTarget) := by
    rw [r.input]
    simp only [St_getStor]
    exact first.rep
  have nonempty : (root.devm.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have inputCode : some (r.second.occurrence.node.devm.getCode sevm.currentTarget).toList =
      sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode r.second.sameFrame).2
      sevm.currentTarget nonempty]
    exact installed
  obtain ⟨paths, queue⟩ := CallOccurrenceStep.sourceSlotQueue r.second sevm.currentTarget 4
  obtain ⟨observed, same, _⟩ := r.secondTransferSourceCall (frame := frame) rep rfl rfl success stateGas queue
  obtain ⟨events, turns, c, added, rets, queue, mappedPaths, mappedTurns, during,
      authentic, afterRep, sourceLogs, rawLogs⟩ :=
    locked_admitted_mutable_source_slot_turnsH inj apart sem image observed rfl
      (by change (sevm.isStatic || false) = false; rw [first.nonstatic]; rfl)
      (by rw [same]; exact inputCode)
      (by rw [same]; exact inputRep)
      (by rw [same, r.sevm_eq]; rfl)
      (by rw [same, r.sevm_eq]; exact stateGas) (by rw [same, r.sevm_eq]; exact bal) good
  rw [same] at afterRep rawLogs
  exact ⟨⟨observed, same, events, turns, c, added, rets, queue, mappedPaths, mappedTurns,
    during, authentic, afterRep, sourceLogs, rawLogs⟩⟩


/-- The final queries resume the same second mutable checkpoint. -/
def BurnSecondMutable.finalFrame {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {r : BurnFiveCalls root sevm b} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {first : BurnFirstMutable r.four U current invocation}
    (second : BurnSecondMutable r first) : Frame :=
  {first.secondFrame with current := second.checkpoint}.beginResume
    (burnTransferRequest1 (r.four.sourcePriced current))

def BurnSecondMutableH.finalFrame {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    {r : BurnFiveCallsH root sevm b w} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {first : BurnFirstMutableH r.four U current invocation}
    (second : BurnSecondMutableH r first) : Frame :=
  {first.secondFrame with current := second.checkpoint}.beginResume
    (burnTransferRequest1 (r.four.sourcePriced current))

theorem BurnFirstMutableH.consume {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    {r : BurnFiveCallsH root sevm b w} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (first : BurnFirstMutableH r.four U current invocation)
    {tail : Transcript} {out : RunResult}
    (rest : AdmittedSourceConsumes LockedAuthH root r.four.transfer.returned 4
      (.suspended first.secondFrame (burnTransferRequest1 (r.four.sourcePriced current))
        (.burnTransfer1 (r.four.sourcePriced current))) tail out) :
    AdmittedSourceConsumes LockedAuthH root r.four.three.fee.occurrence.call.returned 3
      (.suspended (r.four.sourceTransferFrame current invocation)
        (burnTransferRequest0 (r.four.sourcePriced current)) (.burnTransfer0 (r.four.sourcePriced current)))
      (.next (burnTransferResult r.four.transfer.returned.devm.returnData
        r.four.transfer.occurrence.slot.isSome) (mutableTranscript first.turns .done) tail)
      {out with childReturns := first.rets ++ out.childReturns} := by
  have resumed := burn_resumeTransfer0 (frame :=
    {r.four.sourceTransferFrame current invocation with current := first.checkpoint})
    (priced := r.four.sourcePriced current) (entered := r.four.transfer.occurrence.slot.isSome)
    (by
      rcases r.first_accepted with empty | ⟨long, nonzero⟩
      · exact Or.inl empty
      · exact Or.inr ⟨long, by
          simpa only [List.sliceD, List.drop_zero, List.takeD_eq_take _ long] using nonzero⟩)
  dsimp only [BurnFirstMutableH.secondFrame] at rest
  rw [← resumed] at rest
  exact AdmittedSourceConsumes.nextMutableCall first.observed
    (by rw [first.same]; exact r.four.transfer_gap) first.queue rfl
    (first.observed.noCodeMutableTranscript rfl first.queue first.mappedTurns)
    first.mappedTurns first.authentic first.during
    (by simpa only [first.same, burnTransferResult, ite_true] using rest)

theorem BurnSecondMutableH.consume {root : Exec.Deriv} {sevm : Sevm} {b post : Devm} {w : BurnSchedule}
    {r : BurnFiveCallsH root sevm b w} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {first : BurnFirstMutableH r.four U current invocation}
    (second : BurnSecondMutableH r first) (success : root.exn = .ok post)
    (stateGas : sevm.benvStat.rules.stateGas = none)
    {tail : Transcript} {out : RunResult}
    (rest : AdmittedSourceConsumes LockedAuthH root r.second.returned 5
      (.suspended second.finalFrame (burnFinalRequest0 second.finalFrame (r.four.sourcePriced current))
        (.burnFinalBalance0 (r.four.sourcePriced current))) tail out) :
    AdmittedSourceConsumes LockedAuthH root r.four.transfer.returned 4
      (.suspended first.secondFrame (burnTransferRequest1 (r.four.sourcePriced current))
        (.burnTransfer1 (r.four.sourcePriced current)))
      (.next (burnTransferResult r.second.returned.devm.returnData r.second.occurrence.slot.isSome)
        (mutableTranscript second.turns .done) tail)
      {out with childReturns := second.rets ++ out.childReturns} := by
  have accepted := (r.actualReply success stateGas).2.2.2.2.1
  have resumed := burn_resumeTransfer1 (frame := {first.secondFrame with current := second.checkpoint})
    (priced := r.four.sourcePriced current) (entered := r.second.occurrence.slot.isSome)
    (by
      rcases accepted with empty | ⟨long, nonzero⟩
      · exact Or.inl empty
      · exact Or.inr ⟨long, by
          simpa only [List.sliceD, List.drop_zero, List.takeD_eq_take _ long] using nonzero⟩)
  dsimp only [BurnSecondMutableH.finalFrame] at rest
  rw [← resumed] at rest
  exact AdmittedSourceConsumes.nextMutableCall second.observed
    (by rw [second.same]; exact r.gap) second.queue rfl
    (second.observed.noCodeMutableTranscript rfl second.queue second.mappedTurns)
    second.mappedTurns second.authentic second.during
    (by simpa only [second.same, burnTransferResult, ite_true] using rest)

end Blanc.Lift.UniswapV2Pair
