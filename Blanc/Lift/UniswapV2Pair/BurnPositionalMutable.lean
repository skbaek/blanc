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

/-- The actual first CALL supplies its queue and recursive admitted children;
its finite input is derived from the same fee and LP result. -/
theorem BurnFourCalls.firstMutable {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K U : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget)) (invocation : List Nat)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys root, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      LockedGood U F) : Nonempty (BurnFirstMutable r U current invocation) := by
  let frame := r.sourceTransferFrame current invocation
  let request := burnTransferRequest0 (r.sourcePriced current)
  obtain ⟨fresh, feeSub⟩ := r.three.feeUniverse current fork inj apart sub trace
  have inputRep := (r.payoutSource rep fresh tracked
    (resumed := burnPositionalAfterFeeFrame current invocation sevm) rfl success fork).2
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
    r.lp_source_result (r.pricingRep rep fresh) (r.pricingFresh rep fresh tracked) success fork
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
  obtain ⟨observed, same, _⟩ := r.transferSourceCall (frame := frame) rep rfl rfl success fork queue
  obtain ⟨events, turns, c, added, rets, queue, mappedPaths, mappedTurns, during,
      authentic, afterRep, sourceLogs, rawLogs⟩ :=
    locked_admitted_mutable_source_slot_turns inj apart sem image observed rfl
      (by change (sevm.isStatic || false) = false; rw [nonstatic]; rfl)
      (by rw [same]; exact inputCode)
      (by rw [same]; exact inputLocked)
      (by rw [same, r.transfer_sevm]; rfl)
      (by rw [same, r.transfer_sevm]; exact fork) good
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

/-- The first actual returned world is the physical and finite input of the
second CALL's same full event queue and recursively admitted child fold. -/
theorem BurnFiveCalls.secondMutable {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat}
    (r : BurnFiveCalls root sevm b) (first : BurnFirstMutable r.four U current invocation)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      LockedGood U F) : Nonempty (BurnSecondMutable r first) := by
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
  obtain ⟨observed, same, _⟩ := r.secondTransferSourceCall (frame := frame) rep rfl rfl success fork queue
  obtain ⟨events, turns, c, added, rets, queue, mappedPaths, mappedTurns, during,
      authentic, afterRep, sourceLogs, rawLogs⟩ :=
    locked_admitted_mutable_source_slot_turns inj apart sem image observed rfl
      (by change (sevm.isStatic || false) = false; rw [first.nonstatic]; rfl)
      (by rw [same]; exact inputCode)
      (by rw [same]; exact inputRep)
      (by rw [same, r.sevm_eq]; rfl)
      (by rw [same, r.sevm_eq]; exact fork) good
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

end Blanc.Lift.UniswapV2Pair
