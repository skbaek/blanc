import Blanc.RetentionProbeCode
import Blanc.ExecutionTraceSettledFresh
import Blanc.Lift.WithdrawalRequest.HistoryFifo
import Blanc.Lift.WithdrawalRequest.DeploymentHistory

/-!
# `HistoryFifo` with its CREATE-avoidance premise over settled frames (retention probe)

Disposable probe, not a landing candidate. The existing chain from `history_fifo_of_checkpoint`
down to `block_settled_transaction_caller_ne_system` uses `avoid` at that leaf alone; every level
between only passes it on. Since existing modules stay untouched, the levels are restated here
with the leaf's conclusion, `userCallers`, in place of the four premises it consumed.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

private theorem system_observations_eq_nil'
    {benv : Benv} {target : Adr} {data : Bytes} {state : Jaune.State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (code : ByteArray)
    (installed : benv.state.getCode target = code)
    (reach : SpawnFreeReach code) (nondelegating : ¬ isValidDelegation code)
    (foreign : target ≠ withdrawalRequestPredeployAddress) :
    trace.settledFrames.flatMap balanceFrameObservation = [] := by
  have confined := trace.rawFrames_target_of_code
    (installed ▸ reach) (installed ▸ nondelegating)
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  have targetEq := confined (Blanc.Exec.Frame.rootDeriv (frame := frame))
    (trace.mem_rawFrames_of_mem_settledFrames frame member)
  exact balanceFrameObservation_foreign frame (fun target => foreign (targetEq.symm.trans target))

/-- `block_protocol_observation_partition`, from the leaf's conclusion. -/
theorem block_protocol_observation_partition_of_callers
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (userCallers : ∀ frame ∈ block.bodyTrace.transactions.settledFrames,
      frame.sevm.caller ≠ systemAddress) :
    ∃ reset : Exec.Frame,
      block.settledFrames.flatMap balanceFrameObservation =
        block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ++ [reset] ∧
      reset.sevm.currentTarget = withdrawalRequestPredeployAddress ∧
      reset.sevm.caller = systemAddress ∧
      reset.sevm.isStatic = false ∧
      reset.pre.state = block.bodyTrace.requestBenv.state ∧
      reset.post.state = block.bodyTrace.requests.withdrawalState ∧
      (reset.post.getStor withdrawalRequestPredeployAddress).get 1 = 0 ∧
      (∀ frame ∈ block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation,
        frame.sevm.caller ≠ systemAddress) := by
  have beaconMember : (beaconRootsAddress, beaconRootsCode) ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inl trivial
  have historyMember : (historyStorageAddress, historyStorageCode) ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inl trivial)
  have withdrawalMember : (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
      ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
  have consolidationMember : (consolidationRequestPredeployAddress, consolidationRequestCode)
      ∈ systemContracts := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inr trivial))
  have beaconFacts := systemContracts_facts _ beaconMember
  have historyFacts := systemContracts_facts _ historyMember
  have consolidationFacts := systemContracts_facts _ consolidationMember
  have beaconCode := history.block_code_boundaries block beaconRootsAddress beaconRootsCode
    beaconFacts.2.2 beaconFacts.2.1 (installed _ beaconMember)
  have historyCode := history.block_code_boundaries block historyStorageAddress historyStorageCode
    historyFacts.2.2 historyFacts.2.1 (installed _ historyMember)
  have consolidationCode := history.block_code_boundaries block
    consolidationRequestPredeployAddress consolidationRequestCode
    consolidationFacts.2.2 consolidationFacts.2.1 (installed _ consolidationMember)
  have beaconEmpty := system_observations_eq_nil' block.bodyTrace.beacon beaconRootsCode
    beaconCode.1 beaconFacts.1 beaconFacts.2.1 (by decide +kernel)
  have historyEmpty := system_observations_eq_nil' block.bodyTrace.history historyStorageCode
    historyCode.2.1 historyFacts.1 historyFacts.2.1 (by decide +kernel)
  have consolidationEmpty := system_observations_eq_nil' block.bodyTrace.requests.consolidation
    consolidationRequestCode consolidationCode.2.2.2 consolidationFacts.1
    consolidationFacts.2.1 (by decide +kernel)
  obtain ⟨reset, _, target, caller, dynamic, entry, endpoint, _, count, resetObs, _⟩ :=
    block_requests_reset_occurrence history block (installed _ withdrawalMember)
  refine ⟨reset, ?_, target, caller, dynamic, entry, endpoint, count, ?_⟩
  · simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
      RequestsTrace.settledFrames, List.flatMap_append, beaconEmpty, historyEmpty,
      consolidationEmpty, resetObs, List.nil_append, List.append_nil]
  · intro frame member
    obtain ⟨source, sourceMember, observation⟩ := List.mem_flatMap.mp member
    have same : frame = source := by
      unfold balanceFrameObservation at observation
      split at observation
      · exact List.mem_singleton.mp observation
      · exact False.elim (List.not_mem_nil observation)
    rw [same]
    exact userCallers source sourceMember

/-- Model-free partition of one configured block's exact word events into
the earlier history, the block's user transactions and its canonical
withdrawal reset, with the request-boundary storage between them. -/
theorem block_word_event_partition_of_callers
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (callers : ∀ frame ∈ block.bodyTrace.transactions.settledFrames,
      frame.sevm.caller ≠ systemAddress)
    {events : List WordReplayEvent}
    (replay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress) events
      (post.state.getStor withdrawalRequestPredeployAddress))
    (observed : events.map WordReplayEvent.frame =
      (ConfiguredHistoryTrace.step history block).settledFrames.flatMap balanceFrameObservation) :
    ∃ past transactionEvents : List WordReplayEvent, ∃ reset : WordReplayEvent,
      events = (past ++ transactionEvents) ++ [reset] ∧
      past.map WordReplayEvent.frame = history.settledFrames.flatMap balanceFrameObservation ∧
      transactionEvents.map WordReplayEvent.frame =
        block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ∧
      reset.kind = .system ∧
      reset.frame.pre.state = block.bodyTrace.requestBenv.state ∧
      WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
        (past ++ transactionEvents)
        (block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress) ∧
      WordStorageReplay (block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress)
        [reset] (post.state.getStor withdrawalRequestPredeployAddress) ∧
      ∀ state : Blanc.WithdrawalRequest.State,
        wordModelOutputs state (past ++ transactionEvents) = wordModelOutputs state past ∧
        wordModelOutputs state events = wordModelOutputs state past ++
          emitted ((past ++ transactionEvents).foldl wordModelUpdate state) ∧
        events.foldl wordModelUpdate state =
          Blanc.WithdrawalRequest.system ((past ++ transactionEvents).foldl wordModelUpdate state) := by
  obtain ⟨resetFrame, partition, _, resetCaller, _, resetPre, _, _, userCallers⟩ :=
    block_protocol_observation_partition_of_callers history block installed callers
  have mapped : events.map WordReplayEvent.frame =
      history.settledFrames.flatMap balanceFrameObservation ++
        (block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ++ [resetFrame]) := by
    rw [observed]
    simp only [ConfiguredHistoryTrace.settledFrames, List.flatMap_append, partition]
  obtain ⟨past, blockEvents, eventsEq, pastMap, blockMap⟩ := List.map_eq_append_iff.mp mapped
  obtain ⟨transactionEvents, remaining, blockEq, transactionMap, remainingMap⟩ :=
    List.map_eq_append_iff.mp blockMap
  obtain ⟨reset, rest, remainingEq, resetEq, restMap⟩ := List.map_eq_cons_iff.mp remainingMap
  have restEq : rest = [] := List.map_eq_nil_iff.mp restMap
  have equality : events = (past ++ transactionEvents) ++ [reset] := by
    rw [eventsEq, blockEq, remainingEq, restEq, List.append_assoc]
  have splitReplay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      ((past ++ transactionEvents) ++ [reset]) (post.state.getStor withdrawalRequestPredeployAddress) :=
    equality ▸ replay
  have segments := splitReplay.split (left := past ++ transactionEvents) (right := [reset])
  have resetGuard := segments.2.head_guard
  have resetKind : reset.kind = .system := resetGuard.system_kind (by rw [resetEq]; exact resetCaller)
  have prefixBoundary : (past ++ transactionEvents).foldl wordEventUpdate
      (checkpoint.state.getStor withdrawalRequestPredeployAddress) =
      block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress := by
    rw [resetGuard.pre, resetEq]
    change resetFrame.pre.state.getStor withdrawalRequestPredeployAddress = _
    rw [resetPre]
  have transactionReplay := (segments.1.split (left := past) (right := transactionEvents)).2
  have transactionKinds := WordStorageReplay.non_system_kinds transactionReplay (by
    intro event member
    apply userCallers event.frame
    rw [← transactionMap]
    exact List.mem_map.mpr ⟨event, member, rfl⟩)
  refine ⟨past, transactionEvents, reset, equality, pastMap, transactionMap, resetKind,
    resetEq ▸ resetPre, prefixBoundary ▸ segments.1, prefixBoundary ▸ segments.2, ?_⟩
  intro state
  have prefixOutputs : wordModelOutputs state (past ++ transactionEvents) =
      wordModelOutputs state past := by
    rw [wordModelOutputs_append, wordModelOutputs_eq_nil transactionEvents _ transactionKinds,
      List.append_nil]
  refine ⟨prefixOutputs, ?_, ?_⟩
  · rw [equality, wordModelOutputs_append, prefixOutputs]
    simp only [wordModelOutputs, resetKind, List.append_nil]
  · rw [equality, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, wordModelUpdate, resetKind]

/-- Form H: under the original INIT/CODE/SYSTEM hypotheses, every block of a
history with at most `wordOccurrenceCap` submission-payment occurrences since
the checkpoint satisfies exact word-fee FIFO. -/
theorem block_word_fifo_of_callers
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (callers : ∀ frame ∈ block.bodyTrace.transactions.settledFrames,
      frame.sevm.caller ≠ systemAddress)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap) :
    CheckpointBlockWordFifo history block := by
  have code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    apply installed (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
  obtain ⟨events, replay, observed, _, _, prefixes⟩ :=
    history_word_model (.step history block) code init occurrences
  obtain ⟨past, transactionEvents, reset, equality, pastMap, transactionMap, resetKind, resetPre,
      prefixReplay, _, outputs⟩ :=
    block_word_event_partition_of_callers history block installed callers replay observed
  obtain ⟨prefixOutputs, fullOutputs, finalModel⟩ := outputs initial
  subst equality
  obtain ⟨prefixHistory, prefixRep, _, excessLe, countLe, headLe, tailLe, lengthEq, sumLt,
      slotLt, prefixSlots⟩ := prefixes (past ++ transactionEvents) [reset] rfl
  obtain ⟨fullHistory, fullRep, conservation, fullExcessLe, fullCountLe, fullHeadLe, fullTailLe,
      fullLengthEq, fullSumLt, fullSlotLt, fullSlots⟩ :=
    prefixes ((past ++ transactionEvents) ++ [reset]) [] (List.append_nil _).symm
  have resetFrames : wordSubmissionFrames ((past ++ transactionEvents) ++ [reset]) =
      wordSubmissionFrames (past ++ transactionEvents) := by
    simp only [wordSubmissionFrames, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      resetKind, List.append_nil]
  have resetSubmissions : wordModelSubmissions ((past ++ transactionEvents) ++ [reset]) =
      wordModelSubmissions (past ++ transactionEvents) := by
    simp only [wordModelSubmissions, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      resetKind, List.append_nil]
  rw [resetSubmissions] at fullHistory conservation
  have prefixPayloads := prefixReplay.submissionFrames.2
  have fullFrames := (history_word_submission_frames (.step history block) replay observed).1
  rw [resetFrames] at fullFrames
  have entries := wordSubmissionFrames_entries (past ++ transactionEvents)
  rw [prefixReplay.fold_eq, prefixOutputs] at *
  rw [replay.fold_eq, finalModel, fullOutputs] at *
  have payload := block_requests_of_request_rep history block code _ prefixRep
  rw [block.bodyTrace.transaction_requests_eq_nil, List.nil_append] at payload
  exact ⟨⟨past, transactionEvents, reset, replay, pastMap, transactionMap, resetKind, resetPre⟩,
    ⟨init, prefixHistory, prefixRep⟩, ⟨payload.1, payload.2.1, payload.2.2⟩, ⟨init, fullHistory, fullRep⟩,
    conservation, ⟨fullFrames, prefixPayloads, entries.trans conservation⟩,
    ⟨excessLe, countLe, headLe, tailLe, lengthEq, sumLt, slotLt, prefixSlots⟩,
    ⟨fullExcessLe, fullCountLe, fullHeadLe, fullTailLe, fullLengthEq, fullSumLt, fullSlotLt,
      fullSlots⟩⟩

private theorem submissionRecord_eq {frame : Exec.Frame} {entry : Blanc.WithdrawalRequest.Entry}
    (caller : frame.sevm.caller = entry.caller)
    (payload : frame.sevm.data = submissionPayload entry) :
    submissionRecord frame = outputRecord entry := by
  simp only [submissionRecord, caller, payload, submissionPayload, outputRecord,
    ← entry.pubkey.property, List.take_left, List.drop_left]

private theorem submissions_eq_records {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final)
    (pairs : List (Exec.Frame × Blanc.WithdrawalRequest.Entry))
    (frames : pairs.map Prod.fst =
      (history.settledFrames.flatMap submissionFramePayments).map Prod.fst)
    (payloads : ∀ pair ∈ pairs,
      pair.1.sevm.caller = pair.2.caller ∧ pair.1.sevm.data = submissionPayload pair.2) :
    submissions history = (pairs.map Prod.snd).map outputRecord := by
  calc
    submissions history = pairs.map (fun pair => submissionRecord pair.1) := by
      simpa only [submissions, List.map_map, Function.comp_def] using
        congrArg (List.map submissionRecord) frames.symm
    _ = (pairs.map Prod.snd).map outputRecord := by
      rw [List.map_map]
      apply List.map_congr_left
      intro pair member
      exact submissionRecord_eq (payloads pair member).1 (payloads pair member).2

private theorem submissions_eq_replay {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) {pre post : Stor}
    {events : List WordReplayEvent} (replay : WordStorageReplay pre events post)
    (observed : events.map WordReplayEvent.frame =
      history.settledFrames.flatMap balanceFrameObservation) :
    submissions history = ((wordModelSubmissions events).map Submission.entry).map outputRecord := by
  have frames := history_word_submission_frames history replay observed
  have records := submissions_eq_records history (wordSubmissionFrames events) frames.1 frames.2.1
  rwa [wordSubmissionFrames_entries] at records

private theorem historyFifo_step' {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (prior : HistoryFifo history)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (cap : (history.settledFrames.flatMap submissionFramePayments).length ≤ wordOccurrenceCap)
    (info : CheckpointBlockWordFifo history block) :
    HistoryFifo (.step history block) := by
  obtain ⟨r, boundary, emission, afterReset, _, provenance, _, _⟩ := info
  have replay := r.replay
  rw [List.append_assoc] at replay
  have pastReplay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      r.past _ := replay.split.1
  have frames := history_word_submission_frames history pastReplay r.pastObserves
  have pastModel := pastReplay.wordModel WordHistory.start boundary.origin (by
    rw [List.length_nil, Nat.zero_add, frames.2.2]
    exact cap)
  simp only [List.nil_append] at pastModel
  obtain ⟨pastEvents, concreteReplay, concreteObserved⟩ := history_word_storage_replay history code
  have foldFrames (events : List WordReplayEvent) (storage : Stor) :
      events.foldl wordEventUpdate storage =
        (events.map WordReplayEvent.frame).foldl (fun s frame => wordStorageUpdate frame.sevm s)
          storage := by
    rw [List.foldl_map]
    rfl
  have endpoint : r.past.foldl wordEventUpdate
      (checkpoint.state.getStor withdrawalRequestPredeployAddress) =
      pre.state.getStor withdrawalRequestPredeployAddress := by
    rw [foldFrames, r.pastObserves, ← concreteObserved, ← foldFrames, concreteReplay.fold_eq]
  rw [endpoint] at pastModel
  have conserved := pastModel.1.conservation
  change [] ++ _ = _ at conserved
  rw [List.nil_append] at conserved
  have pastRecords := submissions_eq_replay history pastReplay r.pastObserves
  rw [conserved, List.map_append, ← storedQueue_eq pastModel.2] at pastRecords
  have pastEmissions : r.pastOutputs.map outputRecord = emissions history := by
    apply List.append_cancel_right
    exact pastRecords.symm.trans prior
  have fullRecords := submissions_eq_records (.step history block) r.frames
    provenance.stepFrames provenance.payloads
  rw [provenance.entries, List.map_append] at fullRecords
  change submissions (.step history block) = _
  rw [fullRecords, BlockWordReplay.outputs, List.map_append, pastEmissions,
    emissions, emission_eq_records emission, remainingQueue, storedQueue_eq afterReset.represents,
    List.append_assoc]

/-- **`history_fifo_of_checkpoint` with `avoid` over settled frames.** -/
theorem history_fifo_of_checkpoint_settled
    {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : history.NoSenderAt systemAddress)
    (authorities : history.NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ history.settledFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : (history.settledFrames.flatMap submissionFramePayments).length ≤ wordOccurrenceCap) :
    HistoryFifo history := by
  induction history with
  | refl hcfg hctx hid =>
    change [] = [] ++ storedQueue _
    rw [storedQueue_eq init]
    rfl
  | step history block ih =>
    have cap : (history.settledFrames.flatMap submissionFramePayments).length ≤
        wordOccurrenceCap := by
      simp only [ConfiguredHistoryTrace.settledFrames, List.flatMap_append,
        List.length_append] at occurrences
      omega
    have earlierAvoid : ∀ root ∈ history.settledFrames,
        root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress := by
      intro root member
      exact avoid root (List.mem_append_left _ member)
    have code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode := by
      apply installed (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
      simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inr (Or.inl trivial))
    exact historyFifo_step' history block (ih senders.1 authorities.1 earlierAvoid cap) code cap
      (block_word_fifo_of_callers history block installed
        (ConfiguredHistoryTrace.block_settled_caller_excluded history block senders authorities
          avoid systemEmpty)
        init occurrences)

/-- **`history_fifo` with `avoid` over settled frames.** The deployment prefix's own `Admission`
is unchanged. -/
theorem history_fifo_settled
    {cfg : ChainConfig} {checkpoint final : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint)
    (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint final)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : history.NoSenderAt systemAddress)
    (authorities : history.NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ history.settledFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap) :
    HistoryFifo history := by
  have initialized := deployment.initialized admission
  exact history_fifo_of_checkpoint_settled history
    (otherInstalled.with_withdrawal initialized.checkpointCode) senders authorities avoid
    initialized.systemEmpty initialized.checkpointStorage (by
      simpa only [submissions, List.length_map] using occurrences)

/-- Corollary check: the existing raw-premise statement follows, so that premise was never
necessary. -/
theorem history_fifo_of_checkpoint_raw_from_settled
    {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : history.NoSenderAt systemAddress)
    (authorities : history.NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : (history.settledFrames.flatMap submissionFramePayments).length ≤ wordOccurrenceCap) :
    HistoryFifo history :=
  history_fifo_of_checkpoint_settled history installed senders authorities
    (fun root member => avoid (Blanc.Exec.Frame.rootDeriv (frame := root))
      (history.mem_rawFrames_of_mem_settledFrames root member))
    systemEmpty init occurrences

end Blanc.Lift.WithdrawalRequest
