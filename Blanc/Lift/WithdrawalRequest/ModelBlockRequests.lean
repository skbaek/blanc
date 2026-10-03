import Blanc.ExecutionAccountingStoragePrefix
import Blanc.Lift.WithdrawalRequest.WordModelCount
import Blanc.Lift.WithdrawalRequest.ProtocolOccurrences

/-! Conditional wiring from the exact actual word replay to each block's
original-model request bytes: the word-event partition of a configured block and
the request bytes of a block whose request-boundary storage represents a model
state. This component does not establish final E4/E5. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

theorem wordModelOutputs_append (left right : List WordReplayEvent)
    (state : Blanc.WithdrawalRequest.State) :
    wordModelOutputs state (left ++ right) = wordModelOutputs state left ++
      wordModelOutputs (left.foldl wordModelUpdate state) right := by
  induction left generalizing state with
  | nil => simp only [List.nil_append, List.foldl_nil, wordModelOutputs]
  | cons event left ih =>
    simp only [List.cons_append, wordModelOutputs, ih, List.foldl_cons, List.append_assoc]

theorem wordModelOutputs_eq_nil (events : List WordReplayEvent)
    (state : Blanc.WithdrawalRequest.State)
    (nonSystem : ∀ event ∈ events, event.kind ≠ .system) :
    wordModelOutputs state events = [] := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
    have head := nonSystem event List.mem_cons_self
    have tail := ih (wordModelUpdate state event)
      (fun next member => nonSystem next (List.mem_cons_of_mem event member))
    cases kind : event.kind with
    | system => exact False.elim (head kind)
    | submission entry iterations output =>
      simp only [wordModelOutputs, kind, tail, List.nil_append]
    | getter iterations output =>
      simp only [wordModelOutputs, kind, tail, List.nil_append]

theorem WordStorageReplay.non_system_kinds
    {pre post : Stor} {events : List WordReplayEvent}
    (replay : WordStorageReplay pre events post)
    (nonSystem : ∀ event ∈ events, event.frame.sevm.caller ≠ systemAddress) :
    ∀ event ∈ events, event.kind ≠ .system := by
  intro event member kind
  obtain ⟨left, right, equality⟩ := List.append_of_mem member
  have splitReplay : WordStorageReplay pre (left ++ event :: right) post := equality ▸ replay
  have guard := (splitReplay.split (left := left) (right := event :: right)).2.head_guard
  have caller : event.frame.sevm.caller = systemAddress := by
    simpa only [wordEventInput, kind] using guard.input
  exact nonSystem event member caller

/-- Model-free partition of one configured block's exact word events into
the earlier history, the block's user transactions and its canonical
withdrawal reset, with the request-boundary storage between them. -/
theorem block_word_event_partition
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
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
    block_protocol_observation_partition history block installed senders authorities avoid systemEmpty
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

/-- The block's request bytes follow from a model represented at its request boundary. -/
theorem block_requests_of_request_rep {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (model : Blanc.WithdrawalRequest.State)
    (requestRep : RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get model) :
    block.bodyTrace.requests.withdrawalOut.returnData = systemOutput model ∧
    block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
      optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
      optionalRequestEntry 1 (systemOutput model) ++
      optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData ∧
    (optionalRequestEntry 1 block.bodyTrace.requests.withdrawalOut.returnData = [] ↔
      emitted model = []) := by
  have baseRep : RepresentsStorage
      ((systemProtocolBase block.bodyTrace.requestBenv).getStorVal
        withdrawalRequestPredeployAddress) model := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, baseState, _⟩ :=
      systemProtocol_seed block.bodyTrace.requestBenv
    change RepresentsStorage ((systemProtocolBase block.bodyTrace.requestBenv).state.getStor
      withdrawalRequestPredeployAddress).get model
    rw [baseState]
    exact requestRep
  exact block_requests_fifo history block code model baseRep

end Blanc.Lift.WithdrawalRequest
