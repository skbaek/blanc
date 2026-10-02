import Blanc.ExecutionAccountingStoragePrefix
import Blanc.Lift.WithdrawalRequest.WordModelCount
import Blanc.Lift.WithdrawalRequest.ProtocolOccurrences

/-! Conditional wiring from INIT and the exact actual word replay to each
block's original-model request bytes. Exact-prefix Nat payment remains an
explicit unresolved premise; this component does not establish final E4/E5. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

private theorem WordModelAdmission.prefix {bound : Nat}
    {state : Blanc.WithdrawalRequest.State} {left right : List WordReplayEvent}
    (admitted : WordModelAdmission bound state (left ++ right)) :
    WordModelAdmission bound state left := by
  intro before event after equality
  exact admitted before event (after ++ right) (by
    rw [equality, List.append_assoc, List.cons_append])

private theorem wordModelOutputs_append (left right : List WordReplayEvent)
    (state : Blanc.WithdrawalRequest.State) :
    wordModelOutputs state (left ++ right) = wordModelOutputs state left ++
      wordModelOutputs (left.foldl wordModelUpdate state) right := by
  induction left generalizing state with
  | nil => simp only [List.nil_append, List.foldl_nil, wordModelOutputs]
  | cons event left ih =>
    simp only [List.cons_append, wordModelOutputs, ih, List.foldl_cons, List.append_assoc]

private theorem wordModelOutputs_eq_nil (events : List WordReplayEvent)
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

private theorem WordStorageReplay.non_system_kinds
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

/-- Derive this actual block's model request boundary and bytes from INIT and
the exact ordered replay. Nat payment is deliberately still conditional. -/
theorem block_model_requests_of_nat_paid
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    {events : List WordReplayEvent}
    (replay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress) events
      (post.state.getStor withdrawalRequestPredeployAddress))
    (observed : events.map WordReplayEvent.frame =
      (ConfiguredHistoryTrace.step history block).settledFrames.flatMap balanceFrameObservation)
    (natPaid : ∀ before event after, events = before ++ event :: after →
      match event.kind with
      | .submission _ _ _ => fee (before.foldl wordModelUpdate initial) ≤ event.frame.sevm.value.toNat
      | _ => True) :
    ∃ past transactionEvents : List WordReplayEvent, ∃ reset : WordReplayEvent,
      events = (past ++ transactionEvents) ++ [reset] ∧
      past.map WordReplayEvent.frame = history.settledFrames.flatMap balanceFrameObservation ∧
      transactionEvents.map WordReplayEvent.frame =
        block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ∧
      reset.kind = .system ∧
      reset.frame.pre.state = block.bodyTrace.requestBenv.state ∧
      let model := (past ++ transactionEvents).foldl wordModelUpdate initial
      History initial model (wordModelSubmissions (past ++ transactionEvents))
        (wordModelOutputs initial past) ∧
      RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get model ∧
      block.bodyTrace.requests.withdrawalOut.returnData = systemOutput model ∧
      block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
        optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
        optionalRequestEntry 1 (systemOutput model) ++
        optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData ∧
      (optionalRequestEntry 1 block.bodyTrace.requests.withdrawalOut.returnData = [] ↔
        emitted model = []) ∧
      wordModelOutputs initial events = wordModelOutputs initial past ++ emitted model ∧
      events.foldl wordModelUpdate initial = Blanc.WithdrawalRequest.system model ∧
      History initial (events.foldl wordModelUpdate initial) (wordModelSubmissions events)
        (wordModelOutputs initial past ++ emitted model) ∧
      (wordModelSubmissions events).map Submission.entry =
        (wordModelOutputs initial past ++ emitted model) ++
          (events.foldl wordModelUpdate initial).queue ∧
      RepresentsStorage (post.state.getStor withdrawalRequestPredeployAddress).get
        (events.foldl wordModelUpdate initial) := by
  have code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    apply installed (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
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
  let prefixEvents := past ++ transactionEvents
  let prefixStorage := prefixEvents.foldl wordEventUpdate
    (checkpoint.state.getStor withdrawalRequestPredeployAddress)
  let model := prefixEvents.foldl wordModelUpdate initial
  have splitReplay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      (prefixEvents ++ [reset]) (post.state.getStor withdrawalRequestPredeployAddress) :=
    equality ▸ replay
  have segments := splitReplay.split (left := prefixEvents) (right := [reset])
  have resetGuard : WordReplayGuard prefixStorage reset := segments.2.head_guard
  have resetKind : reset.kind = .system := resetGuard.system_kind (by rw [resetEq]; exact resetCaller)
  have prefixBoundary : prefixStorage =
      block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress := by
    rw [resetGuard.pre, resetEq]
    change resetFrame.pre.state.getStor withdrawalRequestPredeployAddress = _
    rw [resetPre]
  have admitted := history_word_model_admission_of_nat_paid
    (.step history block) code replay observed natPaid
  have prefixAdmission : WordModelAdmission (2 * 2 ^ 64) initial prefixEvents :=
    (show WordModelAdmission (2 * 2 ^ 64) initial (prefixEvents ++ [reset]) from
      equality ▸ admitted).prefix
  obtain ⟨prefixHistory, _, prefixRep⟩ := WordStorageReplay.model segments.1 (Nat.le_refl (2 * 2 ^ 64))
    History.start ModelResources.start init prefixAdmission
  obtain ⟨fullHistory, _, finalRep⟩ := replay.model (Nat.le_refl (2 * 2 ^ 64))
    History.start ModelResources.start init admitted
  have transactionReplay := (segments.1.split (left := past) (right := transactionEvents)).2
  have transactionKinds := WordStorageReplay.non_system_kinds transactionReplay (by
    intro event member
    apply userCallers event.frame
    rw [← transactionMap]
    exact List.mem_map.mpr ⟨event, member, rfl⟩)
  have prefixOutputs : wordModelOutputs initial prefixEvents = wordModelOutputs initial past := by
    change wordModelOutputs initial (past ++ transactionEvents) = _
    rw [wordModelOutputs_append, wordModelOutputs_eq_nil transactionEvents _ transactionKinds,
      List.append_nil]
  have fullOutputs : wordModelOutputs initial events = wordModelOutputs initial past ++ emitted model := by
    rw [equality, wordModelOutputs_append]
    simp only [wordModelOutputs, resetKind, List.append_nil]
    change wordModelOutputs initial prefixEvents ++ emitted model = _
    rw [prefixOutputs]
  have finalModel : events.foldl wordModelUpdate initial = Blanc.WithdrawalRequest.system model := by
    rw [equality, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, wordModelUpdate, resetKind]
    rfl
  have requestRep : RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get model := by
    change RepresentsStorage prefixStorage.get model at prefixRep
    rw [prefixBoundary] at prefixRep
    exact prefixRep
  have baseRep : RepresentsStorage
      ((systemProtocolBase block.bodyTrace.requestBenv).getStorVal
        withdrawalRequestPredeployAddress) model := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, baseState, _⟩ :=
      systemProtocol_seed block.bodyTrace.requestBenv
    change RepresentsStorage ((systemProtocolBase block.bodyTrace.requestBenv).state.getStor
      withdrawalRequestPredeployAddress).get model
    rw [baseState]
    exact requestRep
  have payload := block_requests_fifo history block code model baseRep
  have beforeHistory : History initial model (wordModelSubmissions prefixEvents)
      (wordModelOutputs initial past) := by
    simpa only [List.nil_append, prefixOutputs] using prefixHistory
  have afterHistory : History initial (events.foldl wordModelUpdate initial)
      (wordModelSubmissions events) (wordModelOutputs initial past ++ emitted model) := by
    simpa only [List.nil_append, fullOutputs] using fullHistory
  have conservation : (wordModelSubmissions events).map Submission.entry =
      (wordModelOutputs initial past ++ emitted model) ++
        (events.foldl wordModelUpdate initial).queue := by
    simpa only [initial, List.nil_append] using afterHistory.conservation
  exact ⟨past, transactionEvents, reset, equality, pastMap, transactionMap, resetKind,
    resetEq ▸ resetPre, beforeHistory, requestRep, payload.1, payload.2.1, payload.2.2,
    fullOutputs, finalModel, afterHistory, conservation, finalRep⟩

private theorem WordStorageReplay.inhibited_empty {pre post : Stor}
    {events : List WordReplayEvent} (replay : WordStorageReplay pre events post)
    (inhibited : pre.get 0 = B256.max)
    (users : ∀ event ∈ events, event.frame.sevm.caller ≠ systemAddress) :
    events = [] := by
  cases events with
  | nil => rfl
  | cons event events =>
    have input := replay.head_guard.input
    have user := users event List.mem_cons_self
    cases kind : event.kind with
    | system =>
      simp only [wordEventInput, kind] at input
      exact False.elim (user input)
    | submission entry iterations output =>
      simp only [wordEventInput, kind] at input
      exact False.elim (input.2.2.2.1 inhibited)
    | getter iterations output =>
      simp only [wordEventInput, kind] at input
      exact False.elim (input.2.2.2.1 inhibited)

/-- The first actual configured block after INIT has no committed nonstatic
user observation at the withdrawal contract. Its canonical reset emits no
withdrawal request and establishes the activated empty model state. No Nat
payment or fee-domain premise is assumed. This is the activation base case,
not the induction step for later blocks. -/
theorem activation_block_model_requests
    {cfg : ChainConfig} {checkpoint post : BlockChain}
    (valid : cfg.Valid) (context : checkpoint.ValidContext)
    (chain : cfg.chainId = checkpoint.chainId)
    (block : ConfiguredBlockTrace cfg checkpoint post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step (.refl valid context chain) block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step (.refl valid context chain) block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step (.refl valid context chain) block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial) :
    block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation = [] ∧
    block.bodyTrace.requests.withdrawalOut.returnData = [] ∧
    block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
      optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
      optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData ∧
    RepresentsStorage (post.state.getStor withdrawalRequestPredeployAddress).get
      (Blanc.WithdrawalRequest.system initial) := by
  let history : ConfiguredHistoryTrace cfg checkpoint checkpoint := .refl valid context chain
  have code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    apply installed (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
  obtain ⟨events, replay, observed⟩ := history_word_storage_replay (.step history block) code
  obtain ⟨resetFrame, partition, _, resetCaller, _, _, _, _, userCallers⟩ :=
    block_protocol_observation_partition history block installed senders authorities avoid systemEmpty
  have mapped : events.map WordReplayEvent.frame =
      block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ++ [resetFrame] := by
    rw [observed]
    simpa only [history, ConfiguredHistoryTrace.settledFrames, List.flatMap_append,
      List.flatMap_nil, List.nil_append] using partition
  obtain ⟨transactionEvents, remaining, eventsEq, transactionMap, remainingMap⟩ :=
    List.map_eq_append_iff.mp mapped
  obtain ⟨reset, rest, remainingEq, resetEq, restMap⟩ := List.map_eq_cons_iff.mp remainingMap
  have restEq : rest = [] := List.map_eq_nil_iff.mp restMap
  have equality : events = transactionEvents ++ [reset] := by
    rw [eventsEq, remainingEq, restEq]
  have splitReplay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      (transactionEvents ++ [reset]) (post.state.getStor withdrawalRequestPredeployAddress) :=
    equality ▸ replay
  have inhibited : (checkpoint.state.getStor withdrawalRequestPredeployAddress).get 0 =
      B256.max := by
    rw [init.excess]
    rfl
  have transactionNil : transactionEvents = [] :=
    WordStorageReplay.inhibited_empty splitReplay.split.1 inhibited (by
      intro event member
      apply userCallers event.frame
      rw [← transactionMap]
      exact List.mem_map.mpr ⟨event, member, rfl⟩)
  have transactionObsNil :
      block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation = [] := by
    rw [← transactionMap, transactionNil]
    rfl
  have single : events = [reset] := by rw [equality, transactionNil, List.nil_append]
  have singleReplay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      [reset] (post.state.getStor withdrawalRequestPredeployAddress) := single ▸ replay
  have resetKind : reset.kind = .system :=
    singleReplay.head_guard.system_kind (by rw [resetEq]; exact resetCaller)
  have paid : ∀ before event after, events = before ++ event :: after →
      match event.kind with
      | .submission _ _ _ => fee (before.foldl wordModelUpdate initial) ≤ event.frame.sevm.value.toNat
      | _ => True := by
    intro before event after eventEq
    have member : event ∈ events := by
      rw [eventEq]
      exact List.mem_append_right before List.mem_cons_self
    rw [single] at member
    have same : event = reset := List.mem_singleton.mp member
    rw [same, resetKind]
    trivial
  obtain ⟨past, transactions, last, _, pastMap, transactionsMap, _, _, _, _,
      payload, requests, _, _, _, _, _, finalRep⟩ :=
    block_model_requests_of_nat_paid history block installed senders authorities avoid
      systemEmpty init replay observed paid
  have pastNil : past = [] := List.map_eq_nil_iff.mp (by
    simpa only [history, ConfiguredHistoryTrace.settledFrames, List.flatMap_nil] using pastMap)
  have transactionsNil : transactions = [] :=
    List.map_eq_nil_iff.mp (transactionsMap.trans transactionObsNil)
  simp only [pastNil, transactionsNil, List.nil_append, List.foldl_nil] at payload requests
  have finalModel : events.foldl wordModelUpdate initial = Blanc.WithdrawalRequest.system initial := by
    rw [single]
    simp only [List.foldl_cons, List.foldl_nil, wordModelUpdate, resetKind]
  rw [finalModel] at finalRep
  change block.bodyTrace.requests.withdrawalOut.returnData = [] at payload
  change block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
    optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
    optionalRequestEntry 1 [] ++
    optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData at requests
  rw [show optionalRequestEntry 1 [] = [] from rfl, List.append_nil] at requests
  exact ⟨transactionObsNil, payload, requests, finalRep⟩

end Blanc.Lift.WithdrawalRequest
