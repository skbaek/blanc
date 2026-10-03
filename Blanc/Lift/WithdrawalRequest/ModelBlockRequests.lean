import Blanc.ExecutionAccountingStoragePrefix
import Blanc.Lift.WithdrawalRequest.WordModelCount
import Blanc.Lift.WithdrawalRequest.ProtocolOccurrences

/-! Conditional wiring from INIT and the exact actual word replay to each
block's original-model request bytes, with unconditional activation and first
enabled block cases under the original environmental assumptions. Later-block
Nat payment remains unresolved; this component does not establish final E4/E5. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

private theorem WordModelAdmission.prefix {bound : Nat}
    {state : Blanc.WithdrawalRequest.State} {left right : List WordReplayEvent}
    (admitted : WordModelAdmission bound state (left ++ right)) :
    WordModelAdmission bound state left := by
  intro before event after equality
  exact admitted before event (after ++ right) (by
    rw [equality, List.append_assoc, List.cons_append])

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
  obtain ⟨past, transactionEvents, reset, equality, pastMap, transactionMap, resetKind, resetPre,
      prefixReplay, _, outputs⟩ :=
    block_word_event_partition history block installed senders authorities avoid systemEmpty
      replay observed
  obtain ⟨prefixOutputs, fullOutputs, finalModel⟩ := outputs initial
  let prefixEvents := past ++ transactionEvents
  let model := prefixEvents.foldl wordModelUpdate initial
  have admitted := history_word_model_admission_of_nat_paid
    (.step history block) code replay observed natPaid
  have prefixAdmission : WordModelAdmission (2 * 2 ^ 64) initial prefixEvents :=
    (show WordModelAdmission (2 * 2 ^ 64) initial (prefixEvents ++ [reset]) from
      equality ▸ admitted).prefix
  obtain ⟨prefixHistory, _, requestRep⟩ := WordStorageReplay.model prefixReplay
    (Nat.le_refl (2 * 2 ^ 64)) History.start ModelResources.start init prefixAdmission
  obtain ⟨fullHistory, _, finalRep⟩ := replay.model (Nat.le_refl (2 * 2 ^ 64))
    History.start ModelResources.start init admitted
  have payload := block_requests_of_request_rep history block code model requestRep
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
    resetPre, beforeHistory, requestRep, payload.1, payload.2.1, payload.2.2,
    fullOutputs, finalModel, afterHistory, conservation, finalRep⟩

private theorem WordStorageReplay.model_zero_user_span
    {pre post : Stor} {events : List WordReplayEvent}
    (replay : WordStorageReplay pre events post) {bound : Nat}
    (boundCap : bound ≤ 2 * 2 ^ 64)
    {state : Blanc.WithdrawalRequest.State} {submissions : List Submission}
    {outputs : List Blanc.WithdrawalRequest.Entry}
    (history : History initial state submissions outputs)
    (resources : ModelResources bound history) (rep : RepresentsStorage pre.get state)
    (zero : state.excess = 0)
    (users : ∀ event ∈ events, event.frame.sevm.caller ≠ systemAddress)
    (room : state.count + events.length ≤ bound) :
    ∃ nextHistory : History initial (events.foldl wordModelUpdate state)
        (submissions ++ wordModelSubmissions events) (outputs ++ wordModelOutputs state events),
      ModelResources bound nextHistory ∧
        RepresentsStorage post.get (events.foldl wordModelUpdate state) := by
  induction replay generalizing state submissions outputs with
  | nil =>
    simp only [List.foldl_nil, wordModelSubmissions, List.flatMap_nil,
      wordModelOutputs, List.append_nil]
    exact ⟨history, resources, rep⟩
  | @cons storage post event rest guard tail ih =>
    have user := users event List.mem_cons_self
    have step :
        (match event.kind with
        | .submission entry _ _ => fee state ≤ event.frame.sevm.value.toNat ∧
            (submit state entry).count ≤ bound
        | _ => True) ∧
        (wordModelUpdate state event).excess = 0 ∧
        (wordModelUpdate state event).count + rest.length ≤ bound := by
      cases kind : event.kind with
      | system =>
        have input := guard.input
        simp only [wordEventInput, kind] at input
        exact False.elim (user input)
      | submission entry iterations output =>
        have input := guard.input
        simp only [wordEventInput, kind] at input
        have rawZero : storage.get 0 = 0 := by rw [rep.excess, zero]; rfl
        have run := input.2.2.2.2.1
        rw [rawZero] at run
        have zeroRun : WordFakeExponential.Run 0 17 1 17 0 1 17 :=
          .step (by decide) (by exact .stop _ _)
        have outputEq := (run.deterministic zeroRun).2
        have paid := input.2.2.2.2.2
        rw [outputEq] at paid
        change 1 ≤ event.frame.sevm.value.toNat at paid
        rw [fee_at_zero_excess state zero]
        simp only [wordModelUpdate, kind, submit, List.length_cons] at room ⊢
        exact ⟨⟨paid, by omega⟩, zero, by omega⟩
      | getter iterations output =>
        simp only [wordModelUpdate, kind, List.length_cons] at room ⊢
        exact ⟨trivial, zero, by omega⟩
    have oneAdmission : WordModelAdmission bound state [event] := by
      intro before current after equality
      have lengths := congrArg List.length equality
      simp only [List.length_append, List.length_cons, List.length_nil] at lengths
      have beforeNil : before = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst before
      simp only [List.nil_append] at equality
      have currentEq := (List.cons.inj equality).1
      subst current
      cases kind : event.kind with
      | system => trivial
      | getter iterations output => trivial
      | submission entry iterations output =>
        simpa only [kind, List.foldl_nil] using step.1
    have oneReplay : WordStorageReplay storage [event] (wordEventUpdate storage event) :=
      .cons guard (.nil _)
    obtain ⟨nextHistory, nextResources, nextRep⟩ :=
      oneReplay.model boundCap history resources rep oneAdmission
    have result := ih nextHistory nextResources nextRep step.2.1
      (fun next member => users next (List.mem_cons_of_mem event member)) step.2.2
    simpa only [List.foldl_cons, List.foldl_nil, wordModelSubmissions, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, wordModelOutputs, List.append_assoc] using result

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

/-- The first enabled block after the actual activation block has exact
Nat-paid submission provenance and FIFO request bytes. The payment and count
conditions are derived, not premises. Later enabled blocks are not covered. -/
theorem first_enabled_block_model_requests
    {cfg : ChainConfig} {checkpoint activated post : BlockChain}
    (valid : cfg.Valid) (context : checkpoint.ValidContext)
    (chain : cfg.chainId = checkpoint.chainId)
    (activation : ConfiguredBlockTrace cfg checkpoint activated)
    (block : ConfiguredBlockTrace cfg activated post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step
      (.step (.refl valid context chain) activation) block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step
      (.step (.refl valid context chain) activation) block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step
      (.step (.refl valid context chain) activation) block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial) :
    ∃ events : List WordReplayEvent,
      events.map WordReplayEvent.frame =
        block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ∧
      WordStorageReplay (activated.state.getStor withdrawalRequestPredeployAddress) events
        (block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress) ∧
      let model := events.foldl wordModelUpdate (Blanc.WithdrawalRequest.system initial)
      History initial model (wordModelSubmissions events) [] ∧
      RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get model ∧
      block.bodyTrace.requests.withdrawalOut.returnData = systemOutput model ∧
      block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
        optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
        optionalRequestEntry 1 (systemOutput model) ++
        optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData ∧
      (optionalRequestEntry 1 block.bodyTrace.requests.withdrawalOut.returnData = [] ↔
        emitted model = []) ∧
      History initial (Blanc.WithdrawalRequest.system model)
        (wordModelSubmissions events) (emitted model) ∧
      (wordModelSubmissions events).map Submission.entry =
        emitted model ++ (Blanc.WithdrawalRequest.system model).queue ∧
      RepresentsStorage (post.state.getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.system model) := by
  let history : ConfiguredHistoryTrace cfg checkpoint activated :=
    .step (.refl valid context chain) activation
  have activatedRep := (activation_block_model_requests valid context chain activation installed
    senders.1 authorities.1 (by
      intro root member creation
      exact avoid root (List.mem_append_left _ member) creation) systemEmpty init).2.2.2
  have code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    apply installed (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
  have inv : balanceSpec.StateInv withdrawalRequestPredeployAddress activated.state := by
    refine ⟨?_, trivial, trivial⟩
    change some (activated.state.getCode withdrawalRequestPredeployAddress).toList =
      some Blanc.withdrawalRequestCode.toList
    rw [history_canonical_code history code]
  obtain ⟨allEvents, replay, observed⟩ := wordReplayLadder.configuredBlock block
    (history_balanceEntryCondition (.step history block)).2 inv 0
  change List WordReplayEvent at allEvents
  change WordStorageReplay (activated.state.getStor withdrawalRequestPredeployAddress)
    allEvents (post.state.getStor withdrawalRequestPredeployAddress) at replay
  change allEvents.map WordReplayEvent.frame =
    block.settledFrames.flatMap balanceFrameObservation at observed
  obtain ⟨resetFrame, partition, _, resetCaller, _, resetPre, _, _, userCallers⟩ :=
    block_protocol_observation_partition history block installed senders authorities avoid systemEmpty
  have mapped : allEvents.map WordReplayEvent.frame =
      block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ++ [resetFrame] :=
    observed.trans partition
  obtain ⟨events, remaining, eventsEq, transactionMap, remainingMap⟩ :=
    List.map_eq_append_iff.mp mapped
  obtain ⟨reset, rest, remainingEq, resetEq, restMap⟩ := List.map_eq_cons_iff.mp remainingMap
  have restEq : rest = [] := List.map_eq_nil_iff.mp restMap
  have equality : allEvents = events ++ [reset] := by rw [eventsEq, remainingEq, restEq]
  have splitReplay : WordStorageReplay (activated.state.getStor withdrawalRequestPredeployAddress)
      (events ++ [reset]) (post.state.getStor withdrawalRequestPredeployAddress) := equality ▸ replay
  have segments := splitReplay.split
  have users : ∀ event ∈ events, event.frame.sevm.caller ≠ systemAddress := by
    intro event member
    apply userCallers event.frame
    rw [← transactionMap]
    exact List.mem_map.mpr ⟨event, member, rfl⟩
  have lengthBound : events.length ≤ 2 * 2 ^ 64 := by
    have fullLength := congrArg List.length observed
    rw [List.length_map, equality, List.length_append, List.length_singleton] at fullLength
    have observationBound := balanceObservation_length_le block.settledFrames
    have frameBound := block.settledFrames_length_lt
    omega
  have activatedHistory : History initial (Blanc.WithdrawalRequest.system initial) [] [] :=
    .system .start
  have activatedResources : ModelResources (2 * 2 ^ 64) activatedHistory :=
    .system .start
  obtain ⟨prefixHistory, prefixResources, prefixRep⟩ :=
    WordStorageReplay.model_zero_user_span segments.1 (Nat.le_refl (2 * 2 ^ 64))
      activatedHistory activatedResources activatedRep rfl users (by
        change 0 + events.length ≤ 2 * 2 ^ 64
        simpa only [Nat.zero_add] using lengthBound)
  let model := events.foldl wordModelUpdate (Blanc.WithdrawalRequest.system initial)
  have kinds := WordStorageReplay.non_system_kinds segments.1 users
  have noOutputs := wordModelOutputs_eq_nil events (Blanc.WithdrawalRequest.system initial) kinds
  have beforeHistory : History initial model (wordModelSubmissions events) [] := by
    simpa only [List.nil_append, noOutputs] using prefixHistory
  have resetGuard := segments.2.head_guard
  have resetKind : reset.kind = .system := resetGuard.system_kind (by rw [resetEq]; exact resetCaller)
  have prefixBoundary : events.foldl wordEventUpdate
      (activated.state.getStor withdrawalRequestPredeployAddress) =
      block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress := by
    rw [resetGuard.pre, resetEq]
    change resetFrame.pre.state.getStor withdrawalRequestPredeployAddress = _
    rw [resetPre]
  have transactionReplay : WordStorageReplay
      (activated.state.getStor withdrawalRequestPredeployAddress) events
      (block.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress) :=
    prefixBoundary ▸ segments.1
  have requestRep : RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get model := by
    rw [← prefixBoundary]
    exact prefixRep
  have payload := block_requests_of_request_rep history block code model requestRep
  have resetAdmission : WordModelAdmission (2 * 2 ^ 64) model [reset] := by
    intro before event after eq
    have member : event ∈ [reset] := by
      rw [eq]
      exact List.mem_append_right before List.mem_cons_self
    have same := List.mem_singleton.mp member
    rw [same, resetKind]
    trivial
  obtain ⟨_, _, finalRep⟩ := WordStorageReplay.model segments.2 (Nat.le_refl (2 * 2 ^ 64))
    prefixHistory prefixResources prefixRep resetAdmission
  simp only [List.foldl_cons, List.foldl_nil, wordModelUpdate, resetKind] at finalRep
  have afterHistory : History initial (Blanc.WithdrawalRequest.system model)
      (wordModelSubmissions events) (emitted model) := .system beforeHistory
  have conservation : (wordModelSubmissions events).map Submission.entry =
      emitted model ++ (Blanc.WithdrawalRequest.system model).queue := by
    simpa only [initial, List.nil_append] using afterHistory.conservation
  exact ⟨events, transactionMap, transactionReplay, beforeHistory, requestRep, payload.1, payload.2.1,
    payload.2.2, afterHistory, conservation, finalRep⟩

end Blanc.Lift.WithdrawalRequest
