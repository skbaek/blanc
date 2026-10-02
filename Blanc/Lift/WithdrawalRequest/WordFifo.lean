import Blanc.Lift.WithdrawalRequest.ModelBlockRequests
import Blanc.Lift.WithdrawalRequest.WordHistory
import Blanc.Lift.WithdrawalRequest.SubmissionCount

/-!
Full configured-history FIFO under the bytecode's word-fee admission. The
exact actual word replay is composed into `WordHistory`; every queue, count
and excess margin is derived from the number of actual submission-payment
occurrences since INIT. No Nat payment, balance, fee-domain or ENTRY premise
is used. Histories with more than `wordOccurrenceCap` occurrences are the
only excluded case (Form D); at most `2 ^ 190` blocks never reach it.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

/-- The actual guarded word replay is a `WordHistory` replay while the
recorded submissions stay within the occurrence cap. -/
theorem WordStorageReplay.wordModel {pre post : Stor} {events : List WordReplayEvent}
    (replay : WordStorageReplay pre events post)
    {state : Blanc.WithdrawalRequest.State} {submissions : List Submission}
    {outputs : List Blanc.WithdrawalRequest.Entry}
    (history : WordHistory initial state submissions outputs) (rep : RepresentsStorage pre.get state)
    (room : submissions.length + (wordModelSubmissions events).length ≤ wordOccurrenceCap) :
    WordHistory initial (events.foldl wordModelUpdate state)
        (submissions ++ wordModelSubmissions events) (outputs ++ wordModelOutputs state events) ∧
      RepresentsStorage post.get (events.foldl wordModelUpdate state) := by
  induction replay generalizing state submissions outputs with
  | nil =>
    simp only [List.foldl_nil, wordModelSubmissions, List.flatMap_nil,
      wordModelOutputs, List.append_nil]
    exact ⟨history, rep⟩
  | @cons storage post event rest guard tail ih =>
    have margin := history.margin
    cases kind : event.kind with
    | system =>
      have count : (wordModelSubmissions (event :: rest)).length =
          (wordModelSubmissions rest).length := by
        simp only [wordModelSubmissions, List.flatMap_cons, kind, List.nil_append]
      rw [count] at room
      have caller : event.frame.sevm.caller = systemAddress := by
        simpa only [wordEventInput, kind] using guard.input
      have sumBound := (margin.bounds (by omega)).2.2.2.2.2.1
      have nextRep : RepresentsStorage (wordEventUpdate storage event).get
          (Blanc.WithdrawalRequest.system state) := by
        simpa only [wordEventUpdate, wordStorageUpdate, guard.dynamic, caller, ite_true] using
          wordSystemStorage_represents guard rep sumBound
      have result := ih (WordHistory.system history) nextRep room
      simpa only [List.foldl_cons, wordModelUpdate, kind, wordModelSubmissions,
        List.flatMap_cons, List.nil_append, wordModelOutputs, List.append_assoc] using result
    | submission entry iterations output =>
      have count : (wordModelSubmissions (event :: rest)).length =
          (wordModelSubmissions rest).length + 1 := by
        simp only [wordModelSubmissions, List.flatMap_cons, kind, List.length_append,
          List.length_singleton]
        omega
      rw [count] at room
      obtain ⟨caller, entryCaller, payload, active, feeRun, wordPaid⟩ :=
        (show event.frame.sevm.caller ≠ systemAddress ∧ entry.caller = event.frame.sevm.caller ∧
          event.frame.sevm.data = submissionPayload entry ∧ storage.get 0 ≠ B256.max ∧
          WordFakeExponential.Run (storage.get 0) 17 1 17 0 iterations output ∧
          (output / (17 : B256)).toNat ≤ event.frame.sevm.value.toNat from by
            simpa only [wordEventInput, kind] using guard.input)
      have bounds := margin.submission_bounds (by omega)
      have enabled := WordReplayGuard.enabled rep active
      have paid : WordFeePaid state event.frame.sevm.value.toNat := by
        refine ⟨iterations, output, ?_, wordPaid⟩
        rw [← rep.excess]
        exact feeRun
      have length : event.frame.sevm.data.length = 56 := by
        rw [payload, submissionPayload_length]
      have nextRep : RepresentsStorage (wordEventUpdate storage event).get (submit state entry) := by
        simpa only [wordEventUpdate, wordStorageUpdate, guard.dynamic, caller, length,
          ite_true, ite_false] using
          wordSubmissionStorage_represents guard rep bounds entry entryCaller payload
      let submission : Submission := ⟨entry, event.frame.sevm.value.toNat⟩
      have result := ih (WordHistory.submit history submission enabled paid) nextRep (by
        rw [List.length_append, List.length_singleton]
        omega)
      simpa only [List.foldl_cons, wordModelUpdate, kind, wordModelSubmissions,
        List.flatMap_cons, wordModelOutputs, List.nil_append, List.append_assoc,
        submission] using result
    | getter iterations output =>
      have count : (wordModelSubmissions (event :: rest)).length =
          (wordModelSubmissions rest).length := by
        simp only [wordModelSubmissions, List.flatMap_cons, kind, List.nil_append]
      rw [count] at room
      obtain ⟨caller, empty, value, active, feeRun⟩ :=
        (show event.frame.sevm.caller ≠ systemAddress ∧ event.frame.sevm.data = [] ∧
          event.frame.sevm.value = 0 ∧ storage.get 0 ≠ B256.max ∧
          WordFakeExponential.Run (storage.get 0) 17 1 17 0 iterations output from by
            simpa only [wordEventInput, kind] using guard.input)
      have nextRep : RepresentsStorage (wordEventUpdate storage event).get state := by
        simpa only [wordEventUpdate, wordStorageUpdate, guard.dynamic, caller, empty,
          List.length_nil, ite_true, ite_false, (by decide : ¬ (0 : Nat) = 56)] using rep
      have result := ih history nextRep room
      simpa only [List.foldl_cons, wordModelUpdate, kind, wordModelSubmissions,
        List.flatMap_cons, List.nil_append, wordModelOutputs] using result

/-- Each actual submission occurrence's committed frame with its typed entry, in replay order. -/
def wordSubmissionFrames (events : List WordReplayEvent) :
    List (Exec.Frame × Blanc.WithdrawalRequest.Entry) :=
  events.flatMap fun event =>
    match event.kind with
    | .submission entry _ _ => [(event.frame, entry)]
    | _ => []

/-- The typed entries of the occurrence frames are the recorded model submissions. -/
theorem wordSubmissionFrames_entries (events : List WordReplayEvent) :
    (wordSubmissionFrames events).map Prod.snd =
      (wordModelSubmissions events).map Submission.entry := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    cases kind : event.kind <;>
      simp only [wordSubmissionFrames, wordModelSubmissions, List.flatMap_cons, kind,
        List.map_cons, List.nil_append, List.singleton_append] at ih ⊢ <;>
      rw [ih]

/-- Retained observation followed by the submission-payment projection is the
submission-payment projection of the original frames. -/
theorem observed_submissionFramePayments (frames : List Exec.Frame) :
    (frames.flatMap balanceFrameObservation).flatMap submissionFramePayments =
      frames.flatMap submissionFramePayments := by
  rw [List.flatMap_assoc]
  apply congrArg (fun projection => frames.flatMap projection)
  funext frame
  exact submissionFramePayments_observed frame

/-- The occurrence frames are exactly the submission-payment frames of the
replayed frames, in order, and each frame's caller and 56-byte calldata are
its entry's caller and `(pubkey, amount)` payload. -/
theorem WordStorageReplay.submissionFrames {pre post : Stor} {events : List WordReplayEvent}
    (replay : WordStorageReplay pre events post) :
    (wordSubmissionFrames events).map Prod.fst =
      ((events.map WordReplayEvent.frame).flatMap submissionFramePayments).map Prod.fst ∧
    ∀ pair ∈ wordSubmissionFrames events,
      pair.1.sevm.caller = pair.2.caller ∧ pair.1.sevm.data = submissionPayload pair.2 := by
  induction replay with
  | nil =>
    refine ⟨rfl, ?_⟩
    intro pair member
    exact False.elim (List.not_mem_nil member)
  | @cons storage post event rest guard tail ih =>
    have target := guard.target
    have dynamic := guard.dynamic
    have head : (wordSubmissionFrames [event]).map Prod.fst =
          (submissionFramePayments event.frame).map Prod.fst ∧
        ∀ pair ∈ wordSubmissionFrames [event],
          pair.1.sevm.caller = pair.2.caller ∧ pair.1.sevm.data = submissionPayload pair.2 := by
      cases kind : event.kind with
      | system =>
        have caller : event.frame.sevm.caller = systemAddress := by
          simpa only [wordEventInput, kind] using guard.input
        have other : ¬ submissionPaymentFrame event.frame := fun frame => frame.2.1 caller
        simp only [wordSubmissionFrames, List.flatMap_cons, List.flatMap_nil, kind,
          List.append_nil, submissionFramePayments, ite_eq_right other, List.map_nil,
          List.not_mem_nil, false_imp_iff, imp_true_iff, and_self]
      | submission entry iterations output =>
        obtain ⟨caller, entryCaller, payload, _⟩ :=
          (show event.frame.sevm.caller ≠ systemAddress ∧ entry.caller = event.frame.sevm.caller ∧
            event.frame.sevm.data = submissionPayload entry ∧ storage.get 0 ≠ B256.max ∧
            WordFakeExponential.Run (storage.get 0) 17 1 17 0 iterations output ∧
            (output / (17 : B256)).toNat ≤ event.frame.sevm.value.toNat from by
              simpa only [wordEventInput, kind] using guard.input)
        have length : event.frame.sevm.data.length = 56 := by
          rw [payload, submissionPayload_length]
        have frame : submissionPaymentFrame event.frame := ⟨⟨target, dynamic⟩, caller, length⟩
        simp only [wordSubmissionFrames, List.flatMap_cons, List.flatMap_nil, kind,
          List.append_nil, submissionFramePayments, ite_eq_left frame, List.map_cons,
          List.map_nil, List.mem_singleton, true_and]
        intro pair member
        rw [member]
        exact ⟨entryCaller.symm, payload⟩
      | getter iterations output =>
        obtain ⟨_, empty, _⟩ :=
          (show event.frame.sevm.caller ≠ systemAddress ∧ event.frame.sevm.data = [] ∧
            event.frame.sevm.value = 0 ∧ storage.get 0 ≠ B256.max ∧
            WordFakeExponential.Run (storage.get 0) 17 1 17 0 iterations output from by
              simpa only [wordEventInput, kind] using guard.input)
        have other : ¬ submissionPaymentFrame event.frame := by
          intro frame
          have length := frame.2.2
          rw [empty] at length
          exact absurd length (by decide)
        simp only [wordSubmissionFrames, List.flatMap_cons, List.flatMap_nil, kind,
          List.append_nil, submissionFramePayments, ite_eq_right other, List.map_nil,
          List.not_mem_nil, false_imp_iff, imp_true_iff, and_self]
    have split : wordSubmissionFrames (event :: rest) =
        wordSubmissionFrames [event] ++ wordSubmissionFrames rest := by
      simp only [wordSubmissionFrames, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine ⟨?_, ?_⟩
    · rw [split, List.map_cons, List.flatMap_cons, List.map_append, List.map_append, head.1, ih.1]
    · intro pair member
      rw [split, List.mem_append] at member
      rcases member with first | later
      · exact head.2 pair first
      · exact ih.2 pair later

/-- History form: the occurrence frames are exactly the trace's committed
submission-payment frames, with per-frame provenance, and their number is the
number of recorded model submissions. -/
theorem history_word_submission_frames {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {pre post : Stor}
    {events : List WordReplayEvent} (replay : WordStorageReplay pre events post)
    (observed : events.map WordReplayEvent.frame =
      trace.settledFrames.flatMap balanceFrameObservation) :
    (wordSubmissionFrames events).map Prod.fst =
      (trace.settledFrames.flatMap submissionFramePayments).map Prod.fst ∧
    (∀ pair ∈ wordSubmissionFrames events,
      pair.1.sevm.caller = pair.2.caller ∧ pair.1.sevm.data = submissionPayload pair.2) ∧
    (wordModelSubmissions events).length =
      (trace.settledFrames.flatMap submissionFramePayments).length := by
  have frames := replay.submissionFrames
  rw [observed, observed_submissionFramePayments] at frames
  refine ⟨frames.1, frames.2, ?_⟩
  have entries := congrArg List.length (wordSubmissionFrames_entries events)
  have lengths := congrArg List.length frames.1
  simp only [List.length_map] at entries lengths
  omega

/-- Form H, whole history: under INIT and canonical code at the checkpoint,
if at most `wordOccurrenceCap` submission payments occur, every exact prefix
of the actual word replay is a word-admitted model history, its storage
represents that model, and its bookkeeping stays within the cap. -/
theorem history_word_model {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : (trace.settledFrames.flatMap submissionFramePayments).length ≤
      wordOccurrenceCap) :
    ∃ events : List WordReplayEvent,
      WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress) events
        (future.state.getStor withdrawalRequestPredeployAddress) ∧
      events.map WordReplayEvent.frame = trace.settledFrames.flatMap balanceFrameObservation ∧
      (wordModelSubmissions events).length =
        (trace.settledFrames.flatMap submissionFramePayments).length ∧
      RepresentsStorage (future.state.getStor withdrawalRequestPredeployAddress).get
        (events.foldl wordModelUpdate initial) ∧
      ∀ before after, events = before ++ after →
        let model := before.foldl wordModelUpdate initial
        WordHistory initial model (wordModelSubmissions before) (wordModelOutputs initial before) ∧
        RepresentsStorage (before.foldl wordEventUpdate
          (checkpoint.state.getStor withdrawalRequestPredeployAddress)).get model ∧
        (wordModelSubmissions before).map Submission.entry =
          wordModelOutputs initial before ++ model.queue ∧
        effectiveExcess model ≤ wordOccurrenceCap ∧ model.count ≤ wordOccurrenceCap ∧
        model.head ≤ model.tail ∧ model.tail ≤ wordOccurrenceCap ∧
        model.queue.length = model.tail - model.head ∧
        effectiveExcess model + model.count < 2 ^ 256 ∧
        queueBase model.tail + 2 < 2 ^ 256 ∧ QueueSlotsSafe model := by
  obtain ⟨events, replay, observed⟩ := history_word_storage_replay trace code
  have total := (history_word_submission_frames trace replay observed).2.2
  have full := replay.wordModel WordHistory.start init (by
    rw [List.length_nil, Nat.zero_add, total]
    exact occurrences)
  refine ⟨events, replay, observed, total, full.2, ?_⟩
  intro before after split
  have segments := (show WordStorageReplay
    (checkpoint.state.getStor withdrawalRequestPredeployAddress) (before ++ after)
    (future.state.getStor withdrawalRequestPredeployAddress) from split ▸ replay).split
  have lengths : (wordModelSubmissions before).length ≤ (wordModelSubmissions events).length := by
    rw [split]
    simp only [wordModelSubmissions, List.flatMap_append, List.length_append]
    omega
  have prefixModel := WordStorageReplay.wordModel segments.1 WordHistory.start init (by
    rw [List.length_nil, Nat.zero_add]
    omega)
  simp only [List.nil_append] at prefixModel
  have margin := prefixModel.1.margin
  have conservation := prefixModel.1.conservation
  simp only [Blanc.WithdrawalRequest.initial, List.nil_append] at conservation
  obtain ⟨excessLe, countLe, headLe, tailLe, lengthEq, sumLt, slotLt⟩ := margin.bounds (by omega)
  exact ⟨prefixModel.1, prefixModel.2, conservation, excessLe, countLe, headLe, tailLe, lengthEq,
    sumLt, slotLt, margin.slots_safe (by omega)⟩

/-- FIFO for one actual configured block under word-fee admission: the block's
exact word events split into the earlier history, its user transactions and
its canonical reset; the model at the request boundary is a word-admitted
history represented in storage; the block's withdrawal request bytes are
`systemOutput` of that model, i.e. its first `min 16 queue` entries in order;
outputs plus the remaining queue are exactly the committed submissions in
order; each output is, position for position, the `(caller, pubkey, amount)` of
exactly one committed submission frame of the trace before this block's
request phase (an order-preserving bijection onto outputs plus final queue);
every bookkeeping value stays within `wordOccurrenceCap`; and every live
queue read slot and next write slot is the unwrapped `4 + 3 * index + offset`,
never slots 0–3, before and after the block's reset. -/
def BlockWordFifo {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post) : Prop :=
  ∃ past transactionEvents : List WordReplayEvent, ∃ reset : WordReplayEvent,
    WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      ((past ++ transactionEvents) ++ [reset])
      (post.state.getStor withdrawalRequestPredeployAddress) ∧
    past.map WordReplayEvent.frame = history.settledFrames.flatMap balanceFrameObservation ∧
    transactionEvents.map WordReplayEvent.frame =
      block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ∧
    reset.kind = .system ∧
    reset.frame.pre.state = block.bodyTrace.requestBenv.state ∧
    let model := (past ++ transactionEvents).foldl wordModelUpdate initial
    WordHistory initial model (wordModelSubmissions (past ++ transactionEvents))
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
    WordHistory initial (Blanc.WithdrawalRequest.system model)
      (wordModelSubmissions ((past ++ transactionEvents) ++ [reset]))
      (wordModelOutputs initial past ++ emitted model) ∧
    (wordModelSubmissions ((past ++ transactionEvents) ++ [reset])).map Submission.entry =
      (wordModelOutputs initial past ++ emitted model) ++
        (Blanc.WithdrawalRequest.system model).queue ∧
    let submissions := wordSubmissionFrames (past ++ transactionEvents)
    submissions.map Prod.fst =
      ((history.settledFrames ++ block.bodyTrace.transactions.settledFrames).flatMap
        submissionFramePayments).map Prod.fst ∧
    submissions.map Prod.fst =
      ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
        submissionFramePayments).map Prod.fst ∧
    (∀ pair ∈ submissions,
      pair.1.sevm.caller = pair.2.caller ∧ pair.1.sevm.data = submissionPayload pair.2) ∧
    submissions.map Prod.snd = (wordModelOutputs initial past ++ emitted model) ++
      (Blanc.WithdrawalRequest.system model).queue ∧
    RepresentsStorage (post.state.getStor withdrawalRequestPredeployAddress).get
      (Blanc.WithdrawalRequest.system model) ∧
    effectiveExcess model ≤ wordOccurrenceCap ∧ model.count ≤ wordOccurrenceCap ∧
    model.head ≤ model.tail ∧ model.tail ≤ wordOccurrenceCap ∧
    model.queue.length = model.tail - model.head ∧
    effectiveExcess model + model.count < 2 ^ 256 ∧ queueBase model.tail + 2 < 2 ^ 256 ∧
    effectiveExcess (Blanc.WithdrawalRequest.system model) ≤ wordOccurrenceCap ∧
    (Blanc.WithdrawalRequest.system model).tail ≤ wordOccurrenceCap ∧
    QueueSlotsSafe model ∧ QueueSlotsSafe (Blanc.WithdrawalRequest.system model)

/-- Form H: under the original INIT/CODE/SYSTEM hypotheses, every block of a
history with at most `wordOccurrenceCap` submission-payment occurrences since
the checkpoint satisfies exact word-fee FIFO. -/
theorem block_word_fifo
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
    (occurrences : ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap) :
    BlockWordFifo history block := by
  have code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    apply installed (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
  obtain ⟨events, replay, observed, _, _, prefixes⟩ :=
    history_word_model (.step history block) code init occurrences
  obtain ⟨past, transactionEvents, reset, equality, pastMap, transactionMap, resetKind, resetPre,
      prefixReplay, _, outputs⟩ :=
    block_word_event_partition history block installed senders authorities avoid systemEmpty
      replay observed
  obtain ⟨prefixOutputs, fullOutputs, finalModel⟩ := outputs initial
  subst equality
  obtain ⟨prefixHistory, prefixRep, _, excessLe, countLe, headLe, tailLe, lengthEq, sumLt,
      slotLt, prefixSlots⟩ := prefixes (past ++ transactionEvents) [reset] rfl
  obtain ⟨fullHistory, fullRep, conservation, fullExcessLe, _, _, fullTailLe, _, _, _,
      fullSlots⟩ := prefixes ((past ++ transactionEvents) ++ [reset]) [] (List.append_nil _).symm
  have resetFrames : wordSubmissionFrames ((past ++ transactionEvents) ++ [reset]) =
      wordSubmissionFrames (past ++ transactionEvents) := by
    simp only [wordSubmissionFrames, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      resetKind, List.append_nil]
  have resetSubmissions : wordModelSubmissions ((past ++ transactionEvents) ++ [reset]) =
      wordModelSubmissions (past ++ transactionEvents) := by
    simp only [wordModelSubmissions, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      resetKind, List.append_nil]
  have prefixFrames := prefixReplay.submissionFrames
  rw [List.map_append, pastMap, transactionMap, ← List.flatMap_append,
    observed_submissionFramePayments] at prefixFrames
  have fullFrames := (history_word_submission_frames (.step history block) replay observed).1
  rw [resetFrames] at fullFrames
  have entries := wordSubmissionFrames_entries (past ++ transactionEvents)
  rw [← resetSubmissions] at entries
  rw [prefixReplay.fold_eq, prefixOutputs] at *
  rw [replay.fold_eq, finalModel, fullOutputs] at *
  have payload := block_requests_of_request_rep history block code _ prefixRep
  exact ⟨past, transactionEvents, reset, replay, pastMap, transactionMap, resetKind, resetPre,
    prefixHistory, prefixRep, payload.1, payload.2.1, payload.2.2, fullHistory, conservation,
    prefixFrames.1, fullFrames, prefixFrames.2, entries.trans conservation,
    fullRep, excessLe, countLe, headLe, tailLe, lengthEq, sumLt, slotLt, fullExcessLe, fullTailLe,
    prefixSlots, fullSlots⟩

/-- Form D: the same FIFO with no length premise, or more than
`wordOccurrenceCap` submission-payment occurrences since the checkpoint. -/
theorem block_word_fifo_or_overflow
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial) :
    BlockWordFifo history block ∨
      wordOccurrenceCap < ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
        submissionFramePayments).length := by
  by_cases occurrences : ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap
  · exact Or.inl (block_word_fifo history block installed senders authorities avoid
      systemEmpty init occurrences)
  · exact Or.inr (Nat.lt_of_not_le occurrences)

/-- Corollary: every block of a history of at most `2 ^ 190` blocks since
the checkpoint satisfies exact word-fee FIFO, with no occurrence premise. -/
theorem block_word_fifo_of_blockCount
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
    (blocks : (ConfiguredHistoryTrace.step history block).blockCount ≤ 2 ^ 190) :
    BlockWordFifo history block := by
  apply block_word_fifo history block installed senders authorities avoid systemEmpty init
  have payments := submissionFramePayments_length_le
    (ConfiguredHistoryTrace.step history block).settledFrames
  have frames := (ConfiguredHistoryTrace.step history block).settledFrames_length_le
  have product : (ConfiguredHistoryTrace.step history block).blockCount * 2 ^ 64 ≤
      2 ^ 190 * 2 ^ 64 := Nat.mul_le_mul_right _ blocks
  have cap : (2 : Nat) ^ 190 * 2 ^ 64 = wordOccurrenceCap := by decide
  omega

end Blanc.Lift.WithdrawalRequest
