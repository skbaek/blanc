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

/-- The bookkeeping of one model state is safe: every counter is within
`wordOccurrenceCap`, the queue pointers are ordered and span exactly the queue,
the two word sums the bytecode forms never wrap, and every live queue slot and
the next write slot are the unwrapped `4 + 3 * index + offset` (never slots 0–3).

Three fields follow from others and stay for readers: `sumLt` from `excessLe`
and `countLe`, and `slotLt` from `tailLe`, by arithmetic (`3 * wordOccurrenceCap
+ 6 < 2 ^ 256`); `slots` from `slotLt` by `submission_queueSlot_toNat`. For a
state that storage represents, `headLe` and `length` also follow from
`RepresentsStorage.coherent`. -/
structure WordBookkeepingSafe (state : Blanc.WithdrawalRequest.State) : Prop where
  /-- The effective excess is within the cap. -/
  excessLe : effectiveExcess state ≤ wordOccurrenceCap
  /-- The pending submission count is within the cap. -/
  countLe : state.count ≤ wordOccurrenceCap
  /-- The queue head does not pass the tail. -/
  headLe : state.head ≤ state.tail
  /-- The queue tail is within the cap. -/
  tailLe : state.tail ≤ wordOccurrenceCap
  /-- The queue holds exactly the entries between head and tail. -/
  length : state.queue.length = state.tail - state.head
  /-- Excess plus count fits a word (follows from `excessLe` and `countLe`). -/
  sumLt : effectiveExcess state + state.count < 2 ^ 256
  /-- The tail's last slot fits a word (follows from `tailLe`). -/
  slotLt : queueBase state.tail + 2 < 2 ^ 256
  /-- Every live read slot and the next write slot is unwrapped and above
  slot 3 (follows from `slotLt` by `submission_queueSlot_toNat`). -/
  slots : QueueSlotsSafe state

/-- The witness for one actual configured block: the exact guarded word replay
of the predeploy from the checkpoint to the state after the block, split into
the earlier history's events, this block's user-transaction events and this
block's withdrawal system call (the reset), each tied to the trace. -/
structure BlockWordReplay {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post) where
  /-- The word events of the earlier history. -/
  past : List WordReplayEvent
  /-- The word events of this block's user transactions. -/
  transactions : List WordReplayEvent
  /-- This block's withdrawal system call. -/
  reset : WordReplayEvent
  /-- The guarded word replay runs from the checkpoint's predeploy storage over
  the earlier events, this block's transactions and the reset, to the
  predeploy storage after the block. -/
  replay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
    ((past ++ transactions) ++ [reset]) (post.state.getStor withdrawalRequestPredeployAddress)
  /-- The earlier events' frames are the earlier history's observed settled frames. -/
  pastObserves : past.map WordReplayEvent.frame =
    history.settledFrames.flatMap balanceFrameObservation
  /-- The transaction events' frames are this block's observed transaction frames. -/
  transactionsObserve : transactions.map WordReplayEvent.frame =
    block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation
  /-- The reset is a system-call event. -/
  resetSystem : reset.kind = .system
  /-- The reset starts at this block's request boundary. -/
  resetAtBoundary : reset.frame.pre.state = block.bodyTrace.requestBenv.state

namespace BlockWordReplay

variable {cfg : ChainConfig} {checkpoint pre post : BlockChain}
  {history : ConfiguredHistoryTrace cfg checkpoint pre}
  {block : ConfiguredBlockTrace cfg pre post}

/-- The model at this block's request boundary: the word model replayed from
INIT over the earlier events and this block's transactions. -/
def model (r : BlockWordReplay history block) : Blanc.WithdrawalRequest.State :=
  (r.past ++ r.transactions).foldl wordModelUpdate initial

/-- The committed submissions through this block, in order. The reset adds
none (`resetSystem`). -/
def submissions (r : BlockWordReplay history block) : List Submission :=
  wordModelSubmissions (r.past ++ r.transactions)

/-- The entries emitted by earlier blocks' system calls, in order. -/
def pastOutputs (r : BlockWordReplay history block) : List Blanc.WithdrawalRequest.Entry :=
  wordModelOutputs initial r.past

/-- All entries emitted through this block: the earlier outputs, then this
block's emitted prefix of the queue. -/
def outputs (r : BlockWordReplay history block) : List Blanc.WithdrawalRequest.Entry :=
  r.pastOutputs ++ emitted r.model

/-- Each committed submission's frame with its typed entry, in order. -/
def frames (r : BlockWordReplay history block) :
    List (Exec.Frame × Blanc.WithdrawalRequest.Entry) :=
  wordSubmissionFrames (r.past ++ r.transactions)

/-- At the request boundary, the model is a word-admitted history of the
committed submissions that emitted the earlier outputs, and the predeploy's
storage represents it. -/
structure BoundaryModel (r : BlockWordReplay history block) : Prop where
  /-- The model is a word-admitted history from INIT. -/
  wordHistory : WordHistory initial r.model r.submissions r.pastOutputs
  /-- The request-boundary storage represents the model. -/
  represents : RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
    withdrawalRequestPredeployAddress).get r.model

/-- This block's withdrawal request bytes are `systemOutput` of the boundary
model, i.e. its first `min 16 queue` entries in order; they take their place in
the block's request list; and the type-1 entry is omitted exactly when nothing
is emitted. -/
structure Emission (r : BlockWordReplay history block) : Prop where
  /-- The system call returns the model's emitted entries' records. -/
  withdrawal : block.bodyTrace.requests.withdrawalOut.returnData = systemOutput r.model
  /-- The block's request list carries them as its type-1 entry. -/
  requests : block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
    optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
    optionalRequestEntry 1 (systemOutput r.model) ++
    optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData
  /-- The type-1 entry is omitted iff nothing is emitted (follows from
  `withdrawal` by `optionalRequestEntry_eq_nil_iff` and `outputRecords_length`). -/
  omittedIff : optionalRequestEntry 1 block.bodyTrace.requests.withdrawalOut.returnData = [] ↔
    emitted r.model = []

/-- After this block's reset, the system-stepped model is a word-admitted
history of the same submissions that emitted all outputs so far, and the
predeploy's storage after the block represents it. -/
structure AfterReset (r : BlockWordReplay history block) : Prop where
  /-- The reset model is a word-admitted history from INIT (follows from
  `BoundaryModel.wordHistory` by the constructor `WordHistory.system`). -/
  wordHistory : WordHistory initial (Blanc.WithdrawalRequest.system r.model) r.submissions
    r.outputs
  /-- The storage after the block represents the reset model. -/
  represents : RepresentsStorage (post.state.getStor withdrawalRequestPredeployAddress).get
    (Blanc.WithdrawalRequest.system r.model)

/-- FIFO: the committed submissions' entries, in order, are exactly all outputs
so far followed by the queue left after the reset; nothing is dropped,
duplicated, reordered or emitted early. Follows from `AfterReset.wordHistory`
by `WordHistory.conservation` (INIT's queue is empty). -/
def Fifo (r : BlockWordReplay history block) : Prop :=
  r.submissions.map Submission.entry = r.outputs ++ (Blanc.WithdrawalRequest.system r.model).queue

/-- Each committed submission is, in order, exactly one committed
submission-payment frame of the trace, whose caller and calldata are its
entry's caller and `(pubkey, amount)` payload; in trace terms, those frames'
entries are all outputs followed by the remaining queue. -/
structure Provenance (r : BlockWordReplay history block) : Prop where
  /-- The submission frames are the submission-payment frames of the earlier
  history and this block's transactions (follows from `BlockWordReplay.replay`,
  `pastObserves` and `transactionsObserve` by `WordStorageReplay.submissionFrames`
  and `observed_submissionFramePayments`). -/
  historyFrames : r.frames.map Prod.fst =
    ((history.settledFrames ++ block.bodyTrace.transactions.settledFrames).flatMap
      submissionFramePayments).map Prod.fst
  /-- The submission frames are the submission-payment frames of the history
  extended by this block. -/
  stepFrames : r.frames.map Prod.fst =
    ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).map Prod.fst
  /-- Each frame's caller and calldata are its entry's caller and payload
  (follows from `BlockWordReplay.replay` by `WordStorageReplay.submissionFrames`). -/
  payloads : ∀ pair ∈ r.frames,
    pair.1.sevm.caller = pair.2.caller ∧ pair.1.sevm.data = submissionPayload pair.2
  /-- The frames' entries are all outputs followed by the remaining queue
  (follows from `Fifo` by `wordSubmissionFrames_entries`). -/
  entries : r.frames.map Prod.snd = r.outputs ++ (Blanc.WithdrawalRequest.system r.model).queue

end BlockWordReplay

/-- FIFO for one actual configured block under word-fee admission. A witness
`r : BlockWordReplay` splits the block's exact word replay into the earlier
history, its user transactions and its canonical reset, and seven units hold:
- `BoundaryModel`: the request-boundary model is a word-admitted history that
  storage represents;
- `Emission`: the block's withdrawal request bytes are `systemOutput` of that
  model, its first `min 16 queue` entries in order;
- `AfterReset`: the system-stepped model is a word-admitted history that the
  storage after the block represents;
- `Fifo`: outputs plus the remaining queue are exactly the committed
  submissions in order;
- `Provenance`: each output or queued entry is, position for position, the
  `(caller, pubkey, amount)` of exactly one committed submission frame of the
  trace;
- `WordBookkeepingSafe`, before and after the reset: every bookkeeping value
  stays within `wordOccurrenceCap` and every live queue slot is the unwrapped
  `4 + 3 * index + offset`, never slots 0–3. -/
def BlockWordFifo {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post) : Prop :=
  ∃ r : BlockWordReplay history block,
    r.BoundaryModel ∧ r.Emission ∧ r.AfterReset ∧ r.Fifo ∧ r.Provenance ∧
    WordBookkeepingSafe r.model ∧ WordBookkeepingSafe (Blanc.WithdrawalRequest.system r.model)

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
  have prefixFrames := prefixReplay.submissionFrames
  rw [List.map_append, pastMap, transactionMap, ← List.flatMap_append,
    observed_submissionFramePayments] at prefixFrames
  have fullFrames := (history_word_submission_frames (.step history block) replay observed).1
  rw [resetFrames] at fullFrames
  have entries := wordSubmissionFrames_entries (past ++ transactionEvents)
  rw [prefixReplay.fold_eq, prefixOutputs] at *
  rw [replay.fold_eq, finalModel, fullOutputs] at *
  have payload := block_requests_of_request_rep history block code _ prefixRep
  exact ⟨⟨past, transactionEvents, reset, replay, pastMap, transactionMap, resetKind, resetPre⟩,
    ⟨prefixHistory, prefixRep⟩, ⟨payload.1, payload.2.1, payload.2.2⟩, ⟨fullHistory, fullRep⟩,
    conservation, ⟨prefixFrames.1, fullFrames, prefixFrames.2, entries.trans conservation⟩,
    ⟨excessLe, countLe, headLe, tailLe, lengthEq, sumLt, slotLt, prefixSlots⟩,
    ⟨fullExcessLe, fullCountLe, fullHeadLe, fullTailLe, fullLengthEq, fullSumLt, fullSlotLt,
      fullSlots⟩⟩

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
