import Blanc.Lift.WithdrawalRequest.WordFifo

/-!
# FIFO observed directly from an execution history

The three observers below read only committed call frames, block request bytes,
and final contract storage. They return lists of withdrawal records: each valid
record is the caller's 20 bytes, the public key's 48 bytes, and the amount's
8 little-endian bytes. Comparing these records compares every field and its order.
No observer chooses an abstract model or a replay witness.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

/-- A submission's caller and literal calldata, serialized in withdrawal-output
format (the input amount is big-endian, so its eight bytes are reversed). -/
def submissionRecord (frame : Exec.Frame) : Bytes :=
  frame.sevm.caller.toBytes ++ frame.sevm.data.take 48 ++ (frame.sevm.data.drop 48).reverse

/-- All committed EIP-7002 submissions in execution order, including calls inside
transactions. `settledFrames` excludes reverted effects; `submissionFramePayments`
selects nonstatic, non-SYSTEM calls to EIP-7002 with exactly 56 bytes of calldata. -/
def submissions {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) : List Bytes :=
  (history.settledFrames.flatMap submissionFramePayments).map
    (fun pair => submissionRecord pair.1)

/-- Split a withdrawal batch into 76-byte records. A short trailing record is
retained, never dropped or padded, so equality with valid records detects it. -/
def withdrawalRecords (bytes : Bytes) : List Bytes :=
  (List.range ((bytes.length + 75) / 76)).map fun i => (bytes.drop (76 * i)).take 76

/-- Read only type-1 payloads from the actual block request list, preserving
batch and record order and removing only the request-type byte. -/
def withdrawalRequestRecords (requests : List Bytes) : List Bytes :=
  requests.flatMap fun request =>
    match request with
    | tag :: payload => if tag = 1 then withdrawalRecords payload else []
    | [] => []

/-- All withdrawal records actually published in the history's block request lists. -/
def emissions {cfg : ChainConfig} {checkpoint : BlockChain} :
    {final : BlockChain} → ConfiguredHistoryTrace cfg checkpoint final → List Bytes
  | _, .refl _ _ _ => []
  | _, .step prior block =>
    emissions prior ++ withdrawalRequestRecords block.blockOutput.requests

/-- Read one queue entry's three concrete storage words in withdrawal-output format. -/
def storedQueueRecord (storage : B256 → B256) (index : Nat) : Bytes :=
  (storage (queueSlot index 0)).toAdr.toBytes ++
    (storage (queueSlot index 1)).toBytes ++
    (storage (queueSlot index 2)).toBytes.take 16 ++
    ((storage (queueSlot index 2)).toBytes.drop 16 |>.take 8).reverse

/-- Read exactly the live queue, from the stored head (slot 2) up to but excluding
the stored tail (slot 3). Stale entries outside that interval are ignored. -/
def storedQueue (storage : B256 → B256) : List Bytes :=
  (List.range ((storage 3).toNat - (storage 2).toNat)).map fun i =>
    storedQueueRecord storage ((storage 2).toNat + i)

/-- The queue remaining in the final concrete EIP-7002 storage of this history. -/
def remainingQueue {cfg : ChainConfig} {checkpoint final : BlockChain}
    (_history : ConfiguredHistoryTrace cfg checkpoint final) : List Bytes :=
  storedQueue (final.state.getStor withdrawalRequestPredeployAddress).get

/-- Every committed submission is, in order, either an emitted withdrawal record
or an entry still in the final concrete queue. All three lists are direct observations
of this history, with no existential replay or abstract state in the statement. -/
def HistoryFifo {cfg : ChainConfig} {checkpoint final : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint final) : Prop :=
  submissions history = emissions history ++ remainingQueue history

/-! The rest of this file proves the correspondence to the internal model. -/

private theorem submissionRecord_eq {frame : Exec.Frame} {entry : Blanc.WithdrawalRequest.Entry}
    (caller : frame.sevm.caller = entry.caller)
    (payload : frame.sevm.data = submissionPayload entry) :
    submissionRecord frame = outputRecord entry := by
  simp only [submissionRecord, caller, payload, submissionPayload, outputRecord,
    ← entry.pubkey.property, List.take_left, List.drop_left]

private theorem storedQueueRecord_eq {storage : B256 → B256}
    {state : Blanc.WithdrawalRequest.State} (rep : RepresentsStorage storage state)
    (i : Nat) (hi : i < state.queue.length) :
    storedQueueRecord storage (state.head + i) = outputRecord state.queue[i] := by
  obtain ⟨caller, pubkey, packed⟩ := rep.live i hi
  have suffixLength : (state.queue[i].pubkey.val.drop 32).length = 16 := by
    rw [List.length_drop, state.queue[i].pubkey.property]
  rw [storedQueueRecord, caller, pubkey, packed, callerWord_address,
    List.append_assoc _ _ (List.take 16 _), queueWords_pubkey]
  simp only [pubkeyAmountWord_bytes, pubkeyAmountBytes, List.append_assoc]
  rw [← suffixLength, List.drop_left, ← UInt64.length_toBytes state.queue[i].amount,
    List.take_left]
  rfl

theorem storedQueue_eq {storage : B256 → B256}
    {state : Blanc.WithdrawalRequest.State} (rep : RepresentsStorage storage state) :
    storedQueue storage = state.queue.map outputRecord := by
  have coherent : state.head + state.queue.length = state.tail := rep.coherent
  have length : state.tail - state.head = state.queue.length := by omega
  simp only [storedQueue, rep.head, rep.tail,
    B256.toNat_toB256_of_lt rep.bounds.head_lt,
    B256.toNat_toB256_of_lt rep.bounds.tail_lt, length]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simpa only [List.getElem_map, List.getElem_range] using storedQueueRecord_eq rep i hi

theorem withdrawalRecords_outputRecords (entries : List Blanc.WithdrawalRequest.Entry) :
    withdrawalRecords (outputRecords entries) = entries.map outputRecord := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    have count : ((outputRecords (entry :: entries)).length + 75) / 76 = entries.length + 1 := by
      rw [outputRecords_length, List.length_cons]
      omega
    rw [withdrawalRecords, count, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.mul_zero, List.drop_zero, outputRecords, List.map_cons]
    rw [List.take_append_of_le_length (by rw [outputRecord_length]),
      List.take_of_length_le (by rw [outputRecord_length])]
    congr 1
    rw [← ih, withdrawalRecords, outputRecords_length]
    have count' : (76 * entries.length + 75) / 76 = entries.length := by omega
    rw [count']
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_def]
    change ((outputRecord entry ++ outputRecords entries).drop (76 * (i + 1))).take 76 = _
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm (76 * i) 76,
      ← outputRecord_length entry, List.drop_append, Nat.add_sub_cancel_left,
      List.drop_eq_nil_of_le (by omega), List.nil_append]

theorem withdrawalRequestRecords_optional (tag : UInt8) (payload : Bytes) :
    withdrawalRequestRecords (optionalRequestEntry tag payload) =
      if tag = 1 then withdrawalRecords payload else [] := by
  by_cases nonempty : payload.length > 0
  · simp only [optionalRequestEntry, ite_eq_left nonempty, withdrawalRequestRecords,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append]
  · have empty : payload = [] := List.length_eq_zero_iff.mp (by omega)
    subst payload
    simp only [optionalRequestEntry, List.length_nil, Nat.lt_irrefl, ite_false,
      withdrawalRequestRecords, List.flatMap_nil, withdrawalRecords, Nat.zero_add,
      Nat.reduceDiv, List.range_zero, List.map_nil, ite_self]

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

theorem emission_eq_records {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint pre}
    {block : ConfiguredBlockTrace cfg pre post} {r : BlockWordReplay history block}
    (emission : r.Emission) :
    withdrawalRequestRecords block.blockOutput.requests = (emitted r.model).map outputRecord := by
  rw [emission.requests]
  simp only [withdrawalRequestRecords, List.flatMap_append]
  change withdrawalRequestRecords (optionalRequestEntry 0 _) ++
    withdrawalRequestRecords (optionalRequestEntry 1 _) ++
    withdrawalRequestRecords (optionalRequestEntry 2 _) = _
  rw [withdrawalRequestRecords_optional, withdrawalRequestRecords_optional,
    withdrawalRequestRecords_optional]
  simp only [show (0 : UInt8) ≠ 1 from by decide, show (2 : UInt8) ≠ 1 from by decide,
    ite_false, ite_true, List.nil_append, List.append_nil, systemOutput,
    withdrawalRecords_outputRecords]

private theorem historyFifo_step {cfg : ChainConfig} {checkpoint pre post : BlockChain}
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

/-- Direct history-level FIFO from a represented INIT checkpoint. This supporting
form retains the original environmental assumptions; the deployment-rooted
headline below derives the initialization and EIP-7002 installation facts. -/
theorem history_fifo_of_checkpoint
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
    have earlierAvoid : ∀ root ∈ history.rawFrames,
        root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress := by
      intro root member
      exact avoid root (List.mem_append_left _ member)
    have code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode := by
      apply installed (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
      simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr (Or.inr (Or.inl trivial))
    exact historyFifo_step history block (ih senders.1 authorities.1 earlierAvoid cap) code cap
      (block_word_fifo_of_checkpoint history block installed senders authorities avoid
        systemEmpty init occurrences)

/-- After canonical Cancun deployment and its admitted preactivation prefix,
every committed submission in the subsequent configured history is, in order,
either a withdrawal record actually published by its blocks or a record still
in the final concrete queue. The empty history is included. No replay witness,
abstract state, or separate last block occurs in the conclusion.

The prefix selects Cancun; the history's blocks select Prague/Osaka/BPO1/BPO2.
Other system-code installation, SYSTEM exclusions and the cumulative submission
cap are the same explicit assumptions as the supporting block theorem. -/
theorem history_fifo
    {cfg : ChainConfig} {checkpoint final : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint)
    (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint final)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : history.NoSenderAt systemAddress)
    (authorities : history.NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions history).length ≤ wordOccurrenceCap) :
    HistoryFifo history := by
  have initialized := deployment.initialized admission
  exact history_fifo_of_checkpoint history
    (otherInstalled.with_withdrawal initialized.checkpointCode) senders authorities avoid
    initialized.systemEmpty initialized.checkpointStorage (by
      simpa only [submissions, List.length_map] using occurrences)

end Blanc.Lift.WithdrawalRequest
