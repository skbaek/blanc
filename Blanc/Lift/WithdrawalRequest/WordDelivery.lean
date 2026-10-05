import Blanc.ExecutionHistoryExtension
import Blanc.Lift.WithdrawalRequest.WordFifo

/-!
Delivery bound for the EIP-7002 queue over actual configured histories: an entry
at index `q` of the queue model at a block's request boundary is emitted by the
block exactly `q / 16` blocks later, at position `q % 16` of its request output,
after exactly the entries that were ahead of it.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

/-! ## Uniqueness of the represented model -/

theorem entry_eq_of_words {left right : Blanc.WithdrawalRequest.Entry}
    (caller : callerWord left = callerWord right) (pubkey : pubkeyWord left = pubkeyWord right)
    (pubkeyAmount : pubkeyAmountWord left = pubkeyAmountWord right) : left = right := by
  have callerEq : left.caller = right.caller := Adr.toB256_inj caller
  have bytes : pubkeyAmountBytes left = pubkeyAmountBytes right := by
    rw [← pubkeyAmountWord_bytes, ← pubkeyAmountWord_bytes, pubkeyAmount]
  have pubkeyEq : left.pubkey.val = right.pubkey.val := by
    rw [← queueWords_pubkey left, ← queueWords_pubkey right, pubkey, pubkeyAmount]
  have amountBytes : left.amount.toBytes = right.amount.toBytes := by
    simp only [pubkeyAmountBytes, pubkeyEq, List.append_assoc, List.append_cancel_left_eq,
      List.append_cancel_right_eq] at bytes
    exact bytes
  have amountEq : left.amount = right.amount := by
    rw [← UInt64.toUInt64_toBytes left.amount, amountBytes, UInt64.toUInt64_toBytes]
  obtain ⟨leftCaller, ⟨leftPubkey, _⟩, leftAmount⟩ := left
  obtain ⟨rightCaller, ⟨rightPubkey, _⟩, rightAmount⟩ := right
  simp only at callerEq pubkeyEq amountEq
  subst callerEq pubkeyEq amountEq
  rfl

/-- Storage determines the queue model it represents. -/
theorem RepresentsStorage.unique {storage : B256 → B256}
    {left right : Blanc.WithdrawalRequest.State} (leftRep : RepresentsStorage storage left)
    (rightRep : RepresentsStorage storage right) : left = right := by
  have word : ∀ {a b : Nat}, a < 2 ^ 256 → b < 2 ^ 256 → a.toB256 = b.toB256 → a = b := by
    intro a b aLt bLt eq
    have numeric := congrArg B256.toNat eq
    rwa [B256.toNat_toB256_of_lt aLt, B256.toNat_toB256_of_lt bLt] at numeric
  have excess := word leftRep.bounds.excess_lt rightRep.bounds.excess_lt
    (leftRep.excess.symm.trans rightRep.excess)
  have count := word leftRep.bounds.count_lt rightRep.bounds.count_lt
    (leftRep.count.symm.trans rightRep.count)
  have head := word leftRep.bounds.head_lt rightRep.bounds.head_lt
    (leftRep.head.symm.trans rightRep.head)
  have tail := word leftRep.bounds.tail_lt rightRep.bounds.tail_lt
    (leftRep.tail.symm.trans rightRep.tail)
  have leftCoherent := leftRep.coherent
  have rightCoherent := rightRep.coherent
  change left.head + left.queue.length = left.tail at leftCoherent
  change right.head + right.queue.length = right.tail at rightCoherent
  have length : left.queue.length = right.queue.length := by omega
  have queue : left.queue = right.queue := by
    apply List.ext_getElem length
    intro i leftLt rightLt
    obtain ⟨leftCaller, leftPubkey, leftAmount⟩ := leftRep.live i leftLt
    obtain ⟨rightCaller, rightPubkey, rightAmount⟩ := rightRep.live i rightLt
    rw [head] at leftCaller leftPubkey leftAmount
    exact entry_eq_of_words (leftCaller.symm.trans rightCaller)
      (leftPubkey.symm.trans rightPubkey) (leftAmount.symm.trans rightAmount)
  obtain ⟨_, _, _, _, _⟩ := left
  obtain ⟨_, _, _, _, _⟩ := right
  simp only at excess count head tail queue
  subst excess count head tail queue
  rfl

/-! ## Pure queue drain along the per-event model -/

/-- The canonical reset events of a replay (the specification's `system` steps). -/
def WordReplayEvent.isReset (event : WordReplayEvent) : Bool :=
  match event.kind with
  | .system => true
  | _ => false

/-- Along any sequence of model updates with `n` resets, a queue whose first
`16 * n` entries all exist loses exactly that prefix; everything else is appended. -/
theorem wordModel_queue_drain (events : List WordReplayEvent)
    (state : Blanc.WithdrawalRequest.State) (queue later : List Blanc.WithdrawalRequest.Entry)
    (m : Nat) (current : state.queue = queue.drop (16 * m) ++ later)
    (room : 16 * (m + events.countP WordReplayEvent.isReset) ≤ queue.length) :
    ∃ later', (events.foldl wordModelUpdate state).queue =
      queue.drop (16 * (m + events.countP WordReplayEvent.isReset)) ++ later' := by
  induction events generalizing state m later with
  | nil => exact ⟨later, by simpa only [List.foldl_nil, List.countP_nil, Nat.add_zero] using current⟩
  | cons event events ih =>
    rw [List.foldl_cons]
    cases kind : event.kind with
    | system =>
      have reset : event.isReset = true := by simp only [WordReplayEvent.isReset, kind]
      rw [List.countP_cons_of_pos reset] at room ⊢
      have step : (wordModelUpdate state event).queue =
          queue.drop (16 * (m + 1)) ++ later := by
        simp only [wordModelUpdate, kind, Blanc.WithdrawalRequest.system, maxPerBlock, current]
        rw [List.drop_append_of_le_length (by rw [List.length_drop]; omega), List.drop_drop]
        congr 2
      obtain ⟨later', eq⟩ := ih _ later (m + 1) step (by omega)
      exact ⟨later', by rw [eq]; congr 3; omega⟩
    | submission entry iterations output =>
      have reset : event.isReset = false := by simp only [WordReplayEvent.isReset, kind]
      rw [List.countP_cons_of_neg (by simp only [reset, Bool.false_eq_true, not_false_eq_true])]
        at room ⊢
      exact ih _ (later ++ [entry]) m (by
        simp only [wordModelUpdate, kind, submit_queue, current, List.append_assoc]) room
    | getter iterations output =>
      have reset : event.isReset = false := by simp only [WordReplayEvent.isReset, kind]
      rw [List.countP_cons_of_neg (by simp only [reset, Bool.false_eq_true, not_false_eq_true])]
        at room ⊢
      exact ih _ later m (by simp only [wordModelUpdate, kind, current]) room

/-! ## Counting canonical resets -/

/-- In a guarded replay, the reset events are exactly the frames called by the system address. -/
theorem WordStorageReplay.countP_isReset {pre post : Stor} {events : List WordReplayEvent}
    (replay : WordStorageReplay pre events post) :
    events.countP WordReplayEvent.isReset =
      (events.map WordReplayEvent.frame).countP (fun frame => frame.sevm.caller == systemAddress) := by
  induction replay with
  | nil => rfl
  | @cons storage post event rest guard tail ih =>
    have head : event.isReset = (event.frame.sevm.caller == systemAddress) := by
      have input := guard.input
      cases kind : event.kind with
      | system =>
        have caller : event.frame.sevm.caller = systemAddress := by
          simpa only [wordEventInput, kind] using input
        simp only [WordReplayEvent.isReset, kind, caller, beq_self_eq_true]
      | submission entry iterations output =>
        have caller : event.frame.sevm.caller ≠ systemAddress := by
          simp only [wordEventInput, kind] at input
          exact input.1
        simp only [WordReplayEvent.isReset, kind, caller, Bool.false_eq, beq_eq_false_iff_ne, ne_eq, not_false_eq_true]
      | getter iterations output =>
        have caller : event.frame.sevm.caller ≠ systemAddress := by
          simp only [wordEventInput, kind] at input
          exact input.1
        simp only [WordReplayEvent.isReset, kind, caller, Bool.false_eq, beq_eq_false_iff_ne, ne_eq, not_false_eq_true]
    rw [List.countP_cons, List.map_cons, List.countP_cons, ih, head]

/-- Every configured block of a history contributes exactly one retained
system-called frame of the withdrawal-request predeploy: its canonical reset. -/
theorem history_reset_frames {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : history.NoSenderAt systemAddress)
    (authorities : history.NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty) :
    (history.settledFrames.flatMap balanceFrameObservation).countP
      (fun frame => frame.sevm.caller == systemAddress) = history.blockCount := by
  induction history with
  | refl => rfl
  | step prior block ih =>
    obtain ⟨reset, partition, _, resetCaller, _, _, _, _, userCallers⟩ :=
      block_protocol_observation_partition prior block installed senders authorities avoid
        systemEmpty
    have priorCount := ih senders.1 authorities.1 (fun root member =>
      avoid root (by rw [ConfiguredHistoryTrace.rawFrames]; exact List.mem_append_left _ member))
    have users : (block.bodyTrace.transactions.settledFrames.flatMap
        balanceFrameObservation).countP (fun frame => frame.sevm.caller == systemAddress) = 0 := by
      rw [List.countP_eq_zero]
      intro frame member
      simp only [userCallers frame member, beq_iff_eq, not_false_eq_true]
    rw [ConfiguredHistoryTrace.settledFrames, List.flatMap_append, List.countP_append, priorCount,
      partition, List.countP_append, users, List.countP_singleton, resetCaller, beq_self_eq_true,
      ite_eq_left rfl, ConfiguredHistoryTrace.blockCount]

/-! ## Delivery over configured histories -/

/-- Queue drain between two request boundaries. Under the hypotheses of
`block_word_fifo` for the history through block `D`, where that history extends
the history through block `B` by exactly `depth` further blocks, and for the
queue model `modelB` represented by the predeploy's storage at `B`'s request
boundary (unique by `RepresentsStorage.unique`): the storage at `D`'s request
boundary represents a model `modelD`, `D`'s withdrawal request output is
`systemOutput modelD`, and if `modelB` held at least `16 * depth` entries then
`modelD`'s queue is `modelB`'s queue without its first `16 * depth` entries,
followed only by later entries. -/
theorem block_word_queue_after
    {cfg : ChainConfig} {checkpoint preB postB preD postD : BlockChain}
    (historyB : ConfiguredHistoryTrace cfg checkpoint preB)
    (blockB : ConfiguredBlockTrace cfg preB postB)
    (historyD : ConfiguredHistoryTrace cfg checkpoint preD)
    (blockD : ConfiguredBlockTrace cfg preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : ((ConfiguredHistoryTrace.step historyD blockD).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap)
    (modelB : Blanc.WithdrawalRequest.State)
    (repB : RepresentsStorage (blockB.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get modelB) :
    ∃ modelD : Blanc.WithdrawalRequest.State,
      RepresentsStorage (blockD.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get modelD ∧
      blockD.bodyTrace.requests.withdrawalOut.returnData = systemOutput modelD ∧
      (16 * depth ≤ modelB.queue.length →
        ∃ later, modelD.queue = modelB.queue.drop (16 * depth) ++ later) := by
  have code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode := by
    apply installed (withdrawalRequestPredeployAddress, Blanc.withdrawalRequestCode)
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr (Or.inl trivial))
  obtain ⟨events, replay, observed, _, _, prefixes⟩ :=
    history_word_model (.step historyD blockD) code init occurrences
  -- `D`'s request boundary
  obtain ⟨pastD, transactionsD, resetD, eventsD, _, _, resetKindD, _, prefixReplayD, _, _⟩ :=
    block_word_event_partition historyD blockD installed senders authorities avoid systemEmpty
      replay observed
  obtain ⟨_, repD, _⟩ := prefixes (pastD ++ transactionsD) [resetD] eventsD
  rw [prefixReplayD.fold_eq] at repD
  refine ⟨_, repD, (block_requests_of_request_rep historyD blockD code _ repD).1, ?_⟩
  intro room
  -- `B`'s request boundary inside the same replay
  have sendersB := extension.noSenderAt senders
  have authoritiesB := extension.noAuthorityAt authorities
  have avoidB : ∀ root ∈ (ConfiguredHistoryTrace.step historyB blockB).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress :=
    fun root member => avoid root (extension.rawFrames_mem root member)
  obtain ⟨resetFrameB, partitionB, _, _, _, resetPreB, _, _, userCallersB⟩ :=
    block_protocol_observation_partition historyB blockB installed sendersB authoritiesB avoidB
      systemEmpty
  obtain ⟨suffix, framesEq⟩ := extension.settledFrames
  have mapped : events.map WordReplayEvent.frame =
      (historyB.settledFrames.flatMap balanceFrameObservation ++
        blockB.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation) ++
      (resetFrameB :: suffix.flatMap balanceFrameObservation) := by
    rw [observed, framesEq]
    simp only [ConfiguredHistoryTrace.settledFrames, List.flatMap_append, partitionB,
      List.append_assoc, List.singleton_append]
  obtain ⟨prefixB, restB, eventsB, prefixMapB, restMapB⟩ := List.map_eq_append_iff.mp mapped
  obtain ⟨resetB, rest, restEq, resetEqB, _⟩ := List.map_eq_cons_iff.mp restMapB
  rw [restEq] at eventsB
  have segmentsB := (show WordStorageReplay
    (checkpoint.state.getStor withdrawalRequestPredeployAddress) (prefixB ++ resetB :: rest)
    (postD.state.getStor withdrawalRequestPredeployAddress) from eventsB ▸ replay).split
  have boundaryB : prefixB.foldl wordEventUpdate
      (checkpoint.state.getStor withdrawalRequestPredeployAddress) =
      blockB.bodyTrace.requestBenv.state.getStor withdrawalRequestPredeployAddress := by
    rw [segmentsB.2.head_guard.pre, resetEqB]
    change resetFrameB.pre.state.getStor withdrawalRequestPredeployAddress = _
    rw [resetPreB]
  obtain ⟨_, repPrefixB, _⟩ := prefixes prefixB (resetB :: rest) eventsB
  rw [boundaryB] at repPrefixB
  have modelBEq := RepresentsStorage.unique repPrefixB repB
  -- the events between the two request boundaries
  have lengths := congrArg List.length (eventsB.symm.trans eventsD)
  simp only [List.length_append, List.length_cons, List.length_nil] at lengths
  have takeB : (pastD ++ transactionsD).take prefixB.length = prefixB := by
    have whole := congrArg (List.take prefixB.length) (eventsB.symm.trans eventsD)
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length,
      List.take_append_of_le_length (by simp only [List.length_append]; omega)] at whole
    exact whole.symm
  have splitD : pastD ++ transactionsD =
      prefixB ++ (pastD ++ transactionsD).drop prefixB.length := by
    conv => lhs; rw [← List.take_append_drop prefixB.length (pastD ++ transactionsD)]
    rw [takeB]
  -- reset counts
  have countAll := replay.countP_isReset
  rw [observed, history_reset_frames _ installed senders authorities avoid systemEmpty,
    eventsD, List.countP_append, List.countP_singleton] at countAll
  have resetD' : resetD.isReset = true := by simp only [WordReplayEvent.isReset, resetKindD]
  rw [resetD', ite_eq_left rfl] at countAll
  have countB := WordStorageReplay.countP_isReset segmentsB.1
  have usersB : (blockB.bodyTrace.transactions.settledFrames.flatMap
      balanceFrameObservation).countP (fun frame => frame.sevm.caller == systemAddress) = 0 := by
    rw [List.countP_eq_zero]
    intro frame member
    simp only [userCallersB frame member, beq_iff_eq, not_false_eq_true]
  rw [prefixMapB, List.countP_append, usersB, Nat.add_zero,
    history_reset_frames historyB installed sendersB.1 authoritiesB.1 (fun root member =>
      avoidB root (by rw [ConfiguredHistoryTrace.rawFrames]; exact List.mem_append_left _ member))
      systemEmpty] at countB
  have blocks := extension.blockCount
  simp only [ConfiguredHistoryTrace.blockCount] at blocks countAll
  rw [splitD, List.countP_append, countB] at countAll
  have countMid : ((pastD ++ transactionsD).drop prefixB.length).countP
      WordReplayEvent.isReset = depth := by omega
  -- the model at `D` is the model at `B` advanced through those events
  have drain := wordModel_queue_drain ((pastD ++ transactionsD).drop prefixB.length) modelB
    modelB.queue [] 0 (by simp only [Nat.mul_zero, List.drop_zero, List.append_nil])
    (by rw [countMid, Nat.zero_add]; exact room)
  rw [countMid, Nat.zero_add, ← modelBEq, ← List.foldl_append, ← splitD] at drain
  simpa only [← modelBEq] using drain

/-- D1 delivery bound. Let the history through block `D` extend the history
through block `B` by exactly `depth = q / 16` further configured blocks (`B`
counted as depth 0), under the hypotheses of `block_word_fifo` for the history
through `D`. If `entry` sits at index `q` of the queue model `modelB` represented
at `B`'s request boundary (the model of `BlockWordFifo`, unique by
`RepresentsStorage.unique`), then `D`'s withdrawal request output is
`systemOutput modelD` for the model `modelD` represented at `D`'s request
boundary, `entry` is at position `q % 16` of `emitted modelD`, and the emitted
entries up to and including it are exactly `modelB`'s entries at indices
`16 * depth, ..., q`: entries ahead of it in this block were ahead of it at `B`,
and no later submission precedes it. With `block_word_queue_after` at each smaller
depth, every block before `D` emits only entries that were ahead of it at `B`. -/
theorem block_word_delivery
    {cfg : ChainConfig} {checkpoint preB postB preD postD : BlockChain}
    (historyB : ConfiguredHistoryTrace cfg checkpoint preB)
    (blockB : ConfiguredBlockTrace cfg preB postB)
    (historyD : ConfiguredHistoryTrace cfg checkpoint preD)
    (blockD : ConfiguredBlockTrace cfg preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : ((ConfiguredHistoryTrace.step historyD blockD).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap)
    (modelB : Blanc.WithdrawalRequest.State)
    (repB : RepresentsStorage (blockB.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get modelB)
    {q : Nat} {entry : Blanc.WithdrawalRequest.Entry} (queued : modelB.queue[q]? = some entry)
    (exactDepth : depth = q / 16) :
    ∃ modelD : Blanc.WithdrawalRequest.State,
      RepresentsStorage (blockD.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get modelD ∧
      blockD.bodyTrace.requests.withdrawalOut.returnData = systemOutput modelD ∧
      (emitted modelD)[q % 16]? = some entry ∧
      (emitted modelD).take (q % 16 + 1) =
        (modelB.queue.drop (16 * depth)).take (q % 16 + 1) := by
  have bound : q < modelB.queue.length := (List.getElem?_eq_some_iff.mp queued).1
  have split : 16 * depth + q % 16 = q := by
    rw [exactDepth]
    exact Nat.div_add_mod q 16
  have position : q % 16 < 16 := Nat.mod_lt q (by decide)
  obtain ⟨modelD, repD, output, drain⟩ := block_word_queue_after historyB blockB historyD
    blockD extension installed senders authorities avoid systemEmpty init occurrences modelB repB
  obtain ⟨later, queue⟩ := drain (by omega)
  have ahead : q % 16 + 1 ≤ (modelB.queue.drop (16 * depth)).length := by
    rw [List.length_drop]
    omega
  refine ⟨modelD, repD, output, ?_, ?_⟩
  · rw [emitted, queue, maxPerBlock, List.getElem?_take_of_lt position,
      List.getElem?_append_left (by omega), List.getElem?_drop, split, queued]
  · rw [emitted, queue, maxPerBlock, List.take_take, Nat.min_eq_left (by omega),
      List.take_append_of_le_length ahead]

end Blanc.Lift.WithdrawalRequest
