import Blanc.Lift.WithdrawalRequest.WordFifo
import Blanc.Lift.WithdrawalRequest.ProtocolOccurrences

/-!
# E5(ii): what a mid-block drain does to the FIFO conclusion

`block_word_fifo` concludes `BlockWordFifo`: every committed submission is, in order,
an earlier block's output, this block's emitted prefix, or still queued.  If the
queue is empty at this block's request boundary although the block committed a
submission and no earlier block did, the conclusion is false: the submission was
dequeued by something other than a system call (a frame whose caller is
SYSTEM_ADDRESS, see `SystemDrain.drain_exec`) and is never emitted.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

/-- Two model states represented by the same storage have queues of the same length:
the head and tail words and coherence fix it. -/
theorem _root_.Blanc.WithdrawalRequest.RepresentsStorage.queue_length_eq {storage : B256 → B256}
    {s t : Blanc.WithdrawalRequest.State} (hs : RepresentsStorage storage s)
    (ht : RepresentsStorage storage t) : s.queue.length = t.queue.length := by
  have head := congrArg B256.toNat (hs.head.symm.trans ht.head)
  have tail := congrArg B256.toNat (hs.tail.symm.trans ht.tail)
  rw [B256.toNat_toB256_of_lt hs.bounds.head_lt, B256.toNat_toB256_of_lt ht.bounds.head_lt]
    at head
  rw [B256.toNat_toB256_of_lt hs.bounds.tail_lt, B256.toNat_toB256_of_lt ht.bounds.tail_lt]
    at tail
  have cs : s.head + s.queue.length = s.tail := hs.coherent
  have ct : t.head + t.queue.length = t.tail := ht.coherent
  omega

/-- **A drained request boundary refutes the block FIFO.**  If no submission was
committed before the block, the block committed at least one, and the predeploy storage
at the block's request boundary represents a state with an empty queue, then
`BlockWordFifo` fails for that block: the committed submission is neither an earlier
output, nor emitted by this block's system call, nor still queued. -/
theorem not_blockWordFifo_of_drained {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      initial)
    (before : history.settledFrames.flatMap submissionFramePayments = [])
    (committed : block.bodyTrace.transactions.settledFrames.flatMap submissionFramePayments ≠ [])
    (drained : ∃ s : Blanc.WithdrawalRequest.State,
      RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get s ∧ s.queue = []) :
    ¬ BlockWordFifo history block := by
  rintro ⟨past, transactionEvents, reset, replay, pastMap, -, -, -, fifo⟩
  obtain ⟨hist, rep, -, -, -, -, -, frames, -⟩ := fifo
  obtain ⟨s, srep, sempty⟩ := drained
  -- the model at the request boundary has an empty queue
  have modelEmpty := rep.queue_length_eq srep
  rw [sempty, List.length_nil] at modelEmpty
  have initialQueue : (initial : Blanc.WithdrawalRequest.State).queue = [] := rfl
  have conserved := hist.conservation
  rw [initialQueue, List.nil_append] at conserved
  have conservedLen := congrArg List.length conserved
  simp only [List.length_append, List.length_map] at conservedLen
  -- the block committed at least one submission
  have framesLen := congrArg List.length frames
  have entriesLen := congrArg List.length (wordSubmissionFrames_entries (past ++ transactionEvents))
  simp only [List.length_map, List.flatMap_append, List.length_append] at framesLen entriesLen
  have someLen : 0 < (block.bodyTrace.transactions.settledFrames.flatMap
      submissionFramePayments).length := List.length_pos_iff.mpr committed
  -- no earlier block produced an output
  rw [List.append_assoc] at replay
  have pastReplay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      past _ := replay.split.1
  have pastFrames := history_word_submission_frames history pastReplay pastMap
  rw [before, List.length_nil] at pastFrames
  have pastModel := WordStorageReplay.wordModel pastReplay WordHistory.start init (by
    rw [List.length_nil, Nat.zero_add, pastFrames.2.2]
    exact Nat.zero_le _)
  have pastConserved := pastModel.1.conservation
  rw [initialQueue, List.nil_append, List.nil_append, List.nil_append] at pastConserved
  have pastLen := congrArg List.length pastConserved
  simp only [List.length_append, List.length_map, pastFrames.2.2] at pastLen
  rw [before, List.length_nil] at framesLen
  omega

/-- A system message whose target holds spawn-free, non-delegating code other than the
withdrawal predeploy's settles no submission payment: every settled frame targets it. -/
theorem system_submissions_eq_nil
    {benv : Benv} {target : Adr} {data : Bytes} {state : Jaune.State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (code : ByteArray)
    (installed : benv.state.getCode target = code)
    (reach : SpawnFreeReach code) (nondelegating : ¬ isValidDelegation code)
    (foreign : target ≠ withdrawalRequestPredeployAddress) :
    trace.settledFrames.flatMap submissionFramePayments = [] := by
  have confined := trace.rawFrames_target_of_code
    (installed ▸ reach) (installed ▸ nondelegating)
  apply List.flatMap_eq_nil_iff.mpr
  intro frame member
  have targetEq := confined (Blanc.Exec.Frame.rootDeriv (frame := frame))
    (trace.mem_rawFrames_of_mem_settledFrames frame member)
  unfold submissionFramePayments
  exact ite_eq_right (fun submission => foreign (targetEq.symm.trans submission.1.1))

/-- **A block's submission payments are its transactions'.**  With the canonical system code
installed at the checkpoint, the beacon-roots, history-storage and consolidation messages
settle no frame at the predeploy, and the withdrawal message's only frame has caller
SYSTEM_ADDRESS.  No SYSTEM_ADDRESS exclusion is needed. -/
theorem block_submissions_eq_transactions {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state) :
    block.settledFrames.flatMap submissionFramePayments =
      block.bodyTrace.transactions.settledFrames.flatMap submissionFramePayments := by
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
  have beaconEmpty := system_submissions_eq_nil block.bodyTrace.beacon beaconRootsCode
    beaconCode.1 beaconFacts.1 beaconFacts.2.1 (by decide +kernel)
  have historyEmpty := system_submissions_eq_nil block.bodyTrace.history historyStorageCode
    historyCode.2.1 historyFacts.1 historyFacts.2.1 (by decide +kernel)
  have consolidationEmpty := system_submissions_eq_nil block.bodyTrace.requests.consolidation
    consolidationRequestCode consolidationCode.2.2.2 consolidationFacts.1
    consolidationFacts.2.1 (by decide +kernel)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, resetEmpty, _⟩ :=
    block_requests_reset_occurrence history block (installed _ withdrawalMember)
  simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
    RequestsTrace.settledFrames, List.flatMap_append, beaconEmpty, historyEmpty,
    consolidationEmpty, resetEmpty, List.nil_append, List.append_nil]

/-- **The E5(ii) negative control, as a proposition**: a configured history meeting every
hypothesis of `block_word_fifo` except `systemEmpty` (code at SYSTEM_ADDRESS instead) whose
block fails `BlockWordFifo`. -/
def SystemEmptyLoadBearing : Prop :=
  ∃ (cfg : ChainConfig) (checkpoint pre post : BlockChain)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post),
    SystemCodeInstalled checkpoint.state ∧
    (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress ∧
    (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress ∧
    (∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress) ∧
    checkpoint.state.getCode systemAddress ≠ ByteArray.empty ∧
    RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial ∧
    ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap ∧
    ¬ BlockWordFifo history block

/-- **E5(ii), the statement.**  The SYSTEM_ADDRESS exclusion `systemEmpty` is load-bearing
for `block_word_fifo` once one configured history satisfies every other hypothesis of
`block_word_fifo` (installed system code, no sender or authority at SYSTEM_ADDRESS, no
code-free root frame targeting it, INIT, the occurrence cap), has code at SYSTEM_ADDRESS,
commits a submission in a block after none before, and reaches that block's request
boundary with the queue drained.  The witness (block assembly) instantiates the premises;
this theorem turns it into the negative control. -/
theorem systemEmpty_loadBearing {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemCode : checkpoint.state.getCode systemAddress ≠ ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      initial)
    (occurrences : ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap)
    (before : history.settledFrames.flatMap submissionFramePayments = [])
    (committed : block.bodyTrace.transactions.settledFrames.flatMap submissionFramePayments ≠ [])
    (drained : ∃ s : Blanc.WithdrawalRequest.State,
      RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get s ∧ s.queue = []) :
    SystemEmptyLoadBearing :=
  ⟨cfg, checkpoint, pre, post, history, block, installed, senders, authorities, avoid,
    systemCode, init, occurrences,
    not_blockWordFifo_of_drained history block init before committed drained⟩

end Blanc.Lift.WithdrawalRequest
