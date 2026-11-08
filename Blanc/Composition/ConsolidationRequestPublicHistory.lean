import Blanc.Lift.ConsolidationRequest.Chain
import Blanc.Composition.BuilderRequestPublicObservers

/-!
# EIP-7251: FIFO over kept histories, from the checkpoint and at mainnet (C4)

The frozen C4 headlines over the public observers: every committed submission at the consolidation contract is, in
order, a record the blocks published or an entry still in the final queue.

* `history_fifo`: from a state where the predeploy is at its start (`CheckpointStart`: canonical code, the four
  words at inhibitor, 0, 0, 0, no code at SYSTEM_ADDRESS), over every kept history at covered forks with no
  SYSTEM_ADDRESS sender, authority or creation (`HistoryClean`) and at most `2 ^ 253` submissions.
* `history_fifo_mainnet`: the same from the observed pre-Prague checkpoint 22,431,083
  (`ConsolidationCheckpointObservation`), over every kept mainnet history after it. Mainnet's schedule names no
  Amsterdam activation, so its kept blocks are at covered forks and the scope premise is discharged.

Scope: the EIP-7251 user frames are proved on the covered forks (`ConsolidationRequest.exec_user_frame`), so
`history_fifo` takes `∀ b ∈ blocks, CoveredFork b.fork`; an Amsterdam block would need the Amsterdam user frames.

The observers here duplicate, under this module's namespace, those of the frozen statement packet
(`ConsolidationRequestPublicObservers`, written in parallel); integration keeps one copy.
-/

namespace Blanc.Composition.ConsolidationRequestPublicHistory

open Jaune Blanc Blanc.Lift
open Blanc.Lift.ConsolidationRequest (Record keptRecord recordOf data_words)
open Blanc.Lift.BuilderRequest (QueueState queueBase queueSlot)
open Blanc.Lift.RequestQueue (Holds)
open Blanc.Composition.BuilderRequestPublic (HistoryClean)

/-! ## Observers -/

/-- The EIP-7251 predeploy address `0x0000BBdDc7CE488642fb579F8B00f3a590007251`. -/
abbrev addr : Adr := consolidationRequestPredeployAddress

/-- The 414 canonical runtime bytes. -/
abbrev code : ByteArray := Blanc.consolidationRequestCode

/-- The canonical runtime sits at the predeploy. -/
def installed (w : State) : Prop := w.getCode addr = code

/-- Storage slot `k` of the predeploy in world `w`. -/
def word (w : State) (k : B256) : B256 := (w.getStor addr).get k

/-- Queue entry `i`, read from slots `4 + 4i` to `4 + 4i + 3`: the source address, then the 96 submitted bytes. -/
def queueRecord (s : B256 → B256) (i : Nat) : Bytes :=
  (s (4 + 4 * i).toB256).toAdr.toBytes ++ (s (4 + 4 * i + 1).toB256).toBytes ++
    (s (4 + 4 * i + 2).toB256).toBytes ++ (s (4 + 4 * i + 3).toB256).toBytes

/-- The live queue: entries from the head word (slot 2) up to, excluding, the tail word (slot 3). -/
def storedQueue (s : B256 → B256) : List Bytes :=
  (List.range ((s 3).toNat - (s 2).toNat)).map fun i => queueRecord s ((s 2).toNat + i)

/-- The queue still stored in world `w`. -/
def remainingQueue (w : State) : List Bytes := storedQueue (w.getStor addr).get

/-- A submission's record: the caller's 20 bytes, then its 96 calldata bytes (source pubkey, target pubkey). -/
def submissionRecord (f : Exec.Frame) : Bytes := f.sevm.caller.toBytes ++ f.sevm.data

/-- The records of the kept 96-byte user calls at the predeploy, in history order. -/
noncomputable def submissions (blocks : List KeptBlock) : List Bytes :=
  ((blocks.flatMap (KeptBlock.keptAt addr)).filter
    fun f => decide (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96)).map submissionRecord

/-- Split request bytes into 116-byte records; a short tail is kept, never dropped, so equality detects it. -/
def records116 (bytes : Bytes) : List Bytes :=
  (List.range ((bytes.length + 115) / 116)).map fun i => (bytes.drop (116 * i)).take 116

/-- The type-2 (consolidation) payloads of one block's actual request list, in order. -/
def blockConsolidations (b : KeptBlock) : Bytes :=
  (b.output.requests.filterMap fun r => match r with | 2 :: tail => some tail | _ => none).flatten

/-- The consolidation records the history's blocks published, in order. -/
def emissions (blocks : List KeptBlock) : List Bytes := blocks.flatMap fun b => records116 (blockConsolidations b)

/-- The predeploy at the root: canonical code, the deployed words, no code at SYSTEM_ADDRESS. -/
structure CheckpointStart (w : State) : Prop where
  /-- The canonical runtime is installed. -/
  code : installed w
  /-- Slot 0 holds the inhibitor: no user call has succeeded yet. -/
  excess : word w 0 = B256.max
  /-- No submission is counted. -/
  count : word w 1 = 0
  /-- The queue head is 0. -/
  head : word w 2 = 0
  /-- The queue tail is 0: the queue is empty. -/
  tail : word w 3 = 0
  /-- No code at SYSTEM_ADDRESS, so only the block's own call can dequeue. -/
  systemEmpty : w.getCode systemAddress = ByteArray.empty

/-- Chain reads at the shared pre-Prague checkpoint 22,431,083, adopted by the user on 2026-11-08. Provenance: Plans
`evidence/blanc-eip7251-consolidation-requests-v1/recon/` (three providers agree on the four words). The tip is
`Lift.WithdrawalRequest.WithdrawalDeploymentObservation.checkpointTip`'s block, and `code` is that record's
`consolidationAtP`. -/
structure ConsolidationCheckpointObservation (checkpoint : BlockChain) : Prop where
  /-- The checkpoint's last header: number 22431083, hash 0x28fb…f237, state root 0xab35…c0e3. -/
  tip : ∃ t, checkpoint.blocks.getLast? = some t ∧ t.header.number = 22431083 ∧
    t.header.hash = 0x28fb2c1d988435955e569451c6ad772f7fb5e61cddd7463c7b60e933ed5ff237 ∧
    t.header.stateRoot = 0xab350e0fe349aef68947ede26295f8946c34ce3af5e3ec76f4b26ddeef29c0e3
  /-- `eth_getCode(0x…7251)`: the canonical bytes. -/
  code : installed checkpoint.state
  /-- `eth_getStorageAt` slot 0: the inhibitor. -/
  excess : word checkpoint.state 0 = B256.max
  /-- `eth_getStorageAt` slot 1: 0. -/
  count : word checkpoint.state 1 = 0
  /-- `eth_getStorageAt` slot 2: 0. -/
  head : word checkpoint.state 2 = 0
  /-- `eth_getStorageAt` slot 3: 0. -/
  tail : word checkpoint.state 3 = 0
  /-- `eth_getCode(0xff…fe)` is empty. -/
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty

/-- Every committed submission is, in order, a record the blocks published or an entry still in the final queue. -/
def Fifo (blocks : List KeptBlock) (final : State) : Prop :=
  submissions blocks = emissions blocks ++ remainingQueue final

/-! ## Bridges from the observers to the queue model -/

theorem record_out_length (r : Record) : r.out.length = 116 := by
  simp only [Record.out, Adr.toBytes, List.length_append, UInt32.length_toBytes, B128.length_toBytes,
    r.data_length]

/-- Whole records cut back into the records. -/
theorem records116_flatMap (rs : List Record) : records116 (rs.flatMap Record.out) = rs.map Record.out :=
  RequestQueue.Link.chunks_flatMap 116 Record.out record_out_length (by decide) rs

theorem blockConsolidations_eq (b : KeptBlock) :
    blockConsolidations b = RequestQueue.Link.blockDelivered 2 b := by
  unfold blockConsolidations RequestQueue.Link.blockDelivered
  congr 2
  funext r
  rcases r with _ | ⟨t, tail⟩
  · rfl
  · unfold RequestQueue.Link.entryOf
    by_cases h : t = 2
    · subst h
      rfl
    · dsimp only
      rw [ite_eq_right h]
      split
      · rename_i heq
        cases heq
        exact absurd rfl h
      · rfl

/-- The observed submissions are the bytes of the records the kept frames submit. -/
theorem submissions_eq (blocks : List KeptBlock) :
    submissions blocks = ((RequestQueue.Link.kept addr blocks).filterMap keptRecord).map Record.out := by
  unfold submissions
  change (List.filter _ (RequestQueue.Link.kept addr blocks)).map _ = _
  induction RequestQueue.Link.kept addr blocks with
  | nil => rfl
  | cons f fs ih =>
      rw [List.filter_cons, List.filterMap_cons]
      unfold keptRecord
      by_cases h : f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96
      · rw [ite_eq_left (decide_eq_true h), dite_eq_left h, List.map_cons, List.map_cons, ih]
        rfl
      · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using h), dite_eq_right h]
        exact ih

/-- **The stored queue is the represented queue's bytes.** -/
theorem remainingQueue_eq {w : State} {st : QueueState Record}
    (rep : Holds ConsolidationRequest.queue (w.getStor addr) st) :
    remainingQueue w = st.queue.map Record.out := by
  unfold remainingQueue storedQueue
  have hh : ((w.getStor addr).get 2).toNat = st.head := by
    rw [show (w.getStor addr).get 2 = st.head.toB256 from rep.head]
    exact B256.toNat_toB256_of_lt rep.head_lt
  have ht : ((w.getStor addr).get 3).toNat = st.tail := by
    rw [show (w.getStor addr).get 3 = st.tail.toB256 from rep.tail]
    exact B256.toNat_toB256_of_lt rep.tail_lt
  rw [hh, ht, show st.tail - st.head = st.queue.length by have := rep.coherent; omega]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hi : i < st.queue.length := by simpa only [List.length_map] using h2
    have live := rep.live i hi
    have w0 : (w.getStor addr).get (4 + 4 * (st.head + i)).toB256 = st.queue[i].word 0 := live 0 (by decide)
    have w1 : (w.getStor addr).get (4 + 4 * (st.head + i) + 1).toB256 = st.queue[i].word 1 := live 1 (by decide)
    have w2 : (w.getStor addr).get (4 + 4 * (st.head + i) + 2).toB256 = st.queue[i].word 2 := live 2 (by decide)
    have w3 : (w.getStor addr).get (4 + 4 * (st.head + i) + 3).toB256 = st.queue[i].word 3 := live 3 (by decide)
    unfold queueRecord
    rw [w0, w1, w2, w3]
    change (st.queue[i].source.toB256).toAdr.toBytes ++ _ ++ _ ++ _ = st.queue[i].out
    rw [toAdr_toB256, List.append_assoc, List.append_assoc, ← List.append_assoc (Record.word _ 1).toBytes]
    exact congrArg (st.queue[i].source.toBytes ++ ·) (data_words _)

/-- The start words represent the empty queue at the inhibitor. -/
theorem CheckpointStart.holds {w : State} (start : CheckpointStart w) :
    Holds ConsolidationRequest.queue (w.getStor addr) ⟨2 ^ 256 - 1, 0, 0, 0, []⟩ where
  coherent := rfl
  excess_lt := by decide
  count_lt := by decide
  head_lt := by decide
  tail_lt := by decide
  live_lt := fun i hi => absurd hi (Nat.not_lt_zero _)
  excess := start.excess.trans (by decide)
  count := start.count
  head := start.head
  tail := start.tail
  live := fun i hi => absurd hi (Nat.not_lt_zero _)

/-- Whole records per block: the emissions are the records the history's type 2 requests carry. -/
theorem emissions_records {blocks : List KeptBlock}
    (wholes : ∀ b ∈ blocks, ∃ rs : List Record, RequestQueue.Link.blockDelivered 2 b = rs.flatMap Record.out) :
    ∃ rs : List Record, emissions blocks = rs.map Record.out ∧
      RequestQueue.Link.delivered 2 blocks = rs.flatMap Record.out := by
  induction blocks with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons b bs ih =>
      obtain ⟨rs, hr⟩ := wholes b List.mem_cons_self
      obtain ⟨rs', e, d⟩ := ih fun x hx => wholes x (List.mem_cons_of_mem _ hx)
      refine ⟨rs ++ rs', ?_, ?_⟩
      · change records116 (blockConsolidations b) ++ emissions bs = _
        rw [blockConsolidations_eq, hr, records116_flatMap, e, List.map_append]
      · change RequestQueue.Link.blockDelivered 2 b ++ RequestQueue.Link.delivered 2 bs = _
        rw [hr, d, List.flatMap_append]

/-! ## C4 -/

/-- **C4. FIFO from the checkpoint.** For every kept history at covered forks from a state where the predeploy is at
its start, with no SYSTEM_ADDRESS sender, authority or creation, and at most `2 ^ 253` submissions, the FIFO law
holds at its end. -/
theorem history_fifo {cfg : ChainConfig} {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg checkpoint blocks final) (covered : ∀ b ∈ blocks, CoveredFork b.fork)
    (start : CheckpointStart checkpoint.state) (clean : HistoryClean blocks)
    (cap : (submissions blocks).length ≤ 2 ^ 253) :
    Fifo blocks final.state := by
  have hsub := submissions_eq blocks
  have hlen : ((RequestQueue.Link.kept addr blocks).filterMap keptRecord).length ≤ 2 ^ 253 := by
    rw [hsub, List.length_map] at cap
    exact cap
  have hlen' : ((RequestQueue.Link.kept consolidationRequestPredeployAddress blocks).filterMap
      keptRecord).length ≤ 2 ^ 253 := hlen
  have h256 : (2 : Nat) ^ 256 = 8 * 2 ^ 253 := rfl
  obtain ⟨k, st', rep, queue, out, wholes⟩ := ConsolidationRequest.history_delivered history covered start.code
    start.systemEmpty clean.senders clean.authorities clean.creates start.holds
    (by dsimp only; unfold queueBase; omega) (by dsimp only; omega)
  obtain ⟨rs, e, d⟩ := emissions_records wholes
  rw [List.nil_append] at queue out
  have same : rs.map Record.out = (((RequestQueue.Link.kept addr blocks).filterMap keptRecord).take k).map
      Record.out := by
    rw [← records116_flatMap, ← records116_flatMap, ← d, out]
  unfold Fifo
  rw [remainingQueue_eq rep, queue, e, same, ← List.map_append, List.take_append_drop, hsub]

/-- Mainnet's schedule names no Amsterdam activation, so a kept mainnet block is at a covered fork. -/
theorem mainnet_covered {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory mainnetChainConfig checkpoint blocks final) : ∀ b ∈ blocks, CoveredFork b.fork := by
  intro b hb
  obtain ⟨next, step⟩ := history.mem_step b hb
  rcases step.kept with covered | amsterdam
  · exact covered
  · have mem := ChainConfig.forkAt_mem step.forkAt
    rw [amsterdam] at mem
    exact absurd mem (by decide +kernel)

/-- The observation gives the start. -/
theorem ConsolidationCheckpointObservation.start {checkpoint : BlockChain}
    (obs : ConsolidationCheckpointObservation checkpoint) : CheckpointStart checkpoint.state :=
  ⟨obs.code, obs.excess, obs.count, obs.head, obs.tail, obs.systemEmpty⟩

/-- **C4 at mainnet.** From the observed pre-Prague checkpoint 22,431,083, for every kept mainnet history after it. -/
theorem history_fifo_mainnet {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory mainnetChainConfig checkpoint blocks final)
    (obs : ConsolidationCheckpointObservation checkpoint)
    (clean : HistoryClean blocks) (cap : (submissions blocks).length ≤ 2 ^ 253) :
    Fifo blocks final.state :=
  history_fifo history (mainnet_covered history) obs.start clean cap

end Blanc.Composition.ConsolidationRequestPublicHistory
