import Blanc.Lift.ConsolidationRequest.Chain
import Blanc.ExecutionKeptClean
import Blanc.Composition.ConsolidationRequestPublicObservers

/-!
# EIP-7251: FIFO over kept histories, from the checkpoint and at mainnet (C4)

The C4 headlines over the public observers: every committed submission at the consolidation contract is, in
order, a record the blocks published or an entry still in the final queue.

* `history_fifo`: from a state where the predeploy is at its start (`CheckpointStart`: canonical code, the four
  words at inhibitor, 0, 0, 0, no code at SYSTEM_ADDRESS), over every kept history at covered forks with no
  SYSTEM_ADDRESS sender, authority or creation (`HistoryClean`) and at most `2 ^ 253` submissions.
* `history_fifo_mainnet`: the same from the observed pre-Prague checkpoint 22,431,083
  (`ConsolidationCheckpointObservation`), over every kept mainnet history after it. Mainnet's schedule names no
  Amsterdam activation, so its kept blocks are at covered forks and the scope premise is discharged.

Scope: the EIP-7251 user frames are proved on the covered forks (`ConsolidationRequest.exec_user_frame`), so
`history_fifo` takes `∀ b ∈ blocks, CoveredFork b.fork`; an Amsterdam block would need the Amsterdam user frames.

The observers are those of `ConsolidationRequestPublicObservers`; `HistoryClean` is the shared
`Blanc.HistoryClean` (`Blanc/ExecutionKeptClean.lean`).
-/

namespace Blanc.Composition.ConsolidationRequestPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.ConsolidationRequest (Record keptRecord recordOf data_words)
open Blanc.Lift.BuilderRequest (QueueState queueBase queueSlot)
open Blanc.Lift.RequestQueue (Holds)

/-! ## Bridges from the observers to the queue model -/

theorem record_out_length (r : Record) : r.out.length = 116 := by
  simp only [Record.out, Adr.toBytes, List.length_append, UInt32.length_toBytes, B128.length_toBytes,
    r.data_length]

/-- Whole records cut back into the records. -/
theorem records116_flatMap (rs : List Record) : records116 (rs.flatMap Record.out) = rs.map Record.out :=
  RequestQueue.Link.chunks_flatMap 116 Record.out record_out_length (by decide) rs

/-- A block's consolidation payloads are the chain link's type-2 bytes. -/
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

/-- The model's tail after a run of effects is at most the start tail plus the records pushed. -/
theorem run_tail_le (cap : Nat) (st : QueueState Record) (es : List (RequestQueue.Effect Record)) :
    (RequestQueue.run cap st es).tail ≤ st.tail + (RequestQueue.pushed es).length := by
  induction es generalizing st with
  | nil => exact Nat.le_add_right _ _
  | cons e es ih =>
    have h1 := ih (RequestQueue.apply cap st e)
    have h2 := RequestQueue.apply_tail_le cap st e
    have h3 := RequestQueue.pushed_cons_length e es
    change (RequestQueue.run cap (RequestQueue.apply cap st e) es).tail ≤ _
    omega

/-- **The pointers along a history.** Under C4's premises, at the history's end the head is at most the tail, and
the tail at most the number of submissions: the queue grows by one slot per submission and the call only advances
the head or resets both pointers. So `ordered` (C1b, C5a) holds there, and `room` holds while fewer than `2 ^ 253`
submissions have been made. -/
theorem history_pointers {cfg : ChainConfig} {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg checkpoint blocks final) (covered : ∀ b ∈ blocks, CoveredFork b.fork)
    (start : CheckpointStart checkpoint.state) (clean : HistoryClean blocks)
    (cap : (submissions blocks).length ≤ 2 ^ 253) :
    (word final.state 2).toNat ≤ (word final.state 3).toNat ∧
      (word final.state 3).toNat ≤ (submissions blocks).length := by
  obtain ⟨steps, chain, subs, -, -⟩ := RequestQueue.Link.history_chain ConsolidationRequest.linked history covered
    start.code start.systemEmpty clean.senders clean.authorities clean.creates
  have hlen : (RequestQueue.submissions steps).length = (submissions blocks).length := by
    rw [subs, submissions_eq, List.length_map]
    rfl
  have h256 : (2 : Nat) ^ 256 = 8 * 2 ^ 253 := rfl
  obtain ⟨rep, -⟩ := chain.holds start.holds (by rw [hlen]; dsimp only; unfold queueBase; omega)
    (by rw [hlen]; dsimp only; omega)
  have hh : (word final.state 2).toNat = (RequestQueue.queueAfter ⟨2 ^ 256 - 1, 0, 0, 0, []⟩ steps).head := by
    rw [show word final.state 2 = _ from rep.head]
    exact B256.toNat_toB256_of_lt rep.head_lt
  have ht : (word final.state 3).toNat = (RequestQueue.queueAfter ⟨2 ^ 256 - 1, 0, 0, 0, []⟩ steps).tail := by
    rw [show word final.state 3 = _ from rep.tail]
    exact B256.toNat_toB256_of_lt rep.tail_lt
  have coh := rep.coherent
  have tl := run_tail_le ConsolidationRequest.queue.cap ⟨2 ^ 256 - 1, 0, 0, 0, []⟩ (RequestQueue.effects steps)
  have hsubs : (RequestQueue.pushed (RequestQueue.effects steps)).length = (submissions blocks).length := hlen
  refine ⟨?_, ?_⟩
  · rw [hh, ht]
    omega
  · rw [ht]
    change (RequestQueue.run _ _ _).tail ≤ _
    rw [← hsubs]
    simpa only [Nat.zero_add] using tl

/-- Mainnet's schedule names no Amsterdam activation, so a kept mainnet block is at a covered fork. -/
theorem mainnet_covered {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory mainnetChainConfig checkpoint blocks final) : ∀ b ∈ blocks, CoveredFork b.fork :=
  history.mainnet_covered

/-- The observation gives the start. -/
theorem ConsolidationCheckpointObservation.start {checkpoint : BlockChain}
    (obs : ConsolidationCheckpointObservation checkpoint) : CheckpointStart checkpoint.state :=
  ⟨obs.code, obs.excess, obs.count, obs.head, obs.tail, obs.systemEmpty⟩

/-- **C4 at mainnet.**

From the observed pre-Prague checkpoint 22,431,083 (`ConsolidationCheckpointObservation`),
for every kept mainnet history after it without `SYSTEM_ADDRESS` senders, authorities, or creations
and within the `2 ^ 253` submission bound, the committed submissions equal the published consolidation
records followed by the remaining stored queue (`Fifo blocks final.state`), delegating covered-fork
membership to `KeptHistory.mainnet_covered`. -/
theorem history_fifo_mainnet {checkpoint final : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory mainnetChainConfig checkpoint blocks final)
    (obs : ConsolidationCheckpointObservation checkpoint)
    (clean : HistoryClean blocks) (cap : (submissions blocks).length ≤ 2 ^ 253) :
    Fifo blocks final.state :=
  history_fifo history (mainnet_covered history) obs.start clean cap

end Blanc.Composition.ConsolidationRequestPublic
