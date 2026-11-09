import Blanc.Lift.BuilderRequest.Occurrence
import Blanc.Lift.BuilderRequest.Deposit.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.Fifo

/-!
# The deposit contract's history, occurrence-indexed

`Occurrence` for the builder deposit contract (request type `0x03`, 184-byte records, 64 per block), from its deployed
storage, under the premises of `history_delivers`. The observers read the history only: `submissions` (every committed
paid submission, in output form, amount little-endian), `blockEmissions` (a block's type-3 request bytes cut into
184-byte records), `emissions`, `remainingQueue` (the final storage's live queue, read through `recordBytes`),
`queueAtRequests` (the live queue in the storage the block's request step read) and `boundarySubmissions`.

* `history_fifo`: the submissions are the emissions followed by the remaining queue.
* `history_block`: a block's type-3 request bytes are its emitted records; at Amsterdam it emits the first 64 records
  of the queue its request step read, and that queue is the submissions through its request boundary minus the
  earlier emissions; at a covered fork it emits nothing.
* `history_fate`: every submission is emitted at exactly one block and position, or still queued at the end.
* `history_latency`: a record at index `q` of block `j`'s request-boundary queue is emitted by block `j + q / 64` as
  its record `q % 64`, and is submission occurrence `E_j + q`.
-/

namespace Blanc.Lift.BuilderRequest.Deposit.Indexed

open Jaune ChainLink Blanc.Lift.BuilderRequest.Occurrence
open Creation (address)

/-- The deposit queue, read back from storage in output form. -/
def reading : Reading contract where
  read := recordBytes
  size := 184
  size_pos := by decide
  out_length := fun r => by
    show (Record.out r).length = 184
    simp only [Record.out, List.length_append, List.length_reverse, r.pubkey_length, r.credentials_length,
      r.amount_length, r.signature_length]
  read_eq := fun {rd st} rep i hi => by
    have key : ∀ (x : B256) (n : Nat), x = n.toB256 → n < 6 →
        rd (x + recordKey st.head.toB256 i.toB256) = st.queue[i].word n := by
      intro x n hx hn
      subst hx
      have e := record_key_add 6 (st.head + i) 0 n
      rw [Nat.zero_add] at e
      rw [recordKey_slot st.head i, e]
      exact rep.live i hi n hn
    refine recordBytes_eq _ ?_ (key 1 1 (by decide) (by decide)) (key 2 2 (by decide) (by decide))
      (key 3 3 (by decide) (by decide)) (key 4 4 (by decide) (by decide)) (key 5 5 (by decide) (by decide))
    rw [recordKey_slot]
    exact rep.live i hi 0 (by decide)

/-- Every committed paid submission at the deposit contract, in order, in output form. -/
abbrev submissions (blocks : List KeptBlock) : List Bytes := Occurrence.submissions contract blocks

/-- The deposit records a block outputs as type-3 requests. -/
abbrev blockEmissions (b : KeptBlock) : List Bytes := Occurrence.blockEmissions reading 3 b

/-- The deposit records the blocks output as type-3 requests, block by block. -/
abbrev emissions (blocks : List KeptBlock) : List Bytes := Occurrence.emissions reading 3 blocks

/-- The live deposit queue at the history's end. -/
abbrev remainingQueue (stop : BlockChain) : List Bytes := Occurrence.remainingQueue reading stop

/-- The live deposit queue the block's request step read. -/
abbrev queueAtRequests (b : KeptBlock) : List Bytes := Occurrence.queueAtRequests reading b

/-- The deposit submissions a block keeps before its request step. -/
abbrev boundarySubmissions (b : KeptBlock) : List Bytes := Occurrence.boundarySubmissions contract b

/-- The premises of `history_delivers`: a kept history from the deployed storage, with the code installed, no code at
the system address, no system-address sender, authority or creation, and at most `2 ^ 256` wei paid in. -/
structure Clean (cfg : ChainConfig) (start : BlockChain) (blocks : List KeptBlock) (stop : BlockChain) : Prop where
  history : KeptHistory cfg start blocks stop
  installed : start.state.getCode address = code
  fresh : start.state.getStor address = Stor.empty
  noSystemCode : start.state.getCode systemAddress = ByteArray.empty
  senders : History.NoSender systemAddress blocks
  authorities : History.NoAuthority systemAddress blocks
  creates : History.NoCreate systemAddress blocks
  budget : History.paid address blocks ≤ 2 ^ 256

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

theorem Clean.premises (H : Clean cfg start blocks stop) : Premises contract cfg start blocks stop deployedQueue := by
  obtain ⟨frames, -, corr, -⟩ := history_chain H.history H.installed H.fresh H.noSystemCode H.senders
    H.authorities H.creates
  have range := range_of_budget (corr.value_le.trans H.budget)
  have hsub : History.submitted contract blocks = Delivery.submissions frames := corr.submissions.symm
  have slots : queueBase contract.width (deployedQueue.tail + (History.submitted contract blocks).length) ≤
      2 ^ 256 := by
    show 4 + 6 * (0 + _) ≤ 2 ^ 256
    rw [hsub, Nat.zero_add]
    exact range
  refine ⟨H.history, H.installed, ?_, H.noSystemCode, H.senders, H.authorities, H.creates, slots, ?_⟩
  · show Delivery.Holds contract (start.state.getStor address) deployedQueue
    rw [H.fresh]
    exact deployed_represents
  · show 0 + _ < 2 ^ 256
    have : 4 + 6 * (0 + (History.submitted contract blocks).length) ≤ 2 ^ 256 := slots
    omega

theorem start_queue : (deployedQueue.queue.map contract.out) = [] := rfl

/-- **The deposit history FIFO.** Every committed paid deposit submission is, in order, either a record the blocks
emitted as a type-3 request or a record still in the final queue. -/
theorem history_fifo (H : Clean cfg start blocks stop) :
    submissions blocks = emissions blocks ++ remainingQueue stop := by
  have fifo := Occurrence.history_fifo reading linked H.premises
  rwa [start_queue, List.nil_append] at fifo

/-- **One block, at the deposit contract.** A block's type-3 request bytes are its emitted records, 184 bytes each.
At a covered fork it emits nothing. At Amsterdam it emits the first 64 records of the queue its request step read, and
the submissions through its request boundary are the earlier blocks' emissions followed by that queue. -/
theorem history_block (H : Clean cfg start blocks stop) {pre post : List KeptBlock} {b : KeptBlock}
    (split : blocks = pre ++ b :: post) :
    ((blockEmissions b).flatten = blockDelivered 3 b ∧ ∀ e ∈ blockEmissions b, e.length = 184) ∧
    (b.fork ≠ .amsterdam → blockEmissions b = [] ∧ queueAtRequests b = []) ∧
    (b.fork = .amsterdam →
      blockEmissions b = (queueAtRequests b).take 64 ∧
      submissions pre ++ boundarySubmissions b = emissions pre ++ queueAtRequests b) := by
  have h := Occurrence.history_block reading linked H.premises split
  rw [start_queue, List.nil_append] at h
  exact h

/-- **The fate of every deposit submission.** Submission `n` is either emitted as record `k` of block `j` for exactly
one pair `(j, k)` (with `j` before an anchor `a` exactly when `n` is below the first `a` blocks' emissions), or still
queued at the end at position `n − E`. -/
theorem history_fate (H : Clean cfg start blocks stop) (n : Nat) :
    (n < (emissions blocks).length ∧
      ∃ j k, ∃ hj : j < blocks.length, k < (blockEmissions blocks[j]).length ∧
        (emissions (blocks.take j)).length + k = n ∧
        (blockEmissions blocks[j])[k]? = (submissions blocks)[n]? ∧
        (∀ a, j < a ↔ n < (emissions (blocks.take a)).length) ∧
        ∀ j' k' (hj' : j' < blocks.length), k' < (blockEmissions blocks[j']).length →
          (emissions (blocks.take j')).length + k' = n → j' = j ∧ k' = k) ∨
    ((emissions blocks).length ≤ n ∧
      (remainingQueue stop)[n - (emissions blocks).length]? = (submissions blocks)[n]?) := by
  have h := Occurrence.history_fate reading linked H.premises n
  rw [start_queue, List.nil_append] at h
  exact h

/-- **Deposit latency, occurrence-indexed.** A record at index `q` of the queue block `j`'s request step read, with
blocks `j` to `j + q / 64` all at Amsterdam, is record `q % 64` of block `j + q / 64`'s type-3 requests, preceded by
exactly the queue's records from position `64 * (q / 64)`; it is submission occurrence `E_j + q`, which is that
block's record `q % 64` in `history_fate`'s indexing. -/
theorem history_latency (H : Clean cfg start blocks stop) {j q : Nat} {B D : KeptBlock} {r : Bytes}
    (hB : blocks[j]? = some B) (hD : blocks[j + q / 64]? = some D)
    (amsterdam : ∀ i ≤ q / 64, ∀ x, blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (queueAtRequests B)[q]? = some r) :
    (blockEmissions D)[q % 64]? = some r ∧
    (∀ i ≤ q % 64, (blockEmissions D)[i]? = (queueAtRequests B)[64 * (q / 64) + i]?) ∧
    (submissions blocks)[(emissions (blocks.take j)).length + q]? = some r ∧
    (emissions (blocks.take j)).length + q = (emissions (blocks.take (j + q / 64))).length + q % 64 := by
  have h := Occurrence.history_latency reading linked H.premises (by decide) hB hD amsterdam queued
  rw [start_queue, List.nil_append] at h
  exact h

end Blanc.Lift.BuilderRequest.Deposit.Indexed
