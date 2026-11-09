import Blanc.Lift.BuilderRequest.Occurrence
import Blanc.Lift.BuilderRequest.Exit.ChainLink
import Blanc.Lift.BuilderRequest.Exit.Fifo

/-!
# The exit contract's history, occurrence-indexed

`Occurrence` for the builder exit contract (request type `0x04`, 68-byte records: source then public key, 16 per
block), from its deployed inhibited storage, under the premises of `history_delivers`. The observers read the history
only: `submissions` (every committed paid submission, in output form, its caller as the source), `blockEmissions` (a
block's type-4 request bytes cut into 68-byte records), `emissions`, `remainingQueue` (the final storage's live queue, read through `recordBytes`),
`queueAtRequests` (the live queue in the storage the block's request step read) and `boundarySubmissions`.

* `history_fifo`: the submissions are the emissions followed by the remaining queue.
* `history_block`: a block's type-4 request bytes are its emitted records; at Amsterdam it emits the first 16 records
  of the queue its request step read, and that queue is the submissions through its request boundary minus the
  earlier emissions; at a covered fork it emits nothing.
* `Occurrence.history_fate reading linked H.premises n`: every submission is emitted at exactly one block and
  position, or still queued at the end (the generic statement is used as is: the start queue is empty).
* `history_latency`: a record at index `q` of block `j`'s request-boundary queue is emitted by block `j + q / 16` as
  its record `q % 16`, and is submission occurrence `E_j + q`.
-/

namespace Blanc.Lift.BuilderRequest.Exit.Indexed

open Jaune ChainLink Blanc.Lift.BuilderRequest.Occurrence
open Creation (address)

/-- The exit queue, read back from storage in output form. -/
def reading : Reading contract where
  read := recordBytes
  size := 68
  size_pos := by decide
  out_length := fun r => by
    show (Record.out r).length = 68
    simp only [Record.out, List.length_append, r.pubkey_length, Adr.toBytes, UInt32.length_toBytes,
      B128.length_toBytes]
  read_eq := fun {rd st} rep i hi => by
    have key : ∀ (x : B256) (n : Nat), x = n.toB256 → n < 3 →
        rd (x + recordKey st.head.toB256 i.toB256) = st.queue[i].word n := by
      intro x n hx hn
      subst hx
      have e := record_key_add 3 (st.head + i) 0 n
      rw [Nat.zero_add] at e
      rw [recordKey_slot st.head i, e]
      exact rep.live i hi n hn
    refine recordBytes_eq _ ?_ (key 1 1 (by decide) (by decide)) (key 2 2 (by decide) (by decide))
    rw [recordKey_slot]
    exact rep.live i hi 0 (by decide)

/-- Every committed paid submission at the exit contract, in order, in output form. -/
abbrev submissions (blocks : List KeptBlock) : List Bytes := Occurrence.submissions contract blocks

/-- The exit records a block outputs as type-4 requests. -/
abbrev blockEmissions (b : KeptBlock) : List Bytes := Occurrence.blockEmissions reading 4 b

/-- The exit records the blocks output as type-4 requests, block by block. -/
abbrev emissions (blocks : List KeptBlock) : List Bytes := Occurrence.emissions reading 4 blocks

/-- The live exit queue at the history's end. -/
abbrev remainingQueue (stop : BlockChain) : List Bytes := Occurrence.remainingQueue reading stop

/-- The live exit queue the block's request step read. -/
abbrev queueAtRequests (b : KeptBlock) : List Bytes := Occurrence.queueAtRequests reading b

/-- The exit submissions a block keeps before its request step. -/
abbrev boundarySubmissions (b : KeptBlock) : List Bytes := Occurrence.boundarySubmissions contract b

/-- The premises of `history_delivers`: a kept history from the deployed storage, with the code installed, no code at
the system address, no system-address sender, authority or creation, and at most `2 ^ 64` submissions. -/
structure Clean (cfg : ChainConfig) (start : BlockChain) (blocks : List KeptBlock) (stop : BlockChain) : Prop where
  history : KeptHistory cfg start blocks stop
  installed : start.state.getCode address = code
  fresh : start.state.getStor address = deployedStorage
  noSystemCode : start.state.getCode systemAddress = ByteArray.empty
  senders : History.NoSender systemAddress blocks
  authorities : History.NoAuthority systemAddress blocks
  creates : History.NoCreate systemAddress blocks
  few : (History.submitted contract blocks).length ≤ 2 ^ 64

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

theorem Clean.premises (H : Clean cfg start blocks stop) : Premises contract cfg start blocks stop deployedQueue := by
  have few := H.few
  have slots : queueBase contract.width (deployedQueue.tail + (History.submitted contract blocks).length) ≤
      2 ^ 256 := by
    show 4 + 3 * (0 + _) ≤ 2 ^ 256
    omega
  refine ⟨H.history, H.installed, ?_, H.noSystemCode, H.senders, H.authorities, H.creates, slots, ?_⟩
  · show Delivery.Holds contract (start.state.getStor address) deployedQueue
    rw [H.fresh]
    exact deployed_represents
  · show 0 + _ < 2 ^ 256
    omega

theorem start_queue : (deployedQueue.queue.map contract.out) = [] := rfl

/-- **The exit history FIFO.** Every committed paid exit submission is, in order, either a record the blocks
emitted as a type-4 request or a record still in the final queue. -/
theorem history_fifo (H : Clean cfg start blocks stop) :
    submissions blocks = emissions blocks ++ remainingQueue stop := by
  have fifo := Occurrence.history_fifo reading linked H.premises
  rwa [start_queue, List.nil_append] at fifo

/-- **One block, at the exit contract.** A block's type-4 request bytes are its emitted records, 68 bytes each.
At a covered fork it emits nothing. At Amsterdam it emits the first 16 records of the queue its request step read, and
the submissions through its request boundary are the earlier blocks' emissions followed by that queue. -/
theorem history_block (H : Clean cfg start blocks stop) {pre post : List KeptBlock} {b : KeptBlock}
    (split : blocks = pre ++ b :: post) :
    ((blockEmissions b).flatten = blockDelivered 4 b ∧ ∀ e ∈ blockEmissions b, e.length = 68) ∧
    (b.fork ≠ .amsterdam → blockEmissions b = [] ∧ queueAtRequests b = []) ∧
    (b.fork = .amsterdam →
      blockEmissions b = (queueAtRequests b).take 16 ∧
      submissions pre ++ boundarySubmissions b = emissions pre ++ queueAtRequests b) := by
  have h := Occurrence.history_block reading linked H.premises split
  rw [start_queue, List.nil_append] at h
  exact h

/-- **Exit latency, occurrence-indexed.** A record at index `q` of the queue block `j`'s request step read, with
blocks `j` to `j + q / 16` all at Amsterdam, is record `q % 16` of block `j + q / 16`'s type-4 requests, preceded by
exactly the queue's records from position `16 * (q / 16)`; it is submission occurrence `E_j + q`, which is that
block's record `q % 16` in `Occurrence.history_fate`'s indexing. -/
theorem history_latency (H : Clean cfg start blocks stop) {j q : Nat} {B D : KeptBlock} {r : Bytes}
    (hB : blocks[j]? = some B) (hD : blocks[j + q / 16]? = some D)
    (amsterdam : ∀ i ≤ q / 16, ∀ x, blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (queueAtRequests B)[q]? = some r) :
    (blockEmissions D)[q % 16]? = some r ∧
    (∀ i ≤ q % 16, (blockEmissions D)[i]? = (queueAtRequests B)[16 * (q / 16) + i]?) ∧
    (submissions blocks)[(emissions (blocks.take j)).length + q]? = some r ∧
    (emissions (blocks.take j)).length + q = (emissions (blocks.take (j + q / 16))).length + q % 16 := by
  have h := Occurrence.history_latency reading linked H.premises (by decide) hB hD amsterdam queued
  rw [start_queue, List.nil_append] at h
  exact h

end Blanc.Lift.BuilderRequest.Exit.Indexed
