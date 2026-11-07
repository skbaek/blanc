import Jaune.Types
import Jaune.WordFacts

/-!
# The EIP-8282 request queue's storage layout

Both builder contracts keep the excess, count, head and tail in slots 0 to 3 and the queue's records
from slot 4, each record in `width` consecutive slots: 6 for deposits, 3 for exits. `Represents`
says a storage image holds a queue, with `words record j` the word a record keeps at its slot `j`.
This is a representation predicate. It claims nothing about which storage is reachable, and it
constrains only metadata and live records: stale slots may hold anything.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-- A request queue with its metadata, in unbounded naturals. -/
structure QueueState (Record : Type) where
  excess : Nat
  count : Nat
  head : Nat
  tail : Nat
  queue : List Record

/-- A record's first slot, before any word reduction. -/
def queueBase (width index : Nat) : Nat := 4 + width * index

/-- The storage key of a record's slot `offset`, modulo the word. -/
def queueSlot (width index offset : Nat) : B256 := (queueBase width index + offset).toB256

/-- `storage` holds `state`, with records of `width` slots whose contents `words` gives. The word
bounds are explicit premises, for a caller to establish. -/
structure Represents {Record : Type} (width : Nat) (words : Record → Nat → B256)
    (storage : B256 → B256) (state : QueueState Record) : Prop where
  /-- The live records sit between the head and the tail. -/
  coherent : state.head + state.queue.length = state.tail
  excess_lt : state.excess < 2 ^ 256
  count_lt : state.count < 2 ^ 256
  head_lt : state.head < 2 ^ 256
  tail_lt : state.tail < 2 ^ 256
  /-- Every live record's slots fit below the word modulus. -/
  live_lt : ∀ i, i < state.queue.length → queueBase width (state.head + i) + width ≤ 2 ^ 256
  excess : storage 0 = state.excess.toB256
  count : storage 1 = state.count.toB256
  head : storage 2 = state.head.toB256
  tail : storage 3 = state.tail.toB256
  /-- Every live record's words are in place. -/
  live : ∀ i (hi : i < state.queue.length) j, j < width →
    storage (queueSlot width (state.head + i) j) = words state.queue[i] j

/-- The key the contracts compute for a record, `4 + width * index`, is its slot 0. -/
theorem record_key (width index : Nat) :
    (4 : B256) + width.toB256 * index.toB256 = queueSlot width index 0 := by
  apply B256.toNat_inj
  simp only [queueSlot, queueBase, B256.toNat_add, B256.toNat_mul, B256.toNat_toB256, Nat.lo_eq,
    Nat.add_zero]
  change (4 + (width % 2 ^ 256 * (index % 2 ^ 256)) % 2 ^ 256) % 2 ^ 256 =
    (4 + width * index) % 2 ^ 256
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- The contracts step along a record's keys by adding the slot's offset. -/
theorem record_key_add (width index offset n : Nat) :
    n.toB256 + queueSlot width index offset = queueSlot width index (offset + n) := by
  simp only [queueSlot]
  rw [Nat.toB256_add_toB256, show n + (queueBase width index + offset) =
    queueBase width index + (offset + n) by omega]

end Blanc.Lift.BuilderRequest
