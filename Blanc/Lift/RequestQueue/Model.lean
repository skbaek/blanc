import Blanc.Lift.RequestQueue.Drain

/-!
# The request queue model over a list of effects

What one frame at a request contract does to its queue, in unbounded naturals: it pushes one record, keeps
the queue, or drains it, with the excess it stores given as a function of the excess and count it reads.
`run` folds the effects and `deliveries` lists what each drain takes, and `fifo` is the first-in-first-out law:
the records delivered, in order, followed by the records still queued, are the starting queue followed by the
records pushed, in order. Nothing is dropped, duplicated or reordered.

This model is shared by the plain family (EIP-7002 and EIP-7251 shapes: no calldata latch, the excess arm of
`RequestSystem.PlainExcess`) and the EIP-8282 builder family (`BuilderRequest.Delivery.Event.effect`, whose
latch is a drain storing the inhibitor). The layout lemmas below (`represents_push`, `queueSlot_ne_of_lt`) are
the storage side of a push on a `Represents` image.
-/

namespace Blanc.Lift.RequestQueue

open Jaune
open BuilderRequest (QueueState queueBase queueSlot Represents)

/-- What one frame does to a request queue. -/
inductive Effect (Record : Type) where
  /-- A record is appended at the back. -/
  | push (r : Record)
  /-- The queue and its metadata are unchanged. -/
  | keep
  /-- The oldest records leave, the count clears, and the excess becomes `next excess count`. -/
  | drain (next : Nat → Nat → Nat)

variable {Record : Type}

/-- The queue after a push: the record at the back, count and tail one higher. -/
def push (st : QueueState Record) (r : Record) : QueueState Record :=
  ⟨st.excess, st.count + 1, st.head, st.tail + 1, st.queue ++ [r]⟩

/-- The queue after one effect, for a cap of records per drain. -/
def apply (cap : Nat) (st : QueueState Record) : Effect Record → QueueState Record
  | .push r => push st r
  | .keep => st
  | .drain next => drainedBy cap (next st.excess st.count) st

/-- The records one effect delivers: a drain takes the oldest `min(length, cap)`. -/
def taken (cap : Nat) (st : QueueState Record) : Effect Record → List Record
  | .drain _ => st.queue.take cap
  | _ => []

/-- The records a list of effects pushes, in order. -/
def pushed : List (Effect Record) → List Record
  | [] => []
  | .push r :: es => r :: pushed es
  | _ :: es => pushed es

/-- The queue after a list of effects. -/
def run (cap : Nat) (st : QueueState Record) (es : List (Effect Record)) : QueueState Record :=
  es.foldl (apply cap) st

/-- The records each effect of a list delivers, in order. -/
def deliveries (cap : Nat) : QueueState Record → List (Effect Record) → List (List Record)
  | _, [] => []
  | st, e :: es => taken cap st e :: deliveries cap (apply cap st e) es

/-- How many records a list of effects delivers. -/
def deliveredCount (cap : Nat) (st : QueueState Record) (es : List (Effect Record)) : Nat :=
  (deliveries cap st es).flatten.length

theorem pushed_append (xs ys : List (Effect Record)) : pushed (xs ++ ys) = pushed xs ++ pushed ys := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    cases e <;> simp only [List.cons_append, pushed, ih]

theorem pushed_cons_length (e : Effect Record) (es : List (Effect Record)) :
    (pushed (e :: es)).length = (pushed [e]).length + (pushed es).length := by
  rw [show e :: es = [e] ++ es from rfl, pushed_append, List.length_append]

theorem run_append (cap : Nat) (st : QueueState Record) (xs ys : List (Effect Record)) :
    run cap st (xs ++ ys) = run cap (run cap st xs) ys := by
  simp only [run, List.foldl_append]

theorem deliveries_append (cap : Nat) (st : QueueState Record) (xs ys : List (Effect Record)) :
    deliveries cap st (xs ++ ys) = deliveries cap st xs ++ deliveries cap (run cap st xs) ys := by
  induction xs generalizing st with
  | nil => rfl
  | cons e xs ih =>
    simp only [List.cons_append, deliveries, ih]
    rfl

theorem apply_queue_drain (cap : Nat) (st : QueueState Record) (next : Nat → Nat → Nat) :
    (apply cap st (.drain next)).queue = st.queue.drop cap :=
  drainedBy_queue cap _ st

/-- One effect in the FIFO's terms: what it takes, then the next queue, are the queue with what it pushes. -/
theorem taken_apply (cap : Nat) (st : QueueState Record) (e : Effect Record) (rest : List Record) :
    taken cap st e ++ ((apply cap st e).queue ++ rest) = st.queue ++ (pushed [e] ++ rest) := by
  cases e with
  | push r =>
    simp only [taken, apply, push, pushed, List.nil_append, List.append_assoc, List.singleton_append]
  | keep => rfl
  | drain next =>
    rw [apply_queue_drain, taken, ← List.append_assoc, List.take_append_drop]
    rfl

/-- **The FIFO over a list of effects.** The records the effects deliver, in order, followed by the records
still queued, are the starting queue followed by the records pushed, in order. -/
theorem fifo (cap : Nat) (st : QueueState Record) (es : List (Effect Record)) :
    (deliveries cap st es).flatten ++ (run cap st es).queue = st.queue ++ pushed es := by
  induction es generalizing st with
  | nil => simp only [deliveries, List.flatten_nil, pushed, run, List.foldl_nil, List.nil_append, List.append_nil]
  | cons e es ih =>
    have hc := taken_apply cap st e (pushed es)
    have hs : pushed (e :: es) = pushed [e] ++ pushed es := pushed_append [e] es
    simp only [deliveries, List.flatten_cons, List.append_assoc]
    show _ ++ (_ ++ (run cap (apply cap st e) es).queue) = _
    rw [ih, hc, hs]

/-- What has been delivered is a prefix of the pushed records. -/
theorem deliveries_flatten (cap : Nat) (st : QueueState Record) (es : List (Effect Record)) :
    (deliveries cap st es).flatten = (st.queue ++ pushed es).take (deliveredCount cap st es) := by
  rw [← fifo cap st es, deliveredCount, List.take_left]

/-- What is still queued is the pushed records after that prefix. -/
theorem run_queue (cap : Nat) (st : QueueState Record) (es : List (Effect Record)) :
    (run cap st es).queue = (st.queue ++ pushed es).drop (deliveredCount cap st es) := by
  rw [← fifo cap st es, deliveredCount, List.drop_left]

theorem apply_tail_le (cap : Nat) (st : QueueState Record) (e : Effect Record) :
    (apply cap st e).tail ≤ st.tail + (pushed [e]).length := by
  cases e with
  | push r => exact Nat.le_refl _
  | keep => exact Nat.le_refl _
  | drain next => exact (drainedBy_tail_le cap _ st).trans (Nat.le_add_right _ _)

theorem apply_count_le (cap : Nat) (st : QueueState Record) (e : Effect Record) :
    (apply cap st e).count ≤ st.count + (pushed [e]).length := by
  cases e with
  | push r => exact Nat.le_refl _
  | keep => exact Nat.le_refl _
  | drain next =>
    show (drainedBy cap _ st).count ≤ _
    rw [drainedBy_count]
    exact Nat.zero_le _

/-! ## A push on a represented image -/

theorem queueBase_succ (w t : Nat) : queueBase w (t + 1) = queueBase w t + w := by
  simp only [queueBase, Nat.mul_add, Nat.mul_one, Nat.add_assoc]

theorem queueBase_mono (w : Nat) {a b : Nat} (h : a ≤ b) : queueBase w a ≤ queueBase w b := by
  have := Nat.mul_le_mul_left w h
  simp only [queueBase]
  omega

/-- Adding one to a word in the word range. -/
theorem one_add_word (n : Nat) : (1 : B256) + n.toB256 = (n + 1).toB256 := by
  rw [show (1 : B256) = Nat.toB256 1 by decide, Nat.toB256_add_toB256, Nat.add_comm]

/-- Record slots of two records, each in word range, differ when the records do. -/
theorem queueSlot_ne_of_lt {w a b i j : Nat} (hab : a < b) (hi : i < w)
    (ha : queueBase w a + w ≤ 2 ^ 256) (hb : queueBase w b + w ≤ 2 ^ 256) (hj : j < w) :
    queueSlot w a i ≠ queueSlot w b j := by
  intro eq
  have := congrArg B256.toNat eq
  simp only [queueSlot] at this
  rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt (by omega)] at this
  have hle := queueBase_mono w (Nat.succ_le_of_lt hab)
  rw [Nat.succ_eq_add_one, queueBase_succ] at hle
  omega

/-- **A storage after a push represents the queue with the record at its back**: slots 0 and 2 as before, the
count and tail one higher, the new record's words at the tail's slots, and every other slot as before. -/
theorem represents_push {w : Nat} {words : Record → Nat → B256} {f g : B256 → B256} {st : QueueState Record}
    {r : Record} (rep : Represents w words f st) (hw : 0 < w) (slots : queueBase w st.tail + w ≤ 2 ^ 256)
    (count : st.count + 1 < 2 ^ 256) (g0 : g 0 = f 0) (g1 : g 1 = (st.count + 1).toB256) (g2 : g 2 = f 2)
    (g3 : g 3 = (st.tail + 1).toB256) (new : ∀ j, j < w → g (queueSlot w st.tail j) = words r j)
    (old : ∀ key, (1 : B256) ≠ key → (3 : B256) ≠ key → (∀ j, j < w → queueSlot w st.tail j ≠ key) → g key = f key) :
    Represents w words g (push st r) := by
  have coh := rep.coherent
  have htail : st.tail + 1 < 2 ^ 256 := by
    have : st.tail ≤ w * st.tail := Nat.le_mul_of_pos_left _ hw
    simp only [queueBase] at slots
    omega
  have hlen : (push st r).queue.length = st.queue.length + 1 := List.length_append ..
  refine ⟨?_, rep.excess_lt, count, rep.head_lt, htail, ?_, g0.trans rep.excess, g1,
    g2.trans rep.head, g3, ?_⟩
  · show st.head + (st.queue ++ [r]).length = st.tail + 1
    rw [List.length_append, List.length_singleton]
    omega
  · intro i hi
    rw [hlen] at hi
    by_cases h : i < st.queue.length
    · exact rep.live_lt i h
    · have hi' : st.head + i = st.tail := by omega
      show queueBase w (st.head + i) + w ≤ _
      rw [hi']
      exact slots
  · intro i hi j hj
    have hi1 : i < (st.queue ++ [r]).length := hi
    rw [hlen] at hi
    show g (queueSlot w (st.head + i) j) = words ((st.queue ++ [r])[i]'hi1) j
    by_cases h : i < st.queue.length
    · have hl := rep.live_lt i h
      rw [old _ (queueSlot_ne (n := 1) (by omega) (by decide) hl hj) (queueSlot_ne (n := 3) (by omega) (by decide) hl hj)
        (fun j' hj' => (queueSlot_ne_of_lt (by omega) hj hl slots hj').symm), rep.live i h j hj,
        List.getElem_append_left h]
    · have hi' : st.head + i = st.tail := by omega
      have hi2 : i = st.queue.length := by omega
      subst hi2
      rw [hi', new j hj, List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]

end Blanc.Lift.RequestQueue
