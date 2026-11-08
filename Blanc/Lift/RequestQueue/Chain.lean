import Blanc.Lift.RequestQueue.Model

/-!
# Exact delivery over a given sequence of request-contract frames

A `Queue` is a request contract's layout: its record type, the slots per record and the word each keeps, a
record's returned bytes, and the cap per drain. A `Step` is one frame at the contract packaged with its law:
the storage before and after, its `Effect` on the queue, its output, and that on represented storage (with the
pushed record's slots and the count in word range) the storage after represents the queue after the effect and
the output is exactly the records the effect delivers. Each contract builds its steps from its own frame laws
(`BuilderRequest.Delivery.Frame.toStep`, `ConsolidationRequest.Frame.toStep`), and nothing here names a fork, a
fee or a calldata latch.

`Chain` says each step ran on the storage the one before it left. The list is an input: "committed" here means
"in the given sequence", and that a chain's retained frames form such a list is a message and transaction level
statement this module does not make. `Chain.delivered` is the FIFO tied to the storage and the output.
-/

namespace Blanc.Lift.RequestQueue

open Jaune
open BuilderRequest (QueueState queueBase queueSlot Represents)

/-- A request contract's queue layout, as the sequence statements need it. -/
structure Queue where
  /-- A record of the queue. -/
  Record : Type
  /-- Slots per record. -/
  width : Nat
  /-- The word a record keeps at each of its slots. -/
  words : Record → Nat → B256
  /-- A record's bytes in a system call's output. -/
  out : Record → Bytes
  /-- Records a drain returns at most. -/
  cap : Nat

/-- `s` represents `st`, in the queue's layout. -/
abbrev Holds (q : Queue) (s : Stor) (st : QueueState q.Record) : Prop :=
  Represents q.width q.words (fun key => s.get key) st

/-- One frame at the contract with what its frame law gives, in the queue's terms. -/
structure Step (q : Queue) where
  /-- The contract's storage when the frame starts. -/
  before : Stor
  /-- The contract's storage when the frame ends. -/
  after : Stor
  /-- What the frame does to the queue. -/
  effect : Effect q.Record
  /-- What the frame adds to the request output: a drain's return data, otherwise nothing. -/
  output : Bytes
  /-- The frame law's storage side on a represented queue, with a pushed record's slots and the count in word
  range. -/
  holds : ∀ {st : QueueState q.Record}, Holds q before st →
    queueBase q.width (st.tail + (pushed [effect]).length) ≤ 2 ^ 256 →
    st.count + (pushed [effect]).length < 2 ^ 256 → Holds q after (apply q.cap st effect)
  /-- The frame law's output side on a represented queue. -/
  output_eq : ∀ {st : QueueState q.Record}, Holds q before st →
    output = (taken q.cap st effect).flatMap q.out

/-- The steps form a chain from `s` to `t`: each ran on the storage the one before it left. -/
inductive Chain {q : Queue} : Stor → List (Step q) → Stor → Prop where
  | nil (s : Stor) : Chain s [] s
  | cons {s : Stor} {f : Step q} {rest : List (Step q)} {t : Stor} (starts : f.before = s)
      (tail : Chain f.after rest t) : Chain s (f :: rest) t

variable {q : Queue}

/-- The steps' effects, in order. -/
def effects (steps : List (Step q)) : List (Effect q.Record) := steps.map Step.effect

/-- The records the steps push, in order. -/
def submissions (steps : List (Step q)) : List q.Record := pushed (effects steps)

/-- The queue model after the steps. -/
def queueAfter (st : QueueState q.Record) (steps : List (Step q)) : QueueState q.Record :=
  run q.cap st (effects steps)

/-- How many records the steps' drains deliver. -/
def deliveredRecords (st : QueueState q.Record) (steps : List (Step q)) : Nat :=
  deliveredCount q.cap st (effects steps)

/-- The bytes the steps output, concatenated. -/
def output (steps : List (Step q)) : Bytes := steps.flatMap Step.output

/-- **The sequence on a represented queue.** Storage at the chain's end represents the model's queue, and the
concatenated output is the concatenated records each drain delivered. `slots` and `count` are the word range:
every record slot the steps' pushes could reach, and the count, stay below the word modulus. -/
theorem Chain.holds {s t : Stor} {steps : List (Step q)} (chain : Chain s steps t)
    {st : QueueState q.Record} (rep : Holds q s st)
    (slots : queueBase q.width (st.tail + (submissions steps).length) ≤ 2 ^ 256)
    (count : st.count + (submissions steps).length < 2 ^ 256) :
    Holds q t (queueAfter st steps) ∧
      output steps = (deliveries q.cap st (effects steps)).flatten.flatMap q.out := by
  induction chain generalizing st with
  | nil s => exact ⟨rep, rfl⟩
  | @cons s f rest t starts tail ih =>
    subst starts
    have hs : (submissions (f :: rest)).length =
        (pushed [f.effect]).length + (submissions rest).length := pushed_cons_length _ _
    rw [hs] at slots count
    have hrep := f.holds rep ((queueBase_mono q.width (by omega)).trans slots) (by omega)
    have hout := f.output_eq rep
    have ht := apply_tail_le q.cap st f.effect
    have hc := apply_count_le q.cap st f.effect
    obtain ⟨h1, h2⟩ := ih hrep ((queueBase_mono q.width (by omega)).trans slots) (by omega)
    refine ⟨h1, ?_⟩
    show f.output ++ output rest = _
    rw [h2, hout]
    show _ = (taken q.cap st f.effect ++ (deliveries q.cap _ (effects rest)).flatten).flatMap q.out
    rw [List.flatMap_append]

/-- `Chain.holds` in the FIFO's terms. -/
structure Delivered (st : QueueState q.Record) (steps : List (Step q)) (t : Stor) : Prop where
  /-- Storage at the end of the sequence represents the model's queue. -/
  represents : Holds q t (queueAfter st steps)
  /-- The queue holds exactly the submissions not yet delivered, in order. -/
  queue : (queueAfter st steps).queue = (st.queue ++ submissions steps).drop (deliveredRecords st steps)
  /-- The concatenated output is exactly the delivered records' bytes, in order. -/
  output : output steps = ((st.queue ++ submissions steps).take (deliveredRecords st steps)).flatMap q.out

/-- **The sequence delivers exactly.** -/
theorem Chain.delivered {s t : Stor} {steps : List (Step q)} (chain : Chain s steps t)
    {st : QueueState q.Record} (rep : Holds q s st)
    (slots : queueBase q.width (st.tail + (submissions steps).length) ≤ 2 ^ 256)
    (count : st.count + (submissions steps).length < 2 ^ 256) :
    Delivered st steps t := by
  obtain ⟨h1, h2⟩ := chain.holds rep slots count
  refine ⟨h1, run_queue _ _ _, ?_⟩
  rw [h2, deliveries_flatten]
  rfl

theorem Chain.append_split {s t : Stor} {xs ys : List (Step q)} (chain : Chain s (xs ++ ys) t) :
    ∃ m, Chain s xs m ∧ Chain m ys t := by
  induction xs generalizing s with
  | nil => exact ⟨s, .nil s, chain⟩
  | cons f xs ih =>
    cases chain with
    | cons starts tail =>
      obtain ⟨m, h1, h2⟩ := ih tail
      exact ⟨m, .cons starts h1, h2⟩

theorem Chain.append {s m t : Stor} {xs ys : List (Step q)} (first : Chain s xs m) (second : Chain m ys t) :
    Chain s (xs ++ ys) t := by
  induction first with
  | nil s => exact second
  | cons starts tail ih => exact .cons starts (ih second)

/-- **A drain delivers the next records and no others.** On a chain, with the word range over the steps before
it, a drain's output is the oldest `min(length, cap)` of the records submitted before it and not yet delivered.
A record submitted later cannot appear. -/
theorem Chain.drain_delivers {s t : Stor} {xs ys : List (Step q)} {f : Step q} {next : Nat → Nat → Nat}
    (chain : Chain s (xs ++ f :: ys) t) {st : QueueState q.Record} (rep : Holds q s st)
    (slots : queueBase q.width (st.tail + (submissions xs).length) ≤ 2 ^ 256)
    (count : st.count + (submissions xs).length < 2 ^ 256) (drain : f.effect = .drain next) :
    f.output = (((st.queue ++ submissions xs).drop (deliveredRecords st xs)).take q.cap).flatMap q.out := by
  obtain ⟨m, h1, h2⟩ := chain.append_split
  cases h2 with
  | cons starts tail =>
    subst starts
    have hx := h1.delivered rep slots count
    rw [f.output_eq hx.represents, drain, taken, hx.queue]

end Blanc.Lift.RequestQueue
