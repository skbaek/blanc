import Blanc.Lift.BuilderRequest.Latch
import Blanc.Lift.BuilderRequest.UserFrameAmsterdam
import Blanc.RequestFeeWordDomain

/-!
# Exact delivery over a given sequence of frames

The input is a list of frames at one builder contract, each with what its frame law gives: a submission, a fee
read or a system call. `Chain` says each frame ran on the storage the last one left. That list is an input:
"committed" here means "in the given sequence". Nothing here shows that a chain's retained frames form such a
list, which needs message and transaction level.

`Event` is what a frame does to the queue model, and `step` that effect. Over any such list, `replay_queue` and
`chunks_flatten` are the FIFO: the records delivered so far, then the records still queued, are exactly the
submissions in order. `Chain.delivered` ties it to the frames.
-/

namespace Blanc.Lift.BuilderRequest.Delivery

open Jaune
open RequestSystem

/-! ## The queue model over a list of events -/

/-- What one frame does to the queue. -/
inductive Event (Record : Type) where
  /-- A submission of this record. -/
  | submission (r : Record)
  /-- A fee read. -/
  | feeRead
  /-- A system call; `latch` says its calldata was nonempty. -/
  | system (latch : Bool)

variable {Record : Type}

/-- The queue after a submission: the record at the back, count and tail one higher. -/
def submit (st : QueueState Record) (r : Record) : QueueState Record :=
  ⟨st.excess, st.count + 1, st.head, st.tail + 1, st.queue ++ [r]⟩

/-- The queue a calldata-latch call leaves: as a drain, with slot 0 at the inhibitor. -/
def latched (cap : Nat) (target : B256) (st : QueueState Record) : QueueState Record :=
  { drainedState cap target st with excess := 2 ^ 256 - 1 }

/-- The queue after one event. -/
def step (cap : Nat) (target : B256) (st : QueueState Record) : Event Record → QueueState Record
  | .submission r => submit st r
  | .feeRead => st
  | .system false => drainedState cap target st
  | .system true => latched cap target st

/-- The records one event delivers: a system call, either form, takes the oldest `min(length, cap)`. -/
def chunk (cap : Nat) (st : QueueState Record) : Event Record → List Record
  | .system _ => st.queue.take cap
  | _ => []

/-- The queue after a list of events. -/
def replay (cap : Nat) (target : B256) (st : QueueState Record) (es : List (Event Record)) : QueueState Record :=
  es.foldl (step cap target) st

/-- The records each event of a list delivers, in order. -/
def chunks (cap : Nat) (target : B256) : QueueState Record → List (Event Record) → List (List Record)
  | _, [] => []
  | st, e :: es => chunk cap st e :: chunks cap target (step cap target st e) es

/-- How many records a list of events delivers. -/
def deliveredCount (cap : Nat) (target : B256) (st : QueueState Record) (es : List (Event Record)) : Nat :=
  (chunks cap target st es).flatten.length

/-- The records a list of events submits, in order. -/
def submitted : List (Event Record) → List Record
  | [] => []
  | .submission r :: es => r :: submitted es
  | _ :: es => submitted es

theorem drainedState_queue (cap : Nat) (target : B256) (st : QueueState Record) :
    (drainedState cap target st).queue = st.queue.drop cap := by
  unfold drainedState
  dsimp only
  split
  · rename_i h
    exact (List.drop_eq_nil_of_le h).symm
  · rfl

theorem step_queue_system (cap : Nat) (target : B256) (st : QueueState Record) (latch : Bool) :
    (step cap target st (.system latch)).queue = st.queue.drop cap := by
  cases latch
  · exact drainedState_queue cap target st
  · exact drainedState_queue cap target st

theorem submitted_append (xs ys : List (Event Record)) :
    submitted (xs ++ ys) = submitted xs ++ submitted ys := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    cases e <;> simp only [List.cons_append, submitted, ih]

theorem replay_append (cap : Nat) (target : B256) (st : QueueState Record) (xs ys : List (Event Record)) :
    replay cap target st (xs ++ ys) = replay cap target (replay cap target st xs) ys := by
  simp only [replay, List.foldl_append]

theorem chunks_append (cap : Nat) (target : B256) (st : QueueState Record) (xs ys : List (Event Record)) :
    chunks cap target st (xs ++ ys) =
      chunks cap target st xs ++ chunks cap target (replay cap target st xs) ys := by
  induction xs generalizing st with
  | nil => rfl
  | cons e xs ih =>
    simp only [List.cons_append, chunks, ih]
    rfl

/-- One event in the FIFO's terms: `chunk` then the next queue are the queue with what the event submits. -/
theorem chunk_step (cap : Nat) (target : B256) (st : QueueState Record) (e : Event Record) (rest : List Record) :
    chunk cap st e ++ ((step cap target st e).queue ++ rest) =
      st.queue ++ (submitted [e] ++ rest) := by
  cases e with
  | submission r =>
    simp only [chunk, step, submit, submitted, List.nil_append, List.append_assoc, List.singleton_append]
  | feeRead => rfl
  | system latch =>
    rw [step_queue_system, chunk, ← List.append_assoc, List.take_append_drop]
    rfl

/-- **The FIFO over a list of events.** The records the events deliver, in order, followed by the records still
queued, are the starting queue followed by the records submitted, in order. So nothing is dropped, duplicated
or reordered. -/
theorem delivered_append_queue (cap : Nat) (target : B256) (st : QueueState Record) (es : List (Event Record)) :
    (chunks cap target st es).flatten ++ (replay cap target st es).queue = st.queue ++ submitted es := by
  induction es generalizing st with
  | nil => simp only [chunks, List.flatten_nil, submitted, replay, List.foldl_nil, List.nil_append, List.append_nil]
  | cons e es ih =>
    have hc := chunk_step cap target st e (submitted es)
    have hs : submitted (e :: es) = submitted [e] ++ submitted es := submitted_append [e] es
    simp only [chunks, List.flatten_cons, List.append_assoc]
    show _ ++ (_ ++ (replay cap target (step cap target st e) es).queue) = _
    rw [ih, hc, hs]

/-- What has been delivered is a prefix of the submissions. -/
theorem chunks_flatten (cap : Nat) (target : B256) (st : QueueState Record) (es : List (Event Record)) :
    (chunks cap target st es).flatten =
      (st.queue ++ submitted es).take (deliveredCount cap target st es) := by
  rw [← delivered_append_queue cap target st es, deliveredCount, List.take_left]

/-- What is still queued is the submissions after that prefix. -/
theorem replay_queue (cap : Nat) (target : B256) (st : QueueState Record) (es : List (Event Record)) :
    (replay cap target st es).queue =
      (st.queue ++ submitted es).drop (deliveredCount cap target st es) := by
  rw [← delivered_append_queue cap target st es, deliveredCount, List.drop_left]

/-! ## The excess over a list of events -/

theorem drainedState_excess (cap : Nat) (target : B256) (st : QueueState Record) :
    (drainedState cap target st).excess = (excessNext target st.excess.toB256 st.count.toB256).toNat := by
  unfold drainedState
  dsimp only
  split <;> rfl

theorem drainedState_count (cap : Nat) (target : B256) (st : QueueState Record) :
    (drainedState cap target st).count = 0 := by
  unfold drainedState
  dsimp only
  split <;> rfl

theorem drainedState_tail_le (cap : Nat) (target : B256) (st : QueueState Record) :
    (drainedState cap target st).tail ≤ st.tail := by
  unfold drainedState
  dsimp only
  split
  · exact Nat.zero_le _
  · exact Nat.le_refl _

/-- The inhibitor as a natural. -/
theorem max_toNat : B256.max.toNat = 2 ^ 256 - 1 := by decide

/-- Away from the inhibitor and with no word wrap, the next excess is `excess + count - target` in naturals. -/
theorem excessNext_natural (target : B256) {e n : Nat} (hne : e ≠ 2 ^ 256 - 1) (hsum : e + n < 2 ^ 256) :
    (excessNext target e.toB256 n.toB256).toNat = e + n - target.toNat := by
  have hmax : B256.max ≠ e.toB256 := fun h => by
    have := congrArg B256.toNat h
    rw [max_toNat, B256.toNat_toB256_of_lt (by omega)] at this
    omega
  have hadd : n.toB256 + e.toB256 = (e + n).toB256 := by
    rw [Nat.toB256_add_toB256, Nat.add_comm]
  have hv := B256.toNat_toB256_of_lt hsum
  simp only [excessNext, ite_eq_right hmax, hadd]
  by_cases hgt : (e + n).toB256 > target
  · have hlt := B256.lt_iff_toNat_lt_toNat.mp hgt
    rw [hv] at hlt
    rw [ite_eq_left hgt, B256.toNat_sub, hv]
    change (2 ^ 256 + (e + n) - target.toNat) % 2 ^ 256 = _
    have := B256.toNat_lt target
    omega
  · have hle : ¬ target.toNat < e + n := fun hlt =>
      hgt (B256.lt_iff_toNat_lt_toNat.mpr (by rw [hv]; exact hlt))
    rw [ite_eq_right hgt, show (0 : B256).toNat = 0 from rfl]
    omega

/-- Whether slot 0 holds the inhibitor after a list of events, from `start`: the last system call decides, by
its calldata form, and nothing else moves it. -/
def inhibitedAfter : Bool → List (Event Record) → Bool
  | start, [] => start
  | _, .system latch :: es => inhibitedAfter latch es
  | start, _ :: es => inhibitedAfter start es

/-- **When the excess is the inhibitor.** Exactly when the last system call had nonempty calldata, or there has
been no system call and it started there. An empty-calldata call always clears it, for a nonzero target. -/
theorem excess_inhibitor {target : B256} (ht : target ≠ 0) (cap : Nat) (st : QueueState Record)
    (es : List (Event Record)) :
    (replay cap target st es).excess = 2 ^ 256 - 1 ↔
      inhibitedAfter (decide (st.excess = 2 ^ 256 - 1)) es = true := by
  induction es generalizing st with
  | nil => simp only [replay, List.foldl_nil, inhibitedAfter, decide_eq_true_eq]
  | cons e es ih =>
    have hstep : replay cap target st (e :: es) = replay cap target (step cap target st e) es := rfl
    rw [hstep, ih]
    cases e with
    | submission r => rfl
    | feeRead => rfl
    | system latch =>
      cases latch
      · have hne : (step cap target st (.system false)).excess ≠ 2 ^ 256 - 1 := fun h => by
          have hx : (excessNext target st.excess.toB256 st.count.toB256).toNat = 2 ^ 256 - 1 :=
            (drainedState_excess cap target st).symm.trans h
          exact excessNext_ne_max ht _ _ (B256.toNat_inj _ _ (hx.trans max_toNat.symm))
        rw [decide_eq_false hne]
        rfl
      · have hin : (step cap target st (.system true)).excess = 2 ^ 256 - 1 := rfl
        rw [decide_eq_true hin]
        rfl

/-- A list with no system call. -/
def NoSystem (es : List (Event Record)) : Prop := ∀ e ∈ es, ∀ latch, e ≠ .system latch

/-- With no system call, the excess does not move. -/
theorem excess_noSystem (cap : Nat) (target : B256) (st : QueueState Record) {es : List (Event Record)}
    (h : NoSystem es) : (replay cap target st es).excess = st.excess := by
  induction es generalizing st with
  | nil => rfl
  | cons e es ih =>
    have tail : NoSystem es := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hstep : replay cap target st (e :: es) = replay cap target (step cap target st e) es := rfl
    rw [hstep, ih _ tail]
    cases e with
    | submission r => rfl
    | feeRead => rfl
    | system latch => exact absurd rfl (h _ List.mem_cons_self latch)

/-- With no system call, the count grows by exactly what is submitted. -/
theorem count_noSystem (cap : Nat) (target : B256) (st : QueueState Record) {es : List (Event Record)}
    (h : NoSystem es) : (replay cap target st es).count = st.count + (submitted es).length := by
  induction es generalizing st with
  | nil => rfl
  | cons e es ih =>
    have tail : NoSystem es := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hstep : replay cap target st (e :: es) = replay cap target (step cap target st e) es := rfl
    rw [hstep, ih _ tail]
    cases e with
    | submission r =>
      simp only [step, submit, submitted, List.length_cons]
      omega
    | feeRead => rfl
    | system latch => exact absurd rfl (h _ List.mem_cons_self latch)

/-- The excess the next fee is charged on, with what the count adds, away from the inhibitor. -/
def load (st : QueueState Record) : Nat := if st.excess = 2 ^ 256 - 1 then st.count else st.excess + st.count

theorem load_step (cap : Nat) (target : B256) (st : QueueState Record) (e : Event Record)
    (hb : load st + (submitted [e]).length < 2 ^ 256) (he : st.excess < 2 ^ 256) :
    load (step cap target st e) ≤ load st + (submitted [e]).length := by
  cases e with
  | submission r =>
    have hl : (submitted [Event.submission r]).length = 1 := rfl
    rw [hl]
    show load (submit st r) ≤ _
    by_cases hmax : st.excess = 2 ^ 256 - 1
    · have h1 : load st = st.count := ite_eq_left hmax
      have h2 : load (submit st r) = st.count + 1 := ite_eq_left hmax
      omega
    · have h1 : load st = st.excess + st.count := ite_eq_right hmax
      have h2 : load (submit st r) = st.excess + (st.count + 1) := ite_eq_right hmax
      omega
  | feeRead => exact Nat.le_refl _
  | system latch =>
    cases latch
    · have hc := drainedState_count cap target st
      have hx := drainedState_excess cap target st
      show load (drainedState cap target st) ≤ _
      by_cases hmax : st.excess = 2 ^ 256 - 1
      · have h0 : (drainedState cap target st).excess = 0 := by
          rw [hx, hmax, show ((2 ^ 256 - 1 : Nat)).toB256 = B256.max by decide, excessNext_inhibitor]
          rfl
        simp only [load, h0, hc]
        split <;> omega
      · have hsum : st.excess + st.count < 2 ^ 256 := by
          have : load st = st.excess + st.count := ite_eq_right hmax
          simp only [submitted, List.length_nil] at hb
          omega
        have h1 := excessNext_natural target hmax hsum
        have hl : load st = st.excess + st.count := ite_eq_right hmax
        rw [← hx] at h1
        rw [hl]
        simp only [load, h1, hc]
        split <;> omega
    · have hc : (latched cap target st).count = 0 := drainedState_count cap target st
      have hx : (latched cap target st).excess = 2 ^ 256 - 1 := rfl
      show load (latched cap target st) ≤ _
      have hl : load (latched cap target st) = 0 := by
        rw [load, ite_eq_left hx, hc]
      rw [hl]
      exact Nat.zero_le _

theorem step_excess_lt (cap : Nat) (target : B256) (st : QueueState Record) (e : Event Record)
    (he : st.excess < 2 ^ 256) : (step cap target st e).excess < 2 ^ 256 := by
  cases e with
  | submission r => exact he
  | feeRead => exact he
  | system latch =>
    cases latch
    · show (drainedState cap target st).excess < _
      rw [drainedState_excess]
      exact B256.toNat_lt _
    · exact (by decide : 2 ^ 256 - 1 < 2 ^ 256)

/-- **The excess is bounded by the submissions.** Over a list of events with no word wrap in the bound, `load`,
which is `excess + count` away from the inhibitor, grows by at most one per submission. -/
theorem load_replay (cap : Nat) (target : B256) (st : QueueState Record) (es : List (Event Record))
    (hb : load st + (submitted es).length < 2 ^ 256) (he : st.excess < 2 ^ 256) :
    load (replay cap target st es) ≤ load st + (submitted es).length := by
  induction es generalizing st with
  | nil => exact Nat.le_add_right _ _
  | cons e es ih =>
    have hs : (submitted (e :: es)).length = (submitted [e]).length + (submitted es).length := by
      rw [show e :: es = [e] ++ es from rfl, submitted_append, List.length_append]
    have h1 := load_step cap target st e (by omega) he
    have h2 := ih (step cap target st e) (by omega) (step_excess_lt cap target st e he)
    show load (replay cap target (step cap target st e) es) ≤ _
    omega

/-! ## A builder contract, as the sequence needs it -/

/-- The storage a builder system call on empty calldata leaves, as a function of the storage before it. -/
def drainStor (p : SysShape) (s : Stor) : Stor :=
  let c := drainCount p.cap.word (s.get 2) (s.get 3)
  let s1 := if s.get 2 + c = s.get 3 then (s.set 2 0).set 3 0 else s.set 2 (s.get 2 + c)
  (s1.set 0 (p.next (s.get 0) (s.get 1))).set 1 0

/-- The storage a builder system call on nonempty calldata leaves. -/
def latchStor (p : SysShape) (s : Stor) : Stor :=
  let c := drainCount p.cap.word (s.get 2) (s.get 3)
  let s1 := if s.get 2 + c = s.get 3 then (s.set 2 0).set 3 0 else s.set 2 (s.get 2 + c)
  (s1.set 0 B256.max).set 1 0

theorem sysState_getStor (p : SysShape) (σ : State) (a : Adr) :
    (sysState p σ a).getStor a = drainStor p (σ.getStor a) := by
  simp only [sysState, drainStor]
  split <;> simp only [State.getStor_setStorVal_self]

theorem latchState_getStor (p : SysShape) (σ : State) (a : Adr) :
    (latchState p σ a).getStor a = latchStor p (σ.getStor a) := by
  simp only [latchState, latchStor]
  split <;> simp only [State.getStor_setStorVal_self]

/-- A builder contract's facts, which the sequence statements are generic over. Every field is proved per
contract from its frame laws. -/
structure Contract where
  /-- The runtime bytes. -/
  code : ByteArray
  /-- Where they are installed. -/
  address : Adr
  /-- Requests per block the excess is measured against. -/
  target : B256
  /-- Records a system call returns at most. -/
  cap : Nat
  /-- Slots per record. -/
  width : Nat
  /-- A record of the queue. -/
  Record : Type
  /-- The word a record keeps at each of its slots. -/
  words : Record → Nat → B256
  /-- A record's bytes in a system call's output. -/
  out : Record → Bytes
  /-- What a successful submission's frame law gives. -/
  Submitted : ∀ {sevm : Sevm}, StorageSteps sevm → Devm → Devm → Nat → B256 → Prop
  /-- A submission's calldata length. -/
  payload : Nat
  /-- The record a submission's frame enqueues. -/
  recordOf : ∀ sevm : Sevm, sevm.data.length = payload → Record
  /-- What a submission does to the contract's storage. -/
  submitStor : Sevm → Stor → Stor
  /-- The system call's shape. -/
  shape : SysShape
  /-- The successful frame law's calldata length. -/
  length : ∀ {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm} {i : Nat} {out : B256},
    Submitted l pre post i out → sevm.data.length = payload
  /-- The frame law's storage effect. -/
  storage : ∀ {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm} {i : Nat} {out : B256},
    Submitted l pre post i out →
      post.getStor sevm.currentTarget = submitStor sevm (pre.getStor sevm.currentTarget)
  /-- The frame law's guard: slot 0 is off the inhibitor. -/
  active : ∀ {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm} {i : Nat} {out : B256},
    Submitted l pre post i out → pre.getStorVal sevm.currentTarget 0 ≠ B256.max
  /-- The frame law's fee recurrence. -/
  quote : ∀ {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm} {i : Nat} {out : B256},
    Submitted l pre post i out → WordFakeExponential.Run (storedExcess target sevm pre) 17 1 17 0 i out
  /-- The frame law's payment: the value covers the quoted fee. -/
  paid : ∀ {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm} {i : Nat} {out : B256},
    Submitted l pre post i out → (out / (17 : B256)).toNat ≤ sevm.value.toNat
  /-- A submission on a represented queue, with its slots in word range. -/
  represents_submit : ∀ (sevm : Sevm) (h : sevm.data.length = payload) {s : Stor} {st : QueueState Record},
    Represents width words (fun key => s.get key) st → queueBase width st.tail + width ≤ 2 ^ 256 →
    st.count + 1 < 2 ^ 256 →
    Represents width words (fun key => (submitStor sevm s).get key) (submit st (recordOf sevm h))
  /-- The system call's cap, as a word. -/
  cap_word : shape.cap.word.toNat = cap
  /-- The system call's target. -/
  target_eq : shape.target.word = target
  /-- The system call's next excess. -/
  next_eq : shape.next = excessNext shape.target.word
  /-- The target is not zero. -/
  target_ne : target ≠ 0
  /-- The empty-calldata system call: its post state and its output on a represented queue. -/
  system_law : ∀ {benv : Benv} {post : State} {result : MsgCallOutput},
    benv.stat.fork = .amsterdam → benv.state.getCode address = code →
    processCheckedSystemTransaction benv address [] = .ok (post, result) →
    post = sysState shape benv.state address ∧
      ∀ {st : QueueState Record}, Represents width words (storOf benv.state address) st →
        result.returnData = (st.queue.take cap).flatMap out
  /-- The nonempty-calldata system call: its post state and its output on a represented queue. -/
  latch_law : ∀ {benv : Benv} {data : Bytes} {post : State} {result : MsgCallOutput},
    benv.stat.fork = .amsterdam → benv.state.getCode address = code → data ≠ [] → data.length < 2 ^ 256 →
    processCheckedSystemTransaction benv address data = .ok (post, result) →
    post = latchState shape benv.state address ∧
      ∀ {st : QueueState Record}, Represents width words (storOf benv.state address) st →
        result.returnData = (st.queue.take cap).flatMap out

/-- The fork rules a user frame in the sequence ran under: a covered fork or Amsterdam. -/
inductive UserRules {sevm : Sevm} : StorageSteps sevm → Prop where
  | covered : CoveredFork sevm.benvStat.fork → UserRules (coveredSteps sevm)
  | amsterdam : sevm.benvStat.fork = .amsterdam → UserRules (amsterdamSteps sevm)

/-- One frame that ran the contract's code against its storage, with what its frame law gives.

**What `system` means.** The event is the request phase's call: `processCheckedSystemTransaction`, which
`runRequestContracts` makes (`Frame.ofRequestStep`), whose return data goes into the block's requests. The bytes pick
the system path by the caller alone, so a frame with caller `systemAddress` inside a user transaction would also
drain the queue, returning its records to that caller and never to a block's requests. No constructor here is such
a frame: `submission` and `feeRead` carry `caller ≠ systemAddress`, and `system` is the checked transaction. So
**every sequence statement has the premise that no such frame ran**, and `Chain` is where it reads: consecutive
frames share their storage, so nothing outside the list changed it. "Nothing dropped" is only true under this.

The calldata form is kept as data: nonempty calldata reaches the latch, which the request phase never passes
(`request_step_no_latch`); `RequestPhaseOnly` is the premise that the list has none.

The list is an input; there are no reverted frames in it. -/
inductive Frame (c : Contract) where
  /-- A submission by a non-system caller, under a covered fork or Amsterdam. -/
  | submission (sevm : Sevm) (pre post : Devm) (l : StorageSteps sevm) (iterations : Nat) (finalOutput : B256)
      (rules : UserRules l) (at_contract : sevm.currentTarget = c.address) (caller : sevm.caller ≠ systemAddress)
      (law : c.Submitted l pre post iterations finalOutput)
  /-- A fee read by a non-system caller, under a covered fork or Amsterdam. -/
  | feeRead (sevm : Sevm) (pre post : Devm) (l : StorageSteps sevm) (iterations : Nat) (finalOutput : B256)
      (rules : UserRules l) (at_contract : sevm.currentTarget = c.address) (caller : sevm.caller ≠ systemAddress)
      (law : UserPath.FeeReadOn l c.target pre post iterations finalOutput)
  /-- The checked system transaction under Amsterdam, with calldata `data`: the request phase's call when `data` is
  empty. -/
  | system (benv : Benv) (data : Bytes) (post : State) (out : MsgCallOutput)
      (fork : benv.stat.fork = .amsterdam) (installed : benv.state.getCode c.address = c.code)
      (length : data.length < 2 ^ 256)
      (run : processCheckedSystemTransaction benv c.address data = .ok (post, out))

namespace Frame

variable {c : Contract}

/-- The contract's storage when the frame starts. -/
def before : Frame c → Stor
  | .submission _ pre .. => pre.getStor c.address
  | .feeRead _ pre .. => pre.getStor c.address
  | .system benv .. => benv.state.getStor c.address

/-- The contract's storage when the frame ends. -/
def after : Frame c → Stor
  | .submission _ _ post .. => post.getStor c.address
  | .feeRead _ _ post .. => post.getStor c.address
  | .system _ _ post .. => post.getStor c.address

/-- What the frame does to the queue model. A submission's record comes from its own calldata and caller. -/
def event : Frame c → Event c.Record
  | .submission sevm _ _ _ _ _ _ _ _ law => .submission (c.recordOf sevm (c.length law))
  | .feeRead .. => .feeRead
  | .system _ data .. => .system (!data.isEmpty)

/-- What the frame adds to the system-call output: a system call's return data, otherwise nothing. -/
def output : Frame c → Bytes
  | .system _ _ _ out .. => out.returnData
  | _ => []

/-- The storage effect of a frame, as a function of the storage before it. -/
def effect (s : Stor) : Frame c → Stor
  | .submission sevm .. => c.submitStor sevm s
  | .feeRead .. => s
  | .system _ data .. => if data.isEmpty then drainStor c.shape s else latchStor c.shape s

/-- **Each frame's law gives exactly its effect.** -/
theorem after_eq (f : Frame c) : f.after = effect f.before f := by
  cases f with
  | submission sevm pre post l i o rules target caller law =>
    have := c.storage law
    rw [target] at this
    exact this
  | feeRead sevm pre post l i o rules target caller law => exact law.storage c.address
  | system benv data post out fork installed length run =>
    cases data with
    | nil =>
      have := (c.system_law fork installed run).1
      subst this
      exact sysState_getStor _ _ _
    | cons x xs =>
      have := (c.latch_law fork installed (List.cons_ne_nil x xs) length run).1
      subst this
      exact latchState_getStor _ _ _

end Frame

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

/-- **A storage after a submission represents the queue with the record at its back**: slots 0 and 2 as before, the
count and tail one higher, the new record's words at the tail's slots, and every other slot as before. -/
theorem represents_after_submit {w : Nat} {words : Record → Nat → B256} {f g : B256 → B256} {st : QueueState Record}
    {r : Record} (rep : Represents w words f st) (hw : 0 < w) (slots : queueBase w st.tail + w ≤ 2 ^ 256)
    (count : st.count + 1 < 2 ^ 256) (g0 : g 0 = f 0) (g1 : g 1 = (st.count + 1).toB256) (g2 : g 2 = f 2)
    (g3 : g 3 = (st.tail + 1).toB256) (new : ∀ j, j < w → g (queueSlot w st.tail j) = words r j)
    (old : ∀ key, (1 : B256) ≠ key → (3 : B256) ≠ key → (∀ j, j < w → queueSlot w st.tail j ≠ key) → g key = f key) :
    Represents w words g (submit st r) := by
  have coh := rep.coherent
  have htail : st.tail + 1 < 2 ^ 256 := by
    have : st.tail ≤ w * st.tail := Nat.le_mul_of_pos_left _ hw
    simp only [queueBase] at slots
    omega
  have hlen : (submit st r).queue.length = st.queue.length + 1 := List.length_append ..
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

/-- `s` represents `st`, in this contract's layout. -/
abbrev Holds (c : Contract) (s : Stor) (st : QueueState c.Record) : Prop :=
  Represents c.width c.words (fun key => s.get key) st

namespace Frame

variable {c : Contract}

/-- A frame's output on a represented queue is exactly the records its event delivers: nothing, unless it is a
system call. -/
theorem output_eq (f : Frame c) {st : QueueState c.Record} (rep : Holds c f.before st) :
    f.output = (chunk c.cap st f.event).flatMap c.out := by
  cases f with
  | submission sevm pre post l i o rules target caller law => rfl
  | feeRead sevm pre post l i o rules target caller law => rfl
  | system benv data post out fork installed length run =>
    have hrep : Represents c.width c.words (storOf benv.state c.address) st := rep
    cases data with
    | nil => exact (c.system_law fork installed run).2 hrep
    | cons x xs => exact (c.latch_law fork installed (List.cons_ne_nil x xs) length run).2 hrep

/-- **One frame on a represented queue.** The next storage represents the queue after the frame's event, and the
frame's output is exactly the records that event delivers. A submission needs its slots and count in word
range; other frames need nothing of the kind. -/
theorem step_holds (f : Frame c) {st : QueueState c.Record} (rep : Holds c f.before st)
    (slots : queueBase c.width (st.tail + (submitted [f.event]).length) ≤ 2 ^ 256)
    (count : st.count + (submitted [f.event]).length < 2 ^ 256) :
    Holds c f.after (step c.cap c.target st f.event) ∧
      f.output = (chunk c.cap st f.event).flatMap c.out := by
  refine ⟨?_, f.output_eq rep⟩
  have heff := after_eq f
  cases f with
  | submission sevm pre post l i o rules target caller law =>
    have hslots : queueBase c.width (st.tail + 1) ≤ 2 ^ 256 := slots
    rw [queueBase_succ] at hslots
    rw [heff]
    exact c.represents_submit sevm (c.length law) rep hslots count
  | feeRead sevm pre post l i o rules target caller law =>
    rw [heff]
    exact rep
  | system benv data post out fork installed length run =>
    have hrep : Represents c.width c.words (storOf benv.state c.address) st := rep
    cases data with
    | nil =>
      obtain ⟨hpost, -⟩ := c.system_law fork installed run
      subst hpost
      have hd := represents_sysState c.shape c.cap_word c.next_eq hrep
      rw [c.target_eq] at hd
      exact hd
    | cons x xs =>
      obtain ⟨hpost, -⟩ := c.latch_law fork installed (List.cons_ne_nil x xs) length run
      subst hpost
      have hd := represents_latchState c.shape c.cap_word c.next_eq hrep
      rw [c.target_eq] at hd
      exact hd

end Frame

/-! ## The sequence -/

/-- The frames form a chain from `s` to `t`: each ran on the storage the one before it left. -/
inductive Chain {c : Contract} : Stor → List (Frame c) → Stor → Prop where
  | nil (s : Stor) : Chain s [] s
  | cons {s : Stor} {f : Frame c} {rest : List (Frame c)} {t : Stor} (starts : f.before = s)
      (tail : Chain f.after rest t) : Chain s (f :: rest) t

variable {c : Contract}

/-- The frames' events, in order. -/
def events (frames : List (Frame c)) : List (Event c.Record) := frames.map Frame.event

/-- The records the frames submit, in order, each from its frame's calldata and caller. -/
def submissions (frames : List (Frame c)) : List c.Record := submitted (events frames)

/-- The queue model after the frames. -/
def queueAfter (st : QueueState c.Record) (frames : List (Frame c)) : QueueState c.Record :=
  replay c.cap c.target st (events frames)

/-- How many records the frames' system calls deliver: each call `min(length, cap)` of the queue it finds. -/
def deliveredRecords (st : QueueState c.Record) (frames : List (Frame c)) : Nat :=
  deliveredCount c.cap c.target st (events frames)

/-- The bytes the frames' system calls return, concatenated. -/
def systemOutput (frames : List (Frame c)) : Bytes := frames.flatMap Frame.output

theorem step_tail_le (cap : Nat) (target : B256) (st : QueueState Record) (e : Event Record) :
    (step cap target st e).tail ≤ st.tail + (submitted [e]).length := by
  cases e with
  | submission r => exact Nat.le_refl _
  | feeRead => exact Nat.le_refl _
  | system latch =>
    cases latch
    · exact drainedState_tail_le cap target st
    · exact drainedState_tail_le cap target st

theorem step_count_le (cap : Nat) (target : B256) (st : QueueState Record) (e : Event Record) :
    (step cap target st e).count ≤ st.count + (submitted [e]).length := by
  cases e with
  | submission r => exact Nat.le_refl _
  | feeRead => exact Nat.le_refl _
  | system latch =>
    cases latch
    · show (drainedState cap target st).count ≤ _
      rw [drainedState_count]
      exact Nat.zero_le _
    · show (drainedState cap target st).count ≤ _
      rw [drainedState_count]
      exact Nat.zero_le _

theorem submitted_cons_length (e : Event Record) (es : List (Event Record)) :
    (submitted (e :: es)).length = (submitted [e]).length + (submitted es).length := by
  rw [show e :: es = [e] ++ es from rfl, submitted_append, List.length_append]

/-- **The sequence on a represented queue.** Storage at the chain's end represents the model's queue, and the
concatenated output is the concatenated records each call delivered. `slots` and `count` are the word range:
every record slot the frames' submissions could reach, and the count, stay below the word modulus. -/
theorem Chain.holds {s t : Stor} {frames : List (Frame c)} (chain : Chain s frames t)
    {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256) :
    Holds c t (queueAfter st frames) ∧
      systemOutput frames = (chunks c.cap c.target st (events frames)).flatten.flatMap c.out := by
  induction chain generalizing st with
  | nil s => exact ⟨rep, rfl⟩
  | @cons s f rest t starts tail ih =>
    subst starts
    have hs : (submissions (f :: rest)).length =
        (submitted [f.event]).length + (submissions rest).length := submitted_cons_length _ _
    rw [hs] at slots count
    obtain ⟨hrep, hout⟩ := f.step_holds rep ((queueBase_mono c.width (by omega)).trans slots) (by omega)
    have ht := step_tail_le c.cap c.target st f.event
    have hc := step_count_le c.cap c.target st f.event
    obtain ⟨h1, h2⟩ := ih hrep ((queueBase_mono c.width (by omega)).trans slots) (by omega)
    refine ⟨h1, ?_⟩
    show f.output ++ systemOutput rest = _
    rw [h2, hout]
    show _ = (chunk c.cap st f.event ++ (chunks c.cap c.target _ (events rest)).flatten).flatMap c.out
    rw [List.flatMap_append]

/-- `Chain.holds` from an empty queue, with the word range as one premise on the number of submissions. -/
structure Delivered (st : QueueState c.Record) (frames : List (Frame c)) (t : Stor) : Prop where
  /-- Storage at the end of the sequence represents the model's queue. -/
  represents : Holds c t (queueAfter st frames)
  /-- The queue holds exactly the submissions not yet delivered, in order. -/
  queue : (queueAfter st frames).queue =
    (st.queue ++ submissions frames).drop (deliveredRecords st frames)
  /-- The concatenated output is exactly the delivered records' bytes, in order. -/
  output : systemOutput frames =
    ((st.queue ++ submissions frames).take (deliveredRecords st frames)).flatMap c.out

/-- **The sequence delivers exactly.** -/
theorem Chain.delivered {s t : Stor} {frames : List (Frame c)} (chain : Chain s frames t)
    {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256) :
    Delivered st frames t := by
  obtain ⟨h1, h2⟩ := chain.holds rep slots count
  refine ⟨h1, replay_queue _ _ _ _, ?_⟩
  rw [h2, chunks_flatten]
  rfl

theorem Chain.append_split {s t : Stor} {xs ys : List (Frame c)} (chain : Chain s (xs ++ ys) t) :
    ∃ m, Chain s xs m ∧ Chain m ys t := by
  induction xs generalizing s with
  | nil => exact ⟨s, .nil s, chain⟩
  | cons f xs ih =>
    cases chain with
    | cons starts tail =>
      obtain ⟨m, h1, h2⟩ := ih tail
      exact ⟨m, .cons starts h1, h2⟩

theorem Chain.append {s m t : Stor} {xs ys : List (Frame c)} (first : Chain s xs m) (second : Chain m ys t) :
    Chain s (xs ++ ys) t := by
  induction first with
  | nil s => exact second
  | cons starts tail ih => exact .cons starts (ih second)

/-- **A request-phase step at the contract is a `system` frame.** Its calldata is empty, it starts on the state the
phase is at, and its return data is what the phase appends to the block's requests under its type byte. -/
theorem Frame.ofRequestStep {idx : Nat} {ty : UInt8} {rest : List (UInt8 × Adr)} {benv : Benv} {acc : List Bytes}
    {bal : BalBuilder} {post : State} {out : MsgCallOutput} (fork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode c.address = c.code)
    (run : processCheckedSystemTransaction benv c.address [] = .ok (post, out)) :
    ∃ f : Frame c, f.before = benv.state.getStor c.address ∧ f.after = post.getStor c.address ∧
      f.event = .system false ∧ f.output = out.returnData ∧
      runRequestContracts idx ((ty, c.address) :: rest) benv acc bal =
        runRequestContracts idx rest (benv.withState post)
          (if f.output.length > 0 then acc ++ [[ty] ++ f.output] else acc)
          (match benv.stat.rules.bal with
            | none => bal
            | some _ => bal.incorporate idx benv.state post
                (c.address :: out.accountReads.toList) out.storageReads.toList out.storageWrites.toList) :=
  ⟨.system benv [] post out fork installed (by decide) run, rfl, rfl, rfl, rfl, runRequestContracts_step run⟩

/-- The list's system calls are all the request phase's: empty calldata. -/
def RequestPhaseOnly (frames : List (Frame c)) : Prop := ∀ f ∈ frames, ∀ latch, f.event = .system latch → latch = false

/-- With only request-phase calls, nothing sets the inhibitor. -/
theorem inhibitedAfter_requestPhase {frames : List (Frame c)} (start : Bool) (h : RequestPhaseOnly frames) :
    inhibitedAfter start (events frames) = (start && (events frames).all fun e => match e with
      | .system _ => false
      | _ => true) := by
  induction frames generalizing start with
  | nil => simp only [events, List.map_nil, inhibitedAfter, List.all_nil, Bool.and_true]
  | cons f rest ih =>
    have tail : RequestPhaseOnly rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hrest := ih start tail
    show inhibitedAfter start (f.event :: events rest) = (start && (f.event :: events rest).all _)
    rcases he : f.event with r | _ | latch
    · simpa only [inhibitedAfter, List.all_cons, Bool.true_and] using hrest
    · simpa only [inhibitedAfter, List.all_cons, Bool.true_and] using hrest
    · obtain rfl := h f List.mem_cons_self latch he
      have := (ih false tail)
      simp only [inhibitedAfter, List.all_cons, Bool.false_and, Bool.and_false, Bool.false_and] at this ⊢
      exact this

/-- The chain's end is the fold of the frames' storage effects. -/
theorem Chain.fold_effect {s t : Stor} {frames : List (Frame c)} (chain : Chain s frames t) :
    t = frames.foldl Frame.effect s := by
  induction chain with
  | nil s => rfl
  | @cons s f rest t starts tail ih =>
    subst starts
    rw [List.foldl_cons, ← f.after_eq]
    exact ih

theorem submissions_append (xs ys : List (Frame c)) :
    submissions (xs ++ ys) = submissions xs ++ submissions ys := by
  simp only [submissions, events, List.map_append, submitted_append]

theorem deliveredRecords_prefix (st : QueueState c.Record) (xs ys : List (Frame c)) :
    deliveredRecords st xs ≤ deliveredRecords st (xs ++ ys) := by
  simp only [deliveredRecords, deliveredCount, events, List.map_append, chunks_append, List.flatten_append,
    List.length_append]
  omega

/-- **A system call delivers the next records and no others.** On a chain, with the word range over the frames
before it, a system call's output is the oldest `min(length, cap)` of the records submitted before it and not yet
delivered. A record submitted later cannot appear: this is what "not early" means. -/
theorem Chain.call_delivers {s t : Stor} {xs ys : List (Frame c)} {f : Frame c} {latch : Bool}
    (chain : Chain s (xs ++ f :: ys) t) {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions xs).length) ≤ 2 ^ 256)
    (count : st.count + (submissions xs).length < 2 ^ 256) (call : f.event = .system latch) :
    f.output =
      (((st.queue ++ submissions xs).drop (deliveredRecords st xs)).take c.cap).flatMap c.out := by
  obtain ⟨m, h1, h2⟩ := chain.append_split
  cases h2 with
  | cons starts tail =>
    subst starts
    have hx := h1.delivered rep slots count
    rw [f.output_eq hx.represents, call, chunk, hx.queue]

/-- Frames other than system calls output nothing. -/
theorem Frame.output_user (f : Frame c) (user : ∀ latch, f.event ≠ .system latch) : f.output = [] := by
  cases f with
  | submission sevm pre post l i o rules target caller law => rfl
  | feeRead sevm pre post l i o rules target caller law => rfl
  | system benv data post out fork installed length run => exact absurd rfl (user _)

/-- A user frame, and so the first frame after a nonempty-calldata call, needs slot 0 off the inhibitor. -/
theorem Frame.user_active (f : Frame c) (user : ∀ latch, f.event ≠ .system latch) :
    f.before.get 0 ≠ B256.max := by
  cases f with
  | submission sevm pre post l i o rules target caller law =>
    have := c.active law
    rw [target] at this
    exact this
  | feeRead sevm pre post l i o rules target caller law =>
    have := law.active
    rw [target] at this
    exact this
  | system benv data post out fork installed length run => exact absurd rfl (user _)

/-- The inhibitor's word, from the model's. -/
theorem inhibitor_toB256 : (2 ^ 256 - 1 : Nat).toB256 = B256.max := by decide

/-- **No user frame while inhibited.** On a chain, with the word range over the frames before it, a frame that is
not a system call finds the frames before it not inhibited: their last system call had empty calldata, or there
was none and the sequence did not start inhibited. -/
theorem Chain.user_not_inhibited {s t : Stor} {xs ys : List (Frame c)} {f : Frame c}
    (chain : Chain s (xs ++ f :: ys) t) {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions xs).length) ≤ 2 ^ 256)
    (count : st.count + (submissions xs).length < 2 ^ 256) (user : ∀ latch, f.event ≠ .system latch) :
    inhibitedAfter (decide (st.excess = 2 ^ 256 - 1)) (events xs) = false := by
  obtain ⟨m, h1, h2⟩ := chain.append_split
  cases h2 with
  | cons starts tail =>
    subst starts
    have hx := h1.holds rep slots count
    rw [← Bool.not_eq_true, ← excess_inhibitor c.target_ne]
    intro hmax
    have h0 : f.before.get 0 = (queueAfter st xs).excess.toB256 := hx.1.excess
    rw [show (queueAfter st xs).excess = 2 ^ 256 - 1 from hmax, inhibitor_toB256] at h0
    exact f.user_active user h0

/-! ## The fee over the sequence -/

/-- The word fee the frame's recurrence computed, if it quotes one: a submission or a fee read. -/
def Frame.quotedFee : Frame c → Option B256
  | .submission _ _ _ _ _ o .. => some (o / (17 : B256))
  | .feeRead _ _ _ _ _ o .. => some (o / (17 : B256))
  | .system .. => none

/-- The value a frame carries. -/
def Frame.value : Frame c → Nat
  | .submission sevm .. => sevm.value.toNat
  | .feeRead sevm .. => sevm.value.toNat
  | .system .. => 0

/-- A quoting frame's quote is the word recurrence on the excess the bytes compute from the storage it found. -/
theorem Frame.quote_run (f : Frame c) {q : B256} (hq : f.quotedFee = some q) :
    ∃ iterations output, q = output / (17 : B256) ∧
      WordFakeExponential.Run (targetExcess c.target (f.before.get 0) (f.before.get 1)) 17 1 17 0 iterations output := by
  cases f with
  | submission sevm pre post l i o rules target caller law =>
    obtain rfl := Option.some.inj hq
    have := c.quote law
    rw [storedExcess, target] at this
    exact ⟨_, _, rfl, this⟩
  | feeRead sevm pre post l i o rules target caller law =>
    obtain rfl := Option.some.inj hq
    have := law.quote
    rw [storedExcess, target] at this
    exact ⟨_, _, rfl, this⟩
  | system benv data post out fork installed length run => cases hq

/-- A submission's value covers its quote. A fee read carries none. -/
theorem Frame.value_covers (f : Frame c) {q : B256} (hq : f.quotedFee = some q)
    (hs : f.event ≠ .feeRead) : q.toNat ≤ f.value := by
  cases f with
  | submission sevm pre post l i o rules target caller law =>
    obtain rfl := Option.some.inj hq
    exact c.paid law
  | feeRead sevm pre post l i o rules target caller law => exact absurd rfl hs
  | system benv data post out fork installed length run => cases hq

/-- **A quote in naturals.** On a represented queue, with `excess + max(0, count - target)` at most 2892, a frame's
word quote is `fake_exponential(1, excess + max(0, count - target), 17)`. Past 2892 the two differ
(`RequestFeeWord.word_fee_ne_natural_2893`). -/
theorem Frame.quote_natural (f : Frame c) {st : QueueState c.Record} (rep : Holds c f.before st) {q : B256}
    (hq : f.quotedFee = some q) (he : st.excess + (st.count - c.target.toNat) ≤ 2892) :
    q.toNat = fakeExp 1 (st.excess + (st.count - c.target.toNat)) 17 := by
  obtain ⟨i, o, rfl, run⟩ := f.quote_run hq
  have h0 : f.before.get 0 = st.excess.toB256 := rep.excess
  have h1 : f.before.get 1 = st.count.toB256 := rep.count
  have hx : targetExcess c.target (f.before.get 0) (f.before.get 1) =
      (st.excess + (st.count - c.target.toNat)).toB256 := by
    apply B256.toNat_inj
    rw [targetExcess_toNat, h0, h1, B256.toNat_toB256_of_lt rep.excess_lt,
      B256.toNat_toB256_of_lt rep.count_lt, B256.toNat_toB256_of_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hx] at run
  exact RequestFeeWord.word_fee_eq_natural he run

/-- `load` from a represented state, as a bound: away from the inhibitor, `excess + count`. -/
theorem load_bound {st : QueueState Record} {n : Nat} (h : load st ≤ n) :
    st.excess = 2 ^ 256 - 1 ∨ st.excess + st.count ≤ n := by
  by_cases hmax : st.excess = 2 ^ 256 - 1
  · exact .inl hmax
  · exact .inr ((ite_eq_right hmax : load st = _) ▸ h)

/-- **The excess update, in naturals.** Off the inhibitor and with no wrap in `excess + count`, an empty-calldata
system call stores `excess + count - target`; on the inhibitor it stores 0, whatever the count. -/
theorem drained_excess_natural (cap : Nat) (target : B256) (st : QueueState Record)
    (hsum : st.excess + st.count < 2 ^ 256) (hne : st.excess ≠ 2 ^ 256 - 1) :
    (drainedState cap target st).excess = st.excess + st.count - target.toNat := by
  rw [drainedState_excess]
  exact excessNext_natural target hne hsum

/-- **When the excess is the inhibitor, on the chain.** Slot 0 at the chain's end holds the inhibitor exactly when
the last system call had nonempty calldata, or there was none and the start was inhibited. -/
theorem Chain.excess_iff {s t : Stor} {frames : List (Frame c)} (chain : Chain s frames t)
    {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions frames).length) ≤ 2 ^ 256)
    (count : st.count + (submissions frames).length < 2 ^ 256) :
    t.get 0 = B256.max ↔ inhibitedAfter (decide (st.excess = 2 ^ 256 - 1)) (events frames) = true := by
  have hx := (chain.holds rep slots count).1
  rw [← excess_inhibitor c.target_ne]
  have h0 : t.get 0 = (queueAfter st frames).excess.toB256 := hx.excess
  constructor
  · intro h
    have := congrArg B256.toNat (h0.symm.trans h)
    rw [B256.toNat_toB256_of_lt hx.excess_lt, max_toNat] at this
    exact this
  · intro h
    rw [h0]
    show (queueAfter st frames).excess.toB256 = _
    rw [show (queueAfter st frames).excess = 2 ^ 256 - 1 from h, inhibitor_toB256]

/-- **The bound on the excess.** After the frames, in the model `Chain.holds` ties to storage, away from the inhibitor, `excess + count` is at most its
starting value plus the submissions so far. -/
theorem excess_bound {frames : List (Frame c)} {st : QueueState c.Record} (he : st.excess < 2 ^ 256)
    (range : load st + (submissions frames).length < 2 ^ 256) :
    (queueAfter st frames).excess = 2 ^ 256 - 1 ∨
      (queueAfter st frames).excess + (queueAfter st frames).count ≤ load st + (submissions frames).length :=
  load_bound (load_replay c.cap c.target st (events frames) range he)

/-- **A quote over the sequence, in naturals.** On a chain from a state with no load, a frame's word quote, when
at most 2892 submissions came before it, is `fake_exponential(1, excess + max(0, count - target), 17)` of the queue
it finds. -/
theorem Chain.quote_natural {s t : Stor} {xs ys : List (Frame c)} {f : Frame c} {q : B256}
    (chain : Chain s (xs ++ f :: ys) t) {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions xs).length) ≤ 2 ^ 256)
    (count : st.count + (submissions xs).length < 2 ^ 256) (hload : load st = 0)
    (few : (submissions xs).length ≤ 2892) (hq : f.quotedFee = some q) :
    q.toNat = fakeExp 1 ((queueAfter st xs).excess + ((queueAfter st xs).count - c.target.toNat)) 17 := by
  obtain ⟨m, h1, h2⟩ := chain.append_split
  have hb := excess_bound (frames := xs) rep.excess_lt (by omega)
  have hx := (h1.holds rep slots count).1
  have huser : ∀ latch, f.event ≠ .system latch := by
    intro latch he
    cases f with
    | submission sevm pre post l i o rules target caller law => cases he
    | feeRead sevm pre post l i o rules target caller law => cases he
    | system benv data post out fork installed length run => cases hq
  have hne := chain.user_not_inhibited rep slots count huser
  cases h2 with
  | cons starts tail =>
    subst starts
    refine f.quote_natural hx hq ?_
    rcases hb with hmax | hle
    · have : inhibitedAfter (decide (st.excess = 2 ^ 256 - 1)) (events xs) = true :=
        (excess_inhibitor c.target_ne c.cap st (events xs)).mp hmax
      rw [hne] at this
      cases this
    · omega

/-- **The excess update on a sequence.** In the model `Chain.holds` ties to storage: an empty-calldata system call
after frames `xs` stores 0 on the inhibitor, and `excess + count - target` in naturals off it, when the submissions
so far stay below the word. -/
theorem excess_update {xs : List (Frame c)} {f : Frame c} {st : QueueState c.Record} (he : st.excess < 2 ^ 256)
    (hload : load st + (submissions xs).length < 2 ^ 256) (call : f.event = .system false) :
    (queueAfter st (xs ++ [f])).excess =
      if (queueAfter st xs).excess = 2 ^ 256 - 1 then 0
      else (queueAfter st xs).excess + (queueAfter st xs).count - c.target.toNat := by
  have hstep : queueAfter st (xs ++ [f]) =
      drainedState c.cap c.target (queueAfter st xs) := by
    simp only [queueAfter, events, List.map_append, replay_append, List.map_cons, List.map_nil, call]
    rfl
  rw [hstep]
  by_cases hmax : (queueAfter st xs).excess = 2 ^ 256 - 1
  · rw [ite_eq_left hmax, drainedState_excess, hmax, inhibitor_toB256, excessNext_inhibitor]
    rfl
  · rw [ite_eq_right hmax]
    refine drained_excess_natural _ _ _ ?_ hmax
    have hb := excess_bound (frames := xs) he hload
    rcases hb with h | h
    · exact absurd h hmax
    · omega

/-- The empty-calldata calls of a list, as many as it has. -/
theorem events_calls {frames : List (Frame c)} (h : ∀ f ∈ frames, f.event = .system false) :
    events frames = List.replicate frames.length (.system false) := by
  apply List.eq_replicate_iff.mpr
  refine ⟨List.length_map .., fun e he => ?_⟩
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
  exact h f hf

theorem replay_calls_queue (cap : Nat) (target : B256) (st : QueueState Record) (k : Nat) :
    (replay cap target st (List.replicate k (.system false))).queue = st.queue.drop (cap * k) := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
    have hstep : replay cap target st (List.replicate (k + 1) (.system false)) =
        replay cap target (drainedState cap target st) (List.replicate k (.system false)) := rfl
    rw [hstep, ih, drainedState_queue, List.drop_drop, Nat.mul_succ, Nat.add_comm]

/-- `k ≥ 1` empty-calldata calls clear the count and step the excess down by the target each. -/
theorem replay_calls_excess (cap : Nat) (target : B256) (st : QueueState Record) (k : Nat)
    (hne : st.excess ≠ 2 ^ 256 - 1) (hsum : st.excess + st.count < 2 ^ 256 - 1) :
    (replay cap target st (List.replicate (k + 1) (.system false))).excess =
        st.excess + st.count - target.toNat * (k + 1) ∧
      (replay cap target st (List.replicate (k + 1) (.system false))).count = 0 := by
  induction k generalizing st with
  | zero =>
    refine ⟨?_, drainedState_count cap target st⟩
    show (drainedState cap target st).excess = _
    rw [drained_excess_natural cap target st (by omega) hne, Nat.mul_one]
  | succ k ih =>
    have hstep : replay cap target st (List.replicate (k + 1 + 1) (.system false)) =
        replay cap target (drainedState cap target st) (List.replicate (k + 1) (.system false)) := rfl
    have hx := drained_excess_natural cap target st (by omega) hne
    have hc := drainedState_count cap target st
    rw [hstep]
    obtain ⟨h1, h2⟩ := ih (drainedState cap target st) (by omega) (by omega)
    refine ⟨?_, h2⟩
    rw [h1, hx, hc, Nat.add_zero, Nat.sub_sub, Nat.mul_succ target.toNat (k + 1),
      Nat.add_comm target.toNat (target.toNat * (k + 1))]

theorem replay_noSystem_queue (cap : Nat) (target : B256) (st : QueueState Record) {es : List (Event Record)}
    (h : NoSystem es) : (replay cap target st es).queue = st.queue ++ submitted es := by
  have hfifo := delivered_append_queue cap target st es
  have hchunks : (chunks cap target st es).flatten = [] := by
    induction es generalizing st with
    | nil => rfl
    | cons e es ih =>
      have tail : NoSystem es := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hfifo' := delivered_append_queue cap target (step cap target st e) es
      have hc := ih (step cap target st e) tail hfifo'
      cases e with
      | submission r => exact hc
      | feeRead => exact hc
      | system latch => exact absurd rfl (h _ List.mem_cons_self latch)
  rwa [hchunks, List.nil_append] at hfifo

/-! ## Quote against charge -/

/-- A quoting frame ran with slot 0 off the inhibitor. -/
theorem Frame.quoted_active (f : Frame c) {q : B256} (hq : f.quotedFee = some q) : f.before.get 0 ≠ B256.max := by
  refine f.user_active fun latch he => ?_
  cases f with
  | submission sevm pre post l i o rules target caller law => cases he
  | feeRead sevm pre post l i o rules target caller law => cases he
  | system benv data post out fork installed length run => cases hq

/-- **Two quotes at the same storage are the same word.** Whatever else differs between the frames. -/
theorem Frame.same_storage_quote (f g : Frame c) {p q : B256} (same : f.before = g.before)
    (hp : f.quotedFee = some p) (hq : g.quotedFee = some q) : p = q := by
  obtain ⟨_, _, rfl, r1⟩ := f.quote_run hp
  obtain ⟨_, _, rfl, r2⟩ := g.quote_run hq
  rw [same] at r1
  obtain ⟨-, rfl⟩ := r1.deterministic r2
  rfl

/-- **A later quote differs only by the submissions between.** On a chain, with no system call in the frames `ys`
between, a quoting frame after them, with at most 2892 submissions before it, quotes
`fake_exponential(1, excess + max(0, count + m - target), 17)`, where `excess` and `count` are the queue's after `xs` and
`m` is the number of submissions in `ys`. Fee reads in `ys` change nothing. -/
theorem Chain.later_quote {s t : Stor} {xs ys zs : List (Frame c)} {g : Frame c} {q : B256}
    (chain : Chain s ((xs ++ ys) ++ g :: zs) t) {st : QueueState c.Record} (rep : Holds c s st)
    (slots : queueBase c.width (st.tail + (submissions (xs ++ ys)).length) ≤ 2 ^ 256)
    (count : st.count + (submissions (xs ++ ys)).length < 2 ^ 256) (hload : load st = 0)
    (none : NoSystem (events ys)) (few : (submissions (xs ++ ys)).length ≤ 2892) (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 ((queueAfter st xs).excess +
      ((queueAfter st xs).count + (submissions ys).length - c.target.toNat)) 17 := by
  have h := chain.quote_natural rep slots count hload few hq
  have hsplit : queueAfter st (xs ++ ys) = replay c.cap c.target (queueAfter st xs) (events ys) := by
    simp only [queueAfter, events, List.map_append, replay_append]
  rw [hsplit, excess_noSystem _ _ _ none, count_noSystem _ _ _ none] at h
  exact h

/-! ## Empty-calldata calls with no new submissions -/

theorem chunks_calls_get (cap : Nat) (target : B256) (st : QueueState Record) {k j : Nat} (hj : j < k) :
    (chunks cap target st (List.replicate k (.system false)))[j]? = some ((st.queue.drop (cap * j)).take cap) := by
  induction k generalizing st j with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have h := ih (drainedState cap target st) (j := j) (by omega)
      rw [drainedState_queue, List.drop_drop] at h
      rw [Nat.mul_succ, Nat.add_comm (cap * j)]
      exact h

/-- **Where an entry comes out.** With no new submissions, the entry at position `q` of the queue comes out in call
number `q / cap`, counting from 0, at offset `q % cap` of that call's records. -/
theorem position_call (cap : Nat) (target : B256) (st : QueueState Record) {k q : Nat} (hcap : 0 < cap)
    (hk : q / cap < k) :
    ((chunks cap target st (List.replicate k (.system false)))[q / cap]?).bind (·[q % cap]?) = st.queue[q]? := by
  rw [chunks_calls_get cap target st hk]
  show ((st.queue.drop (cap * (q / cap))).take cap)[q % cap]? = _
  rw [List.getElem?_take_of_lt (Nat.mod_lt _ hcap), List.getElem?_drop, Nat.div_add_mod]

/-! ## Machines for a sequence's witnesses -/

/-- A state holding this code and storage at `a`. -/
def holding (a : Adr) (code : ByteArray) (s : Stor) : State :=
  (default : State).set a { (default : State).get a with code := code, stor := s }

theorem holding_getStor (a : Adr) (code : ByteArray) (s : Stor) : (holding a code s).getStor a = s := by
  show ((holding a code s).get a).stor = s
  rw [holding, State.get_set_self]

theorem holding_getCode (a : Adr) (code : ByteArray) (s : Stor) : (holding a code s).getCode a = code :=
  (install_witness default a code s).1

/-- Amsterdam's block environment on that state. -/
def holdingBenv (a : Adr) (code : ByteArray) (s : Stor) : Benv :=
  { (default : Benv) with state := holding a code s, stat := { (default : BenvStat) with fork := .amsterdam } }

/-- A machine on that state. -/
def holdingDevm (a : Adr) (code : ByteArray) (s : Stor) : Devm :=
  (default : Devm).setWorld { (default : Devm).world with state := holding a code s }

/-- From any storage there is a real empty-calldata system call frame, given the call's success at that storage. -/
theorem Frame.exists_system (total : ∀ s, ∃ post out,
      processCheckedSystemTransaction (holdingBenv c.address c.code s) c.address [] = .ok (post, out)) (s : Stor) :
    ∃ f : Frame c, f.before = s ∧ f.event = .system false := by
  obtain ⟨post, out, run⟩ := total s
  exact ⟨.system (holdingBenv c.address c.code s) [] post out rfl (holding_getCode _ _ s) (by decide) run,
    holding_getStor _ _ s, rfl⟩

theorem holdingDevm_getStorVal (a : Adr) (code : ByteArray) (s : Stor) (k : B256) :
    (holdingDevm a code s).getStorVal a k = s.get k := by
  show ((holding a code s).getStor a).get k = _
  rw [holding_getStor]

end Blanc.Lift.BuilderRequest.Delivery
