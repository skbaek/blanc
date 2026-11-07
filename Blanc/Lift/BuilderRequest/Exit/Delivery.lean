import Blanc.Lift.BuilderRequest.Delivery
import Blanc.Lift.BuilderRequest.Exit.Fifo
import Blanc.Lift.BuilderRequest.Exit.Latch
import Blanc.Lift.BuilderRequest.Exit.SubmissionAmsterdam

/-!
# Exact delivery at the exit contract, over a given sequence of frames

The frames are an input: a list of submissions and fee reads under covered forks or Amsterdam, and system calls
under Amsterdam, each with what its frame law gives, each running on the storage the last one left, from the
storage the factory deploys. "Committed" here means "in the given sequence". That a chain's retained frames form
such a list is not claimed: that needs message and transaction level. The deployed storage holds the inhibitor, so
the first frame of any such list is a system call (`first_frame_system`).

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`; the bytes and `sys-asm`
`83f9801`, not the EIP text.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestSystem
open Delivery
open Creation (address)

/-- The record a submission's frame enqueues: the caller as the source, the calldata as the key. -/
def recordOf (sevm : Sevm) (h : sevm.data.length = 48) : Record := ⟨sevm.caller, sevm.data, h⟩

/-- A submission's storage effect on a represented queue, with its slots and count in word range. -/
theorem represents_submit (sevm : Sevm) (h : sevm.data.length = 48) {s : Stor} {st : QueueState Record}
    (rep : Represents 3 Record.word (fun key => s.get key) st)
    (slots : queueBase 3 st.tail + 3 ≤ 2 ^ 256) (count : st.count + 1 < 2 ^ 256) :
    Represents 3 Record.word (fun key => (submittedStorage sevm s).get key) (submit st (recordOf sevm h)) := by
  have ht : s.get 3 = st.tail.toB256 := rep.tail
  have hrec := submittedStorage_record sevm ht slots
  have key : submissionKey (s.get 3) = queueSlot 3 st.tail 0 := by
    rw [ht]
    exact record_key 3 st.tail
  have step : ∀ j, (1 : B256) + queueSlot 3 st.tail j = queueSlot 3 st.tail (j + 1) := fun j => by
    rw [show (1 : B256) = Nat.toB256 1 by decide]
    exact record_key_add 3 st.tail j 1
  have val : ∀ j, j < 3 → (queueSlot 3 st.tail j).toNat = 4 + 3 * st.tail + j := fun j hj => by
    unfold queueSlot queueBase at *
    rw [B256.toNat_toB256_of_lt (by omega)]
  have hmeta : ∀ n, n < 4 → ∀ j, j < 3 → queueSlot 3 st.tail j ≠ n.toB256 := fun n hn j hj e => by
    have := congrArg B256.toNat e
    rw [val j hj, B256.toNat_toB256_of_lt (by omega)] at this
    omega
  have m0 : ∀ j, j < 3 → queueSlot 3 st.tail j ≠ 0 := hmeta 0 (by omega)
  have m1 : ∀ j, j < 3 → queueSlot 3 st.tail j ≠ 1 := hmeta 1 (by omega)
  have m2 : ∀ j, j < 3 → queueSlot 3 st.tail j ≠ 2 := hmeta 2 (by omega)
  have d10 : (1 : B256) ≠ 0 := by decide
  have d30 : (3 : B256) ≠ 0 := by decide
  have d31 : (3 : B256) ≠ 1 := by decide
  have d12 : (1 : B256) ≠ 2 := by decide
  have d32 : (3 : B256) ≠ 2 := by decide
  have hstor : ∀ k, (submittedStorage sevm s).get k =
      if (3 : B256) = k then 1 + s.get 3 else
      if queueSlot 3 st.tail 2 = k then Sevm.dataWord sevm 32 else
      if queueSlot 3 st.tail 1 = k then Sevm.dataWord sevm 0 else
      if queueSlot 3 st.tail 0 = k then sevm.caller.toB256 else
      if (1 : B256) = k then 1 + s.get 1 else s.get k := fun k => by
    simp only [submittedStorage, key, step, Nat.zero_add, Nat.reduceAdd, Stor.get_set_ite]
  refine represents_after_submit rep (by omega) slots count ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hstor]
    simp only [d30, m0 _ (by omega : 2 < 3), m0 _ (by omega : 1 < 3), m0 _ (by omega : 0 < 3), d10, ↓reduceIte]
  · rw [hstor]
    simp only [d31, m1 _ (by omega : 2 < 3), m1 _ (by omega : 1 < 3), m1 _ (by omega : 0 < 3), ↓reduceIte]
    show (1 : B256) + s.get 1 = _
    rw [show s.get 1 = st.count.toB256 from rep.count]
    exact one_add_word _
  · rw [hstor]
    simp only [d32, m2 _ (by omega : 2 < 3), m2 _ (by omega : 1 < 3), m2 _ (by omega : 0 < 3), d12, ↓reduceIte]
  · rw [hstor]
    simp only [↓reduceIte]
    rw [ht]
    exact one_add_word _
  · intro j hj
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact hrec.1
    · exact hrec.2.1
    · exact hrec.2.2
  · intro k h1 h3 hs
    rw [hstor, ite_eq_right h3, ite_eq_right (hs 2 (by omega)), ite_eq_right (hs 1 (by omega)),
      ite_eq_right (hs 0 (by omega)), ite_eq_right h1]

/-- The empty-calldata system call's law. -/
theorem system_law {benv : Benv} {post : State} {result : MsgCallOutput} (hf : benv.stat.fork = .amsterdam)
    (hi : benv.state.getCode address = code)
    (run : processCheckedSystemTransaction benv address [] = .ok (post, result)) :
    post = sysState sysShape benv.state address ∧
      ∀ {st : QueueState Record}, Represents 3 Record.word (storOf benv.state address) st →
        result.returnData = (st.queue.take 16).flatMap Record.out := by
  obtain ⟨o, h, _⟩ := system_call_state hf hi
  have e : (post, result) = (sysState sysShape benv.state address, o) := Except.ok.inj (run.symm.trans h)
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  refine ⟨e1, ?_⟩
  intro st rep
  obtain ⟨_, o', h', _, hout, _⟩ := system_call_fifo hf hi rep
  have e' : (post, result) = (_, o') := Except.ok.inj (run.symm.trans h')
  exact (congrArg (fun x => x.2.returnData) e').trans hout

/-- The nonempty-calldata system call's law. -/
theorem latch_law {benv : Benv} {data : Bytes} {post : State} {result : MsgCallOutput}
    (hf : benv.stat.fork = .amsterdam) (hi : benv.state.getCode address = code) (hne : data ≠ [])
    (hlen : data.length < 2 ^ 256)
    (run : processCheckedSystemTransaction benv address data = .ok (post, result)) :
    post = latchState sysShape benv.state address ∧
      ∀ {st : QueueState Record}, Represents 3 Record.word (storOf benv.state address) st →
        result.returnData = (st.queue.take 16).flatMap Record.out := by
  obtain ⟨o, _, h, _⟩ := latch_call hf hi hne hlen
  have e : (post, result) = (latchState sysShape benv.state address, o) := Except.ok.inj (run.symm.trans h)
  obtain ⟨e1, -⟩ := Prod.mk.inj e
  refine ⟨e1, ?_⟩
  intro st rep
  obtain ⟨_, o', h', _, hout, _⟩ := latch_fifo hf hi hne hlen rep
  have e' : (post, result) = (_, o') := Except.ok.inj (run.symm.trans h')
  exact (congrArg (fun x => x.2.returnData) e').trans hout

/-- The exit contract, as the sequence statements take it. -/
abbrev contract : Contract where
  code := code
  address := address
  target := 2
  cap := 16
  width := 3
  Record := Record
  words := Record.word
  out := Record.out
  Submitted := fun l pre post i o => SubmittedOn l pre post i o
  payload := 48
  recordOf := recordOf
  submitStor := submittedStorage
  shape := sysShape
  length := fun h => h.length
  storage := fun h => h.storage
  active := fun h => h.active
  quote := fun h => h.quote
  paid := fun h => h.covered
  represents_submit := represents_submit
  cap_word := by decide
  target_eq := rfl
  next_eq := rfl
  target_ne := by decide
  system_law := system_law
  latch_law := latch_law

/-- A frame at the exit contract. -/
abbrev Frame := Delivery.Frame contract

/-- The storage the factory deploys: slot 0 at the inhibitor, everything else 0. -/
def deployedStorage : Stor := Stor.empty.set 0 B256.max

/-- The queue the deployed storage holds: empty, every counter 0, the excess at the inhibitor. -/
def deployedQueue : QueueState Record := ⟨2 ^ 256 - 1, 0, 0, 0, []⟩

/-- `Creation.factory_deploy`'s storage represents it. -/
theorem deployed_represents : Holds contract deployedStorage deployedQueue where
  coherent := rfl
  excess_lt := by decide
  count_lt := by decide
  head_lt := by decide
  tail_lt := by decide
  live_lt := fun i hi => absurd hi (Nat.not_lt_zero _)
  excess := by
    show (Stor.empty.set 0 B256.max).get 0 = _
    rw [Stor.get_set_self]
    exact inhibitor_toB256.symm
  count := by
    show (Stor.empty.set 0 B256.max).get 1 = _
    rw [Stor.get_set_ne _ (by decide)]
    rfl
  head := by
    show (Stor.empty.set 0 B256.max).get 2 = _
    rw [Stor.get_set_ne _ (by decide)]
    rfl
  tail := by
    show (Stor.empty.set 0 B256.max).get 3 = _
    rw [Stor.get_set_ne _ (by decide)]
    rfl
  live := fun i hi => absurd hi (Nat.not_lt_zero _)

/-! ## O17 -/

/-- **Exact delivery at the exit contract.** Over any given chain of frames from the deployed storage, with the
word range `4 + 3 * n ≤ 2 ^ 256` on the `n` submissions: storage at the end represents `queueAfter`, whose records
are exactly the submissions not yet delivered, in order; and the system calls' concatenated output is exactly the
delivered submissions' records, in order, each the source then the key (`Record.out`). `deliveredRecords` counts what
the calls took, each `min(length, 16)` of what it found. So nothing is dropped, duplicated or reordered;
`call_delivers` says nothing is early. `recordOf` says each record's source is its frame's caller, an address and so
160 bits by its type. The list has no reverted frame and no frame with caller `systemAddress` other than the request
phase's calls (`Frame`): such a frame would drain the queue to its caller, and the delivery stated here would not be
to the block's requests. -/
theorem delivery {frames : List Frame} {t : Stor} (chain : Chain deployedStorage frames t)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256) :
    Represents 3 Record.word (fun key => t.get key) (queueAfter deployedQueue frames) ∧
      (queueAfter deployedQueue frames).queue =
        (submissions frames).drop (deliveredRecords deployedQueue frames) ∧
      systemOutput frames =
        ((submissions frames).take (deliveredRecords deployedQueue frames)).flatMap Record.out := by
  have h := chain.delivered deployed_represents (by show 4 + _ * (0 + _) ≤ _; rw [Nat.zero_add]; exact range)
    (by show 0 + _ < _; omega)
  exact ⟨h.represents, h.queue, h.output⟩

/-- **The first frame is a system call.** The deployed storage holds the inhibitor, so no user frame can run on
it: the sequence starts with a system call, or is empty. Nothing is assumed about this; it follows from the frame
laws. If that call has nonempty calldata the contract stays inhibited (`excess_iff`). -/
theorem first_frame_system {f : Frame} {rest : List Frame} {t : Stor}
    (chain : Chain deployedStorage (f :: rest) t) : ∃ latch, f.event = .system latch := by
  by_contra hf
  have huser : ∀ latch, f.event ≠ .system latch := fun latch h => hf ⟨latch, h⟩
  have hactive := f.user_active huser
  cases chain with
  | cons starts tail =>
    rw [starts] at hactive
    exact hactive (Stor.get_set_self _ _ _)

/-- **Each system call delivers the next records and no others.** On a chain from the deployed storage, a system
call's output is the oldest `min(length, 16)` of the records submitted before it and not yet delivered. -/
theorem call_delivers {xs ys : List Frame} {f : Frame} {latch : Bool} {t : Stor}
    (chain : Chain deployedStorage (xs ++ f :: ys) t) (call : f.event = .system latch)
    (range : 4 + 3 * (submissions xs).length ≤ 2 ^ 256) :
    f.output = (((submissions xs).drop (deliveredRecords deployedQueue xs)).take 16).flatMap Record.out :=
  chain.call_delivers deployed_represents (by show 4 + _ * (0 + _) ≤ _; rw [Nat.zero_add]; exact range)
    (by show 0 + _ < _; omega) call

/-! ## O18 -/

/-- **The excess over the sequence, at the exit contract.** Over any given chain from the deployed storage, with the
word range: slot 0 is the inhibitor exactly when the last system call had nonempty calldata, or there has been no
system call; away from it `excess + count` is at most the number of submissions so far; and with no system call the
sequence is empty, so the deployed inhibitor is still there. -/
theorem excess_dynamics {frames : List Frame} {t : Stor} (chain : Chain deployedStorage frames t)
    (range : 4 + 3 * (submissions frames).length ≤ 2 ^ 256) :
    (t.get 0 = B256.max ↔ inhibitedAfter true (events frames) = true) ∧
      ((queueAfter deployedQueue frames).excess = 2 ^ 256 - 1 ∨
        (queueAfter deployedQueue frames).excess + (queueAfter deployedQueue frames).count ≤
          (submissions frames).length) ∧
      (NoSystem (events frames) → frames = [] ∧ t.get 0 = B256.max) := by
  have hslots : queueBase 3 (deployedQueue.tail + (submissions frames).length) ≤ 2 ^ 256 := by
    show 4 + _ * (0 + _) ≤ _
    rw [Nat.zero_add]
    exact range
  have hcount : deployedQueue.count + (submissions frames).length < 2 ^ 256 := by
    show 0 + _ < _
    omega
  have hload : load deployedQueue = 0 := by decide
  have hiff := chain.excess_iff deployed_represents hslots hcount
  rw [show decide (deployedQueue.excess = 2 ^ 256 - 1) = true by decide] at hiff
  have hbound := excess_bound (c := contract) (frames := frames) (st := deployedQueue) (by decide)
    (by rw [hload]; omega)
  rw [hload, Nat.zero_add] at hbound
  refine ⟨hiff, hbound, fun none => ?_⟩
  cases frames with
  | nil =>
    cases chain with
    | nil => exact ⟨rfl, Stor.get_set_self _ _ _⟩
  | cons f rest =>
    obtain ⟨latch, h⟩ := first_frame_system chain
    exact absurd h (none _ List.mem_cons_self latch)

/-- **A quote over the sequence, at the exit contract, in naturals.** A frame's word quote, with at most 2892
submissions before it on a chain from the deployed storage, is `fake_exponential(1, excess + max(0, count - 2), 17)`
of the queue it finds. `RequestFeeWord.word_fee_ne_natural_2893` is where this agreement stops. -/
theorem quote_natural {xs ys : List Frame} {f : Frame} {q : B256} {t : Stor}
    (chain : Chain deployedStorage (xs ++ f :: ys) t) (few : (submissions xs).length ≤ 2892)
    (hq : f.quotedFee = some q) :
    q.toNat = fakeExp 1 ((queueAfter deployedQueue xs).excess + ((queueAfter deployedQueue xs).count - 2)) 17 :=
  chain.quote_natural deployed_represents
    (by show 4 + 3 * (0 + _) ≤ _; omega) (by show 0 + _ < _; omega)
    (by decide) few hq

/-- **A submission paying the quote read at the same storage is admitted.** A frame quoted `q` on some storage. A
later machine `b` holding that same storage at the contract, under either fork's steps, with value covering `q`: the submission
runs, at its stated charge and with its exact post state. -/
theorem paying_quote_admitted {f : Frame} {q : B256} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {l : StorageSteps sevm} (v : l.Valid) (hq : f.quotedFee = some q)
    (same : f.before = b.getStor address) (target : sevm.currentTarget = address)
    (hcode : sevm.code = code) (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 48)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) (pay : q.toNat ≤ sevm.value.toNat) :
    ∃ iterations, Nonempty (Exec 0 sevm (St b [] M (G + submissionGasOn l b M iterations))
      (.ok (Steps.submissionPost l (l.feeBase b) M (G + Steps.bodyRepay l (l.feeBase b) M)))) := by
  obtain ⟨i, o, rfl, run⟩ := f.quote_run hq
  have hactive := f.quoted_active hq
  rw [same] at run hactive
  have hread : ∀ k, b.getStorVal sevm.currentTarget k = (b.getStor address).get k := fun k => by
    rw [target]
    rfl
  refine ⟨i, exec_submission_on v hcode caller hlen dynamic slack (by rw [hread]; exact hactive) ?_ pay⟩
  rw [storedExcess, hread, hread]
  exact run

/-- **A later quote at the exit contract, with the count.** With no system call in `ys`, a quoting frame after
them quotes `fake_exponential(1, excess + max(0, count + m - 2), 17)`: `excess` and `count` are the queue's after
`xs` and `m` the number of submissions in `ys`. Nothing else in between moves it. Under 2892 submissions before it. -/
theorem later_quote {xs ys zs : List Frame} {g : Frame} {q : B256} {t : Stor}
    (chain : Chain deployedStorage ((xs ++ ys) ++ g :: zs) t) (none : NoSystem (events ys))
    (few : (submissions (xs ++ ys)).length ≤ 2892) (hq : g.quotedFee = some q) :
    q.toNat = fakeExp 1 ((queueAfter deployedQueue xs).excess +
      ((queueAfter deployedQueue xs).count + (submissions ys).length - 2)) 17 :=
  chain.later_quote deployed_represents
    (by show 4 + 3 * (0 + _) ≤ _; omega) (by show 0 + _ < _; omega) (by decide) none few hq

end Blanc.Lift.BuilderRequest.Exit
