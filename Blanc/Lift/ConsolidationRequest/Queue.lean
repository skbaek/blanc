import Blanc.Lift.ConsolidationRequest.System
import Blanc.Lift.ConsolidationRequest.Frames
import Blanc.Lift.RequestQueue.Chain

/-!
# The EIP-7251 queue model, and the queue effect of each frame

A record of the consolidation queue is the submitting caller and its 96 calldata bytes (source pubkey 48, target
pubkey 48). It is kept in four consecutive slots from `4 + 4 * index`: the caller's address word, then the three
calldata words; the system call returns it as 116 bytes, `caller ++ calldata`. `queue` is this layout as the
shared `RequestQueue.Queue`, width 4, at most 2 records per call.

* **C5, the queue effect of a submission** (`represents_submit`, `submission_represents`): on storage representing
  a queue, a successful submission's storage represents that queue with exactly its record appended (`push`), when
  the record's four slots fit below the word modulus; `tail < 2 ^ 253` is enough (`Delivery.delivered_of_lt`).
* **C4 at frame level** (`system_call_fifo`): on storage representing a queue, the checked system call on a
  covered fork succeeds, returns exactly the oldest `min(2, length)` records, 116 bytes each, and leaves storage
  representing the queue with those records removed, the count cleared and the excess at the runtime's arm
  (`sysExcess`, which is `max(0, e + n - 1)` without word wrap: `sysExcess_eq`).

These are representation statements: they say nothing about which storage is reachable.

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open RequestSystem
open BuilderRequest (QueueState queueBase queueSlot Represents record_key record_key_add)
open RequestQueue (Effect push drainedBy)
open SystemExecution.ConsolidationRequest.Amsterdam (sysShape recordKey)

/-- A record of the consolidation queue: the submitting caller and its 96 calldata bytes. -/
structure Record where
  source : Adr
  data : Bytes
  data_length : data.length = 96

/-- A record's stored words: the caller's address word, then the three calldata words. -/
def Record.word (r : Record) : Nat → B256
  | 0 => r.source.toB256
  | 1 => Bytes.toB256 (r.data.sliceD 0 32 0)
  | 2 => Bytes.toB256 (r.data.sliceD 32 32 0)
  | _ => Bytes.toB256 (r.data.sliceD 64 32 0)

/-- A record as the system call returns it: 20 bytes of caller, then the 96 calldata bytes. -/
def Record.out (r : Record) : Bytes := r.source.toBytes ++ r.data

/-- The record a submission's frame enqueues: its caller and its calldata. -/
def recordOf (sevm : Sevm) (h : sevm.data.length = 96) : Record := ⟨sevm.caller, sevm.data, h⟩

/-- The EIP-7251 queue layout: four slots per record, at most two records per system call. -/
abbrev queue : RequestQueue.Queue := ⟨Record, 4, Record.word, Record.out, 2⟩

/-! ## C5: a submission appends exactly its record -/

/-- The four keys a submission writes are the record slots at the tail. -/
theorem submissionKey_slot (t : Nat) : submissionKey t.toB256 = queueSlot 4 t 0 := record_key 4 t

/-- The submission's storage, slot by slot, at a tail `t`. -/
theorem submittedStorage_get (sevm : Sevm) {s : Stor} {t : Nat} (ht : s.get 3 = t.toB256) (k : B256) :
    (submittedStorage sevm s).get k =
      if (3 : B256) = k then 1 + s.get 3 else
      if queueSlot 4 t 3 = k then Sevm.dataWord sevm 64 else
      if queueSlot 4 t 2 = k then Sevm.dataWord sevm 32 else
      if queueSlot 4 t 1 = k then Sevm.dataWord sevm 0 else
      if queueSlot 4 t 0 = k then sevm.caller.toB256 else
      if (1 : B256) = k then 1 + s.get 1 else s.get k := by
  have key : submissionKey (s.get 3) = queueSlot 4 t 0 := by
    rw [ht]
    exact submissionKey_slot t
  have step : ∀ j, (1 : B256) + queueSlot 4 t j = queueSlot 4 t (j + 1) := fun j => by
    rw [show (1 : B256) = Nat.toB256 1 by decide]
    exact record_key_add 4 t j 1
  simp only [submittedStorage, key, step, Nat.zero_add, Nat.reduceAdd, Stor.get_set_ite]

/-- **A submission's storage on a represented queue represents the queue with its record appended**, when the
record's four slots fit below the word modulus and the count stays in word range. -/
theorem represents_submit (sevm : Sevm) (h : sevm.data.length = 96) {s : Stor} {st : QueueState Record}
    (rep : Represents 4 Record.word (fun key => s.get key) st)
    (slots : queueBase 4 st.tail + 4 ≤ 2 ^ 256) (count : st.count + 1 < 2 ^ 256) :
    Represents 4 Record.word (fun key => (submittedStorage sevm s).get key) (push st (recordOf sevm h)) := by
  have ht : s.get 3 = st.tail.toB256 := rep.tail
  have hstor := submittedStorage_get sevm ht
  have val : ∀ j, j < 4 → (queueSlot 4 st.tail j).toNat = 4 + 4 * st.tail + j := fun j hj => by
    unfold queueSlot queueBase at *
    rw [B256.toNat_toB256_of_lt (by omega)]
  have hmeta : ∀ n, n < 4 → ∀ j, j < 4 → queueSlot 4 st.tail j ≠ n.toB256 := fun n hn j hj e => by
    have := congrArg B256.toNat e
    rw [val j hj, B256.toNat_toB256_of_lt (by omega)] at this
    omega
  have hrec : ∀ i j, i < 4 → j < 4 → i ≠ j → queueSlot 4 st.tail i ≠ queueSlot 4 st.tail j :=
    fun i j hi hj hij e => by
      have := congrArg B256.toNat e
      rw [val i hi, val j hj] at this
      omega
  have m0 : ∀ j, j < 4 → queueSlot 4 st.tail j ≠ 0 := hmeta 0 (by omega)
  have m1 : ∀ j, j < 4 → queueSlot 4 st.tail j ≠ 1 := hmeta 1 (by omega)
  have m2 : ∀ j, j < 4 → queueSlot 4 st.tail j ≠ 2 := hmeta 2 (by omega)
  have m3 : ∀ j, j < 4 → queueSlot 4 st.tail j ≠ 3 := hmeta 3 (by omega)
  have d10 : (1 : B256) ≠ 0 := by decide
  have d30 : (3 : B256) ≠ 0 := by decide
  have d31 : (3 : B256) ≠ 1 := by decide
  have d12 : (1 : B256) ≠ 2 := by decide
  have d32 : (3 : B256) ≠ 2 := by decide
  refine RequestQueue.represents_push rep (by omega) slots count ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hstor]
    simp only [d30, m0 _ (by omega : 3 < 4), m0 _ (by omega : 2 < 4), m0 _ (by omega : 1 < 4),
      m0 _ (by omega : 0 < 4), d10, ↓reduceIte]
  · rw [hstor]
    simp only [d31, m1 _ (by omega : 3 < 4), m1 _ (by omega : 2 < 4), m1 _ (by omega : 1 < 4),
      m1 _ (by omega : 0 < 4), ↓reduceIte]
    show (1 : B256) + s.get 1 = _
    rw [show s.get 1 = st.count.toB256 from rep.count]
    exact RequestQueue.one_add_word _
  · rw [hstor]
    simp only [d32, m2 _ (by omega : 3 < 4), m2 _ (by omega : 2 < 4), m2 _ (by omega : 1 < 4),
      m2 _ (by omega : 0 < 4), d12, ↓reduceIte]
  · rw [hstor]
    simp only [↓reduceIte]
    rw [ht]
    exact RequestQueue.one_add_word _
  · intro j hj
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [hstor, ite_eq_right (m3 0 (by omega)).symm, ite_eq_right (hrec 3 0 (by omega) (by omega) (by omega)),
        ite_eq_right (hrec 2 0 (by omega) (by omega) (by omega)),
        ite_eq_right (hrec 1 0 (by omega) (by omega) (by omega)), ite_eq_left rfl]
      rfl
    · rw [hstor, ite_eq_right (m3 1 (by omega)).symm, ite_eq_right (hrec 3 1 (by omega) (by omega) (by omega)),
        ite_eq_right (hrec 2 1 (by omega) (by omega) (by omega)), ite_eq_left rfl]
      rfl
    · rw [hstor, ite_eq_right (m3 2 (by omega)).symm, ite_eq_right (hrec 3 2 (by omega) (by omega) (by omega)),
        ite_eq_left rfl]
      rfl
    · rw [hstor, ite_eq_right (m3 3 (by omega)).symm, ite_eq_left rfl]
      rfl
  · intro k h1 h3 hs
    rw [hstor, ite_eq_right h3, ite_eq_right (hs 3 (by omega)), ite_eq_right (hs 2 (by omega)),
      ite_eq_right (hs 1 (by omega)), ite_eq_right (hs 0 (by omega)), ite_eq_right h1]

/-- **C5.** A successful submission frame, on storage representing a queue at the contract, leaves storage
representing the queue with exactly its record (its caller and calldata) appended at the back: the count and
tail one higher, the excess and head unchanged, every queued record in place. The premises are the word range of
the record's slots and the count. -/
theorem submission_represents {sevm : Sevm} {pre post : Devm} {i : Nat} {o : B256}
    (law : Submitted sevm pre post i o) {st : QueueState Record}
    (rep : Represents 4 Record.word (fun key => (pre.getStor sevm.currentTarget).get key) st)
    (slots : queueBase 4 st.tail + 4 ≤ 2 ^ 256) (count : st.count + 1 < 2 ^ 256) :
    Represents 4 Record.word (fun key => (post.getStor sevm.currentTarget).get key)
      (push st (recordOf sevm law.length)) := by
  rw [law.storage]
  exact represents_submit sevm law.length rep slots count

/-! ## C4 at frame level: the system call takes the oldest records -/

/-- The excess the runtime stores after a call, in naturals, from the stored excess and count. -/
def sysExcess (e n : Nat) : Nat := (sysShape.next e.toB256 n.toB256).toNat

/-- Without word wrap, the stored excess is `max(0, e + n - 1)`, the inhibitor read as zero. -/
theorem sysExcess_eq {e n : Nat} (e_lt : e < 2 ^ 256) (noWrap : (if e = 2 ^ 256 - 1 then 0 else e) + n < 2 ^ 256) :
    sysExcess e n = excessAfter e n :=
  plainNext_toNat _ e_lt noWrap

/-- Queue keys at a represented head. -/
theorem recordKey_slot (head i : Nat) : recordKey head.toB256 i.toB256 = queueSlot 4 (head + i) 0 := by
  unfold recordKey
  rw [Nat.toB256_add_toB256, ← record_key, Nat.add_comm i head]
  rfl

/-- The three calldata words of a record, in order, are its calldata. -/
theorem data_words (r : Record) :
    (Bytes.toB256 (r.data.sliceD 0 32 0)).toBytes ++ (Bytes.toB256 (r.data.sliceD 32 32 0)).toBytes ++
      (Bytes.toB256 (r.data.sliceD 64 32 0)).toBytes = r.data := by
  rw [Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _),
    Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _),
    Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)]
  have h1 := List.sliceD_split r.data (0 : UInt8) 32 0 64
  have h2 := List.sliceD_split r.data (0 : UInt8) 32 32 32
  simp only [Nat.reduceAdd] at h1 h2
  rw [List.append_assoc, ← h2, ← h1]
  exact sliceD_self _ r.data_length

/-- A record's returned bytes, from its stored words. -/
theorem recordBytes_eq {rd : B256 → B256} {h i : B256} (r : Record)
    (h0 : rd (recordKey h i) = r.word 0) (h1 : rd (1 + recordKey h i) = r.word 1)
    (h2 : rd (2 + recordKey h i) = r.word 2) (h3 : rd (3 + recordKey h i) = r.word 3) :
    recordBytes rd h i = r.out := by
  unfold recordBytes Record.out
  rw [h0, h1, h2, h3]
  have ha : (r.word 0 <<< 96).toBytes.sliceD 0 20 0 = r.source.toBytes := by
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega),
      WordByteCodecs.shift96_take20_toAdr_bytes]
    show (r.source.toB256).toAdr.toBytes = _
    rw [toAdr_toB256]
  rw [ha, List.append_assoc, List.append_assoc, ← List.append_assoc (Record.word r 1).toBytes]
  exact congrArg (r.source.toBytes ++ ·) (data_words r)

/-- **C4 at frame level.** On storage representing a queue at the consolidation address, with the canonical
code installed under a covered fork, the checked system call (empty calldata) succeeds with no error within
114,177 gas, returns exactly the oldest `min(2, length)` records, each `caller ++ calldata`, and leaves storage
representing the queue with those records removed: the head advanced past them (both pointers reset when the
queue empties), the count cleared and the excess at `sysExcess`. -/
theorem system_call_fifo {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    {st : QueueState Record}
    (rep : Represents 4 Record.word (storOf benv.state consolidationRequestPredeployAddress) st) :
    ∃ post out, processCheckedSystemTransaction benv consolidationRequestPredeployAddress [] = .ok (post, out) ∧
      post = sysState sysShape benv.state consolidationRequestPredeployAddress ∧
      out.error = none ∧ RegularGasWithin out.gasLeft 114177 ∧
      out.returnData = (st.queue.take 2).flatMap Record.out ∧
      Represents 4 Record.word (storOf post consolidationRequestPredeployAddress)
        (drainedBy 2 (sysExcess st.excess st.count) st) := by
  obtain ⟨out, hcall, herr, hgas, hret⟩ := system_call_ok fork installed
  refine ⟨_, out, hcall, rfl, herr, hgas, ?_, RequestQueue.represents_drain sysShape (by decide) rep⟩
  rw [hret]
  refine RequestQueue.drained_represented sysOutput rep ?_
  intro i hi _
  have hlive := rep.live i hi
  have key : ∀ j : Nat, j < 4 → (j : Nat).toB256 + queueSlot 4 (st.head + i) 0 = queueSlot 4 (st.head + i) j :=
    fun j _ => by simpa only [Nat.zero_add] using record_key_add 4 (st.head + i) 0 j
  refine recordBytes_eq _ ?_ ?_ ?_ ?_
  · rw [recordKey_slot]
    exact hlive 0 (by decide)
  · rw [recordKey_slot, show (1 : B256) = Nat.toB256 1 by decide, key 1 (by decide)]
    exact hlive 1 (by decide)
  · rw [recordKey_slot, show (2 : B256) = Nat.toB256 2 by decide, key 2 (by decide)]
    exact hlive 2 (by decide)
  · rw [recordKey_slot, show (3 : B256) = Nat.toB256 3 by decide, key 3 (by decide)]
    exact hlive 3 (by decide)

end Blanc.Lift.ConsolidationRequest
