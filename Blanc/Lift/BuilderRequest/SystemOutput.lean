import Blanc.Lift.RequestSystem.Output
import Blanc.Lift.BuilderRequest.SystemPath
import Blanc.Lift.BuilderRequest.QueueLayout

/-!
# What a builder system call leaves on a represented queue

`represents_sysState` is the storage half of the FIFO: on storage representing a queue, the post storage
represents the drained queue, with the oldest `min(length, cap)` records gone. These are representation
statements. Nothing here says which storage is reachable, or that a stored record came from a real
submission.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestSystem

variable {Record : Type}

/-- The queue a call leaves: the oldest `min(length, cap)` records gone, the pointers moved as the bytes
move them, the excess as stored, and the count cleared. -/
def drainedState (cap : Nat) (target : B256) (st : QueueState Record) : QueueState Record :=
  let excess := (excessNext target st.excess.toB256 st.count.toB256).toNat
  if st.queue.length ≤ cap then ⟨excess, 0, 0, 0, []⟩
  else ⟨excess, 0, st.head + cap, st.tail, st.queue.drop cap⟩

/-- The count of records a call drains, on a represented queue. -/
theorem drainCount_represented {head len tail capN : Nat} {cap : B256} (hcap : cap.toNat = capN)
    (coherent : head + len = tail) (tail_lt : tail < 2 ^ 256) :
    drainCount cap head.toB256 tail.toB256 = (min len capN).toB256 := by
  have hdiff : tail.toB256 - head.toB256 = len.toB256 := by
    apply B256.toNat_inj
    rw [B256.toNat_sub, B256.toNat_toB256_of_lt tail_lt, B256.toNat_toB256_of_lt (by omega),
      B256.toNat_toB256_of_lt (by omega)]
    change (2 ^ 256 + tail - head) % 2 ^ 256 = len
    omega
  unfold drainCount
  rw [hdiff]
  by_cases hlt : len < capN
  · have hgt : cap > len.toB256 := by
      apply B256.lt_iff_toNat_lt_toNat.mpr
      rw [B256.toNat_toB256_of_lt (by omega), hcap]
      exact hlt
    rw [ite_eq_left_iff.mpr (fun no => absurd hgt no), Nat.min_eq_left (by omega)]
  · have hgt : ¬ cap > len.toB256 := by
      intro h
      have := B256.lt_iff_toNat_lt_toNat.mp h
      rw [B256.toNat_toB256_of_lt (by omega), hcap] at this
      omega
    rw [ite_eq_right_iff.mpr (fun yes => absurd yes hgt), Nat.min_eq_right (by omega), ← hcap,
      toB256_toNat]

/-- A live record's slot is none of the four metadata slots. -/
theorem queueSlot_ne {width index offset n : Nat} (hn : n < 4) {x : B256} (hx : x.toNat = n)
    (hlt : queueBase width index + width ≤ 2 ^ 256) (hj : offset < width) :
    x ≠ queueSlot width index offset := by
  intro eq
  have := congrArg B256.toNat eq
  rw [hx, queueSlot, B256.toNat_toB256_of_lt (by omega)] at this
  unfold queueBase at this
  omega

/-- **The storage half of the FIFO.** On storage representing a queue, a call's post storage represents
the queue with its oldest `min(length, cap)` records gone. -/
theorem represents_sysState {width : Nat} {words : Record → Nat → B256} (p : SysShape) {capN : Nat}
    (hcap : p.cap.word.toNat = capN) (hnext : p.next = excessNext p.target.word) {σ : State} {a : Adr}
    {st : QueueState Record}
    (rep : Represents width words (storOf σ a) st) :
    Represents width words (storOf (sysState p σ a) a) (drainedState capN p.target.word st) := by
  have hcount := drainCount_represented hcap rep.coherent rep.tail_lt
  have hc : drainCount p.cap.word (storOf σ a 2) (storOf σ a 3) = (min st.queue.length capN).toB256 := by
    rw [rep.head, rep.tail]
    exact hcount
  have hadd : storOf σ a 2 + (min st.queue.length capN).toB256 =
      (st.head + min st.queue.length capN).toB256 := by
    rw [rep.head, Nat.toB256_add_toB256]
  have tail_lt := rep.tail_lt
  have coh := rep.coherent
  have hget : ∀ key, storOf (sysState p σ a) a key =
      if (1 : B256) = key then 0
      else if (0 : B256) = key then excessNext p.target.word st.excess.toB256 st.count.toB256
      else if st.queue.length ≤ capN then
        (if (3 : B256) = key then 0 else if (2 : B256) = key then 0 else storOf σ a key)
      else (if (2 : B256) = key then (st.head + capN).toB256 else storOf σ a key) := by
    intro key
    show ((sysState p σ a).getStor a).get key = _
    rw [sysState_get, hnext]
    dsimp only
    rw [hc, hadd, rep.excess, rep.count]
    by_cases hle : st.queue.length ≤ capN
    · have hem : (st.head + min st.queue.length capN).toB256 = storOf σ a 3 := by
        rw [rep.tail, Nat.min_eq_left hle, coh]
      rw [ite_eq_left_iff.mpr (fun no => absurd hem no), if_pos hle]
    · have hmin : min st.queue.length capN = capN := Nat.min_eq_right (by omega)
      have hne : ¬ (st.head + capN).toB256 = storOf σ a 3 := by
        rw [rep.tail]
        intro eq
        have := congrArg B256.toNat eq
        rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt tail_lt] at this
        omega
      rw [hmin, if_neg hne, if_neg hle]
  have h0 : (0 : Nat) < 2 ^ 256 := by decide
  unfold drainedState
  dsimp only
  by_cases hle : st.queue.length ≤ capN
  · rw [if_pos hle]
    refine ⟨by simp only [List.length_nil], B256.toNat_lt _, h0, h0, h0,
      fun i hi => absurd hi (by simp only [List.length_nil]; omega), ?_, ?_, ?_, ?_,
      fun i hi => absurd hi (by simp only [List.length_nil]; omega)⟩
    · rw [hget, if_neg (by decide), if_pos rfl, toB256_toNat]
    · rw [hget, if_pos rfl]
      rfl
    · rw [hget, if_neg (by decide), if_neg (by decide), if_pos hle, if_neg (by decide), if_pos rfl]
      rfl
    · rw [hget, if_neg (by decide), if_neg (by decide), if_pos hle, if_pos rfl]
      rfl
  · rw [if_neg hle]
    refine ⟨?_, B256.toNat_lt _, h0, (by show st.head + capN < 2 ^ 256; omega), tail_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_drop]
      omega
    · intro i hi
      simp only [List.length_drop] at hi
      have := rep.live_lt (capN + i) (by omega)
      rw [show st.head + capN + i = st.head + (capN + i) by omega]
      exact this
    · rw [hget, if_neg (by decide), if_pos rfl, toB256_toNat]
    · rw [hget, if_pos rfl]
      rfl
    · rw [hget, if_neg (by decide), if_neg (by decide), if_neg hle, if_pos rfl]
    · rw [hget, if_neg (by decide), if_neg (by decide), if_neg hle, if_neg (by decide)]
      exact rep.tail
    · intro i hi j hj
      simp only [List.length_drop] at hi
      have hl := rep.live_lt (capN + i) (by omega)
      have hslot : st.head + capN + i = st.head + (capN + i) := by omega
      rw [hslot]
      rw [hget, if_neg (queueSlot_ne (n := 1) (by omega) (by decide) hl hj),
        if_neg (queueSlot_ne (n := 0) (by omega) (by decide) hl hj), if_neg hle,
        if_neg (queueSlot_ne (n := 2) (by omega) (by decide) hl hj)]
      rw [rep.live (capN + i) (by omega) j hj, List.getElem_drop]

/-- On a represented queue, the first records are its oldest. -/
theorem flatMap_range_eq {out : Record → Bytes} (q : List Record) (f : Nat → Bytes) (n : Nat)
    (hn : n ≤ q.length) (hf : ∀ i (hi : i < q.length), i < n → f i = out q[i]) :
    (List.range n).flatMap f = (q.take n).flatMap out := by
  induction n with
  | zero => simp only [List.range_zero, List.flatMap_nil, List.take_zero]
  | succ n ih =>
    have hlt : n < q.length := by omega
    rw [List.range_succ, List.flatMap_append, ih (by omega) (fun i hi hin => hf i hi (by omega)),
      List.take_succ_eq_append_getElem hlt, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hf n hlt (by omega)]

/-- **The output half of the FIFO.** On storage representing a queue, the call returns the oldest
`min(length, cap)` records. -/
theorem output_represented {k : SysPath} {m : SysMemory k} (o : SysOutput k m)
    {width : Nat} {words : Record → Nat → B256} {out : Record → Bytes} {benv : Benv} {target : Adr}
    {st : QueueState Record} (rep : Represents width words (storOf benv.state target) st)
    (hrec : ∀ i (hi : i < st.queue.length), i < k.capN →
      o.record (storOf benv.state target) st.head.toB256 i.toB256 = out st.queue[i]) :
    (SysPath.callPost k benv target).output = (st.queue.take k.capN).flatMap out := by
  rw [o.callPost_output]
  have h2 : (benv.state.getStor target).get 2 = st.head.toB256 := rep.head
  have h3 : (benv.state.getStor target).get 3 = st.tail.toB256 := rep.tail
  rw [h2, h3, drainCount_represented k.cap_word rep.coherent rep.tail_lt]
  have hcap : k.capN < 2 ^ 256 := by
    have := k.cap_word
    have := B256.toNat_lt k.shape.cap.word
    omega
  rw [B256.toNat_toB256_of_lt (by omega)]
  have htake : st.queue.take k.capN = st.queue.take (min st.queue.length k.capN) := by
    rw [← List.take_take]
    exact (List.take_of_length_le (List.length_take_le' _ _)).symm
  rw [htake]
  exact flatMap_range_eq st.queue _ _ (by omega) (fun i hi hin => hrec i hi (by omega))

/-- The inhibitor resets the excess. -/
theorem excessNext_inhibitor (target count : B256) : excessNext target B256.max count = 0 := by
  simp only [excessNext, ite_true]

/-- **The next excess is never the inhibitor**, for a nonzero target. The inhibitor case gives 0;
otherwise the result is 0 or `(count + excess) - target`, a word difference with a positive subtrahend
below the minuend. -/
theorem excessNext_ne_max {target : B256} (ht : target ≠ 0) (excess count : B256) :
    excessNext target excess count ≠ B256.max := by
  have hzero : (0 : B256) ≠ B256.max := by decide
  unfold excessNext
  split
  · exact hzero
  · split
    · rename_i hgt
      intro h
      have hlt := B256.lt_iff_toNat_lt_toNat.mp hgt
      have hnat := congrArg B256.toNat h
      rw [B256.toNat_sub, show B256.max.toNat = 2 ^ 256 - 1 by decide] at hnat
      change (2 ^ 256 + (count + excess).toNat - target.toNat) % 2 ^ 256 = _ at hnat
      have hpos : target.toNat ≠ 0 := fun h0 =>
        ht (B256.toNat_inj _ _ (h0.trans (by decide)))
      have hw := B256.toNat_lt (count + excess)
      have ht' := B256.toNat_lt target
      omega
    · exact hzero

/-- With no excess, the next excess is the count over the target, in naturals. -/
theorem excessNext_zero (target : B256) {count : Nat} (hc : count < 2 ^ 256) :
    (excessNext target (0 : Nat).toB256 count.toB256).toNat = count - target.toNat := by
  have hmax : B256.max ≠ (0 : Nat).toB256 := by decide
  have hz : count.toB256 + (0 : Nat).toB256 = count.toB256 := by
    rw [Nat.toB256_add_toB256, Nat.add_zero]
  have hcn := B256.toNat_toB256_of_lt hc
  simp only [excessNext, if_neg hmax, hz]
  by_cases hgt : count.toB256 > target
  · have hlt := B256.lt_iff_toNat_lt_toNat.mp hgt
    rw [hcn] at hlt
    rw [if_pos hgt, B256.toNat_sub, hcn]
    change (2 ^ 256 + count - target.toNat) % 2 ^ 256 = _
    have := B256.toNat_lt target
    omega
  · have hle : ¬ target.toNat < count := fun hlt =>
      hgt (B256.lt_iff_toNat_lt_toNat.mpr (by rw [hcn]; exact hlt))
    rw [if_neg hgt, show (0 : B256).toNat = 0 from rfl]
    omega

end Blanc.Lift.BuilderRequest
