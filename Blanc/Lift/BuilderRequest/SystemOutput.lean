import Blanc.Lift.RequestSystem.Output
import Blanc.Lift.BuilderRequest.SystemPath
import Blanc.Lift.BuilderRequest.QueueLayout
import Blanc.Lift.RequestQueue.Drain

/-!
# What a builder system call leaves on a represented queue

`represents_sysState` is the storage half of the FIFO: on storage representing a queue, the post storage
represents the drained queue, with the oldest `min(length, cap)` records gone. These are representation
statements. Nothing here says which storage is reachable, or that a stored record came from a real
submission. The drain itself is the shared `RequestQueue.Drain` for any excess arm; this module is the builder
arm's instance (`excessNext`), with the shared lemmas restated under their builder names.
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
    drainCount cap head.toB256 tail.toB256 = (min len capN).toB256 :=
  RequestQueue.drainCount_represented hcap coherent tail_lt

/-- A live record's slot is none of the four metadata slots. -/
theorem queueSlot_ne {width index offset n : Nat} (hn : n < 4) {x : B256} (hx : x.toNat = n)
    (hlt : queueBase width index + width ≤ 2 ^ 256) (hj : offset < width) :
    x ≠ queueSlot width index offset :=
  RequestQueue.queueSlot_ne hn hx hlt hj

/-- **The storage half of the FIFO.** On storage representing a queue, a call's post storage represents
the queue with its oldest `min(length, cap)` records gone. -/
theorem represents_sysState {width : Nat} {words : Record → Nat → B256} (p : SysShape) {capN : Nat}
    (hcap : p.cap.word.toNat = capN) (hnext : p.next = excessNext p.target.word) {σ : State} {a : Adr}
    {st : QueueState Record}
    (rep : Represents width words (storOf σ a) st) :
    Represents width words (storOf (sysState p σ a) a) (drainedState capN p.target.word st) := by
  have h := RequestQueue.represents_drain p hcap rep
  rw [hnext] at h
  exact h

/-- On a represented queue, the first records are its oldest. -/
theorem flatMap_range_eq {out : Record → Bytes} (q : List Record) (f : Nat → Bytes) (n : Nat)
    (hn : n ≤ q.length) (hf : ∀ i (hi : i < q.length), i < n → f i = out q[i]) :
    (List.range n).flatMap f = (q.take n).flatMap out :=
  RequestQueue.flatMap_range_eq q f n hn hf

/-- **The output half of the FIFO.** On storage representing a queue, the call returns the oldest
`min(length, cap)` records. -/
theorem output_represented {k : SysPath} {m : SysMemory k} (o : SysOutput k m)
    {width : Nat} {words : Record → Nat → B256} {out : Record → Bytes} {benv : Benv} {target : Adr}
    {st : QueueState Record} (rep : Represents width words (storOf benv.state target) st)
    (hrec : ∀ i (hi : i < st.queue.length), i < k.capN →
      o.record (storOf benv.state target) st.head.toB256 i.toB256 = out st.queue[i]) :
    (SysPath.callPost k benv target).output = (st.queue.take k.capN).flatMap out :=
  RequestQueue.output_represented o rep hrec

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
