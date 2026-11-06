import Blanc.Lift.WalkCost

/-!
# Forward walks past a moving free-memory pointer

solc allocates its revert strings eagerly (`SafeMath.sub(a, b, "...")`), so the free-memory pointer
moves within a frame. These are the steps `xs` leaves to its caller there: the pointer's own store
and a store that grows the image. Each hands the continuation the new image's invariant, which `xfp`
then reads from the context.
-/

namespace Blanc.Lift.AccumulatedWalk

open Jaune Blanc Blanc.Lift

theorem FpM.moved {fp new : B256} {n : Nat} {M : Mem} (h : FpM fp n M) :
    FpM new n (M.write 64 new.toBytes) := by
  obtain ⟨bs, hr, -⟩ := h.reads
  refine ⟨Mem.size_write_word_of_le h.size (by have := h.ge; omega), h.n32, h.ge, h.wf.write _ _,
    ⟨Bytes.writeAt bs 64 new.toBytes, hr.write h.wf 64 _, ?_⟩⟩
  exact sliceD_word_same _ _ _

theorem FpM.grown {fp : B256} {n : Nat} {M : Mem} (h : FpM fp n M) (v : B256) (hn : 96 ≤ n) :
    FpM fp (n + 32) (M.write n v.toBytes) := by
  obtain ⟨bs, hr, hf⟩ := h.reads
  have h32 := h.n32
  have hc : ceil32 (n + 32) = n + 32 := by
    unfold ceil32
    split <;> omega
  refine ⟨by rw [Mem.size_write_word_at, h.size, if_neg (by omega), hc], by have := h.n32; omega, by omega, h.wf.write _ _,
    ⟨Bytes.writeAt bs n v.toBytes, hr.write h.wf n _, ?_⟩⟩
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
  exact hf

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome} {n : Nat} {fp : B256}

/-- `MSTORE` of a new free-memory pointer. -/
theorem rx_mstoreMove {i new : B256} (hM : FpM fp n M) (hi : i.toNat = 64)
    (k : FpM new n (M.write 64 new.toBytes) →
      SFunc.RunExact fs sevm (St b S (M.write 64 new.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: new :: S) M (G + 3)) (.next (.reg .mstore) f) o := by
  refine rx_mstore (c := 3) ?_ (by rw [hi]) (by rw [hi] at *; exact k hM.moved)
  rw [hi, hM.extCost (by have := hM.ge; omega)]; rfl

/-- `MSTORE` of a word just above the image. -/
theorem rx_mstoreGrow {i v : B256} {c : Nat} (hM : FpM fp n M) (hi : i.toNat = n) (hn : 96 ≤ n)
    (hc : gVerylow + (calculateMemoryGasCost (memExtSize n n 32) - calculateMemoryGasCost n) = c)
    (k : FpM fp (n + 32) (M.write n v.toBytes) →
      SFunc.RunExact fs sevm (St b S (M.write n v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + c)) (.next (.reg .mstore) f) o := by
  refine rx_mstore (c := c) ?_ (by rw [hi]) (k (hM.grown v hn))
  rw [hi, St.extCost_eq hM.size]
  exact hc

/-- `LOG3` of a word just written at the pointer. -/
theorem rx_log3At {M0 : Mem} {v i sz t1 t2 t3 : B256} {i0 n0 : Nat} (hstatic : sevm.isStatic = false)
    (hM1 : M = M0.write i0 v.toBytes) (hM0 : FpM fp n0 M0) (hM : FpM fp n M) (hi : i.toNat = i0)
    (hin : i0 + 32 ≤ n) (hsz : sz.toNat = 32)
    (k : SFunc.RunExact fs sevm
      (St (b.addLog ⟨sevm.currentTarget, [t1, t2, t3], v.toBytes⟩) S M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: t1 :: t2 :: t3 :: S) M (G + 1756))
      (.next (.reg (.log 3)) f) o := by
  subst hM1
  refine rx_log3 (c := 1756) hstatic ?_ ?_ ?_ k
  · rw [hi, hsz, hM.extCost hin]; decide
  · rw [hi, hsz]; exact hM0.readback i0 v
  · rw [hi, hsz]; exact hM.read_self hin

/-- `RETURN` of a word just written at the pointer. -/
theorem rx_returnAt {M1 : Mem} {v i sz : B256} {i0 n0 : Nat} (hM1 : M = M1.write i0 v.toBytes)
    (hM0 : FpM fp n0 M1) (hM : FpM fp n M) (hi : i.toNat = i0) (hin : i0 + 32 ≤ n) (hsz : sz.toNat = 32) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) M G) (.last .return_)
      (.halted (((St b S M G).memRead i.toNat sz.toNat).2.withOutput v.toBytes)) := by
  subst hM1
  refine rx_return ?_ ?_
  · rw [hi, hsz]; exact hM.extCost hin
  · rw [hi, hsz]; exact hM0.readback i0 v

end Steps

end Blanc.Lift.AccumulatedWalk
