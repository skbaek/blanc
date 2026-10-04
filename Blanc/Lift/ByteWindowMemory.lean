import Blanc.Lift.ExactWalkMemory
/-! Covered byte windows preserve the independent free-memory pointer. -/

namespace Blanc.Lift
open Jaune

/-- An arbitrary in-bounds byte write outside the pointer word keeps allocation and pointer. -/
theorem PtrMem.write_bytes_of_le {p : B256} {n : Nat} {M : Mem}
    (h : PtrMem p n M) (i : Nat) (bs : Bytes) (fit : i + bs.length ≤ n)
    (miss : i + bs.length ≤ 64 ∨ 96 ≤ i) :
    PtrMem p n (M.write i bs) := by
  refine ⟨(Mem.size_write_of_le (by rw [h.size]; exact fit)).trans h.size,
    h.n32, h.wf.write _ _, ?_⟩
  intro o av hav
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hav
  cases hav
  have hag := Mem.write_agree M i bs
  refine ⟨le_trans (by rw [h.size]; exact h.ge) hag.1, ?_⟩
  change memWord (M.write i bs) 64 = p
  rw [memWord_congr (μ := M) (fun j hj => hag.2 (64 + j)
    (by rw [h.size]; have := h.ge; omega) (by omega))]
  exact h.word

/-- Four high bytes from the source and twenty-eight low bytes from the destination. -/
theorem mergeFour_bytes (x y : B256) :
    let mask := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256)
    ((x &&& ~~~mask) ||| (y &&& mask)).toBytes = x.toBytes.take 4 ++ y.toBytes.drop 4 := by
  rcases x with ⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩
  rcases y with ⟨⟨y3, y2⟩, ⟨y1, y0⟩⟩
  change (B256.toBytes (⟨⟨(x3 &&& 0xffffffff00000000) ||| (y3 &&& 0xffffffff),
    (x2 &&& 0) ||| (y2 &&& (-1 : UInt64))⟩,
    ⟨(x1 &&& 0) ||| (y1 &&& (-1 : UInt64)),
      (x0 &&& 0) ||| (y0 &&& (-1 : UInt64))⟩⟩ : B256)) = _
  simp only [UInt64.and_zero, UInt64.and_neg_one, UInt64.zero_or]
  have high : (((x3 &&& 0xffffffff00000000) ||| (y3 &&& 0xffffffff)) >>> 32).toUInt32 =
      (x3 >>> 32).toUInt32 := by
    rw [UInt64.shiftRight_or, UInt64.shiftRight_and, UInt64.shiftRight_and,
      UInt64.toUInt32_or, UInt64.toUInt32_and, UInt64.toUInt32_and]
    change ((x3 >>> 32).toUInt32 &&& (-1 : UInt32)) ||| ((y3 >>> 32).toUInt32 &&& 0) = _
    simp only [UInt32.and_neg_one, UInt32.and_zero, UInt32.or_zero]
  have low : ((x3 &&& 0xffffffff00000000) ||| (y3 &&& 0xffffffff)).toUInt32 = y3.toUInt32 := by
    rw [UInt64.toUInt32_or, UInt64.toUInt32_and, UInt64.toUInt32_and]
    change (x3.toUInt32 &&& 0) ||| (y3.toUInt32 &&& (-1 : UInt32)) = _
    simp only [UInt32.and_zero, UInt32.and_neg_one, UInt32.zero_or]
  simp only [B256.toBytes, B128.toBytes, UInt64.toBytes, high, low,
    UInt32.toBytes, UInt16.toBytes, List.cons_append, List.nil_append, List.take, List.drop]

end Blanc.Lift
