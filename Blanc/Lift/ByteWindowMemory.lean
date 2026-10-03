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

end Blanc.Lift
