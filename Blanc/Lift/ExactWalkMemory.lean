import Blanc.Lift.ExactWalkOps
import Blanc.Lift.MemMap

/-!
# Parameterized free-pointer memory for exact lifted walks

The recorded pointer value is independent of allocated memory size. The carrier
uses the existing abstract word map; it introduces no alternate memory image.
-/

namespace Blanc.Lift
open Jaune

structure PtrMem (p : B256) (n : Nat) (M : Mem) : Prop where
  size : M.size = n
  n32 : n % 32 = 0
  wf : Mem.Wf M
  map : MemMatches 0 [(64, .const p)] M

theorem PtrMem.ge {p : B256} {n : Nat} {M : Mem} (h : PtrMem p n M) : 96 ≤ n := by
  have hs := (h.map 64 (.const p) (List.mem_cons_self)).1
  rw [h.size] at hs
  exact hs

theorem PtrMem.word {p : B256} {n : Nat} {M : Mem} (h : PtrMem p n M) :
    memWord M 64 = p :=
  (h.map 64 (.const p) (List.mem_cons_self)).2

theorem PtrMem.init (p : B256) : PtrMem p 96 (Mem.empty.write 64 p.toBytes) := by
  refine ⟨?_, by decide, Mem.wf_empty.write _ _, ?_⟩
  · rw [Mem.size_write_word_at]
    rfl
  · intro o v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    cases hv
    exact ⟨(Mem.memWord_write_word Mem.empty 64 p).2,
      (Mem.memWord_write_word Mem.empty 64 p).1⟩

theorem PtrMem.write {p : B256} {n : Nat} {M : Mem} (h : PtrMem p n M)
    (i : Nat) (v : B256) (miss : i + 32 ≤ 64 ∨ 96 ≤ i) :
    PtrMem p (memExtSize n i 32) (M.write i v.toBytes) := by
  refine ⟨Mem.size_write_of_size h.size h.n32 (B256.length_toBytes v),
    memExtSize_mod_32 h.n32, h.wf.write _ _, ?_⟩
  intro o av hav
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hav
  cases hav
  have hag := Mem.write_agree M i v.toBytes
  rw [B256.length_toBytes] at hag
  refine ⟨le_trans (by rw [h.size]; exact h.ge) hag.1, ?_⟩
  change memWord (M.write i v.toBytes) 64 = p
  rw [memWord_congr (μ := M) (fun j hj => hag.2 (64 + j)
    (by rw [h.size]; have := h.ge; omega) (by omega))]
  exact h.word

theorem PtrMem.set {p q : B256} {n : Nat} {M : Mem} (h : PtrMem p n M) :
    PtrMem q n (M.write 64 q.toBytes) := by
  refine ⟨?_, h.n32, h.wf.write _ _, ?_⟩
  · rw [Mem.size_write_of_size h.size h.n32 (B256.length_toBytes q)]
    exact memExtSize_of_le h.n32 h.ge
  · intro o v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    cases hv
    exact ⟨(Mem.memWord_write_word M 64 q).2, (Mem.memWord_write_word M 64 q).1⟩

theorem PtrMem.read_self {p : B256} {n : Nat} {M : Mem} (h : PtrMem p n M)
    {i sz : Nat} (fit : i + sz ≤ n) : (M.read i sz).2 = M :=
  Mem.read_snd_eq_self (by rw [h.size]; exact memExtSize_of_le h.n32 fit)

end Blanc.Lift
