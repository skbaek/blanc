import Blanc.MemoryLayout

/-!
# Reading a window of a `MemoryStage`'s image

`window_at` reads any window inside one write that no later write touches, the general form of
`MemoryStage.read_written`. `avoids_tac` closes its side condition over literal offsets.
-/

namespace Blanc

open Jaune

/-- A window fully inside one write that no later write touches reads that write. -/
theorem window_at {stage : MemoryStage} (n : Nat) {off d w m : Nat} {p : Bytes} (image : Bytes)
    (hn : stage[n]? = some (off, p)) (avoid : MemoryStage.avoids (stage.drop (n + 1)) w m = true)
    (hw : w = off + d) (hend : d + m ≤ p.length) :
    (stage.applyImage image).sliceD w m 0 = p.sliceD d m 0 := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hn
  have split : stage = stage.take n ++ (off, p) :: stage.drop (n + 1) := by
    conv_lhs => rw [← List.take_append_drop n stage, List.drop_eq_getElem_cons hlt, heq]
  generalize stage.drop (n + 1) = later at split avoid
  generalize stage.take n = earlier at split
  subst split
  rw [MemoryStage.applyImage_append, MemoryStage.applyImage_cons,
    MemoryStage.applyImage_sliceD_of_avoids _ _ _ _ avoid]
  dsimp only
  rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by omega)]
  rw [show w - off = d by omega]

/-- Close a `MemoryStage.avoids` goal over literal offsets. -/
macro "avoids_tac" : tactic => `(tactic| (
  simp only [List.drop_succ_cons, List.drop_zero, List.drop_nil, MemoryStage.avoids, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] <;>
  simp only [B256.length_toBytes, List.length_cons, List.length_nil] <;> omega))

/-- A whole list as its own slice. -/
theorem sliceD_self (p : Bytes) {m : Nat} (h : p.length = m) : p.sliceD 0 m 0 = p := by
  subst h
  unfold List.sliceD
  rw [List.drop_zero, List.takeD_eq_take _ (Nat.le_refl _), List.take_length]

/-- A slice of a slice, inside it. -/
theorem sliceD_sliceD (xs : Bytes) {a n b m : Nat} (h : b + m ≤ n) :
    (xs.sliceD a n 0).sliceD b m 0 = xs.sliceD (a + b) m 0 := by
  rw [List.sliceD_eq_map (xs.sliceD a n 0) 0 m b, List.sliceD_eq_map xs 0 m (a + b)]
  apply List.map_congr_left
  intro j hj
  have hj' : j < m := List.mem_range.mp hj
  rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by omega), Nat.add_assoc]

end Blanc
