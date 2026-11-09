/-!
# Fixed-width pieces of a list, and a list's one marked element

* `List.chunksOf w l` cuts `l` into consecutive pieces of `w` elements, keeping a short last piece
  (never padding or dropping it), so comparing the pieces with whole records detects a ragged tail.
  `List.chunksOf_flatMap`: when every block of `xs.flatMap f` has exactly `w` elements, the pieces
  are the blocks, `xs.map f`.
* `List.split_of_filter_length_one`: a list with exactly one element satisfying `p` is
  `pre ++ x :: post` with `p x` and no other element satisfying `p`; `find? p` returns `x` and the
  longest prefix avoiding `p` is `pre`. `List.filter_length_zero` is the empty case.
-/

namespace Blanc

/-- `l` cut into consecutive pieces of `w` elements; a short last piece is kept. -/
def List.chunksOf {α : Type _} (w : Nat) (l : List α) : List (List α) :=
  (List.range ((l.length + w - 1) / w)).map fun i => (l.drop (w * i)).take w

private theorem length_flatMap_const {α β : Type _} (w : Nat) (f : α → List β) :
    ∀ xs : List α, (∀ x ∈ xs, (f x).length = w) → (xs.flatMap f).length = w * xs.length
  | [], _ => by simp
  | x :: xs, h => by
    have rest := length_flatMap_const w f xs fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self, rest, List.length_cons, Nat.mul_succ]
    omega

/-- **Re-chunking fixed-width blocks gives the blocks back.** -/
theorem List.chunksOf_flatMap {α β : Type _} {w : Nat} (hw : 0 < w) (f : α → List β) :
    ∀ xs : List α, (∀ x ∈ xs, (f x).length = w) → List.chunksOf w (xs.flatMap f) = xs.map f
  | [], _ => by
    simp only [List.chunksOf, List.flatMap_nil, List.length_nil, Nat.zero_add, List.map_nil]
    rw [Nat.div_eq_of_lt (by omega), List.range_zero, List.map_nil]
  | x :: xs, h => by
    have hx : (f x).length = w := h x List.mem_cons_self
    have hxs : ∀ y ∈ xs, (f y).length = w := fun y hy => h y (List.mem_cons_of_mem _ hy)
    have tail := List.chunksOf_flatMap hw f xs hxs
    have len := length_flatMap_const w f xs hxs
    have count : ((x :: xs).flatMap f).length + w - 1 = w * (xs.length + 1) + (w - 1) := by
      rw [List.flatMap_cons, List.length_append, hx, len]
      rw [Nat.mul_succ]
      omega
    have count' : (xs.flatMap f).length + w - 1 = w * xs.length + (w - 1) := by
      rw [len]
      omega
    have div : (w * (xs.length + 1) + (w - 1)) / w = xs.length + 1 := by
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have div' : (w * xs.length + (w - 1)) / w = xs.length := by
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    rw [List.chunksOf, count, div, List.range_succ_eq_map, List.map_cons, List.map_map, List.map_cons]
    rw [List.chunksOf, count', div'] at tail
    rw [← tail]
    congr 1
    · rw [Nat.mul_zero, List.drop_zero, List.flatMap_cons, List.take_append_of_le_length (by rw [hx]; exact Nat.le_refl w),
        List.take_of_length_le (by rw [hx]; exact Nat.le_refl w)]
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      rw [List.flatMap_cons, Nat.mul_succ, Nat.add_comm (w * i) w, ← hx, List.drop_append,
        Nat.add_sub_cancel_left, List.drop_eq_nil_of_le (by omega), List.nil_append]

/-- A list with no element satisfying `p` keeps nothing under `filter p`, and conversely. -/
theorem List.filter_length_zero {α : Type _} (p : α → Bool) {l : List α} (h : (l.filter p).length = 0) :
    ∀ y ∈ l, p y = false := by
  intro y hy
  cases hp : p y
  · rfl
  · have : y ∈ l.filter p := List.mem_filter.mpr ⟨hy, hp⟩
    rw [List.length_eq_zero_iff.mp h] at this
    exact absurd this List.not_mem_nil

/-- **The one marked element.** A list with exactly one element satisfying `p` splits around it;
`find? p` returns it, and the longest prefix avoiding `p` is the part before it. -/
theorem List.split_of_filter_length_one {α : Type _} (p : α → Bool) :
    ∀ {l : List α}, (l.filter p).length = 1 →
      ∃ pre x post, l = pre ++ x :: post ∧ p x = true ∧ (∀ y ∈ pre ++ post, p y = false) ∧
        l.find? p = some x ∧ l.takeWhile (fun y => !p y) = pre
  | [], h => by simp only [List.filter_nil, List.length_nil] at h; omega
  | a :: t, h => by
    cases ha : p a
    · rw [List.filter_cons_of_neg (by rw [ha]; decide)] at h
      obtain ⟨pre, x, post, rfl, hx, others, found, taken⟩ := List.split_of_filter_length_one p h
      refine ⟨a :: pre, x, post, rfl, hx, ?_, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ha
        · exact others y hy
      · rw [List.find?_cons_of_neg (by rw [ha]; decide)]
        exact found
      · rw [List.takeWhile_cons_of_pos (by rw [ha]; rfl), taken]
    · rw [List.filter_cons_of_pos ha, List.length_cons] at h
      have rest := List.filter_length_zero p (l := t) (by omega)
      refine ⟨[], a, t, rfl, ha, ?_, ?_, ?_⟩
      · intro y hy
        exact rest y (by simpa only [List.nil_append] using hy)
      · exact List.find?_cons_of_pos ha
      · rw [List.takeWhile_cons_of_neg (by rw [ha]; decide)]

/-- The element at a block-and-offset position of `l.flatMap f` is that block's element at that offset. -/
theorem List.getElem?_flatMap_position {α β : Type _} (f : α → List β) (l : List α) {j k : Nat}
    (hj : j < l.length) (hk : k < (f l[j]).length) :
    (l.flatMap f)[((l.take j).flatMap f).length + k]? = (f l[j])[k]? := by
  have e : l.flatMap f = (l.take j).flatMap f ++ (f l[j] ++ (l.drop (j + 1)).flatMap f) := by
    conv => lhs; rw [← List.take_append_drop j l, List.drop_eq_getElem_cons hj]
    rw [List.flatMap_append, List.flatMap_cons]
  rw [e, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

end Blanc
