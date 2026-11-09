import Batteries.Data.List.Basic

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
  | [], _ => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.mul_zero]
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

/-- A list with element `x` at index `j` is its first `j` elements, then `x`, then the rest. -/
theorem List.eq_take_cons_drop {α : Type _} {l : List α} {j : Nat} {x : α} (h : l[j]? = some x) :
    l = l.take j ++ x :: l.drop (j + 1) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  conv => lhs; rw [← List.take_append_drop j l, List.drop_eq_getElem_cons hj]

/-- Two lists related pointwise split alike around a block of the second. -/
theorem List.forall₂_split {α β : Type _} {R : α → β → Prop} :
    ∀ {pre : List β} {b : β} {post : List β} {xs : List α}, List.Forall₂ R xs (pre ++ b :: post) →
      ∃ xpre x xpost, xs = xpre ++ x :: xpost ∧ List.Forall₂ R xpre pre ∧ R x b ∧ List.Forall₂ R xpost post
  | [], _, _, _, .cons hb rest => ⟨[], _, _, rfl, .nil, hb, rest⟩
  | _ :: _, _, _, _, .cons hb rest => by
    obtain ⟨xpre, x, xpost, rfl, h1, h2, h3⟩ := List.forall₂_split rest
    exact ⟨_ :: xpre, x, xpost, rfl, .cons hb h1, h2, h3⟩

/-- **Draining a queue at a fixed rate, by position.** A family of queues indexed along `xs`, where element `i`
(when it satisfies `am`) drains the first `cap` entries of its queue `Q x` (`A2`), its queue is the tail past `E i`
of a log `T i x` (`A1`), the logs grow along `xs` (`B2`) and `E` counts what was drained (`B3`). Then entry `q` of the
queue at index `j` is drained at index `j + q / cap` as its entry `q % cap`, at log position `E j + q`. -/
theorem List.drain_position {α β : Type _} (cap : Nat) (hcap : 0 < cap) (xs : List α) (am : α → Prop)
    (be Q : α → List β) (T : Nat → α → List β) (E : Nat → Nat)
    (A1 : ∀ (i : Nat) x, xs[i]? = some x → am x → ∀ k : Nat, (T i x)[E i + k]? = (Q x)[k]?)
    (A2 : ∀ (i : Nat) x, xs[i]? = some x → am x → be x = (Q x).take cap)
    (B2 : ∀ (i : Nat) x y, xs[i]? = some x → xs[i + 1]? = some y → T i x <+: T (i + 1) y)
    (B3 : ∀ (i : Nat) x, xs[i]? = some x → E (i + 1) = E i + (be x).length) :
    ∀ (d j q : Nat) (x : α) (r : β), q / cap = d → xs[j]? = some x → j + d < xs.length →
      (∀ i ≤ d, ∀ y, xs[j + i]? = some y → am y) → (T j x)[E j + q]? = some r →
      ∃ y, xs[j + d]? = some y ∧ (be y)[q % cap]? = some r ∧ E j + q = E (j + d) + q % cap := by
  intro d
  induction d with
  | zero =>
    intro j q x r hq hx _ ham hr
    have lt : q < cap := (Nat.div_eq_zero_iff_lt hcap).mp hq
    have amx := ham 0 (Nat.le_refl _) x hx
    refine ⟨x, hx, ?_, by rw [Nat.mod_eq_of_lt lt, Nat.add_zero]⟩
    rw [Nat.mod_eq_of_lt lt, A2 j x hx amx, List.getElem?_take_of_lt lt, ← A1 j x hx amx]
    exact hr
  | succ d ih =>
    intro j q x r hq hx hlen ham hr
    have amx := ham 0 (Nat.zero_le _) x hx
    have le : cap ≤ q := by
      rcases Nat.lt_or_ge q cap with h | h
      · rw [Nat.div_eq_of_lt h] at hq
        omega
      · exact h
    have hQ : (Q x)[q]? = some r := by rw [← A1 j x hx amx]; exact hr
    have qlt : q < (Q x).length := (List.getElem?_eq_some_iff.mp hQ).1
    have beLen : (be x).length = cap := by
      rw [A2 j x hx amx, List.length_take]
      omega
    obtain ⟨y, hy⟩ : ∃ y, xs[j + 1]? = some y :=
      ⟨xs[j + 1], List.getElem?_eq_getElem (by omega)⟩
    have hE := B3 j x hx
    rw [beLen] at hE
    have pre := B2 j x y hx hy
    obtain ⟨u, hu⟩ := pre
    have hr' : (T (j + 1) y)[E (j + 1) + (q - cap)]? = some r := by
      rw [← hu, hE, show E j + cap + (q - cap) = E j + q by omega,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).1]
      exact hr
    have hq' : (q - cap) / cap = d := by
      rw [show q - cap = q - cap * 1 by rw [Nat.mul_one], Nat.sub_mul_div, hq, Nat.add_sub_cancel]
    obtain ⟨z, hz, hbe, hidx⟩ := ih (j + 1) (q - cap) y r hq' hy (by omega)
      (fun i hi w hw => ham (i + 1) (by omega) w (by rw [show j + (i + 1) = j + 1 + i by omega]; exact hw)) hr'
    have mod : (q - cap) % cap = q % cap := (Nat.mod_eq_sub_mod le).symm
    rw [mod] at hbe hidx
    rw [show j + 1 + d = j + (d + 1) by omega] at hz hidx
    refine ⟨z, hz, hbe, ?_⟩
    omega

end Blanc
