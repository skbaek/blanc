/-!
# Positions in a `flatMap`

Element `i` of `l.flatMap f` is element `k` of `f l[j]` for exactly one pair `(j, k)` with
`k < (f l[j]).length`, and its position is `((l.take j).flatMap f).length + k`.

* `List.exists_flatMap_position`: every position below the length has such a pair.
* `List.flatMap_position_inj`: the pair is unique.

Element identity at the pair follows from `List.getElem?_append_right`/`_left` on the split
`l = l.take j ++ l[j] :: l.drop (j + 1)`.
-/

namespace Blanc

/-- Every position of `l.flatMap f` is the position of element `k` of block `j`. -/
theorem List.exists_flatMap_position {α β : Type _} (f : α → List β) :
    ∀ (l : List α) {i : Nat}, i < (l.flatMap f).length →
      ∃ j k, ∃ hj : j < l.length, k < (f l[j]).length ∧
        ((l.take j).flatMap f).length + k = i
  | [], i, h => by
    rw [List.flatMap_nil, List.length_nil] at h
    exact absurd h (Nat.not_lt_zero i)
  | a :: t, i, h => by
    rw [List.flatMap_cons, List.length_append] at h
    by_cases hi : i < (f a).length
    · refine ⟨0, i, Nat.zero_lt_succ _, hi, ?_⟩
      rw [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add]
    · obtain ⟨j, k, hj, hk, hpos⟩ :=
        List.exists_flatMap_position f t (i := i - (f a).length) (by omega)
      refine ⟨j + 1, k, Nat.succ_lt_succ hj, hk, ?_⟩
      rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
      omega

/-- The block-and-offset pair of a position of `l.flatMap f` is unique. -/
theorem List.flatMap_position_inj {α β : Type _} (f : α → List β) :
    ∀ (l : List α) {j k j' k' : Nat} (hj : j < l.length) (hj' : j' < l.length),
      k < (f l[j]).length → k' < (f l[j']).length →
      ((l.take j).flatMap f).length + k = ((l.take j').flatMap f).length + k' →
      j = j' ∧ k = k'
  | [], _, _, _, _, hj, _, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | _ :: _, 0, _, 0, _, _, _, _, _, h => by
    rw [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add, Nat.zero_add] at h
    exact ⟨rfl, h⟩
  | a :: t, 0, k, j' + 1, k', _, _, hk, _, h => by
    rw [List.take_zero, List.take_succ_cons, List.flatMap_nil, List.flatMap_cons,
      List.length_nil, List.length_append] at h
    have hk : k < (f a).length := hk
    omega
  | a :: t, j + 1, k, 0, k', _, _, _, hk', h => by
    rw [List.take_zero, List.take_succ_cons, List.flatMap_nil, List.flatMap_cons,
      List.length_nil, List.length_append] at h
    have hk' : k' < (f a).length := hk'
    omega
  | a :: t, j + 1, k, j' + 1, k', hj, hj', hk, hk', h => by
    rw [List.take_succ_cons, List.take_succ_cons, List.flatMap_cons, List.flatMap_cons,
      List.length_append, List.length_append] at h
    obtain ⟨h1, h2⟩ := List.flatMap_position_inj f t (Nat.lt_of_succ_lt_succ hj)
      (Nat.lt_of_succ_lt_succ hj') hk hk' (by omega)
    exact ⟨congrArg (· + 1) h1, h2⟩

end Blanc
