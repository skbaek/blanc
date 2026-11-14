import Init.Data.List.Pairwise

/-! Original-list positions of selected rows with distinct occurrence keys. -/

namespace Blanc.List

/-- Equal selected keys identify one original list position. Unselected rows may
repeat, and payloads need not be distinct. This supplies no chronology or order policy. -/
theorem index_eq_of_nodup_filter_map
    {α κ : Type _} {selected : α → Bool} {key : α → κ} {xs : List α}
    (fresh : ((xs.filter selected).map key).Nodup)
    {i j : Nat} {x y : α}
    (at_i : xs[i]? = some x) (at_j : xs[j]? = some y)
    (selected_i : selected x = true) (selected_j : selected y = true)
    (same : key x = key y) : i = j := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map, List.pairwise_filter] at fresh
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp at_i
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp at_j
  by_cases equal : i = j
  · exact equal
  · rcases Nat.lt_or_gt_of_ne equal with hlt | hgt
    · exact False.elim ((List.pairwise_iff_getElem.mp fresh i j hi hj hlt
        selected_i selected_j) same)
    · exact False.elim ((List.pairwise_iff_getElem.mp fresh j i hj hi hgt
        selected_j selected_i) same.symm)

end Blanc.List
