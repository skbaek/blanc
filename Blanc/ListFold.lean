import Init.Data.List.Lemmas

namespace Blanc

/-- A tail-recursive fold's defining equations determine its result after one final input. -/
theorem fold_snoc_of_equations {α σ : Type _} (run : σ → List α → σ) (step : σ → α → σ)
    (base : ∀ s, run s [] = s) (next : ∀ s x xs, run s (x :: xs) = run (step s x) xs)
    (s : σ) (xs : List α) (x : α) : run s (xs ++ [x]) = step (run s xs) x := by
  induction xs generalizing s with
  | nil => simp only [List.nil_append, next, base]
  | cons y ys ih => rw [List.cons_append, next, ih, next]

end Blanc
