import Mathlib.Data.Nat.Sqrt

/-! Natural-number arithmetic for the source Babylonian square-root routine.
The result iterator is Lean's existing `Nat.sqrt.iter`; the source executes
one body before adopting that iterator's stopping test on its large branch.
-/

namespace Blanc.BabylonianSqrt

/-- One arithmetic body, before its division by two. -/
def bodySum (y x : Nat) : Nat := y / x + x

/-- The arithmetic value produced by one source body. -/
def next (y x : Nat) : Nat := bodySum y x / 2

/-- The source's initial candidate on its large branch. -/
def initialGuess (y : Nat) : Nat := y / 2 + 1

/-- Every executed source body has a nonzero divisor and a sum bounded by its input. -/
theorem bodySum_le {y x : Nat} (hx : 2 ≤ x) (hxy : x < y) : bodySum y x ≤ y := by
  have hd : 1 ≤ y - x := by omega
  have hm := Nat.mul_le_mul_left (y - x) hx
  have hp : y < (y - x + 1) * x := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hdiv := (Nat.div_lt_iff_lt_mul (by omega : 0 < x)).2 hp
  unfold bodySum
  omega

/-- The unchecked body addition is safe for every bounded input, including a stored word. -/
theorem bodySum_lt {y x limit : Nat} (hy : y < limit) (hx : 2 ≤ x) (hxy : x < y) :
    bodySum y x < limit :=
  lt_of_le_of_lt (bodySum_le hx hxy) hy

/-- The source's half-plus-one candidate starts above the mathematical root. -/
theorem sqrt_le_initialGuess (y : Nat) : Nat.sqrt y ≤ initialGuess y := by
  have hs := Nat.sqrt_le y
  unfold initialGuess
  by_cases h : 2 ≤ Nat.sqrt y
  · have hm := Nat.mul_le_mul_left (Nat.sqrt y) h
    omega
  · omega

/-- Large inputs enter the body immediately, with a positive candidate. -/
theorem initialGuess_bounds {y : Nat} (hy : 3 < y) :
    2 ≤ Nat.sqrt y ∧ Nat.sqrt y ≤ initialGuess y ∧ initialGuess y < y := by
  have hs : 2 ≤ Nat.sqrt y := Nat.le_sqrt.2 (by omega)
  exact ⟨hs, sqrt_le_initialGuess y, by unfold initialGuess; omega⟩

private theorem balanced_product_le_square (r x : Nat) : x * (2 * r - x) ≤ r * r := by
  by_cases hlarge : 2 * r ≤ x
  · rw [Nat.sub_eq_zero_of_le hlarge, Nat.mul_zero]
    exact Nat.zero_le _
  · rcases Nat.le_total x r with h | h
    · let d := r - x
      have hr : r = x + d := by omega
      have hb : 2 * r - x = x + d + d := by omega
      rw [hb, hr]
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm d x]
      omega
    · have hx : x = r + (x - r) := by omega
      have hr : r = (2 * r - x) + (x - r) := by omega
      have hb : 2 * r - x ≤ r := by omega
      have hm := Nat.mul_le_mul_left (x - r) hb
      calc
        x * (2 * r - x) = (r + (x - r)) * (2 * r - x) :=
          congrArg (fun t => t * (2 * r - x)) hx
        _ = r * (2 * r - x) + (x - r) * (2 * r - x) := Nat.add_mul _ _ _
        _ ≤ r * (2 * r - x) + (x - r) * r := Nat.add_le_add_left hm _
        _ = r * r := by
          rw [Nat.mul_comm (x - r) r, ← Nat.mul_add, ← hr]

/-- A Newton body keeps every lower square bound below its next candidate. -/
theorem root_le_next {r y x : Nat} (hr : r * r ≤ y) (hx : 0 < x) : r ≤ next y x := by
  have hp : (2 * r - x) * x ≤ y := by
    rw [Nat.mul_comm]
    exact le_trans (balanced_product_le_square r x) hr
  have hd := (Nat.le_div_iff_mul_le hx).2 hp
  unfold next bodySum
  omega

unseal Nat.sqrt.iter in
/-- Lean's existing iterator is correct from every candidate above the root. -/
theorem iter_eq_sqrt (y guess : Nat) (hguess : Nat.sqrt y ≤ guess) :
    Nat.sqrt.iter y guess = Nat.sqrt y := by
  unfold Nat.sqrt.iter
  by_cases hd : (guess + y / guess) / 2 < guess
  · have hg : 0 < guess := Nat.lt_of_le_of_lt (Nat.zero_le _) hd
    have hnext : Nat.sqrt y ≤ (guess + y / guess) / 2 := by
      simpa only [next, bodySum, Nat.add_comm] using root_le_next (Nat.sqrt_le y) hg
    simp only [dite_eq_left hd]
    exact iter_eq_sqrt y ((guess + y / guess) / 2) hnext
  · simp only [dite_eq_right hd]
    apply Nat.le_antisymm
    · apply Nat.le_sqrt.2
      apply Nat.mul_le_of_le_div guess guess y
      omega
    · exact hguess
termination_by guess

/-- Source branch structure, using the existing iterator after its mandatory first body. -/
def sourceResult (y : Nat) : Nat :=
  if 3 < y then Nat.sqrt.iter y (initialGuess y) else if y = 0 then 0 else 1

/-- The full-domain source arithmetic returns the exact floor square root. -/
theorem sourceResult_eq_sqrt (y : Nat) : sourceResult y = Nat.sqrt y := by
  unfold sourceResult
  split
  · exact iter_eq_sqrt y (initialGuess y) (sqrt_le_initialGuess y)
  · rename_i hy
    split
    · rename_i hz
      subst y
      exact Nat.sqrt_zero.symm
    · rename_i hz
      apply Nat.eq_sqrt.2
      constructor <;> omega

/-- Strict descent occurs exactly when a positive guess exceeds the root. -/
theorem next_lt_iff {y x : Nat} (hx : 0 < x) : next y x < x ↔ Nat.sqrt y < x := by
  constructor
  · exact fun h => lt_of_le_of_lt (root_le_next (Nat.sqrt_le y) hx) h
  · intro h
    by_contra hn
    have hd : x ≤ y / x := by unfold next bodySum at hn; omega
    have hs : x ≤ Nat.sqrt y := Nat.le_sqrt.2 (Nat.mul_le_of_le_div x x y hd)
    omega

/-- Number of strict-descending bodies after the source's mandatory first body. -/
def iterCount (y guess : Nat) : Nat :=
  if _h : next y guess < guess then 1 + iterCount y (next y guess) else 0
termination_by guess

/-- The exact source body count includes its mandatory first large-input body. -/
def sourceCount (y : Nat) : Nat :=
  if 3 < y then 1 + iterCount y (initialGuess y) else 0

/-- The iterator's true header contributes one body before recurring. -/
theorem iterCount_of_descend {y guess : Nat} (h : next y guess < guess) :
    iterCount y guess = 1 + iterCount y (next y guess) := by
  rw [iterCount]
  simp only [dite_eq_left h]

/-- A false iterator header executes no further body. -/
theorem iterCount_of_stop {y guess : Nat} (h : ¬next y guess < guess) :
    iterCount y guess = 0 := by
  rw [iterCount]
  simp only [dite_eq_right h]

/-- The zero count is exactly the iterator's stopping guard. -/
theorem iterCount_eq_zero_iff (y guess : Nat) :
    iterCount y guess = 0 ↔ ¬next y guess < guess := by
  by_cases h : next y guess < guess
  · rw [iterCount_of_descend h]
    omega
  · rw [iterCount_of_stop h]
    omega

/-- With the root invariant, a zero count identifies the loop's returned candidate. -/
theorem iterCount_eq_zero_iff_root {y guess : Nat} (hx : 0 < guess)
    (hguess : Nat.sqrt y ≤ guess) : iterCount y guess = 0 ↔ guess = Nat.sqrt y := by
  rw [iterCount_eq_zero_iff, next_lt_iff hx]
  omega

/-- The positive count is exactly the iterator's descending guard. -/
theorem iterCount_pos_iff (y guess : Nat) :
    0 < iterCount y guess ↔ next y guess < guess := by
  have h := iterCount_eq_zero_iff y guess
  omega

/-- The large source branch accounts for the inlined first header/body. -/
theorem sourceCount_of_large {y : Nat} (h : 3 < y) :
    sourceCount y = 1 + iterCount y (initialGuess y) := by
  simp only [sourceCount, ite_eq_left h]

/-- Bounds used by every large-source body, for an arbitrary bounded input. -/
theorem body_bounds {y x limit : Nat} (hy : 3 < y) (hlimit : y < limit)
    (hroot : Nat.sqrt y ≤ x) (hupper : x ≤ initialGuess y) :
    initialGuess y < limit ∧ 0 < x ∧ bodySum y x < limit ∧
      Nat.sqrt y ≤ next y x ∧ next y x < initialGuess y := by
  obtain ⟨hs, _, hi⟩ := initialGuess_bounds hy
  have hx : 2 ≤ x := le_trans hs hroot
  have hxy : x < y := lt_of_le_of_lt hupper hi
  have hsum := bodySum_le hx hxy
  refine ⟨lt_trans hi hlimit, by omega, bodySum_lt hlimit hx hxy,
    root_le_next (Nat.sqrt_le y) (by omega), ?_⟩
  unfold next initialGuess
  have hd := Nat.div_le_div_right hsum (c := 2)
  unfold bodySum at hd
  omega

end Blanc.BabylonianSqrt
