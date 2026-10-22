import Blanc.Lift.StableSwapNewton.Defs

/-! The exact root of the three-coin StableSwap invariant: `aboveRoot` is upward
closed in `D`, `floorRoot` is the last point not above the root, and the floor
root is monotone in each balance and in `ann`. -/

namespace Blanc.StableSwapNewton

/-- Being above the root is upward closed. -/
theorem aboveRoot_mono {x : Fin 3 → Nat} {ann D D' : Nat} (h : aboveRoot x ann D)
    (hD : D ≤ D') : aboveRoot x ann D' := by
  unfold aboveRoot at *
  have h4 : D ^ 4 ≤ D' ^ 4 := Nat.pow_le_pow_left hD 4
  have h1 : 27 * prod3 x * (ann - 1) * D ≤ 27 * prod3 x * (ann - 1) * D' :=
    Nat.mul_le_mul_left _ hD
  omega

/-- Zero is never above the root. -/
theorem not_aboveRoot_zero (x : Fin 3 → Nat) (ann : Nat) : ¬ aboveRoot x ann 0 := by
  unfold aboveRoot
  rw [show (0 : Nat) ^ 4 = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  exact Nat.not_lt_zero _

/-- The floor root is not above the root. -/
theorem floorRoot_spec (x : Fin 3 → Nat) (ann : Nat) : ¬ aboveRoot x ann (floorRoot x ann) :=
  Nat.findGreatest_spec (P := fun D => ¬ aboveRoot x ann D) (Nat.zero_le _)
    (not_aboveRoot_zero x ann)

/-- The floor root is at most `S`. -/
theorem floorRoot_le_sum3 (x : Fin 3 → Nat) (ann : Nat) : floorRoot x ann ≤ sum3 x :=
  Nat.findGreatest_le _

/-- Every point above the root lies above the floor root. -/
theorem floorRoot_lt_of_aboveRoot {x : Fin 3 → Nat} {ann D : Nat} (h : aboveRoot x ann D) :
    floorRoot x ann < D := by
  rcases Nat.lt_or_ge (floorRoot x ann) D with hlt | hge
  · exact hlt
  · exact absurd (aboveRoot_mono h hge) (floorRoot_spec x ann)

/-- `aboveRoot x ann (v + 1)` says `v ≥ ⌊D*⌋`. -/
theorem floorRoot_le_of_aboveRoot_succ {x : Fin 3 → Nat} {ann v : Nat}
    (h : aboveRoot x ann (v + 1)) : floorRoot x ann ≤ v :=
  Nat.lt_succ_iff.mp (floorRoot_lt_of_aboveRoot h)

/-- The floor root is monotone in the balances, each one separately or all at once. -/
theorem floorRoot_mono {x x' : Fin 3 → Nat} (h : ∀ i, x i ≤ x' i) (ann : Nat) :
    floorRoot x ann ≤ floorRoot x' ann := by
  have hS : sum3 x ≤ sum3 x' := by
    unfold sum3
    have := h 0
    have := h 1
    have := h 2
    omega
  have hP : prod3 x ≤ prod3 x' := by
    unfold prod3
    exact Nat.mul_le_mul (Nat.mul_le_mul (h 0) (h 1)) (h 2)
  have hmS := floorRoot_le_sum3 x ann
  apply Nat.le_findGreatest (le_trans hmS hS)
  have h0 := floorRoot_spec x ann
  generalize floorRoot x ann = m at h0 hmS ⊢
  unfold aboveRoot at *
  generalize hK : 27 * prod3 x = K at h0
  generalize hK' : 27 * prod3 x' = K'
  have hKK : K ≤ K' := by omega
  have ham : (ann - 1) * m ≤ ann * sum3 x := Nat.mul_le_mul (Nat.sub_le _ _) hmS
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le ham
  have hS' : ann * sum3 x ≤ ann * sum3 x' := Nat.mul_le_mul_left _ hS
  have e1 : K * ann * sum3 x = K * ((ann - 1) * m) + K * t := by
    rw [Nat.mul_assoc, ht, Nat.mul_add]
  have e2 : K * (ann - 1) * m = K * ((ann - 1) * m) := Nat.mul_assoc _ _ _
  have e3 : K' * (ann - 1) * m = K' * ((ann - 1) * m) := Nat.mul_assoc _ _ _
  have e4 : K' * ann * sum3 x' = K' * (ann * sum3 x') := Nat.mul_assoc _ _ _
  have hKt : K * t ≤ K' * t := Nat.mul_le_mul_right _ hKK
  have hK'S : K' * (ann * sum3 x) ≤ K' * (ann * sum3 x') := Nat.mul_le_mul_left _ hS'
  have e5 : K' * (ann * sum3 x) = K' * ((ann - 1) * m) + K' * t := by
    rw [ht, Nat.mul_add]
  omega

/-- The floor root is monotone in `ann`. -/
theorem floorRoot_mono_ann (x : Fin 3 → Nat) {ann ann' : Nat} (h : ann ≤ ann') :
    floorRoot x ann ≤ floorRoot x ann' := by
  have hmS := floorRoot_le_sum3 x ann
  apply Nat.le_findGreatest hmS
  have h0 := floorRoot_spec x ann
  generalize floorRoot x ann = m at h0 hmS ⊢
  unfold aboveRoot at *
  generalize 27 * prod3 x = K at h0 ⊢
  generalize sum3 x = S at h0 hmS ⊢
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hsub : ann + d - 1 ≤ (ann - 1) + d := by omega
  have h1 : K * (ann + d - 1) * m ≤ K * (ann - 1) * m + K * d * m := by
    rw [← Nat.add_mul, ← Nat.mul_add]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsub)
  have h2 : K * d * m ≤ K * d * S := Nat.mul_le_mul_left _ hmS
  have e : K * (ann + d) * S = K * ann * S + K * d * S := by
    rw [Nat.mul_add, Nat.add_mul]
  omega

/-- The floor root is pinned by one point not above the root whose successor is. -/
theorem floorRoot_eq {x : Fin 3 → Nat} {ann m : Nat} (h1 : ¬ aboveRoot x ann m)
    (h2 : aboveRoot x ann (m + 1)) (hm : m ≤ sum3 x) : floorRoot x ann = m :=
  Nat.le_antisymm (floorRoot_le_of_aboveRoot_succ h2) (Nat.le_findGreatest hm h1)

end Blanc.StableSwapNewton
