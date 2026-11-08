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

/-- The floor root is pinned by one point not above the root whose successor is. -/
theorem floorRoot_eq {x : Fin 3 → Nat} {ann m : Nat} (h1 : ¬ aboveRoot x ann m)
    (h2 : aboveRoot x ann (m + 1)) (hm : m ≤ sum3 x) : floorRoot x ann = m :=
  Nat.le_antisymm (floorRoot_le_of_aboveRoot_succ h2) (Nat.le_findGreatest hm h1)

end Blanc.StableSwapNewton
