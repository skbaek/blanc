import Blanc.Lift.StableSwapNewton.D

/-! The `y` loop of `get_y` and `get_y_D`: the checked loop returns the plain
loop's value whenever it does not revert, and from any start at or above the floor
root `rootQ` the plain loop returns exactly `rootQ`, halving its distance to the
root at every body, provided the quadratic is not tangent-degenerate at the root
(`rootGap`). -/

namespace Blanc.StableSwapNewton

/-! ## Bridges -/

theorem cOfChk_some {u v D ann r : Nat} (h : cOfChk u v D ann = some r) : r = cOf u v D ann := by
  unfold cOfChk at h
  obtain ⟨a0, ha0, h⟩ := bind_some h
  obtain ⟨b0, hb0, h⟩ := bind_some h
  obtain ⟨c0, hc0, h⟩ := bind_some h
  obtain ⟨a1, ha1, h⟩ := bind_some h
  obtain ⟨b1, hb1, h⟩ := bind_some h
  obtain ⟨c1, hc1, h⟩ := bind_some h
  obtain ⟨a2, ha2, h⟩ := bind_some h
  obtain ⟨b2, hb2, h⟩ := bind_some h
  rw [(chkDiv_some h).1, chkMul_some ha2, chkMul_some hb2, (chkDiv_some hc1).1, chkMul_some ha1,
    chkMul_some hb1, (chkDiv_some hc0).1, chkMul_some ha0, chkMul_some hb0]
  rfl

theorem bOfChk_some {u v D ann r : Nat} (h : bOfChk u v D ann = some r) : r = bOf u v D ann := by
  unfold bOfChk at h
  obtain ⟨s0, hs0, h⟩ := bind_some h
  obtain ⟨s, hs, h⟩ := bind_some h
  obtain ⟨d, hd, h⟩ := bind_some h
  rw [chkAdd_some h, (chkDiv_some hd).1, chkAdd_some hs, chkAdd_some hs0]
  unfold bOf
  omega

theorem bodyYChk_some {c b D y r : Nat} (h : bodyYChk c b D y = some r) : r = bodyY c b D y := by
  unfold bodyYChk at h
  obtain ⟨m, hm, h⟩ := bind_some h
  obtain ⟨num, hnum, h⟩ := bind_some h
  obtain ⟨t, ht, h⟩ := bind_some h
  obtain ⟨s, hs, h⟩ := bind_some h
  obtain ⟨den, hden, h⟩ := bind_some h
  rw [(chkDiv_some h).1, chkAdd_some hnum, chkMul_some hm, (chkSub_some hden).1, chkAdd_some hs,
    chkMul_some ht]
  rfl

theorem loopY_succ (c b D tol fuel y : Nat) :
    loopY c b D tol (fuel + 1) y =
      if closeEnough tol (bodyY c b D y) y then bodyY c b D y
      else loopY c b D tol fuel (bodyY c b D y) := rfl

theorem loopYChk_some {c b D tol : Nat} :
    ∀ {fuel y r : Nat}, loopYChk c b D tol fuel y = some r → r = loopY c b D tol fuel y
  | 0, y, r, h => by
    unfold loopYChk at h
    exact (Option.some.inj h).symm
  | fuel + 1, y, r, h => by
    unfold loopYChk at h
    obtain ⟨y', hy', h⟩ := bind_some h
    have e := bodyYChk_some hy'
    subst e
    rw [loopY_succ]
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      exact (Option.some.inj h).symm
    · rename_i hc
      simp only [hc, ↓reduceIte]
      exact loopYChk_some h

/-- Bridge: a non-reverting checked `get_y` returns the plain `getY`. -/
theorem getYChk_some {amp : Nat} {i j : Fin 3} {x : Nat} {xp : Fin 3 → Nat} {r : Nat}
    (h : getYChk amp i j x xp = some r) : r = getY amp i j x xp := by
  unfold getYChk at h
  split at h
  · cases h
  · obtain ⟨D, hD, h⟩ := bind_some h
    obtain ⟨ann, hann, h⟩ := bind_some h
    obtain ⟨c, hc, h⟩ := bind_some h
    obtain ⟨b, hb, h⟩ := bind_some h
    rw [loopYChk_some h, bOfChk_some hb, cOfChk_some hc, chkMul_some hann, getDChk_some hD]
    rfl

/-- Bridge: a non-reverting checked `get_y_D` returns the plain `getYD`. -/
theorem getYDChk_some {amp : Nat} {i : Fin 3} {xp : Fin 3 → Nat} {D r : Nat}
    (h : getYDChk amp i xp D = some r) : r = getYD amp i xp D := by
  unfold getYDChk at h
  obtain ⟨ann, hann, h⟩ := bind_some h
  obtain ⟨c, hc, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  rw [loopYChk_some h, bOfChk_some hb, cOfChk_some hc, chkMul_some hann]
  rfl

/-! ## The floor root of the quadratic -/

theorem rootQ_spec (c b D : Nat) :
    rootQ c b D * rootQ c b D + b * rootQ c b D ≤ c + D * rootQ c b D :=
  Nat.findGreatest_spec (P := fun y => y * y + b * y ≤ c + D * y) (Nat.zero_le _)
    (by omega)

/-- Every point beyond the floor root is strictly outside. -/
theorem lt_of_rootQ_lt {c b D y : Nat} (hy : rootQ c b D < y) : c + D * y < y * y + b * y := by
  rcases Nat.lt_or_ge (c + D) y with hb | hb
  · have h1 : (c + D + 1) * y ≤ y * y := Nat.mul_le_mul_right _ hb
    have h2 : c * 1 ≤ c * y := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · have h := Nat.findGreatest_is_greatest (P := fun y => y * y + b * y ≤ c + D * y) hy hb
    omega

/-- The non-degeneracy the exactness needs: the quadratic exceeds `c` by at least 2 one
step past the floor root (it always exceeds it by at least 1). -/
def rootGap (c b D : Nat) : Prop :=
  c + D * (rootQ c b D + 1) + 2 ≤ (rootQ c b D + 1) * (rootQ c b D + 1) + b * (rootQ c b D + 1)

/-! ## One body, in the integers -/

/-- Newton from any point with a positive denominator lands at or above the floor root. -/
theorem body_ge_root_int {c b D r y q : Int} (hR1 : r * r + b * r ≤ c + D * r)
    (hden : 0 < 2 * y + b - D) (hq : y * y + c < (q + 1) * (2 * y + b - D)) : r ≤ q := by
  by_contra hc
  have h1 : (q + 1) * (2 * y + b - D) ≤ r * (2 * y + b - D) :=
    mul_le_mul_of_nonneg_right (by omega) hden.le
  nlinarith [sq_nonneg (y - r)]

/-- Above the floor root, one body at least halves the distance to it. -/
theorem body_halves_int {c b D r y q : Int} (hR2 : c + D * (r + 1) < (r + 1) * (r + 1) + b * (r + 1))
    (hrb : D + 1 ≤ 2 * r + b) (hy : r + 1 ≤ y) (hq : q * (2 * y + b - D) ≤ y * y + c) :
    2 * q ≤ y + r + 1 := by
  by_contra hc
  have h1 : (y + r + 2) * (2 * y + b - D) ≤ (2 * q) * (2 * y + b - D) :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  nlinarith [mul_pos (by omega : (0 : Int) < y - r) (by omega : (0 : Int) < b - D + 2 * r + 4)]

/-- Two or more above the floor root, one body moves down by at least 2. -/
theorem body_drops_int {c b D r y q : Int}
    (hH : c + D * (r + 1) + 2 ≤ (r + 1) * (r + 1) + b * (r + 1))
    (hrb : D + 1 ≤ 2 * r + b) (hy : r + 2 ≤ y) (hq : q * (2 * y + b - D) ≤ y * y + c) :
    q + 2 ≤ y := by
  by_contra hc
  have h1 : (y - 1) * (2 * y + b - D) ≤ q * (2 * y + b - D) :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  nlinarith [mul_nonneg (by omega : (0 : Int) ≤ y - r - 2) (by omega : (0 : Int) ≤ y + r + b - D)]

/-- At or one above the floor root, one body lands at most on it. -/
theorem body_le_root_int {c b D r y q : Int}
    (hH : c + D * (r + 1) + 2 ≤ (r + 1) * (r + 1) + b * (r + 1))
    (hrb : D + 1 ≤ 2 * r + b) (hy0 : r ≤ y) (hy1 : y ≤ r + 1)
    (hq : q * (2 * y + b - D) ≤ y * y + c) : q ≤ r := by
  by_contra hc
  have h1 : (r + 1) * (2 * y + b - D) ≤ q * (2 * y + b - D) :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  rcases (by omega : y = r ∨ y = r + 1) with rfl | rfl <;> nlinarith

/-! ## One body, in the naturals -/

theorem closeEnough_iff {tol a b : Nat} : closeEnough tol a b ↔ a ≤ b + tol ∧ b ≤ a + tol := by
  unfold closeEnough
  split <;> omega

/-- The source denominator is positive from the floor root upwards. -/
theorem rootQ_den {c b D : Nat} (hgap : rootGap c b D) : D + 1 ≤ 2 * rootQ c b D + b := by
  have h := rootQ_spec c b D
  unfold rootGap at hgap
  generalize rootQ c b D = r at h hgap ⊢
  nlinarith

/-- One body from `y ≥ ⌊y*⌋`: it lands on or above the floor root; from at most one
above it lands exactly on it; from two or more above it moves down by at least 2 and
at least halves the distance. -/
theorem bodyY_step {c b D y : Nat} (hgap : rootGap c b D) (hy : rootQ c b D ≤ y) :
    rootQ c b D ≤ bodyY c b D y ∧
    (y ≤ rootQ c b D + 1 → bodyY c b D y = rootQ c b D) ∧
    (rootQ c b D + 2 ≤ y →
      bodyY c b D y + 2 ≤ y ∧ 2 * bodyY c b D y ≤ y + rootQ c b D + 1) := by
  have hrb := rootQ_den hgap
  have hR1 := rootQ_spec c b D
  have hR2 := lt_of_rootQ_lt (Nat.lt_succ_self (rootQ c b D))
  have hden : 0 < 2 * y + b - D := by omega
  have hq1 : bodyY c b D y * (2 * y + b - D) ≤ y * y + c := Nat.div_mul_le_self _ _
  have hq2 : y * y + c < (bodyY c b D y + 1) * (2 * y + b - D) := by
    have h := Nat.lt_div_mul_add (a := y * y + c) hden
    unfold bodyY
    linarith
  unfold rootGap at hgap
  generalize bodyY c b D y = q at hq1 hq2 ⊢
  generalize rootQ c b D = r at hrb hR1 hR2 hgap hy ⊢
  have hcast : ((2 * y + b - D : Nat) : Int) = 2 * (y : Int) + b - D := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have zq1 : (q : Int) * (2 * y + b - D) ≤ y * y + c := by
    rw [← hcast]
    exact_mod_cast hq1
  have zq2 : (y : Int) * y + c < (q + 1) * (2 * y + b - D) := by
    rw [← hcast]
    exact_mod_cast hq2
  have zR1 : (r : Int) * r + b * r ≤ c + D * r := by exact_mod_cast hR1
  have zR2 : (c : Int) + D * (r + 1) < (r + 1) * (r + 1) + b * (r + 1) := by exact_mod_cast hR2
  have zH : (c : Int) + D * (r + 1) + 2 ≤ (r + 1) * (r + 1) + b * (r + 1) := by
    exact_mod_cast hgap
  have zrb : (D : Int) + 1 ≤ 2 * r + b := by exact_mod_cast hrb
  have zden : (0 : Int) < 2 * y + b - D := by omega
  have hlo : r ≤ q := by exact_mod_cast body_ge_root_int zR1 zden zq2
  refine ⟨hlo, fun h1 => ?_, fun h2 => ?_⟩
  · have := body_le_root_int zH zrb (by exact_mod_cast hy) (by exact_mod_cast h1) zq1
    omega
  · have h3 := body_drops_int zH zrb (by exact_mod_cast h2) zq1
    have h4 := body_halves_int zR2 zrb (by omega) zq1
    omega

/-! ## The loop -/

/-- From at most one above the floor root, one body returns it and the stopping test
at tolerance 1 fires. -/
theorem loopY_near {c b D : Nat} (hgap : rootGap c b D) {fuel y : Nat} (hy0 : rootQ c b D ≤ y)
    (hy1 : y ≤ rootQ c b D + 1) : loopY c b D 1 (fuel + 1) y = rootQ c b D := by
  have h := (bodyY_step hgap hy0).2.1 hy1
  have hc : closeEnough 1 (bodyY c b D y) y := closeEnough_iff.2 (by omega)
  rw [loopY_succ]
  simp only [hc, ↓reduceIte]
  exact h

/-- **Iteration bound.** From any `y ≥ ⌊y*⌋` within `2^k` of it, the tolerance-1 loop
returns exactly `⌊y*⌋` within `k + 1` bodies. -/
theorem loopY_eq_rootQ_of_le {c b D : Nat} (hgap : rootGap c b D) :
    ∀ (k : Nat) {fuel y : Nat}, rootQ c b D ≤ y → y - rootQ c b D ≤ 2 ^ k → k + 1 ≤ fuel →
      loopY c b D 1 fuel y = rootQ c b D
  | 0, fuel, y, hy0, hyk, hf => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    exact loopY_near hgap hy0 (by rw [Nat.pow_zero] at hyk; omega)
  | k + 1, fuel, y, hy0, hyk, hf => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    rcases Nat.lt_or_ge y (rootQ c b D + 2) with hy1 | hy1
    · exact loopY_near hgap hy0 (by omega)
    · obtain ⟨hlo, -, hstep⟩ := bodyY_step hgap hy0
      obtain ⟨hdrop, hhalf⟩ := hstep hy1
      have hc : ¬ closeEnough 1 (bodyY c b D y) y := fun h => by
        have := closeEnough_iff.1 h
        omega
      rw [loopY_succ]
      simp only [hc, ↓reduceIte]
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := Nat.pow_succ'
      exact loopY_eq_rootQ_of_le hgap k hlo (by omega) (by omega)

/-- A start below the floor root with a positive denominator: the first body lands at
or above the root, and from there the bound above applies. -/
theorem loopY_eq_rootQ_of_lt {c b D : Nat} (hgap : rootGap c b D) (k : Nat) {fuel y : Nat}
    (hy : y < rootQ c b D) (hden : D + 1 ≤ 2 * y + b)
    (hk : bodyY c b D y - rootQ c b D ≤ 2 ^ k) (hf : k + 2 ≤ fuel) :
    loopY c b D 1 fuel y = rootQ c b D := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  have hq1 : bodyY c b D y * (2 * y + b - D) ≤ y * y + c := Nat.div_mul_le_self _ _
  have hq2 : y * y + c < (bodyY c b D y + 1) * (2 * y + b - D) := by
    have h := Nat.lt_div_mul_add (a := y * y + c) (by omega : 0 < 2 * y + b - D)
    unfold bodyY
    linarith
  have hR1 := rootQ_spec c b D
  generalize hq : bodyY c b D y = q at hq1 hq2 hk
  have hcast : ((2 * y + b - D : Nat) : Int) = 2 * (y : Int) + b - D := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have zq2 : (y : Int) * y + c < (q + 1) * (2 * y + b - D) := by
    rw [← hcast]
    exact_mod_cast hq2
  have zR1 : (rootQ c b D : Int) * rootQ c b D + b * rootQ c b D ≤ c + D * rootQ c b D := by
    exact_mod_cast hR1
  have hlo : rootQ c b D ≤ q := by
    have := body_ge_root_int zR1 (by omega) zq2
    exact_mod_cast this
  rw [loopY_succ, hq]
  by_cases hc : closeEnough 1 q y
  · simp only [hc, ↓reduceIte]
    have := closeEnough_iff.1 hc
    omega
  · simp only [hc, ↓reduceIte]
    exact loopY_eq_rootQ_of_le hgap k hlo hk (by omega)

/-- **`get_y`'s loop is exact.** Started at `D` with `⌊y*⌋ ≤ D ≤ 2^254` and the
non-degeneracy `rootGap`, the source loop (tolerance 1, 255 bodies) returns exactly the
floor root of `y^2 + (b - D)·y = c`, after at most `log2 D + 2` bodies. -/
theorem loopY_eq_rootQ {c b D : Nat} (hgap : rootGap c b D) (hstart : rootQ c b D ≤ D)
    (hD : D ≤ 2 ^ 254) : loopY c b D 1 255 D = rootQ c b D :=
  loopY_eq_rootQ_of_le hgap 254 hstart (by omega) (by omega)

/-- `get_y_D` returns the floor root of its floored-coefficient quadratic. -/
theorem getYD_eq_rootQ {amp : Nat} {i : Fin 3} {xp : Fin 3 → Nat} {D : Nat}
    (hgap : rootGap (cOf (xp (others i).1) (xp (others i).2) D (amp * 3))
      (bOf (xp (others i).1) (xp (others i).2) D (amp * 3)) D)
    (hstart : rootQ (cOf (xp (others i).1) (xp (others i).2) D (amp * 3))
      (bOf (xp (others i).1) (xp (others i).2) D (amp * 3)) D ≤ D)
    (hD : D ≤ 2 ^ 254) :
    getYD amp i xp D = rootQ (cOf (xp (others i).1) (xp (others i).2) D (amp * 3))
      (bOf (xp (others i).1) (xp (others i).2) D (amp * 3)) D :=
  loopY_eq_rootQ hgap hstart hD

/-- `get_y` returns the floor root of its floored-coefficient quadratic, with
`D = get_D(xp_, amp)` and the balances other than `j`, `x` substituted at `i`. -/
theorem getY_eq_rootQ {amp : Nat} {i j : Fin 3} {x : Nat} {xp : Fin 3 → Nat}
    (hgap : rootGap (cOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (bOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (getD xp amp 1))
    (hstart : rootQ (cOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (bOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (getD xp amp 1) ≤ getD xp amp 1)
    (hD : getD xp amp 1 ≤ 2 ^ 254) :
    getY amp i j x xp = rootQ (cOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (bOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (getD xp amp 1) :=
  loopY_eq_rootQ hgap hstart hD

end Blanc.StableSwapNewton
