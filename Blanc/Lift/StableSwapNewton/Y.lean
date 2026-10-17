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

/-! ## Without the non-degeneracy: the floor root or one above it -/

/-- The loop's answer: `⌊y*⌋`, or `⌊y*⌋ + 1` only when `rootGap` fails, that is when the
quadratic exceeds `c` by exactly 1 one step past the floor root. -/
def rootOrSucc (c b D v : Nat) : Prop :=
  v = rootQ c b D ∨ (v = rootQ c b D + 1 ∧ ¬ rootGap c b D)

/-- The floor root is never below `D - b`. -/
theorem le_rootQ_add (c b D : Nat) : D ≤ rootQ c b D + b := by
  have h := lt_of_rootQ_lt (by omega : rootQ c b D < rootQ c b D + 1)
  generalize rootQ c b D = r at h ⊢
  by_contra hc
  have h1 : (r + b + 1) * (r + 1) ≤ D * (r + 1) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem body_lt_self_int {c b D y q : Int} (hpos : c + D * y < y * y + b * y)
    (hq : q * (2 * y + b - D) ≤ y * y + c) (hden : 0 < 2 * y + b - D) : q + 1 ≤ y := by
  by_contra hc
  have h1 : y * (2 * y + b - D) ≤ q * (2 * y + b - D) :=
    mul_le_mul_of_nonneg_right (by omega) hden.le
  nlinarith

theorem body_root_succ_int {c b D r q : Int}
    (hR2 : c + D * (r + 1) < (r + 1) * (r + 1) + b * (r + 1))
    (hq : q * (2 * r + b - D) ≤ r * r + c) (hden : 0 < 2 * r + b - D) : q ≤ r + 1 := by
  by_contra hc
  have h1 : (r + 2) * (2 * r + b - D) ≤ q * (2 * r + b - D) :=
    mul_le_mul_of_nonneg_right (by omega) hden.le
  nlinarith

theorem body_drops3_int {c b D r y q : Int}
    (hR2 : c + D * (r + 1) < (r + 1) * (r + 1) + b * (r + 1))
    (hr : 0 ≤ r) (hrb : D ≤ r + b) (hy : r + 3 ≤ y) (hq : q * (2 * y + b - D) ≤ y * y + c) :
    q + 2 ≤ y := by
  by_contra hc
  have h1 : (y - 1) * (2 * y + b - D) ≤ q * (2 * y + b - D) :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  nlinarith [mul_pos (by omega : (0 : Int) < y - r - 2) (by omega : (0 : Int) < y + r + b - D)]

theorem body_halves'_int {c b D r y q : Int}
    (hR2 : c + D * (r + 1) < (r + 1) * (r + 1) + b * (r + 1))
    (hr : 0 ≤ r) (hrb : D ≤ r + b) (hy : r + 1 ≤ y) (hq : q * (2 * y + b - D) ≤ y * y + c) :
    2 * q ≤ y + r + 1 := by
  by_contra hc
  have h1 : (y + r + 2) * (2 * y + b - D) ≤ (2 * q) * (2 * y + b - D) :=
    mul_le_mul_of_nonneg_right (by omega) (by omega)
  nlinarith [mul_pos (by omega : (0 : Int) < y - r) (by omega : (0 : Int) < b - D + 2 * r + 4)]

/-- One body's floor facts, cast to the integers. -/
theorem bodyY_int {c b D y : Nat} (hle : D ≤ 2 * y + b) :
    (bodyY c b D y : Int) * (2 * y + b - D) ≤ (y : Int) * y + c ∧
    (D < 2 * y + b → (y : Int) * y + c < (bodyY c b D y + 1) * (2 * y + b - D)) := by
  have hcast : ((2 * y + b - D : Nat) : Int) = 2 * (y : Int) + b - D := by
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hq1 : bodyY c b D y * (2 * y + b - D) ≤ y * y + c := Nat.div_mul_le_self _ _
  refine ⟨?_, fun hlt => ?_⟩
  · rw [← hcast]
    exact_mod_cast hq1
  · have h := Nat.lt_div_mul_add (a := y * y + c) (by omega : 0 < 2 * y + b - D)
    have hq2 : y * y + c < (bodyY c b D y + 1) * (2 * y + b - D) := by
      unfold bodyY
      linarith
    rw [← hcast]
    exact_mod_cast hq2

/-- One body from `y ≥ ⌊y*⌋`, with no non-degeneracy assumed. -/
theorem bodyY_step' {c b D y : Nat} (hy : rootQ c b D ≤ y) :
    rootQ c b D ≤ bodyY c b D y ∧
    (y = rootQ c b D → bodyY c b D y ≤ rootQ c b D + 1 ∧
      (rootGap c b D → bodyY c b D y = rootQ c b D)) ∧
    (y = rootQ c b D + 1 → bodyY c b D y = rootQ c b D) ∧
    (y = rootQ c b D + 2 → bodyY c b D y ≤ rootQ c b D + 1 ∧
      (rootGap c b D → bodyY c b D y = rootQ c b D)) ∧
    (rootQ c b D + 3 ≤ y →
      bodyY c b D y + 2 ≤ y ∧ 2 * bodyY c b D y ≤ y + rootQ c b D + 1) := by
  have hrb := le_rootQ_add c b D
  have hR1 := rootQ_spec c b D
  have hR2 := lt_of_rootQ_lt (Nat.lt_succ_self (rootQ c b D))
  have hR3 := lt_of_rootQ_lt (by omega : rootQ c b D < rootQ c b D + 2)
  have hgapden : rootGap c b D → D + 1 ≤ 2 * rootQ c b D + b := rootQ_den
  have hle : D ≤ 2 * y + b := by omega
  obtain ⟨zq1, zq2⟩ := bodyY_int (c := c) hle
  have hq0 : 2 * y + b ≤ D → bodyY c b D y = 0 := fun h => by
    unfold bodyY
    rw [show 2 * y + b - D = 0 by omega, Nat.div_zero]
  unfold rootGap at hgapden ⊢
  generalize bodyY c b D y = q at zq1 zq2 hq0 ⊢
  generalize rootQ c b D = r at hrb hR1 hR2 hR3 hgapden hy ⊢
  have zR1 : (r : Int) * r + b * r ≤ c + D * r := by exact_mod_cast hR1
  have zR2 : (c : Int) + D * (r + 1) < (r + 1) * (r + 1) + b * (r + 1) := by exact_mod_cast hR2
  have zR3 : (c : Int) + D * (r + 2) < (r + 2) * (r + 2) + b * (r + 2) := by exact_mod_cast hR3
  have zrb : (D : Int) ≤ r + b := by exact_mod_cast hrb
  have zy : (r : Int) ≤ y := by exact_mod_cast hy
  -- the lower bound, including the zero-denominator corner (then `r = 0`)
  have hlo : r ≤ q := by
    rcases Nat.lt_or_ge D (2 * y + b) with hlt | hge
    · have := body_ge_root_int zR1 (by omega) (zq2 hlt)
      exact_mod_cast this
    · have := hq0 hge
      omega
  have zr : (0 : Int) ≤ r := Int.natCast_nonneg r
  refine ⟨hlo, fun h0 => ?_, fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · subst h0
    rcases Nat.lt_or_ge D (2 * y + b) with hlt | hge
    · have hup := body_root_succ_int zR2 zq1 (by omega)
      refine ⟨by exact_mod_cast hup, fun hg => ?_⟩
      have hg' : (c : Int) + D * (y + 1) + 2 ≤ (y + 1) * (y + 1) + b * (y + 1) := by
        exact_mod_cast hg
      have := body_le_root_int hg' (by exact_mod_cast hgapden hg) le_rfl (by omega) zq1
      omega
    · have := hq0 hge
      omega
  · have zy : (y : Int) = r + 1 := by exact_mod_cast h1
    have := body_lt_self_int (y := (y : Int)) (by rw [zy]; linarith) zq1 (by omega)
    omega
  · have zy : (y : Int) = r + 2 := by exact_mod_cast h2
    have := body_lt_self_int (y := (y : Int)) (by rw [zy]; linarith) zq1 (by omega)
    refine ⟨by omega, fun hg => ?_⟩
    have hg' : (c : Int) + D * (r + 1) + 2 ≤ (r + 1) * (r + 1) + b * (r + 1) := by
      exact_mod_cast hg
    have := body_drops_int hg' (by exact_mod_cast hgapden hg) (by omega) zq1
    omega
  · have hd := body_drops3_int zR2 zr zrb (by exact_mod_cast h3) zq1
    have hh := body_halves'_int zR2 zr zrb (by omega) zq1
    omega

theorem loopY_at_root {c b D fuel : Nat} :
    rootOrSucc c b D (loopY c b D 1 (fuel + 1) (rootQ c b D)) := by
  obtain ⟨hlo, hB, -, -, -⟩ := bodyY_step' (c := c) (b := b) (D := D) (le_refl (rootQ c b D))
  obtain ⟨hup, hgap⟩ := hB rfl
  have hc : closeEnough 1 (bodyY c b D (rootQ c b D)) (rootQ c b D) :=
    closeEnough_iff.2 (by omega)
  rw [loopY_succ]
  simp only [hc, ↓reduceIte]
  rcases Nat.lt_or_ge (bodyY c b D (rootQ c b D)) (rootQ c b D + 1) with h | h
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, fun hg => by have := hgap hg; omega⟩

theorem loopY_at_root_succ {c b D fuel : Nat} :
    loopY c b D 1 (fuel + 1) (rootQ c b D + 1) = rootQ c b D := by
  obtain ⟨-, -, hC, -, -⟩ := bodyY_step' (c := c) (b := b) (D := D)
    (by omega : rootQ c b D ≤ rootQ c b D + 1)
  have h := hC rfl
  have hc : closeEnough 1 (bodyY c b D (rootQ c b D + 1)) (rootQ c b D + 1) :=
    closeEnough_iff.2 (by omega)
  rw [loopY_succ]
  simp only [hc, ↓reduceIte]
  exact h

theorem loopY_at_root_two {c b D fuel : Nat} :
    rootOrSucc c b D (loopY c b D 1 (fuel + 2) (rootQ c b D + 2)) := by
  obtain ⟨hlo, -, -, hD2, -⟩ := bodyY_step' (c := c) (b := b) (D := D)
    (by omega : rootQ c b D ≤ rootQ c b D + 2)
  obtain ⟨hup, hgap⟩ := hD2 rfl
  rw [loopY_succ]
  rcases Nat.lt_or_ge (bodyY c b D (rootQ c b D + 2)) (rootQ c b D + 1) with h | h
  · have hc : ¬ closeEnough 1 (bodyY c b D (rootQ c b D + 2)) (rootQ c b D + 2) := fun hc => by
      have := closeEnough_iff.1 hc
      omega
    simp only [hc, ↓reduceIte]
    rw [show bodyY c b D (rootQ c b D + 2) = rootQ c b D by omega]
    exact loopY_at_root
  · have hc : closeEnough 1 (bodyY c b D (rootQ c b D + 2)) (rootQ c b D + 2) :=
      closeEnough_iff.2 (by omega)
    simp only [hc, ↓reduceIte]
    exact Or.inr ⟨by omega, fun hg => by have := hgap hg; omega⟩

/-- **The `y` loop without non-degeneracy.** From any `y ≥ ⌊y*⌋` within `2^k` of it,
the tolerance-1 loop returns `⌊y*⌋`, or `⌊y*⌋ + 1` only if `rootGap` fails, within
`k + 1` bodies. -/
theorem loopY_rootOrSucc_of_le {c b D : Nat} :
    ∀ (k : Nat) {fuel y : Nat}, rootQ c b D ≤ y → y - rootQ c b D ≤ 2 ^ k → k + 1 ≤ fuel →
      rootOrSucc c b D (loopY c b D 1 fuel y)
  | 0, fuel, y, hy0, hyk, hf => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    rw [Nat.pow_zero] at hyk
    rcases (by omega : y = rootQ c b D ∨ y = rootQ c b D + 1) with rfl | rfl
    · exact loopY_at_root
    · exact Or.inl loopY_at_root_succ
  | k + 1, fuel, y, hy0, hyk, hf => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    rcases (by omega : y = rootQ c b D ∨ y = rootQ c b D + 1 ∨ y = rootQ c b D + 2 ∨
        rootQ c b D + 3 ≤ y) with rfl | rfl | rfl | hy3
    · exact loopY_at_root
    · exact Or.inl loopY_at_root_succ
    · exact loopY_at_root_two
    · obtain ⟨hlo, -, -, -, hE⟩ := bodyY_step' (c := c) (b := b) (D := D) hy0
      obtain ⟨hdrop, hhalf⟩ := hE hy3
      have hc : ¬ closeEnough 1 (bodyY c b D y) y := fun h => by
        have := closeEnough_iff.1 h
        omega
      rw [loopY_succ]
      simp only [hc, ↓reduceIte]
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := Nat.pow_succ'
      exact loopY_rootOrSucc_of_le k hlo (by omega) (by omega)

/-- A start below the floor root with a positive denominator. -/
theorem loopY_rootOrSucc_of_lt {c b D : Nat} (k : Nat) {fuel y : Nat}
    (hy : y < rootQ c b D) (hden : D + 1 ≤ 2 * y + b)
    (hk : bodyY c b D y - rootQ c b D ≤ 2 ^ k) (hf : k + 2 ≤ fuel) :
    rootOrSucc c b D (loopY c b D 1 fuel y) := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  have hR1 := rootQ_spec c b D
  obtain ⟨-, zq2⟩ := bodyY_int (c := c) (by omega : D ≤ 2 * y + b)
  have zR1 : (rootQ c b D : Int) * rootQ c b D + b * rootQ c b D ≤ c + D * rootQ c b D := by
    exact_mod_cast hR1
  have hlo : rootQ c b D ≤ bodyY c b D y := by
    have := body_ge_root_int zR1 (by omega) (zq2 (by omega))
    exact_mod_cast this
  rw [loopY_succ]
  by_cases hc : closeEnough 1 (bodyY c b D y) y
  · simp only [hc, ↓reduceIte]
    have := closeEnough_iff.1 hc
    exact Or.inl (by omega)
  · simp only [hc, ↓reduceIte]
    exact loopY_rootOrSucc_of_le k hlo hk (by omega)

/-- The source start `y = D`, at or above the floor root. -/
theorem loopY_rootOrSucc {c b D : Nat} (hstart : rootQ c b D ≤ D) (hD : D ≤ 2 ^ 254) :
    rootOrSucc c b D (loopY c b D 1 255 D) :=
  loopY_rootOrSucc_of_le 254 hstart (by omega) (by omega)

/-! ## Every non-reverting call -/

theorem chkAdd_some_lt {a b r : Nat} (h : chkAdd a b = some r) : a + b < wordSize := by
  unfold chkAdd at h
  split at h
  · assumption
  · cases h

theorem chkMul_some_lt {a b r : Nat} (h : chkMul a b = some r) : a * b < wordSize := by
  unfold chkMul at h
  split at h
  · assumption
  · cases h

/-- The floored `c` never exceeds `D^4`. -/
theorem cOf_le_pow (u v D ann : Nat) : cOf u v D ann ≤ D ^ 4 := by
  unfold cOf
  have h1 : D * D / (u * 3) ≤ D * D := Nat.div_le_self _ _
  have h2 : D * D / (u * 3) * D / (v * 3) ≤ D * D * D :=
    le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_right _ h1)
  have h3 : D * D / (u * 3) * D / (v * 3) * D / (ann * 3) ≤ D * D * D * D :=
    le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_right _ h2)
  calc _ ≤ D * D * D * D := h3
    _ = D ^ 4 := by ring

/-- **The checked `y` loop from the source start.** Whenever it does not revert, it
returns `⌊y*⌋`, or `⌊y*⌋ + 1` only if `rootGap` fails, from any start `D`, above or
below the root: non-reversion of the first body bounds `D` and the first iterate. -/
theorem loopYChk_rootOrSucc {c b D v : Nat} (h : loopYChk c b D 1 255 D = some v)
    (hc : c ≤ D ^ 4) : rootOrSucc c b D v := by
  rw [loopYChk_some h]
  have h' := h
  rw [show (255 : Nat) = 254 + 1 from rfl] at h'
  unfold loopYChk at h'
  obtain ⟨y1, hy1, -⟩ := bind_some h'
  unfold bodyYChk at hy1
  obtain ⟨m, hm, hy1⟩ := bind_some hy1
  obtain ⟨num, hnum, hy1⟩ := bind_some hy1
  obtain ⟨t, ht, hy1⟩ := bind_some hy1
  obtain ⟨s', hs', hy1⟩ := bind_some hy1
  obtain ⟨den, hden, hy1⟩ := bind_some hy1
  have hDD := chkMul_some_lt hm
  have hnum' := chkAdd_some_lt hnum
  rw [chkMul_some hm] at hnum'
  obtain ⟨-, hden0⟩ := chkDiv_some hy1
  obtain ⟨hdv, -⟩ := chkSub_some hden
  rw [chkAdd_some hs', chkMul_some ht] at hdv
  subst hdv
  have hW : wordSize = 2 ^ 128 * 2 ^ 128 := rfl
  have hD : D < 2 ^ 128 := by
    by_contra hc'
    have := Nat.mul_le_mul (Nat.le_of_not_lt hc') (Nat.le_of_not_lt hc')
    omega
  have h128 : (2 : Nat) ^ 128 ≤ 2 ^ 253 := Nat.pow_le_pow_right (by omega) (by omega)
  have h253 : (2 : Nat) ^ 253 ≤ 2 ^ 254 := Nat.pow_le_pow_right (by omega) (by omega)
  rcases Nat.lt_or_ge D (rootQ c b D) with hlt | hge
  · apply loopY_rootOrSucc_of_lt 253 hlt (by omega) _ (by omega)
    have hb : bodyY c b D D < 2 ^ 253 := by
      unfold bodyY
      rcases Nat.lt_or_ge (2 * D + b - D) 8 with h8 | h8
      · have hD7 : D ≤ 7 := by omega
        have h4 : D ^ 4 ≤ 7 ^ 4 := Nat.pow_le_pow_left hD7 4
        have hDD7 : D * D ≤ 7 * 7 := Nat.mul_le_mul hD7 hD7
        have hle := Nat.div_le_self (D * D + c) (2 * D + b - D)
        have h49 : 7 * 7 + 7 ^ 4 < (2 : Nat) ^ 253 := by decide
        omega
      · apply (Nat.div_lt_iff_lt_mul (by omega)).2
        have h8' : 2 ^ 253 * 8 ≤ 2 ^ 253 * (2 * D + b - D) := Nat.mul_le_mul_left _ h8
        have hW' : wordSize = 2 ^ 253 * 8 := rfl
        omega
    omega
  · exact loopY_rootOrSucc hge (by omega)

/-- **`get_y_D`, every non-reverting call.** -/
theorem getYDChk_rootOrSucc {amp : Nat} {i : Fin 3} {xp : Fin 3 → Nat} {D v : Nat}
    (h : getYDChk amp i xp D = some v) :
    rootOrSucc (cOf (xp (others i).1) (xp (others i).2) D (amp * 3))
      (bOf (xp (others i).1) (xp (others i).2) D (amp * 3)) D v := by
  unfold getYDChk at h
  obtain ⟨ann, hann, h⟩ := bind_some h
  obtain ⟨c, hc, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  have e1 := chkMul_some hann
  subst e1
  have e2 := cOfChk_some hc
  have e3 := bOfChk_some hb
  subst e2 e3
  exact loopYChk_rootOrSucc h (cOf_le_pow _ _ _ _)

/-- **`get_y`, every non-reverting call**, with `D = get_D(xp_, amp)`. -/
theorem getYChk_rootOrSucc {amp : Nat} {i j : Fin 3} {x : Nat} {xp : Fin 3 → Nat} {v : Nat}
    (h : getYChk amp i j x xp = some v) :
    rootOrSucc (cOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (bOf (withAt xp i x (others j).1)
      (withAt xp i x (others j).2) (getD xp amp 1) (amp * 3)) (getD xp amp 1) v := by
  unfold getYChk at h
  split at h
  · cases h
  · obtain ⟨D, hD, h⟩ := bind_some h
    obtain ⟨ann, hann, h⟩ := bind_some h
    obtain ⟨c, hc, h⟩ := bind_some h
    obtain ⟨b, hb, h⟩ := bind_some h
    have e0 := getDChk_some hD
    have e1 := chkMul_some hann
    subst e0 e1
    have e2 := cOfChk_some hc
    have e3 := bOfChk_some hb
    subst e2 e3
    exact loopYChk_rootOrSucc h (cOf_le_pow _ _ _ _)

/-- `get_y_D` at the source start, under the start premise and a bound on `D`. -/
theorem getYD_rootOrSucc {amp : Nat} {i : Fin 3} {xp : Fin 3 → Nat} {D : Nat}
    (hstart : rootQ (cOf (xp (others i).1) (xp (others i).2) D (amp * 3))
      (bOf (xp (others i).1) (xp (others i).2) D (amp * 3)) D ≤ D)
    (hD : D ≤ 2 ^ 254) :
    rootOrSucc (cOf (xp (others i).1) (xp (others i).2) D (amp * 3))
      (bOf (xp (others i).1) (xp (others i).2) D (amp * 3)) D (getYD amp i xp D) :=
  loopY_rootOrSucc hstart hD

/-- `get_y` at the source start, under the start premise and a bound on `D`. -/
theorem getY_rootOrSucc {amp : Nat} {i j : Fin 3} {x : Nat} {xp : Fin 3 → Nat}
    (hstart : rootQ (cOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (bOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (getD xp amp 1) ≤ getD xp amp 1)
    (hD : getD xp amp 1 ≤ 2 ^ 254) :
    rootOrSucc (cOf (withAt xp i x (others j).1) (withAt xp i x (others j).2)
      (getD xp amp 1) (amp * 3)) (bOf (withAt xp i x (others j).1)
      (withAt xp i x (others j).2) (getD xp amp 1) (amp * 3)) (getD xp amp 1)
      (getY amp i j x xp) :=
  loopY_rootOrSucc hstart hD

/-! ## The start premise fails on reachable calls -/

/-- Scaled balances after a first deposit of `[2, 869, 2]` (DAI wei, USDC and USDT units). -/
def startWxp : Fin 3 → Nat := fun k =>
  if k = 0 then 2 else if k = 1 then 869000000000000 else 2000000000000

/-- **`get_y_D` can start below its root.** After the first deposit `[2, 869, 2]` at
`A = 2000` (supply `T = D0`), `calc_withdraw_one_coin(100461080667, 1)` passes
`D1 = D0 - 100461080667·D0/T` to `get_y_D`, and `D1` is below the floor root of the
quadratic it solves; the checked call still succeeds. So `rootQ ≤ D` is not a
premise the pool can discharge, and `getYDChk_rootOrSucc` does without it. -/
theorem getYD_start_below_root :
    getD startWxp 2000 1 = 836659811965 ∧
    836659811965 - 100461080667 * 836659811965 / 836659811965 = 736198731298 ∧
    736198731298 < rootQ (cOf (startWxp (others 1).1) (startWxp (others 1).2) 736198731298 (2000 * 3))
      (bOf (startWxp (others 1).1) (startWxp (others 1).2) 736198731298 (2000 * 3)) 736198731298 ∧
    getYDChk 2000 1 startWxp 736198731298 = some 672659051234812 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  unfold rootQ
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (Nat.le_findGreatest (by decide +kernel) (by decide +kernel))

/-- Scaled balances after a first deposit of `[9, 9, 1]`. -/
def startWxpY : Fin 3 → Nat := fun k =>
  if k = 0 then 9 else if k = 1 then 9000000000000 else 1000000000000

/-- **`get_y` can start below its root.** After the first deposit `[9, 9, 1]` at
`A = 1`, `exchange(0, 1, 1)` calls `get_y(0, 1, 10, xp)` with `D = get_D(xp, 1)` below
the floor root of its quadratic; the checked call still succeeds. -/
theorem getY_start_below_root :
    getD startWxpY 1 1 = 16000245046 ∧
    16000245046 < rootQ (cOf (withAt startWxpY 0 10 (others 1).1) (withAt startWxpY 0 10 (others 1).2)
      16000245046 (1 * 3)) (bOf (withAt startWxpY 0 10 (others 1).1)
      (withAt startWxpY 0 10 (others 1).2) 16000245046 (1 * 3)) 16000245046 ∧
    getYChk 1 0 1 10 startWxpY = some 8514123217434 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  unfold rootQ
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (Nat.le_findGreatest (by decide +kernel) (by decide +kernel))

end Blanc.StableSwapNewton
