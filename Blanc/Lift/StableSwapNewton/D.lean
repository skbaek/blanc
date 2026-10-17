import Blanc.Lift.StableSwapNewton.Root
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! `get_D`: the checked loop returns the plain loop's value whenever it does not
revert, and the plain value is never below the floor root `⌊D*⌋`, at every
tolerance and whether the loop stopped or ran out of fuel. -/

namespace Blanc.StableSwapNewton

/-! ## Checked arithmetic agrees with plain arithmetic when it does not revert -/

theorem chkAdd_some {a b r : Nat} (h : chkAdd a b = some r) : r = a + b := by
  unfold chkAdd at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem chkSub_some {a b r : Nat} (h : chkSub a b = some r) : r = a - b ∧ b ≤ a := by
  unfold chkSub at h
  split at h
  · exact ⟨(Option.some.inj h).symm, by assumption⟩
  · cases h

theorem chkMul_some {a b r : Nat} (h : chkMul a b = some r) : r = a * b := by
  unfold chkMul at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem chkDiv_some {a b r : Nat} (h : chkDiv a b = some r) : r = a / b ∧ b ≠ 0 := by
  unfold chkDiv at h
  split at h
  · cases h
  · exact ⟨(Option.some.inj h).symm, by assumption⟩

/-- Inversion of one `Option` bind that returned a value. -/
theorem bind_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : (o >>= f) = some b) : ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem dPChk_some {x : Fin 3 → Nat} {D v : Nat} (h : dPChk x D = some v) : v = dP x D := by
  unfold dPChk at h
  obtain ⟨a0, ha0, h⟩ := bind_some h
  obtain ⟨b0, hb0, h⟩ := bind_some h
  obtain ⟨p0, hp0, h⟩ := bind_some h
  obtain ⟨a1, ha1, h⟩ := bind_some h
  obtain ⟨b1, hb1, h⟩ := bind_some h
  obtain ⟨p1, hp1, h⟩ := bind_some h
  obtain ⟨a2, ha2, h⟩ := bind_some h
  obtain ⟨b2, hb2, h⟩ := bind_some h
  rw [(chkDiv_some h).1, chkMul_some ha2, chkMul_some hb2, (chkDiv_some hp1).1, chkMul_some ha1,
    chkMul_some hb1, (chkDiv_some hp0).1, chkMul_some ha0, chkMul_some hb0]
  rfl

theorem bodyDChk_some {x : Fin 3 → Nat} {ann D v : Nat} (h : bodyDChk x ann (sum3 x) D = some v) :
    v = bodyD x ann D := by
  unfold bodyDChk at h
  obtain ⟨p, hp, h⟩ := bind_some h
  obtain ⟨a, ha, h⟩ := bind_some h
  obtain ⟨b, hb, h⟩ := bind_some h
  obtain ⟨c, hc, h⟩ := bind_some h
  obtain ⟨num, hnum, h⟩ := bind_some h
  obtain ⟨s, hs, h⟩ := bind_some h
  obtain ⟨d, hd, h⟩ := bind_some h
  obtain ⟨e, he, h⟩ := bind_some h
  obtain ⟨den, hden, h⟩ := bind_some h
  rw [(chkDiv_some h).1, chkMul_some hnum, chkAdd_some hc, chkMul_some ha, chkMul_some hb,
    chkAdd_some hden, chkMul_some hd, chkMul_some he, (chkSub_some hs).1, dPChk_some hp]
  rfl

theorem loopDChk_some {x : Fin 3 → Nat} {ann tol : Nat} :
    ∀ {fuel D v : Nat}, loopDChk x ann (sum3 x) tol fuel D = some v →
      v = loopD x ann tol fuel D
  | 0, D, v, h => by
    unfold loopDChk at h
    exact (Option.some.inj h).symm
  | fuel + 1, D, v, h => by
    unfold loopDChk at h
    obtain ⟨D', hD', h⟩ := bind_some h
    have e := bodyDChk_some hD'
    subst e
    unfold loopD
    split at h
    · rename_i hc
      simp only [hc, ↓reduceIte]
      exact (Option.some.inj h).symm
    · rename_i hc
      simp only [hc, ↓reduceIte]
      exact loopDChk_some h

/-- Bridge: a non-reverting checked `get_D` returns the plain `getD`. -/
theorem getDChk_some {x : Fin 3 → Nat} {amp tol v : Nat} (h : getDChk x amp tol = some v) :
    v = getD x amp tol := by
  unfold getDChk at h
  obtain ⟨s0, hs0, h⟩ := bind_some h
  obtain ⟨s1, hs1, h⟩ := bind_some h
  obtain ⟨S, hS, h⟩ := bind_some h
  have eS : S = sum3 x := by
    rw [chkAdd_some hS, chkAdd_some hs1, chkAdd_some hs0]
    unfold sum3
    omega
  subst eS
  unfold getD
  split at h
  · rename_i h0
    simp only [h0, ↓reduceIte]
    exact (Option.some.inj h).symm
  · rename_i h0
    simp only [h0, ↓reduceIte]
    obtain ⟨ann, hann, h⟩ := bind_some h
    rw [chkMul_some hann] at h
    exact loopDChk_some h

/-! ## The lower bound -/

/-- The floored `D_P` never exceeds the real `D^4 / (27·P)`. -/
theorem dP_mul_le (x : Fin 3 → Nat) (D : Nat) : 27 * prod3 x * dP x D ≤ D ^ 4 := by
  unfold dP prod3
  generalize hq0 : D * D / (x 0 * 3) = q0
  generalize hq1 : q0 * D / (x 1 * 3) = q1
  generalize hq2 : q1 * D / (x 2 * 3) = q2
  have h0 : q0 * (x 0 * 3) ≤ D * D := hq0 ▸ Nat.div_mul_le_self _ _
  have h1 : q1 * (x 1 * 3) ≤ q0 * D := hq1 ▸ Nat.div_mul_le_self _ _
  have h2 : q2 * (x 2 * 3) ≤ q1 * D := hq2 ▸ Nat.div_mul_le_self _ _
  calc 27 * (x 0 * x 1 * x 2) * q2 = 9 * (x 0 * x 1) * (q2 * (x 2 * 3)) := by ring
    _ ≤ 9 * (x 0 * x 1) * (q1 * D) := Nat.mul_le_mul_left _ h2
    _ = 3 * x 0 * D * (q1 * (x 1 * 3)) := by ring
    _ ≤ 3 * x 0 * D * (q0 * D) := Nat.mul_le_mul_left _ h1
    _ = D * D * (q0 * (x 0 * 3)) := by ring
    _ ≤ D * D * (D * D) := Nat.mul_le_mul_left _ h0
    _ = D ^ 4 := by ring

/-- Tangent-line bound of `E ↦ E^4` at `D`. -/
theorem quartic_tangent (D E : Nat) : 4 * D ^ 3 * E ≤ E ^ 4 + 3 * D ^ 4 := by
  have h : (4 * D ^ 3 * E : Int) ≤ E ^ 4 + 3 * D ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg ((E : Int) - D))
      (add_nonneg (add_nonneg (sq_nonneg (E : Int)) (mul_nonneg (mul_nonneg (by omega : (0 : Int) ≤ 2) (Int.natCast_nonneg E)) (Int.natCast_nonneg D))) (mul_nonneg (by omega : (0 : Int) ≤ 3) (sq_nonneg (D : Int))))]
  exact_mod_cast h

/-- One body from an iterate in the upper range `3·(ann-1)·D ≤ 4·ann·S`: the value
is at least `⌊D*⌋`, stays in the upper range, and is positive. -/
theorem bodyD_step {x : Fin 3 → Nat} {ann D : Nat} (hx : 1 ≤ prod3 x) (hS : 1 ≤ sum3 x)
    (hann : 2 ≤ ann) (hD : 1 ≤ D) (hU : 3 * (ann - 1) * D ≤ 4 * ann * sum3 x) :
    aboveRoot x ann (bodyD x ann D + 1) ∧ 3 * (ann - 1) * bodyD x ann D ≤ 4 * ann * sum3 x ∧
      1 ≤ bodyD x ann D := by
  have hq := dP_mul_le x D
  unfold aboveRoot bodyD
  generalize dP x D = q at hq ⊢
  generalize sum3 x = S at hS hU ⊢
  generalize hK : 27 * prod3 x = K at hq ⊢
  have hK1 : 1 ≤ K := by omega
  obtain ⟨a, rfl⟩ : ∃ a, ann = a + 1 := ⟨ann - 1, by omega⟩
  have ha : a + 1 - 1 = a := Nat.add_sub_cancel a 1
  rw [ha] at hU ⊢
  have ha1 : 1 ≤ a := by omega
  have hden : 0 < a * D + 4 * q := Nat.lt_of_lt_of_le (Nat.mul_pos ha1 hD) (Nat.le_add_right _ _)
  generalize hB : ((a + 1) * S + q * 3) * D / (a * D + 4 * q) = B
  have hB1 : B * (a * D + 4 * q) ≤ ((a + 1) * S + q * 3) * D := hB ▸ Nat.div_mul_le_self _ _
  have hB2 : ((a + 1) * S + q * 3) * D < (B + 1) * (a * D + 4 * q) := by
    have h := Nat.lt_div_mul_add (a := ((a + 1) * S + q * 3) * D) hden
    rw [hB] at h
    linarith
  have hE : 3 * D ≤ 4 * (B + 1) := by
    by_contra hc
    have hc' : 4 * (B + 1) ≤ 3 * D := by omega
    have h1 : q * (4 * (B + 1)) ≤ q * (3 * D) := Nat.mul_le_mul_left _ hc'
    have h2 : (a + 1) * S * D < (B + 1) * a * D := by linarith
    have h3 : (a + 1) * S < (B + 1) * a := Nat.lt_of_mul_lt_mul_right h2
    have h4 : a * (3 * D) < a * (4 * (B + 1)) := by linarith
    have h5 := Nat.lt_of_mul_lt_mul_left h4
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hq
  have h6 : K * (((a + 1) * S + q * 3) * D) < K * ((B + 1) * (a * D + 4 * q)) :=
    Nat.mul_lt_mul_of_pos_left hB2 hK1
  have h7 : r * (3 * D) ≤ r * (4 * (B + 1)) := Nat.mul_le_mul_left _ hE
  have e1 : D * (K * (a + 1) * S + 3 * D ^ 4) = K * (a + 1) * S * D + 3 * D * (K * q + r) := by
    rw [← hr]
    ring
  have e2 : D * ((B + 1) * (4 * D ^ 3 + K * a)) = (B + 1) * (4 * (K * q + r) + K * a * D) := by
    rw [← hr]
    ring
  have h8 : D * (K * (a + 1) * S + 3 * D ^ 4) < D * ((B + 1) * (4 * D ^ 3 + K * a)) := by
    rw [e1, e2]
    linarith
  have h9 := Nat.lt_of_mul_lt_mul_left h8
  have h10 := quartic_tangent D (B + 1)
  have hlow : K * (a + 1) * S < (B + 1) ^ 4 + K * a * (B + 1) := by linarith
  refine ⟨hlow, ?_, ?_⟩
  · rcases Nat.lt_or_ge (4 * B) (3 * D) with h | h
    · have h11 : 3 * a * (4 * B) ≤ 3 * a * (3 * D) := Nat.mul_le_mul_left _ h.le
      linarith [Nat.zero_le (a * S)]
    · have h11 : q * (3 * D) ≤ q * (4 * B) := Nat.mul_le_mul_left _ h
      have h12 : B * a * D ≤ (a + 1) * S * D := by linarith
      have h13 := Nat.le_of_mul_le_mul_right h12 hD
      linarith [Nat.zero_le (a * S)]
  · rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0
      have h11 : K * (a + 1) * 1 ≤ K * (a + 1) * S := Nat.mul_le_mul_left _ hS
      linarith
    · exact h0

theorem loopD_succ (x : Fin 3 → Nat) (ann tol fuel D : Nat) :
    loopD x ann tol (fuel + 1) D =
      if closeEnough tol (bodyD x ann D) D then bodyD x ann D
      else loopD x ann tol fuel (bodyD x ann D) := rfl

/-- Every value the loop returns after at least one body, stopped or not, is at least
`⌊D*⌋`, in the upper range and positive, when it starts in the upper range. -/
theorem loopD_lower {x : Fin 3 → Nat} {ann tol : Nat} (hx : 1 ≤ prod3 x) (hS : 1 ≤ sum3 x)
    (hann : 2 ≤ ann) : ∀ {fuel D : Nat}, 1 ≤ D → 3 * (ann - 1) * D ≤ 4 * ann * sum3 x →
      aboveRoot x ann (loopD x ann tol (fuel + 1) D + 1) ∧
        3 * (ann - 1) * loopD x ann tol (fuel + 1) D ≤ 4 * ann * sum3 x ∧
          1 ≤ loopD x ann tol (fuel + 1) D
  | 0, D, hD, hU => by
    rw [loopD_succ]
    split
    · exact bodyD_step hx hS hann hD hU
    · exact bodyD_step hx hS hann hD hU
  | fuel + 1, D, hD, hU => by
    obtain ⟨_, h2, h3⟩ := bodyD_step hx hS hann hD hU
    rw [loopD_succ]
    split
    · exact bodyD_step hx hS hann hD hU
    · exact loopD_lower hx hS hann h3 h2

/-- **U4 lower bound.** For positive balances and `A ≥ 1`, `get_D` is never below
`⌊D*⌋`, at every stopping tolerance, whether the loop stopped or exhausted its 255
bodies. No word bound is needed: the plain arithmetic is unbounded. -/
theorem getD_lower {x : Fin 3 → Nat} {amp : Nat} (hx : ∀ i, 0 < x i) (hamp : 1 ≤ amp)
    (tol : Nat) : aboveRoot x (amp * 3) (getD x amp tol + 1) := by
  have hP : 1 ≤ prod3 x := Nat.mul_pos (Nat.mul_pos (hx 0) (hx 1)) (hx 2)
  have hS : 1 ≤ sum3 x := by
    unfold sum3
    have := hx 0
    omega
  have hU : 3 * (amp * 3 - 1) * sum3 x ≤ 4 * (amp * 3) * sum3 x :=
    Nat.mul_le_mul_right _ (by omega)
  have h0 : ¬ sum3 x = 0 := by omega
  unfold getD
  simp only [h0, ↓reduceIte]
  exact (loopD_lower (fuel := 254) hP hS (by omega) hS hU).1

/-- `get_D ≥ ⌊D*⌋` stated with the floor root. -/
theorem floorRoot_le_getD {x : Fin 3 → Nat} {amp : Nat} (hx : ∀ i, 0 < x i) (hamp : 1 ≤ amp)
    (tol : Nat) : floorRoot x (amp * 3) ≤ getD x amp tol :=
  floorRoot_le_of_aboveRoot_succ (getD_lower hx hamp tol)

/-- The lower bound for a non-reverting checked `get_D`. -/
theorem getDChk_lower {x : Fin 3 → Nat} {amp tol v : Nat} (h : getDChk x amp tol = some v)
    (hx : ∀ i, 0 < x i) (hamp : 1 ≤ amp) : aboveRoot x (amp * 3) (v + 1) :=
  getDChk_some h ▸ getD_lower hx hamp tol

/-! ## Witnesses: the cap, non-monotonicity, and the ceil mutation control -/

/-- The loop runs all `fuel` bodies from `D` without its stopping test firing. -/
def runsOut (x : Fin 3 → Nat) (ann tol : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, D =>
    !decide (closeEnough tol (bodyD x ann D) D) && runsOut x ann tol fuel (bodyD x ann D)

/-- A loop that runs out returns its `fuel`-th iterate (line 218). -/
theorem loopD_of_runsOut {x : Fin 3 → Nat} {ann tol : Nat} :
    ∀ {fuel D : Nat}, runsOut x ann tol fuel D = true →
      loopD x ann tol fuel D = (bodyD x ann)^[fuel] D
  | 0, D, _ => rfl
  | fuel + 1, D, h => by
    unfold runsOut at h
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    rw [loopD_succ, Function.iterate_succ_apply]
    simp only [h.1, ↓reduceIte]
    exact loopD_of_runsOut h.2

/-- Spec cap witness: `xp = (10^27, 10^27, 10^21)`, `A = 2000`. -/
def capW : Fin 3 → Nat := fun k => if k = 0 then 10 ^ 27 else if k = 1 then 10 ^ 27 else 10 ^ 21

/-- **Cap.** At `A = 2000`, `get_D` on `capW` never meets its stopping test in 255 bodies:
the iterates cycle between two values 3 apart and the source returns the last one,
`⌊D*⌋ + 2`, without reverting. -/
theorem getD_cap_cycle :
    runsOut capW 6000 1 255 (sum3 capW) = true ∧
    getD capW 2000 1 = (bodyD capW 6000)^[255] (sum3 capW) ∧
    getD capW 2000 1 = 680031527231617479170632831 ∧
    bodyD capW 6000 680031527231617479170632831 = 680031527231617479170632834 ∧
    bodyD capW 6000 680031527231617479170632834 = 680031527231617479170632831 ∧
    floorRoot capW 6000 + 2 = 680031527231617479170632831 := by
  have hf : floorRoot capW 6000 = 680031527231617479170632829 :=
    floorRoot_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hr : runsOut capW 6000 1 255 (sum3 capW) = true := by decide +kernel
  have hs : ¬ sum3 capW = 0 := by decide +kernel
  have hi : getD capW 2000 1 = (bodyD capW 6000)^[255] (sum3 capW) := by
    unfold getD
    simp only [hs, ↓reduceIte]
    exact loopD_of_runsOut hr
  rw [hf]
  exact ⟨hr, hi, by decide +kernel⟩

/-- Spec witness #2 before the donation: the scaled balances after a first deposit of
`[220465013637442144357580800, 180845591198, 100000000000000]`. -/
def monoPre : Fin 3 → Nat := fun k =>
  if k = 0 then 220465013637442144357580800
  else if k = 1 then 180845591198000000000000 else 100000000000000000000000000

/-- Spec witness #2 after one more wei of coin 0. -/
def monoPost : Fin 3 → Nat := fun k => if k = 0 then monoPre 0 + 1 else monoPre k

/-- **Integer `get_D` is not monotone.** One more wei of coin 0 lowers `get_D` at
`A = 1`, both loops having stopped normally; the same holds at tolerance 2, so the
tolerance is not what breaks monotonicity. -/
theorem getD_not_mono :
    (∀ i, monoPre i ≤ monoPost i) ∧
    getD monoPost 1 1 < getD monoPre 1 1 ∧ getD monoPost 1 2 < getD monoPre 1 2 := by
  decide +kernel

/-- Ceiling division, the mutation of `/`. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- Mutation control: `D_P` with every floor replaced by a ceiling. -/
def dPCeil (x : Fin 3 → Nat) (D : Nat) : Nat :=
  ceilDiv (ceilDiv (ceilDiv (D * D) (x 0 * 3) * D) (x 1 * 3) * D) (x 2 * 3)

/-- The body with the mutated `D_P`. -/
def bodyDCeil (x : Fin 3 → Nat) (ann D : Nat) : Nat :=
  (ann * sum3 x + dPCeil x D * 3) * D / ((ann - 1) * D + 4 * dPCeil x D)

/-- The loop with the mutated body. -/
def loopDCeil (x : Fin 3 → Nat) (ann tol : Nat) : Nat → Nat → Nat
  | 0, D => D
  | fuel + 1, D =>
    let D' := bodyDCeil x ann D
    if closeEnough tol D' D then D' else loopDCeil x ann tol fuel D'

/-- `get_D` with the mutated body. -/
def getDCeil (x : Fin 3 → Nat) (amp tol : Nat) : Nat :=
  if sum3 x = 0 then 0 else loopDCeil x (amp * 3) tol 255 (sum3 x)

/-- Spec ceil-control witness, `A = 200`. -/
def ceilW : Fin 3 → Nat := fun k =>
  if k = 0 then 49618383664099511762944
  else if k = 1 then 15502547668752764928 else 104186921517217513472

/-- **Mutation control for `getD_lower`.** Rounding `D_P` up instead of down breaks
the lower bound: the mutant returns `⌊D*⌋ - 2` on `ceilW`, while the source returns
`⌊D*⌋ + 2`. The step of `getD_lower` the mutation removes is `dP_mul_le`: a rounded-up
`D_P` can exceed `D^4 / (27·P)`. -/
theorem getDCeil_breaks_lower :
    ¬ aboveRoot ceilW 600 (getDCeil ceilW 200 1 + 1) ∧
    getDCeil ceilW 200 1 = 14615550493253435060542 ∧
    floorRoot ceilW 600 = 14615550493253435060544 ∧
    getD ceilW 200 1 = 14615550493253435060546 := by
  have hf : floorRoot ceilW 600 = 14615550493253435060544 :=
    floorRoot_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [hf]
  decide +kernel

end Blanc.StableSwapNewton
