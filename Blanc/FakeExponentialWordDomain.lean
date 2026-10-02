import Blanc.FakeExponentialWordCorrespondence

namespace Blanc.FakeExponentialWordDomain

open Jaune

private theorem denominator_lt {d c N : Nat} (dPos : 0 < d) (cPos : 0 < c)
    (horizon : d * d * (c + N) ≤ 2 ^ 256) : d < 2 ^ 256 := by
  have square : d * d ≤ 2 ^ 256 :=
    (Nat.le_mul_of_pos_right (d * d) (by omega : 0 < c + N)).trans horizon
  by_cases one : d = 1
  · rw [one]
    decide
  · have twice : 2 * d ≤ d * d := Nat.mul_le_mul_right d (by omega)
    omega

private theorem divisor_lt {d c N : Nat} (dPos : 0 < d)
    (horizon : d * (c + (N + 1)) ≤ 2 ^ 256) : d * c < 2 ^ 256 := by
  have strict : d * c < d * (c + (N + 1)) :=
    Nat.mul_lt_mul_of_pos_left (by omega) dPos
  omega

private theorem next_toNat {e a : B256} {d c : Nat}
    (dPos : 0 < d) (dBound : d < 2 ^ 256) (divisorBound : d * c < 2 ^ 256) :
    (WordFakeExponential.nextAccumulator e d.toB256 c.toB256 a).toNat =
      (a.toNat * e.toNat % (2 ^ 256)) / (d * c) := by
  have cBound : c < 2 ^ 256 :=
    (Nat.le_mul_of_pos_left c dPos).trans_lt divisorBound
  have quotientBound :
      (a * e).toNat / (d.toB256 * c.toB256).toNat < 2 ^ 256 :=
    (Nat.div_le_self _ _).trans_lt (B256.toNat_lt _)
  rw [WordFakeExponential.nextAccumulator, wordDiv_eq_toB256_div,
    B256.toNat_toB256_of_lt quotientBound, B256.toNat_mul_mod,
    B256.toNat_mul_mod, B256.toNat_toB256_of_lt dBound,
    B256.toNat_toB256_of_lt cBound, Nat.mod_eq_of_lt divisorBound]

private theorem comparison {e counter a p r : B256} {d N : Nat}
    (run : WordFakeExponential.Run e d.toB256 counter a p N r) :
    ∀ c A : Nat, counter = c.toB256 → 0 < d → 0 < c → d < 2 ^ 256 →
      d * (c + N) ≤ 2 ^ 256 → a.toNat ≤ A →
      r.toNat + (A - a.toNat) ≤ p.toNat + fakeExpAux e.toNat d c A := by
  induction run with
  | stop counter p =>
    intro c A counterEq dPos cPos dBound horizon larger
    have first := FakeExponential.accumulator_le e.toNat d c A
    simp only [B256.toNat_zero, Nat.sub_zero]
    omega
  | @step counter a p N r active next ih =>
    intro c A counterEq dPos cPos dBound horizon larger
    have divisorBound := divisor_lt dPos horizon
    have activeNat : a.toNat ≠ 0 := by
      intro zero
      exact active (B256.toNat_inj _ _ zero)
    have activeA : A ≠ 0 := by omega
    have nextNat := next_toNat (e := e) (a := a) dPos dBound divisorBound
    have nextLe :
        (WordFakeExponential.nextAccumulator e d.toB256 counter a).toNat ≤
          A * e.toNat / (d * c) := by
      rw [counterEq, nextNat]
      exact Nat.div_le_div_right
        ((Nat.mod_le _ _).trans (Nat.mul_le_mul_right e.toNat larger))
    have nextWindow : d * (c + 1 + N) ≤ 2 ^ 256 := by
      have indices : c + 1 + N = c + (N + 1) := by omega
      rw [indices]
      exact horizon
    have nextCounter : counter + 1 = (c + 1).toB256 := by
      rw [counterEq, toB256_add_one]
    have tail := ih (c + 1) (A * e.toNat / (d * c)) nextCounter dPos
      (by omega) dBound nextWindow nextLe
    have prefixLe : (p + a).toNat ≤ p.toNat + a.toNat := by
      rw [B256.toNat_add, Nat.lo_eq]
      exact Nat.mod_le _ _
    rw [fakeExpAux_succ activeA]
    omega

private theorem noWrap_of_close {e counter a p r : B256} {d N : Nat}
    (run : WordFakeExponential.Run e d.toB256 counter a p N r) :
    ∀ c : Nat, counter = c.toB256 → 0 < d → 0 < c → d < 2 ^ 256 →
      d * d * (c + N) ≤ 2 ^ 256 →
      p.toNat + fakeExpAux e.toNat d c a.toNat < r.toNat + d →
      ∃ output, ∃ natRun : FakeExponential.Run e.toNat d c a.toNat N output,
        FakeExponentialWordCorrespondence.NoWrap natRun p.toNat := by
  induction run with
  | stop counter p =>
    intro c counterEq dPos cPos dBound horizon close
    exact ⟨0, FakeExponential.Run.stop c,
      FakeExponentialWordCorrespondence.NoWrap.stop c p.toNat (B256.toNat_lt p)⟩
  | @step counter a p N r active next ih =>
    intro c counterEq dPos cPos dBound horizon close
    have activeNat : a.toNat ≠ 0 := by
      intro zero
      exact active (B256.toNat_inj _ _ zero)
    have weakWindow : d * (c + (N + 1)) ≤ 2 ^ 256 :=
      (Nat.mul_le_mul_right (c + (N + 1))
        (Nat.le_mul_of_pos_left d dPos)).trans horizon
    have divisorBound := divisor_lt dPos weakWindow
    have nextCounter : counter + 1 = (c + 1).toB256 := by
      rw [counterEq, toB256_add_one]
    have nextWindow : d * d * (c + 1 + N) ≤ 2 ^ 256 := by
      have indices : c + 1 + N = c + (N + 1) := by omega
      rw [indices]
      exact horizon
    have weakNext : d * (c + 1 + N) ≤ 2 ^ 256 :=
      (Nat.mul_le_mul_right (c + 1 + N)
        (Nat.le_mul_of_pos_left d dPos)).trans nextWindow
    let A := a.toNat * e.toNat / (d * c)
    have nextNat :
        (WordFakeExponential.nextAccumulator e d.toB256 counter a).toNat =
          (a.toNat * e.toNat % (2 ^ 256)) / (d * c) := by
      rw [counterEq]
      exact next_toNat dPos dBound divisorBound
    have nextLe :
        (WordFakeExponential.nextAccumulator e d.toB256 counter a).toNat ≤ A := by
      rw [nextNat]
      exact Nat.div_le_div_right (Nat.mod_le _ _)
    have tail := comparison next (c + 1) A nextCounter dPos (by omega)
      dBound weakNext nextLe
    have prefixLe : (p + a).toNat ≤ p.toNat + a.toNat := by
      rw [B256.toNat_add, Nat.lo_eq]
      exact Nat.mod_le _ _
    rw [fakeExpAux_succ activeNat] at close
    have productBound : a.toNat * e.toNat < 2 ^ 256 := by
      by_contra wrapped
      have wraps : 2 ^ 256 ≤ a.toNat * e.toNat := by omega
      have payDivisor : d * (d * c) ≤ 2 ^ 256 := by
        rw [← Nat.mul_assoc]
        exact (Nat.mul_le_mul_left (d * d) (Nat.le_add_right c (N + 1))).trans horizon
      have gap :
          (WordFakeExponential.nextAccumulator e d.toB256 counter a).toNat + d ≤ A := by
        rw [nextNat]
        apply (Nat.le_div_iff_mul_le (Nat.mul_pos dPos cPos)).2
        rw [Nat.add_mul]
        have quotient := Nat.div_mul_le_self (a.toNat * e.toNat % (2 ^ 256)) (d * c)
        have remainder := Nat.mod_le (a.toNat * e.toNat - 2 ^ 256) (2 ^ 256)
        rw [← Nat.mod_eq_sub_mod wraps] at remainder
        omega
      change p.toNat + (a.toNat + fakeExpAux e.toNat d (c + 1) A) < r.toNat + d at close
      omega
    have sumBound : p.toNat + a.toNat < 2 ^ 256 := by
      by_contra wrapped
      have wraps : 2 ^ 256 ≤ p.toNat + a.toNat := by omega
      have pBound := B256.toNat_lt p
      have aBound := B256.toNat_lt a
      have prefixEq : (p + a).toNat = p.toNat + a.toNat - 2 ^ 256 := by
        rw [B256.toNat_add, Nat.lo_eq, Nat.mod_eq_sub_mod wraps,
          Nat.mod_eq_of_lt (by omega)]
      rw [prefixEq] at tail
      change p.toNat + (a.toNat + fakeExpAux e.toNat d (c + 1) A) < r.toNat + d at close
      omega
    have prefixEq : (p + a).toNat = p.toNat + a.toNat := by
      rw [B256.toNat_add, Nat.lo_eq, Nat.mod_eq_of_lt sumBound]
    have nextEq :
        (WordFakeExponential.nextAccumulator e d.toB256 counter a).toNat = A := by
      rw [nextNat, Nat.mod_eq_of_lt productBound]
    have nextClose :
        (p + a).toNat + fakeExpAux e.toNat d (c + 1)
          (WordFakeExponential.nextAccumulator e d.toB256 counter a).toNat < r.toNat + d := by
      rw [prefixEq, nextEq]
      change p.toNat + (a.toNat + fakeExpAux e.toNat d (c + 1) A) < r.toNat + d at close
      omega
    have reconstruction := ih (c + 1) nextCounter dPos (by omega)
      dBound nextWindow nextClose
    rw [nextEq, prefixEq] at reconstruction
    obtain ⟨output, natRun, safe⟩ := reconstruction
    exact ⟨a.toNat + output, FakeExponential.Run.step activeNat natRun,
      FakeExponentialWordCorrespondence.NoWrap.step (active := activeNat)
        sumBound productBound divisorBound safe⟩

private theorem quotient_toNat (r : B256) {d : Nat} (dBound : d < 2 ^ 256) :
    (r / d.toB256).toNat = r.toNat / d := by
  rw [wordDiv_eq_toB256_div, B256.toNat_toB256_of_lt
    ((Nat.div_le_self _ _).trans_lt (B256.toNat_lt r)),
    B256.toNat_toB256_of_lt dBound]

/-- In the bounded positive-divisor window, equality of the final quotients
is exactly the existing Nat trace's no-wrap domain at the same iteration count. -/
theorem Run.quotient_eq_iff_noWrap {e a r : B256} {d c N : Nat}
    (run : WordFakeExponential.Run e d.toB256 c.toB256 a 0 N r)
    (dPos : 0 < d) (cPos : 0 < c)
    (horizon : d * d * (c + N) ≤ 2 ^ 256) :
    (r / d.toB256).toNat = fakeExpAux e.toNat d c a.toNat / d ↔
      ∃ output, ∃ natRun : FakeExponential.Run e.toNat d c a.toNat N output,
        FakeExponentialWordCorrespondence.NoWrap natRun 0 := by
  have dBound := denominator_lt dPos cPos horizon
  constructor
  · intro quotientEq
    rw [quotient_toNat r dBound] at quotientEq
    have decomposition := Nat.div_add_mod' (fakeExpAux e.toNat d c a.toNat) d
    have remainder := Nat.mod_lt (fakeExpAux e.toNat d c a.toNat) dPos
    have lower := Nat.div_mul_le_self r.toNat d
    rw [quotientEq] at lower
    have close : fakeExpAux e.toNat d c a.toNat < r.toNat + d := by omega
    exact noWrap_of_close run c rfl dPos cPos dBound horizon
      (by simpa only [B256.toNat_zero, Nat.zero_add] using close)
  · rintro ⟨output, natRun, safe⟩
    have imageRun : WordFakeExponential.Run e.toNat.toB256 d.toB256 c.toB256
        a.toNat.toB256 0 N r := by
      rw [toB256_toNat, toB256_toNat]
      exact run
    have result := safe.word_result imageRun
    rw [quotient_toNat r dBound, result.2, Nat.zero_add]

end Blanc.FakeExponentialWordDomain
