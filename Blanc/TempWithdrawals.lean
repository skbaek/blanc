import Blanc.Solvent
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

-- ## Pair toNat helpers

lemma B128.toNat_mk (h l : B64) :
    B128.toNat ⟨h, l⟩ = h.toNat * 2 ^ 64 + l.toNat := by
  show h.toNat <<< 64 ||| l.toNat = _
  rw [← Nat.add_eq_or Nat.two_pow_dvd_shl B64.toNat_lt, Nat.shiftLeft_eq]

lemma B256.toNat_mk (h l : B128) :
    B256.toNat ⟨h, l⟩ = h.toNat * 2 ^ 128 + l.toNat := by
  show h.toNat <<< 128 ||| l.toNat = _
  rw [← Nat.add_eq_or Nat.two_pow_dvd_shl B128.toNat_lt, Nat.shiftLeft_eq]

-- name checks (to be removed)
example (a b : UInt64) : (a * b).toNat = a.toNat * b.toNat % 2 ^ 64 :=
  UInt64.toNat_mul a b
example (a b : UInt64) : (a &&& b).toNat = a.toNat &&& b.toNat :=
  UInt64.toNat_and a b
example (n : Nat) : n &&& (2 ^ 32 - 1) = n % 2 ^ 32 :=
  Nat.and_two_pow_sub_one_eq_mod n 32

-- ## Multiplication correctness

lemma nat_and_mask32 (n : Nat) : n &&& 4294967295 = n % 4294967296 := by
  have h := Nat.and_two_pow_sub_one_eq_mod n 32
  norm_num at h
  exact h

lemma B64.toNat_mulx (x y : B64) :
    (B64.mulx x y).toNat = x.toNat * y.toNat := by
  have hX := UInt64.toNat_lt x
  have hY := UInt64.toNat_lt y
  have d1 : UInt64.toNat x / 4294967296 < 4294967296 := by omega
  have d2 : UInt64.toNat y / 4294967296 < 4294967296 := by omega
  have m1 : UInt64.toNat x % 4294967296 < 4294967296 := by omega
  have m2 : UInt64.toNat y % 4294967296 < 4294967296 := by omega
  have hP1 : UInt64.toNat x / 4294967296 * (UInt64.toNat y / 4294967296) <
      4294967296 * 4294967296 := Nat.mul_lt_mul'' d1 d2
  have hP2 : UInt64.toNat x % 4294967296 * (UInt64.toNat y / 4294967296) <
      4294967296 * 4294967296 := Nat.mul_lt_mul'' m1 d2
  have hP3 : UInt64.toNat x / 4294967296 * (UInt64.toNat y % 4294967296) <
      4294967296 * 4294967296 := Nat.mul_lt_mul'' d1 m2
  have hP4 : UInt64.toNat x % 4294967296 * (UInt64.toNat y % 4294967296) <
      4294967296 * 4294967296 := Nat.mul_lt_mul'' m1 m2
  have hexp : UInt64.toNat x * UInt64.toNat y =
      UInt64.toNat x / 4294967296 * (UInt64.toNat y / 4294967296) *
        18446744073709551616 +
      UInt64.toNat x % 4294967296 * (UInt64.toNat y / 4294967296) * 4294967296 +
      UInt64.toNat x / 4294967296 * (UInt64.toNat y % 4294967296) * 4294967296 +
      UInt64.toNat x % 4294967296 * (UInt64.toNat y % 4294967296) := by
    conv_lhs => rw [← Nat.div_add_mod (UInt64.toNat x) 4294967296,
      ← Nat.div_add_mod (UInt64.toNat y) 4294967296]
    ring
  simp only [B64.mulx, B64.highs', B64.lows']
  rw [B128.toNat_mk]
  split <;>
  · rename_i h1 h2
    simp only [decide_eq_true_eq, decide_eq_false_iff_not,
      UInt64.lt_iff_toNat_lt] at h1 h2
    simp only [B64.toNat, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_and,
      UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.reduceToNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod,
      nat_and_mask32] at h1 h2 ⊢
    omega

lemma B128.toNat_mulx (x y : B128) :
    (B128.mulx x y).toNat = x.toNat * y.toNat := by
  sorry

lemma B256.toNat_mul (x y : B256) :
    (x * y).toNat = (x.toNat * y.toNat) ↾ 256 := by
  sorry

-- ## Sum after addBal

lemma sum_addBal_eq (st : _root_.State) (a : Adr) (v : B256)
    (h : sum st.bal + v.toNat < 2 ^ 256) :
    sum (st.addBal a v).bal = sum st.bal + v.toNat := by
  have hnof : B256.Nof (st.bal a) v := by
    unfold B256.Nof; have := @le_sum st.bal a; omega
  have h1 := State.balSum_setBal st a (st.bal a + v)
  rw [B256.toNat_add_eq_of_nof _ _ hnof] at h1
  have h2 : State.balSum (st.setBal a (st.bal a + v)) =
      sum (st.addBal a v).bal := rfl
  have h3 : State.balSum st = sum st.bal := rfl
  omega

-- ## Main lemma

lemma main (wa : Adr)
    (st : _root_.State) (wds : List Withdrawal)
    (h_bound : sum st.bal + wdsum wds < 2 ^ 256)
    (h_inv : State.Inv wa st) :
    State.Inv wa (processWithdrawalsState st wds) := by
  induction wds generalizing st with
  | nil => exact h_inv
  | cons wd wds ih =>
    have h_cons : wdsum (wd :: wds) = wd.amount.toNat * 10 ^ 9 + wdsum wds := by
      simp [wdsum]
    rw [h_cons] at h_bound
    have h_val : (wd.amount * (10 ^ 9).toB256).toNat =
        wd.amount.toNat * 10 ^ 9 := by
      have h9 : (10 : Nat) ^ 9 ↾ 256 = 10 ^ 9 := Nat.lo_eq_of_lt (by omega)
      rw [B256.toNat_mul, toNat_toB256, h9, Nat.lo_eq_of_lt (by omega)]
    have h_step : processWithdrawalsState st (wd :: wds) =
        processWithdrawalsState
          (st.addBal wd.recipient (wd.amount * (10 ^ 9).toB256)) wds := rfl
    rw [h_step]
    have hb : sum st.bal + (wd.amount * (10 ^ 9).toB256).toNat < 2 ^ 256 := by
      rw [h_val]; omega
    have h_sum := sum_addBal_eq st wd.recipient _ hb
    apply ih
    · rw [h_sum, h_val]; omega
    · exact State.Inv.addBal hb h_inv
