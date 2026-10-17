import Blanc.Lift.WalkCutKit
import Blanc.Lift.Usdc.FootprintLedger
import Blanc.WordArithmetic

/-!
# Reading FiatTokenV2_2's packed storage words after the admin calls' writes (U6f)

The admin calls write whole words built by masking (`CLR20 &&& w`, `a ||| hi96 &&& w`, …); the
ledger (`Blanc/Lift/Usdc/Footprint.lean`) reads fields of them (`toAdr`, `flag20`, `boolBit`,
`balanceBits`, `frozenBit`).  A field is a bit range of the word's natural number (`field_eq`), so
each read reduces to closed facts about the constant masks' bits, decided.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-! ## Bit ranges -/

/-- A field of a number is determined by its bits in the field's range. -/
theorem field_eq {w y lo n : Nat} (h : ∀ i < n, w.testBit (lo + i) = y.testBit (lo + i)) :
    w / 2 ^ lo % 2 ^ n = y / 2 ^ lo % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hi : i < n
  · rw [Nat.add_comm i lo, h i hi]
  · simp only [hi, decide_false, Bool.false_and]

/-- Keep: a mask of ones over the range, a constant of zeros there. -/
theorem field_or_and_keep {c m y lo n : Nat} (hc : ∀ i < n, c.testBit (lo + i) = false)
    (hm : ∀ i < n, m.testBit (lo + i) = true) :
    (c ||| (m &&& y)) / 2 ^ lo % 2 ^ n = y / 2 ^ lo % 2 ^ n :=
  field_eq fun i hi => by
    rw [Nat.testBit_or, Nat.testBit_and, hc i hi, hm i hi, Bool.false_or, Bool.true_and]

/-- Overwrite: a mask of zeros over the range. -/
theorem field_or_and_const {c m y lo n : Nat} (hm : ∀ i < n, m.testBit (lo + i) = false) :
    (c ||| (m &&& y)) / 2 ^ lo % 2 ^ n = c / 2 ^ lo % 2 ^ n :=
  field_eq fun i hi => by
    rw [Nat.testBit_or, Nat.testBit_and, hm i hi, Bool.false_and, Bool.or_false]

theorem mod_eq_field (w n : Nat) : w % 2 ^ n = w / 2 ^ 0 % 2 ^ n := by
  rw [Nat.pow_zero, Nat.div_one]

/-! ## The ledger's field reads, as bit ranges -/

theorem toAdr_eq_of_mod {x y : B256} (h : x.toNat % 2 ^ 160 = y.toNat % 2 ^ 160) :
    x.toAdr = y.toAdr := by
  have hx : (ff20 &&& x).toNat = x.toNat % 2 ^ 160 := by
    rw [B256.toNat_and, show (ff20 : B256).toNat = 2 ^ 160 - 1 from by decide, Nat.and_comm,
      Nat.and_two_pow_sub_one_eq_mod]
  have hy : (ff20 &&& y).toNat = y.toNat % 2 ^ 160 := by
    rw [B256.toNat_and, show (ff20 : B256).toNat = 2 ^ 160 - 1 from by decide, Nat.and_comm,
      Nat.and_two_pow_sub_one_eq_mod]
  have e : ff20 &&& x = ff20 &&& y := B256.toNat_inj _ _ (by rw [hx, hy, h])
  rw [ff20_and_word, ff20_and_word] at e
  have := congrArg B256.toAdr e
  rwa [toAdr_toB256, toAdr_toB256] at this

theorem flag20_eq_of {x y : B256} (h : x.toNat / 2 ^ 160 % 2 ^ 8 = y.toNat / 2 ^ 160 % 2 ^ 8) :
    flag20 x = flag20 y := by
  unfold flag20
  rw [show (256 : Nat) = 2 ^ 8 from rfl, h]

theorem balanceBits_eq_of {x y : B256}
    (h : x.toNat / 2 ^ 0 % 2 ^ 255 = y.toNat / 2 ^ 0 % 2 ^ 255) :
    balanceBits x = balanceBits y := by
  unfold balanceBits
  rw [mod_eq_field, h, ← mod_eq_field]

theorem frozenBit_eq_field (x : B256) : frozenBit x = decide (x.toNat / 2 ^ 255 % 2 ^ 1 = 1) := by
  unfold frozenBit
  have hlt := B256.toNat_lt x
  have hd : x.toNat / 2 ^ 255 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 255)]
    omega
  have : (2 ^ 255 ≤ x.toNat) ↔ x.toNat / 2 ^ 255 % 2 ^ 1 = 1 := by
    rw [Nat.pow_one, Nat.mod_eq_of_lt hd]
    constructor
    · intro h
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 255)).mpr (by omega : 1 * 2 ^ 255 ≤ x.toNat)
      omega
    · intro h
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 255)).mp (by omega : 1 ≤ x.toNat / 2 ^ 255)
      omega
  exact decide_eq_decide.mpr this

theorem Adr.toB256_toNat_lt (a : Adr) : a.toB256.toNat < 2 ^ 160 := by
  rw [← ff20_and_adr a, B256.toNat_and, show (ff20 : B256).toNat = 2 ^ 160 - 1 from by decide,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos 160)

theorem Adr.toB256_testBit (a : Adr) {i : Nat} (hi : 160 ≤ i) : a.toB256.toNat.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (Adr.toB256_toNat_lt a) (Nat.pow_le_pow_right (by decide) hi))


theorem toNat_shr255 (y : B256) : (y >>> (255 : Nat)).toNat = y.toNat / 2 ^ 255 := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := y
  show B256.toNat (B256.shiftRight ((a, b), (c, d)) 255) = B256.toNat ((a, b), (c, d)) / 2 ^ 255
  have e : B256.shiftRight ((a, b), (c, d)) 255 = ((0, 0), (0, a >>> (63 : UInt64))) := rfl
  rw [e]
  simp only [B256.toNat, B128.toNat, UInt64.toNat_zero, Nat.zero_shiftLeft, Nat.zero_or,
    UInt64.toNat_shiftRight]
  rw [show (63 : UInt64).toNat % 64 = 63 from rfl, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_or_distrib, Nat.shiftRight_or_distrib,
    show (255 : Nat) = 128 + 127 from rfl, Nat.shiftRight_add, Nat.shiftLeft_shiftRight,
    Nat.shiftRight_or_distrib, show (127 : Nat) = 64 + 63 from rfl, Nat.shiftRight_add (a.toNat <<< 64),
    Nat.shiftLeft_shiftRight]
  have hb : b.toNat >>> (64 + 63) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt (lt_of_lt_of_le (UInt64.toNat_lt _) (by decide))
  have hc : (c.toNat <<< 64 ||| d.toNat) >>> (128 + (64 + 63)) = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le (B128.toNat_lt (x := (c, d))) (by decide))
  rw [hb, Nat.or_zero, ← Nat.shiftRight_or_distrib, hc, Nat.or_zero]


/-! ## The masks of the admin calls' writes -/

/-- `paused` in slot 1 set: bit 160. -/
abbrev bit160 : B256 := Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Slot 1 with its `paused` byte cleared. -/
abbrev clr20 : B256 := Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 255,
  255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255]
/-- A word with its low byte cleared. -/
abbrev clr0 : B256 := Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
  255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0]
/-- The blacklist flag: bit 255. -/
abbrev bit255 : B256 := Bytes.toB256 [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem toAdr_pauseWord (y : B256) : (bit160 ||| clr20 &&& y).toAdr = y.toAdr := by
  apply toAdr_eq_of_mod
  rw [B256.toNat_or, B256.toNat_and, mod_eq_field, mod_eq_field y.toNat]
  exact field_or_and_keep (by decide +kernel) (by decide +kernel)

theorem flag20_pauseWord (y : B256) : flag20 (bit160 ||| clr20 &&& y) = true := by
  have h : (bit160 ||| clr20 &&& y).toNat / 2 ^ 160 % 2 ^ 8 = 1 := by
    rw [B256.toNat_or, B256.toNat_and, field_or_and_const (by decide +kernel)]
    decide
  unfold flag20
  rw [show (256 : Nat) = 2 ^ 8 from rfl, h]
  rfl

theorem toAdr_unpauseWord (y : B256) : (clr20 &&& y).toAdr = y.toAdr := by
  apply toAdr_eq_of_mod
  rw [B256.toNat_and, mod_eq_field, mod_eq_field y.toNat, ← Nat.zero_or (_ &&& _)]
  exact field_or_and_keep (by decide +kernel) (by decide +kernel)

theorem flag20_unpauseWord (y : B256) : flag20 (clr20 &&& y) = false := by
  have h : (clr20 &&& y).toNat / 2 ^ 160 % 2 ^ 8 = 0 := by
    rw [B256.toNat_and, ← Nat.zero_or (_ &&& _), field_or_and_const (by decide +kernel)]
    decide
  unfold flag20
  rw [show (256 : Nat) = 2 ^ 8 from rfl, h]
  rfl

theorem toAdr_addrWord (a : Adr) (y : B256) : (a.toB256 ||| hi96 &&& y).toAdr = a := by
  conv => rhs; rw [← toAdr_toB256 a]
  apply toAdr_eq_of_mod
  rw [B256.toNat_or, B256.toNat_and, mod_eq_field, mod_eq_field a.toB256.toNat]
  exact field_or_and_const (by decide +kernel)

theorem flag20_addrWord (a : Adr) (y : B256) : flag20 (a.toB256 ||| hi96 &&& y) = flag20 y := by
  apply flag20_eq_of
  rw [B256.toNat_or, B256.toNat_and]
  exact field_or_and_keep (fun i _ => Adr.toB256_testBit a (by omega)) (by decide +kernel)

theorem boolBit_clearWord (y : B256) : boolBit (clr0 &&& y) = false := by
  have h : (clr0 &&& y).toNat / 2 ^ 0 % 2 ^ 8 = 0 := by
    rw [B256.toNat_and, ← Nat.zero_or (_ &&& _), field_or_and_const (by decide +kernel)]
    decide
  unfold boolBit
  rw [show (256 : Nat) = 2 ^ 8 from rfl, mod_eq_field, h]
  rfl

theorem boolBit_setWord (y : B256) : boolBit ((1 : B256) ||| clr0 &&& y) = true := by
  rw [show (1 : B256) = Bytes.toB256 [1] from by decide]
  have h : (Bytes.toB256 [1] ||| clr0 &&& y).toNat / 2 ^ 0 % 2 ^ 8 = 1 := by
    rw [B256.toNat_or, B256.toNat_and, field_or_and_const (by decide +kernel)]
    decide
  unfold boolBit
  rw [show (256 : Nat) = 2 ^ 8 from rfl, mod_eq_field, h]
  rfl

theorem balanceBits_blacklistWord (y : B256) : balanceBits (bit255 ||| y) = balanceBits y := by
  apply balanceBits_eq_of
  rw [B256.toNat_or]
  refine field_eq fun i hi => ?_
  rw [Nat.testBit_or, (by decide +kernel : ∀ i < 255, (bit255 : B256).toNat.testBit (0 + i) = false) i hi,
    Bool.false_or]

theorem frozenBit_blacklistWord (y : B256) : frozenBit (bit255 ||| y) = true := by
  rw [frozenBit_eq_field]
  have h : (bit255 ||| y).toNat / 2 ^ 255 % 2 ^ 1 = 1 := by
    rw [show (1 : Nat) = (bit255 : B256).toNat / 2 ^ 255 % 2 ^ 1 from by decide +kernel, B256.toNat_or]
    conv => rhs; rw [← Nat.or_self (bit255 : B256).toNat]
    refine field_eq fun i hi => ?_
    rw [Nat.testBit_or, Nat.testBit_or, (by decide +kernel : ∀ i < 1,
      (bit255 : B256).toNat.testBit (255 + i) = true) i hi, Bool.true_or, Bool.true_or]
  rw [h]
  rfl

theorem balanceBits_unBlacklistWord (y : B256) : balanceBits (lo255 &&& y) = balanceBits y := by
  apply balanceBits_eq_of
  rw [B256.toNat_and, ← Nat.zero_or (_ &&& _)]
  exact field_or_and_keep (by decide +kernel) (by decide +kernel)

theorem frozenBit_unBlacklistWord (y : B256) : frozenBit (lo255 &&& y) = false := by
  rw [frozenBit_eq_field]
  have h : (lo255 &&& y).toNat / 2 ^ 255 % 2 ^ 1 = 0 := by
    rw [B256.toNat_and, ← Nat.zero_or (_ &&& _), field_or_and_const (by decide +kernel)]
    decide
  rw [h]
  rfl

theorem balanceBits_of_le {x : B256} (h : B256.gtCheck x lo255 = 0) : balanceBits x = x.toNat := by
  have := toNat_le_of_gtCheck_eq_zero h
  rw [show (lo255 : B256).toNat = 2 ^ 255 - 1 from by decide +kernel] at this
  unfold balanceBits
  exact Nat.mod_eq_of_lt (by omega)

theorem frozenBit_of_le {x : B256} (h : B256.gtCheck x lo255 = 0) : frozenBit x = false := by
  have := toNat_le_of_gtCheck_eq_zero h
  rw [show (lo255 : B256).toNat = 2 ^ 255 - 1 from by decide +kernel] at this
  unfold frozenBit
  exact decide_eq_false (by omega)

/-! ## The guards the admin calls read -/

theorem flag20_of_notPaused {y : B256} (h : (Bytes.toB256 [255] &&& y / bit160) =? 0 ≠ 0) :
    flag20 y = false := by
  have e := congrArg B256.toNat (eq_of_eqCheck_ne_zero h)
  rw [B256.toNat_and, B256.toNat_div (by decide), show (Bytes.toB256 [255]).toNat = 2 ^ 8 - 1 from
    by decide, show (bit160 : B256).toNat = 2 ^ 160 from by decide +kernel, B256.toNat_zero,
    Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod] at e
  unfold flag20
  rw [show (256 : Nat) = 2 ^ 8 from rfl, e]
  rfl

theorem boolBit_of_ne {y : B256} (h : Bytes.toB256 [255] &&& y ≠ 0) : boolBit y = true := by
  unfold boolBit
  refine decide_eq_true fun hy => h (B256.toNat_inj _ _ ?_)
  rw [B256.toNat_and, show (Bytes.toB256 [255]).toNat = 2 ^ 8 - 1 from by decide, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod, B256.toNat_zero]
  exact hy

theorem frozenBit_of_free {y : B256} (h : (Bytes.toB256 [1] =? (y >>> (Bytes.toB256 [255]).toNat)) = 0) :
    frozenBit y = false := by
  have hne := ne_of_eqCheck_eq_zero h
  rw [show (Bytes.toB256 [255]).toNat = 255 from by decide] at hne
  rw [frozenBit_eq_field]
  refine decide_eq_false fun h1 => hne ?_
  apply B256.toNat_inj
  rw [toNat_shr255, show (Bytes.toB256 [1]).toNat = 1 from by decide]
  have hlt := B256.toNat_lt y
  have hd : y.toNat / 2 ^ 255 < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 255)]
    omega
  rw [Nat.pow_one, Nat.mod_eq_of_lt hd] at h1
  exact h1.symm

end Blanc.Lift.Usdc
