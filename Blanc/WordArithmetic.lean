import Blanc.CommonProofs
import Jaune.MulDiv
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-!
# Fixed-width word arithmetic

Small contract-neutral bridges between natural-number division/bit tests and
the fixed-width word operations used by compiled EVM loops.
-/

namespace Blanc

open Jaune

/-! ## EVM word bounds -/

/-- The cardinality of the EVM's 256-bit word ring. -/
def wordModulusN : Nat := 2 ^ 256

/-- The greatest natural number represented by an EVM word. -/
def maxWordN : Nat := wordModulusN - 1

theorem wordModulusN_pos : 0 < wordModulusN := by
  simp [wordModulusN]

theorem maxWordN_lt_wordModulusN : maxWordN < wordModulusN := by
  unfold maxWordN
  have := wordModulusN_pos
  omega

theorem maxWord_toNat : B256.max.toNat = maxWordN := by
  decide +kernel

theorem div_two_div_pow (n k : Nat) :
    n / 2 / 2 ^ k = n / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem div_pow_div_two (n k : Nat) :
    n / 2 ^ k / 2 = n / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]

theorem one_and_toB256_eq_mod_two (n : Nat) (hn : n < 2 ^ 256) :
    ((1 : B256) &&& Nat.toB256 n) = Nat.toB256 (n % 2) := by
  apply B256.toNat_inj
  rw [B256.toNat_and, B256.toNat_toB256_of_lt hn]
  rw [B256.toNat_toB256_of_lt (by omega : n % 2 < 2 ^ 256)]
  exact Nat.one_and_eq_mod_two n

theorem toB256_add_one_of_lt (n : Nat) (hn : n + 1 < 2 ^ 256) :
    Nat.toB256 n + 1 = Nat.toB256 (n + 1) := by
  apply B256.toNat_inj
  rw [B256.toNat_add_eq_of_nof]
  · rw [B256.toNat_toB256_of_lt (by omega : n < 2 ^ 256),
      B256.toNat_toB256_of_lt hn]
    rfl
  · unfold B256.Nof
    rw [B256.toNat_toB256_of_lt (by omega : n < 2 ^ 256)]
    exact hn

theorem toUInt64_shiftRight_one (n : Nat) (hn : n < 2 ^ 64) :
    n.toUInt64 >>> (1 : Nat).toUInt64 = (n / 2).toUInt64 := by
  rw [← UInt64.toNat_inj]
  rw [UInt64.toNat_shiftRight, toNat_toUInt64]
  rw [Nat.lo_eq_of_lt hn]
  have hright : (n / 2).toUInt64.toNat = n / 2 := by
    rw [toNat_toUInt64, Nat.lo_eq_of_lt (by omega : n / 2 < 2 ^ 64)]
  rw [hright, show ((1 : Nat).toUInt64).toNat = 1 by rfl]
  norm_num [Nat.shiftRight_eq_div_pow]

theorem toB128_shiftRight_one (n : Nat) (hn : n < 2 ^ 64) :
    Nat.toB128 n >>> 1 = Nat.toB128 (n / 2) := by
  have hn64 : n >>> 64 = 0 := Nat.shiftRight_eq_zero n 64 (by omega)
  have hhalf64 : (n / 2) >>> 64 = 0 :=
    Nat.shiftRight_eq_zero (n / 2) 64 (by omega)
  have hnword : Nat.toB128 n = ((0 : UInt64), n.toUInt64) := by
    unfold Nat.toB128
    rw [hn64]
    rfl
  have hhword : Nat.toB128 (n / 2) =
      ((0 : UInt64), (n / 2).toUInt64) := by
    unfold Nat.toB128
    rw [hhalf64]
    rfl
  rw [hnword, hhword]
  change B128.shiftRight ((0 : UInt64), n.toUInt64) 1 =
    ((0 : UInt64), (n / 2).toUInt64)
  simp only [B128.shiftRight, if_false, if_true, Nat.one_ne_zero,
    Nat.reduceLT]
  apply Prod.ext
  · rfl
  · simpa only [UInt64.zero_shiftLeft, UInt64.zero_or] using
      toUInt64_shiftRight_one n hn

theorem toB256_shiftRight_one (n : Nat) (hn : n < 2 ^ 64) :
    Nat.toB256 n >>> 1 = Nat.toB256 (n / 2) := by
  have hn128 : n >>> 128 = 0 := Nat.shiftRight_eq_zero n 128 (by omega)
  have hhalf128 : (n / 2) >>> 128 = 0 :=
    Nat.shiftRight_eq_zero (n / 2) 128 (by omega)
  have hnword : Nat.toB256 n = ((0 : B128), Nat.toB128 n) := by
    unfold Nat.toB256
    rw [hn128]
    rfl
  have hhword : Nat.toB256 (n / 2) =
      ((0 : B128), Nat.toB128 (n / 2)) := by
    unfold Nat.toB256
    rw [hhalf128]
    rfl
  rw [hnword, hhword]
  change B256.shiftRight ((0 : B128), Nat.toB128 n) 1 =
    ((0 : B128), Nat.toB128 (n / 2))
  simp only [B256.shiftRight, if_false, if_true, Nat.one_ne_zero,
    Nat.reduceLT]
  apply Prod.ext
  · rfl
  · have hzeroShift : (0 : B128) <<< 127 = 0 := by
      change B128.shiftLeft ((0 : UInt64), (0 : UInt64)) 127 =
        ((0 : UInt64), (0 : UInt64))
      norm_num [B128.shiftLeft]
    rw [show 128 - 1 = 127 by omega, hzeroShift, B128.zero_or]
    exact toB128_shiftRight_one n hn

/-! ## Bitwise word projections -/

/-- Bitwise `xor` distributes over a shift-and-or split of both sides when
the low halves fit below the shift. -/
theorem Nat.xor_or_shiftLeft {a b c d k : Nat}
    (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    ((a <<< k ||| b) ^^^ (c <<< k ||| d)) =
      ((a ^^^ c) <<< k) ||| (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hi : k ≤ i
  · have hpow : (2 : Nat) ^ k ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) hi
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hd hpow)]
    simp [hi]
  · simp [hi]

theorem B128.toNat_xor (x y : B128) :
    (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by
  show ((x.1 ^^^ y.1).toNat <<< 64) ||| (x.2 ^^^ y.2).toNat = _
  rw [UInt64.toNat_xor, UInt64.toNat_xor]
  exact (Nat.xor_or_shiftLeft (UInt64.toNat_lt x.2)
    (UInt64.toNat_lt y.2)).symm

theorem B256.toNat_xor (x y : B256) :
    (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by
  show ((x.1 ^^^ y.1).toNat <<< 128) ||| (x.2 ^^^ y.2).toNat = _
  rw [B128.toNat_xor, B128.toNat_xor]
  exact (Nat.xor_or_shiftLeft (B128.toNat_lt (x := x.2))
    (B128.toNat_lt (x := y.2))).symm

/-! ## Newton inverse refinement -/

/-- The four-bit inverse seed used by full-width unsigned division. -/
def inverseSeedWord (denominator : B256) : B256 :=
  3 * denominator ^^^ 2

/-- One Newton refinement in the EVM word ring. -/
def inverseNewtonStepWord (denominator inverse : B256) : B256 :=
  inverse * (2 - inverse * denominator)

/-- Repeated Newton refinement in the EVM word ring. -/
def inverseNewtonIter (denominator : B256) : Nat → B256 → B256
  | 0, inverse => inverse
  | count + 1, inverse =>
      inverseNewtonIter denominator count
        (inverseNewtonStepWord denominator inverse)

/-- A Newton inverse step squares the modulus on which the inverse is known. -/
theorem newtonStep_modEq_square
    (denominator inverse modulus : Int)
    (inverseCorrect :
      denominator * inverse ≡ 1 [ZMOD modulus]) :
    denominator * (inverse * (2 - denominator * inverse)) ≡ 1
      [ZMOD modulus * modulus] := by
  rw [Int.modEq_iff_dvd] at inverseCorrect ⊢
  rcases inverseCorrect with ⟨factor, factorEq⟩
  refine ⟨factor * factor, ?_⟩
  rw [show
      1 - denominator * (inverse * (2 - denominator * inverse)) =
        (1 - denominator * inverse) * (1 - denominator * inverse) by
      ring,
    factorEq]
  ring

/-- Word multiplication agrees with unbounded multiplication modulo the EVM
word modulus. -/
theorem b256_mul_modEq_wordModulus (x y : B256) :
    ((x * y).toNat : Int) ≡
      (x.toNat * y.toNat : Nat)
      [ZMOD (wordModulusN : Int)] := by
  rw [Int.natCast_modEq_iff]
  rw [B256.toNat_mul_mod]
  exact Nat.mod_modEq _ _

/-- Word subtraction agrees with integer subtraction modulo the EVM word
modulus, including the wrapped branch. -/
theorem b256_sub_modEq_wordModulus (x y : B256) :
    ((x - y).toNat : Int) ≡
      (x.toNat : Int) - (y.toNat : Int)
      [ZMOD (wordModulusN : Int)] := by
  rw [Int.modEq_iff_dvd]
  by_cases h : y ≤ x
  · have hnat : y.toNat ≤ x.toNat := B256.toNat_le_toNat h
    rw [B256.toNat_sub_eq_of_le x y h, Nat.cast_sub hnat]
    simp
  · have hltWord : x < y := B256.not_le.mp h
    have hlt : x.toNat < y.toNat := B256.toNat_lt_toNat hltWord
    have hsum : y.toNat ≤ wordModulusN + x.toNat := by
      have yBound := B256.toNat_lt y
      unfold wordModulusN
      omega
    have hbound :
        wordModulusN + x.toNat - y.toNat < wordModulusN := by
      omega
    rw [B256.toNat_sub]
    change (wordModulusN : Int) ∣
      (x.toNat : Int) - (y.toNat : Int) -
        ↑((wordModulusN + x.toNat - y.toNat) ↾ 256)
    rw [Nat.lo_eq_of_lt hbound, Nat.cast_sub hsum, Nat.cast_add]
    ring_nf
    exact Int.dvd_neg.mpr (dvd_refl (wordModulusN : Int))

/-- The exact word update represents the algebraic Newton update modulo
`2^256`. -/
theorem inverseNewtonStepWord_modEq_wordModulus
    (denominator inverse : B256) :
    ((inverseNewtonStepWord denominator inverse).toNat : Int) ≡
      (inverse.toNat : Int) *
        (2 - (inverse.toNat : Int) * (denominator.toNat : Int))
      [ZMOD (wordModulusN : Int)] := by
  have product := b256_mul_modEq_wordModulus inverse denominator
  have difference :=
    b256_sub_modEq_wordModulus (2 : B256) (inverse * denominator)
  have two : ((2 : B256).toNat : Int) = 2 := rfl
  have difference' :
      (((2 : B256) - inverse * denominator).toNat : Int) ≡
        2 - (inverse.toNat : Int) * (denominator.toNat : Int)
        [ZMOD (wordModulusN : Int)] := by
    apply difference.trans
    rw [two]
    exact (Int.ModEq.refl 2).sub product
  unfold inverseNewtonStepWord
  exact (b256_mul_modEq_wordModulus inverse
      ((2 : B256) - inverse * denominator)).trans
    ((Int.ModEq.refl (inverse.toNat : Int)).mul difference')

/-- A word-level Newton step squares any correctness modulus whose square
divides the EVM word modulus. -/
theorem inverseNewtonStepWord_modEq_square
    {denominator inverse : B256} {modulus : Int}
    (squareDvdWord : modulus * modulus ∣ (wordModulusN : Int))
    (inverseCorrect :
      (denominator.toNat : Int) * (inverse.toNat : Int) ≡ 1
        [ZMOD modulus]) :
    (denominator.toNat : Int) *
        ((inverseNewtonStepWord denominator inverse).toNat : Int) ≡ 1
      [ZMOD modulus * modulus] := by
  have stepCongruence :=
    (inverseNewtonStepWord_modEq_wordModulus denominator inverse).of_dvd
      squareDvdWord
  have lifted :=
    (Int.ModEq.refl (denominator.toNat : Int)).mul stepCongruence
  apply lifted.trans
  simpa [Int.mul_comm (inverse.toNat : Int) (denominator.toNat : Int)] using
    newtonStep_modEq_square (denominator.toNat : Int)
      (inverse.toNat : Int) modulus inverseCorrect

/-- Six word-level Newton refinements lift a four-bit inverse seed to a full
inverse modulo `2^256`. -/
theorem inverseNewtonIter_six_modEq
    {denominator seed : B256}
    (seedCorrect :
      (denominator.toNat : Int) * (seed.toNat : Int) ≡ 1 [ZMOD 16]) :
    (denominator.toNat : Int) *
        ((inverseNewtonIter denominator 6 seed).toNat : Int) ≡ 1
      [ZMOD (wordModulusN : Int)] := by
  have h1 := inverseNewtonStepWord_modEq_square
    (denominator := denominator) (inverse := seed) (modulus := 16)
    (by norm_num [wordModulusN]) seedCorrect
  have h2 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator seed)
    (modulus := 256) (by norm_num [wordModulusN]) h1
  have h3 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator
      (inverseNewtonStepWord denominator seed))
    (modulus := 65536) (by norm_num [wordModulusN]) h2
  have h4 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator
      (inverseNewtonStepWord denominator
        (inverseNewtonStepWord denominator seed)))
    (modulus := 4294967296) (by norm_num [wordModulusN]) h3
  have h5 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator
      (inverseNewtonStepWord denominator
        (inverseNewtonStepWord denominator
          (inverseNewtonStepWord denominator seed))))
    (modulus := 18446744073709551616)
    (by norm_num [wordModulusN]) h4
  have h6 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator
      (inverseNewtonStepWord denominator
        (inverseNewtonStepWord denominator
          (inverseNewtonStepWord denominator
            (inverseNewtonStepWord denominator seed)))))
    (modulus := 340282366920938463463374607431768211456)
    (by norm_num [wordModulusN]) h5
  simpa [inverseNewtonIter, wordModulusN] using h6

private theorem inverseSeedNat_mod_sixteen
    (n : Nat) (odd : n % 2 = 1) :
    (n * ((3 * n) ^^^ 2)) % 16 = 1 := by
  have h16 : n % 16 < 16 := Nat.mod_lt _ (by omega)
  have hodd16 : (n % 16) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by omega : 2 ∣ 16)]
    exact odd
  rw [Nat.mul_mod n ((3 * n) ^^^ 2) 16]
  rw [show 16 = 2 ^ 4 by norm_num, Nat.xor_mod_two_pow]
  rw [← show 16 = 2 ^ 4 by norm_num]
  rw [Nat.mul_mod 3 n 16]
  change
    (n % 16 * (((3 * (n % 16)) % 16) ^^^ 2)) % 16 = 1
  generalize n % 16 = r at h16 hodd16 ⊢
  have hr :
      r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨
      r = 9 ∨ r = 11 ∨ r = 13 ∨ r = 15 := by
    omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem inverseSeedWord_mod_sixteen (denominator : B256) :
    (inverseSeedWord denominator).toNat % 16 =
      ((3 * denominator.toNat) ^^^ 2) % 16 := by
  unfold inverseSeedWord
  rw [B256.toNat_xor, B256.toNat_mul_mod]
  change
    ((((3 * denominator.toNat) % (2 ^ 256)) ^^^ 2) % (2 ^ 4)) =
      (((3 * denominator.toNat) ^^^ 2) % (2 ^ 4))
  simp only [Nat.xor_mod_two_pow]
  rw [Nat.mod_mod_of_dvd]
  norm_num

/-- For every odd word, `(3 * denominator) xor 2` is an inverse modulo
`16`. -/
theorem inverseSeedWord_modEq_sixteen
    {denominator : B256} (odd : denominator.toNat % 2 = 1) :
    (denominator.toNat : Int) *
        ((inverseSeedWord denominator).toNat : Int) ≡ 1 [ZMOD 16] := by
  change
    ((denominator.toNat *
      (inverseSeedWord denominator).toNat : Nat) : Int) ≡
        ((1 : Nat) : Int) [ZMOD ((16 : Nat) : Int)]
  rw [Int.natCast_modEq_iff]
  change
    (denominator.toNat * (inverseSeedWord denominator).toNat) % 16 = 1
  rw [Nat.mul_mod]
  rw [inverseSeedWord_mod_sixteen]
  have h := inverseSeedNat_mod_sixteen denominator.toNat odd
  rw [Nat.mul_mod denominator.toNat
    ((3 * denominator.toNat) ^^^ 2) 16] at h
  exact h

/-- Six Newton refinements of the standard seed invert any odd EVM word
modulo the full word modulus. -/
theorem inverseNewtonIter_six_seed_modEq_wordModulus
    {denominator : B256} (odd : denominator.toNat % 2 = 1) :
    (denominator.toNat : Int) *
        ((inverseNewtonIter denominator 6
          (inverseSeedWord denominator)).toNat : Int) ≡ 1
      [ZMOD (wordModulusN : Int)] :=
  inverseNewtonIter_six_modEq (inverseSeedWord_modEq_sixteen odd)

end Blanc
