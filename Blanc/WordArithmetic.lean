import Blanc.CommonProofs

/-!
# Fixed-width word arithmetic

Small contract-neutral bridges between natural-number division/bit tests and
the fixed-width word operations used by compiled EVM loops.
-/

namespace Blanc

open Jaune

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

end Blanc
