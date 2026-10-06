import Blanc.CommonProofs

/-! Bounded-width masks on EVM words. -/
namespace Blanc.Lift.PackedWord
open Jaune

/-- Masking the low `k` bits gives the natural residue, including `k = 256`. -/
theorem lowMask_toNat (word : B256) {k : Nat} (width : k ≤ 256) :
    (word &&& (2 ^ k - 1).toB256).toNat = word.toNat % 2 ^ k := by
  have positive : 0 < 2 ^ k := Nat.two_pow_pos k
  have bounded : 2 ^ k ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) width
  have maskBound : 2 ^ k - 1 < 2 ^ 256 := by omega
  rw [B256.toNat_and, B256.toNat_toB256_of_lt maskBound,
    Nat.and_two_pow_sub_one_eq_mod]

/-- A bounded word is unchanged by its low-bit mask. -/
theorem lowMask_eq_self_of_lt {word : B256} {k : Nat} (width : k ≤ 256)
    (bounded : word.toNat < 2 ^ k) : word &&& (2 ^ k - 1).toB256 = word := by
  apply B256.toNat_inj
  rw [lowMask_toNat word width, Nat.mod_eq_of_lt bounded]

/-- Low-bit subtraction is modular at the field width, even when the full
word subtraction borrows. -/
theorem lowMask_sub_toNat {x y : B256} {k : Nat} (width : k ≤ 256)
    (hy : y.toNat < 2 ^ k) :
    ((x - y) &&& (2 ^ k - 1).toB256).toNat =
      (x.toNat + 2 ^ k - y.toNat) % 2 ^ k := by
  have powEq : 2 ^ 256 = 2 ^ (256 - k) * 2 ^ k := by
    rw [← Nat.pow_add, Nat.sub_add_cancel width]
  have divided : 2 ^ k ∣ 2 ^ 256 := ⟨2 ^ (256 - k), by rw [Nat.mul_comm]; exact powEq⟩
  have positive : 0 < 2 ^ (256 - k) := Nat.two_pow_pos _
  have shift : 2 ^ 256 + x.toNat - y.toNat =
      (2 ^ (256 - k) - 1) * 2 ^ k + (x.toNat + 2 ^ k - y.toNat) := by
    rw [Nat.mul_sub_right_distrib, Nat.one_mul, ← powEq]
    have bound : 2 ^ k ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) width
    omega
  rw [lowMask_toNat _ width, B256.toNat_sub, Nat.lo_eq,
    Nat.mod_mod_of_dvd _ divided, shift, Nat.add_mod, Nat.mul_mod,
    Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]

end Blanc.Lift.PackedWord
