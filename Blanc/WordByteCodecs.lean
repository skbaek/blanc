import Jaune.Types

/-! Fixed-width, big-endian byte conversions for word shifts and masks. -/

namespace Blanc.WordByteCodecs

open Jaune

/-- Keep the first sixteen bytes of a word and clear the final sixteen. -/
def high128Mask : B256 := Bytes.toB256
  [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem high128_mask_bytes (w : B256) :
    (high128Mask &&& w).toBytes = w.toBytes.take 16 ++ List.replicate 16 0 := by
  rcases w with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  change B256.toBytes ⟨⟨(-1 : UInt64) &&& a, (-1 : UInt64) &&& b⟩,
    ⟨(0 : UInt64) &&& c, (0 : UInt64) &&& d⟩⟩ = _
  rw [UInt64.neg_one_and, UInt64.neg_one_and, UInt64.zero_and, UInt64.zero_and]
  change B128.toBytes (a, b) ++ B128.toBytes (0, 0) = _
  have zeroBytes : B128.toBytes ⟨(0 : UInt64), 0⟩ = List.replicate 16 0 := rfl
  rw [zeroBytes]
  change B128.toBytes (a, b) ++ List.replicate 16 0 =
    (B128.toBytes (a, b) ++ B128.toBytes (c, d)).take 16 ++ _
  exact congrArg (fun xs => xs ++ List.replicate 16 0)
    (List.take_length_append' (B128.length_toBytes (a, b)).symm).symm

private theorem shifted_low_byte_zero (x k : UInt64)
    (lower : 8 ≤ k.toNat) (upper : k.toNat < 64) : (x <<< k).toUInt8 = 0 := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftLeft]
  rw [Nat.mod_eq_of_lt upper, Nat.shiftLeft_eq]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 64)]
  exact Nat.mod_eq_zero_of_dvd
    ((Nat.pow_dvd_pow 2 lower).trans (Nat.dvd_mul_left (2 ^ k.toNat) x.toNat))

/-- The low bytes after `SHR 64`, in ascending byte shifts, reverse the
big-endian eight-byte lane at offsets 16 through 23. -/
theorem shift64_low_bytes_reverse_slice16 (w : B256) :
    [(w >>> 64).2.2.toUInt8,
     ((w >>> 64) >>> 8).2.2.toUInt8,
     ((w >>> 64) >>> 16).2.2.toUInt8,
     ((w >>> 64) >>> 24).2.2.toUInt8,
     ((w >>> 64) >>> 32).2.2.toUInt8,
     ((w >>> 64) >>> 40).2.2.toUInt8,
     ((w >>> 64) >>> 48).2.2.toUInt8,
     ((w >>> 64) >>> 56).2.2.toUInt8] =
      (w.toBytes.sliceD 16 8 0).reverse := by
  rcases w with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  change [((0 : UInt64) ||| (c >>> 0)).toUInt8,
    ((0 : UInt64) ||| (((b <<< 0) ||| (0 : UInt64)) <<< 56 ||| (((0 : UInt64) ||| (c >>> 0)) >>> 8))).toUInt8,
    ((0 : UInt64) ||| (((b <<< 0) ||| (0 : UInt64)) <<< 48 ||| (((0 : UInt64) ||| (c >>> 0)) >>> 16))).toUInt8,
    ((0 : UInt64) ||| (((b <<< 0) ||| (0 : UInt64)) <<< 40 ||| (((0 : UInt64) ||| (c >>> 0)) >>> 24))).toUInt8,
    ((0 : UInt64) ||| (((b <<< 0) ||| (0 : UInt64)) <<< 32 ||| (((0 : UInt64) ||| (c >>> 0)) >>> 32))).toUInt8,
    ((0 : UInt64) ||| (((b <<< 0) ||| (0 : UInt64)) <<< 24 ||| (((0 : UInt64) ||| (c >>> 0)) >>> 40))).toUInt8,
    ((0 : UInt64) ||| (((b <<< 0) ||| (0 : UInt64)) <<< 16 ||| (((0 : UInt64) ||| (c >>> 0)) >>> 48))).toUInt8,
    ((0 : UInt64) ||| (((b <<< 0) ||| (0 : UInt64)) <<< 8 ||| (((0 : UInt64) ||| (c >>> 0)) >>> 56))).toUInt8] = _
  simp only [UInt64.zero_or, UInt64.or_zero, UInt64.shiftLeft_zero,
    UInt64.shiftRight_zero, UInt64.toUInt8_or]
  change _ = c.toBytes.reverse
  rw [shifted_low_byte_zero b 56 (by decide) (by decide),
    shifted_low_byte_zero b 48 (by decide) (by decide),
    shifted_low_byte_zero b 40 (by decide) (by decide),
    shifted_low_byte_zero b 32 (by decide) (by decide),
    shifted_low_byte_zero b 24 (by decide) (by decide),
    shifted_low_byte_zero b 16 (by decide) (by decide),
    shifted_low_byte_zero b 8 (by decide) (by decide)]
  simp only [UInt8.zero_or]
  simp only [UInt64.toBytes, UInt32.toBytes, UInt16.toBytes, List.cons_append,
    List.nil_append, List.reverse_cons, List.reverse_nil]
  repeat' apply congrArg₂ List.cons
  all_goals first | rfl | apply UInt8.toNat_inj.mp
  all_goals
    simp only [UInt64.toNat_toUInt8, UInt16.toNat_toUInt8,
      UInt64.toNat_toUInt32, UInt32.toNat_toUInt16,
      UInt64.toNat_shiftRight, UInt32.toNat_shiftRight, UInt16.toNat_shiftRight,
      UInt64.toNat_ofNat, UInt32.toNat_ofNat, UInt16.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]
    omega

private theorem shifted_merge_nat (x y : UInt64) :
    ((x <<< 32) ||| (y >>> 32)).toNat =
      (x.toNat % 2 ^ 32) * 2 ^ 32 + y.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo, UInt64.toNat_shiftRight]
  change ((x.toNat <<< 32) ↾ 64) ||| (y.toNat >>> 32) = _
  rw [← @Nat.lo_shl x.toNat 32 32]
  have low : y.toNat >>> 32 < 2 ^ 32 := by
    rw [Nat.shiftRight_eq_div_pow]
    have bound := UInt64.toNat_lt y
    omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt low]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.lo_eq]

/-- Left alignment of the low 160 bits produces the address bytes first. -/
theorem shift96_take20_toAdr_bytes (w : B256) :
    (w <<< 96).toBytes.take 20 = w.toAdr.toBytes := by
  rcases w with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  change ((UInt64.toBytes ((b <<< 32) ||| (c >>> 32)) ++
    UInt64.toBytes ((0 : UInt64) ||| ((c <<< 32) ||| (d >>> 32)))) ++
    (UInt64.toBytes (d <<< 32) ++ UInt64.toBytes 0)).take 20 =
      b.toUInt32.toBytes ++ (c.toBytes ++ d.toBytes)
  rw [UInt64.zero_or]
  simp only [UInt64.toBytes, UInt32.toBytes, UInt16.toBytes, List.cons_append,
    List.nil_append, List.take_succ_cons, List.take_zero]
  repeat' apply congrArg₂ List.cons
  all_goals first | rfl | apply UInt8.toNat_inj.mp
  all_goals
    simp only [UInt16.toNat_toUInt8,
      UInt64.toNat_toUInt32, UInt32.toNat_toUInt16,
      UInt64.toNat_shiftRight, UInt32.toNat_shiftRight, UInt16.toNat_shiftRight,
      UInt64.toNat_ofNat, UInt32.toNat_ofNat, UInt16.toNat_ofNat,
      shifted_merge_nat, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceMod]
    have boundC := UInt64.toNat_lt c
    have boundD := UInt64.toNat_lt d
    omega

end Blanc.WordByteCodecs
