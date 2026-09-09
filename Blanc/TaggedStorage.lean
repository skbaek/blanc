import Blanc.CommonProofs

/-! A bounded tag/payload algebra for logical storage keys. -/

namespace Blanc.TaggedStorage

open Jaune

/-- The low 252-bit payload mask used by four-bit logical storage tags. -/
def low252Mask : B256 := Nat.toB256 (2 ^ 252 - 1)

/-- Place a natural-number tag in the high four bits of a word. -/
def regionWord (region : Nat) : B256 := Nat.toB256 (region * 2 ^ 252)

/-- Encode a tag and a payload, discarding payload bits above bit 251. -/
def encode (region : Nat) (payload : B256) : B256 :=
  B256.or (regionWord region) (payload &&& low252Mask)

private theorem payload_and_low252Mask {payload : B256}
    (hpayload : payload.toNat < 2 ^ 252) :
    payload &&& low252Mask = payload := by
  apply B256.toNat_inj
  rw [B256.toNat_and, low252Mask,
    B256.toNat_toB256_of_lt (by norm_num : 2 ^ 252 - 1 < 2 ^ 256)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 252
  · simp [hi]
  · rw [Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hpayload
        (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hi]

/-- A payload already below the 252-bit boundary is unchanged by masking. -/
theorem encode_eq_of_payload_lt {region : Nat} {payload : B256}
    (hpayload : payload.toNat < 2 ^ 252) :
    encode region payload = B256.or (regionWord region) payload := by
  rw [encode, payload_and_low252Mask hpayload]

private theorem toB256_or (a b : Nat) :
    Nat.toB256 (a ||| b) =
      B256.or (Nat.toB256 a) (Nat.toB256 b) := by
  simp only [Nat.toB256, B256.or, Nat.shiftRight_or_distrib, toB128_or]

/-- Numeric form of a bounded tag/payload encoding. -/
theorem encode_toNat_of_bounds
    {region : Nat} {payload : B256}
    (hregion : region < 16) (hpayload : payload.toNat < 2 ^ 252) :
    (encode region payload).toNat =
      region * 2 ^ 252 + payload.toNat := by
  rw [encode_eq_of_payload_lt hpayload, regionWord]
  have hdiv : 2 ^ 252 ∣ region * 2 ^ 252 := Nat.dvd_mul_left _ _
  have hor :
      region * 2 ^ 252 ||| payload.toNat =
        region * 2 ^ 252 + payload.toNat :=
    (Nat.add_eq_or hdiv hpayload).symm
  have hsum :
      region * 2 ^ 252 + payload.toNat < 2 ^ 256 := by
    calc
      region * 2 ^ 252 + payload.toNat <
          region * 2 ^ 252 + 2 ^ 252 :=
        Nat.add_lt_add_left hpayload _
      _ = (region + 1) * 2 ^ 252 := by omega
      _ ≤ 16 * 2 ^ 252 :=
        Nat.mul_le_mul_right (2 ^ 252) (Nat.succ_le_iff.mpr hregion)
      _ = 2 ^ 256 := by
        rw [show 256 = 4 + 252 by omega, pow_add]
        norm_num
  have horlt :
      region * 2 ^ 252 ||| payload.toNat < 2 ^ 256 := by
    rwa [hor]
  calc
    (B256.or (Nat.toB256 (region * 2 ^ 252)) payload).toNat =
        (B256.or (Nat.toB256 (region * 2 ^ 252))
          (Nat.toB256 payload.toNat)).toNat := by
      rw [toB256_toNat]
    _ = (Nat.toB256
          (region * 2 ^ 252 ||| payload.toNat)).toNat := by
      rw [toB256_or]
    _ = region * 2 ^ 252 ||| payload.toNat :=
      B256.toNat_toB256_of_lt horlt
    _ = region * 2 ^ 252 + payload.toNat := hor

/-- Within the four-bit tag range, encoding is injective in a bounded payload. -/
theorem encode_injective_of_payload_lt
    {region : Nat} {left right : B256}
    (hregion : region < 16)
    (hleft : left.toNat < 2 ^ 252)
    (hright : right.toNat < 2 ^ 252)
    (hencode : encode region left = encode region right) :
    left = right := by
  apply B256.toNat_inj
  have hnat := congrArg B256.toNat hencode
  rw [encode_toNat_of_bounds hregion hleft,
    encode_toNat_of_bounds hregion hright] at hnat
  omega

/-- Distinct four-bit tags encode to distinct words for bounded payloads. -/
theorem encode_ne_of_region_ne
    {leftRegion rightRegion : Nat} {left right : B256}
    (hlr : leftRegion < 16) (hrr : rightRegion < 16)
    (hleft : left.toNat < 2 ^ 252)
    (hright : right.toNat < 2 ^ 252)
    (hne : leftRegion ≠ rightRegion) :
    encode leftRegion left ≠ encode rightRegion right := by
  intro hencode
  apply hne
  have hnat := congrArg B256.toNat hencode
  rw [encode_toNat_of_bounds hlr hleft,
    encode_toNat_of_bounds hrr hright] at hnat
  omega

end Blanc.TaggedStorage
