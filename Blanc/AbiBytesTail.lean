import Blanc.CommonProofs.MemImage

/-! # Length-delimited ABI byte-tail cancellation -/

namespace Blanc

open Jaune

theorem abiBytesTail_length (data : Bytes) :
    (abiBytesTail data).length = 32 + ceil32 data.length := by
  simp only [abiBytesTail, List.length_append, B256.length_toBytes,
    List.length_replicate]
  have hle := Nat.le_ceil32 data.length
  omega

theorem abiBytesTail_append_inj {a b ra rb : Bytes}
    (ha : a.length < 2 ^ 256) (hb : b.length < 2 ^ 256)
    (heq : abiBytesTail a ++ ra = abiBytesTail b ++ rb) :
    a = b ∧ ra = rb := by
  have htake : ∀ x r : Bytes,
      ((abiBytesTail x ++ r).take 32) = (Nat.toB256 x.length).toBytes := by
    intro x r
    simp only [abiBytesTail, List.append_assoc]
    rw [List.take_left' (B256.length_toBytes _)]
  have hw : (Nat.toB256 a.length).toBytes = (Nat.toB256 b.length).toBytes := by
    have h := congrArg (List.take 32) heq
    rwa [htake, htake] at h
  have hlen : a.length = b.length := by
    have h := congrArg (fun bs => (Bytes.toB256 bs).toNat) hw
    rwa [B256.toB256_toBytes, B256.toB256_toBytes,
      B256.toNat_toB256_of_lt ha, B256.toNat_toB256_of_lt hb] at h
  have htail_len : (abiBytesTail a).length = (abiBytesTail b).length := by
    rw [abiBytesTail_length, abiBytesTail_length, hlen]
  obtain ⟨htail, hr⟩ := List.append_inj heq htail_len
  rw [abiBytesTail, abiBytesTail, hlen] at htail
  have hpad := (List.append_inj (by simpa only [List.append_assoc] using htail) rfl).2
  exact ⟨(List.append_inj hpad hlen).1, hr⟩

end Blanc
