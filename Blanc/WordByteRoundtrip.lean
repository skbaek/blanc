import Blanc.CommonProofs

/-! Reverse fixed-width limb encoding through the public complete-word codec. -/

namespace Blanc.Bytes

open Jaune

/-- Decoding exactly eight big-endian bytes into a limb preserves every byte. -/
theorem toBytes_toUInt64_of_length {xs : Jaune.Bytes} (h : xs.length = 8) :
    (Jaune.Bytes.toUInt64 xs).toBytes = xs := by
  rcases xs with _ | ⟨a0, xs⟩
  · cases h
  rcases xs with _ | ⟨a1, xs⟩
  · cases h
  rcases xs with _ | ⟨a2, xs⟩
  · cases h
  rcases xs with _ | ⟨a3, xs⟩
  · cases h
  rcases xs with _ | ⟨a4, xs⟩
  · cases h
  rcases xs with _ | ⟨a5, xs⟩
  · cases h
  rcases xs with _ | ⟨a6, xs⟩
  · cases h
  rcases xs with _ | ⟨a7, xs⟩
  · cases h
  have tailNil : xs = [] := List.eq_nil_of_length_eq_zero
    (Nat.add_right_cancel (show xs.length + 8 = 0 + 8 from by
      simpa only [List.length_cons, Nat.add_assoc] using h))
  subst xs
  let padded : Jaune.Bytes := [a0, a1, a2, a3, a4, a5, a6, a7] ++
    (0 : UInt64).toBytes ++ (0 : UInt64).toBytes ++ (0 : UInt64).toBytes
  have length32 : padded.length = 32 := rfl
  have word := toBytes_toB256_of_length length32
  have lane := congrArg (fun bs : Jaune.Bytes => bs.take 8) word
  dsimp only [padded] at lane
  simp only [List.cons_append, List.nil_append, Jaune.Bytes.toB256] at lane
  rw [Jaune.Bytes.toB256_go_eight_cons] at lane
  rw [List.append_assoc, Jaune.Bytes.toB256_go_append_toBytes,
    Jaune.Bytes.toB256_go_append_toBytes] at lane
  rw [show (0 : UInt64).toBytes = (0 : UInt64).toBytes ++ [] from
    (List.append_nil _).symm, Jaune.Bytes.toB256_go_append_toBytes] at lane
  change (UInt64.ofBytes a0 a1 a2 a3 a4 a5 a6 a7).toBytes =
    [a0, a1, a2, a3, a4, a5, a6, a7] at lane
  rw [UInt64.ofBytes_eq_toUInt64] at lane
  exact lane

end Blanc.Bytes
