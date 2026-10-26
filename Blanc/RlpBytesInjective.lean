import Blanc.RlpConcrete

/-! Unbounded byte-payload encoder injectivity and natural receipt-key separation. -/

namespace Blanc.RlpConcrete

open Jaune

private theorem natBytes_aux_length (n : Nat) (acc : Bytes) :
    (Nat.toBytes.aux acc n).length = n.toBytes.length + acc.length := by
  induction n using Nat.strong_induction_on generalizing acc with
  | h n ih =>
    cases n with
    | zero => simp only [Nat.toBytes, Nat.toBytes.aux, List.length_nil, Nat.zero_add]
    | succ n =>
      change (Nat.toBytes.aux acc (n + 1)).length =
        (Nat.toBytes.aux [] (n + 1)).length + acc.length
      rw [Nat.toBytes.aux, Nat.toBytes.aux]
      rw [ih ((n + 1) / 256) (by omega), ih ((n + 1) / 256) (by omega)]
      simp only [List.length_cons, List.length_nil]
      omega

/-- Natural byte width is monotone, including its zero-width encoding of zero. -/
theorem nat_bytes_length_mono {m n : Nat} (le : m ≤ n) :
    m.toBytes.length ≤ n.toBytes.length := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    cases m with
    | zero => simp only [Nat.toBytes, Nat.toBytes.aux, List.length_nil, Nat.zero_le]
    | succ m =>
      cases n with
      | zero => omega
      | succ n =>
        have smaller : ((m + 1) / 256).toBytes.length ≤
            ((n + 1) / 256).toBytes.length := ih _ (by omega) (by omega)
        change (Nat.toBytes.aux [] (m + 1)).length ≤
          (Nat.toBytes.aux [] (n + 1)).length
        rw [Nat.toBytes.aux, Nat.toBytes.aux, natBytes_aux_length, natBytes_aux_length]
        simpa only [List.length_cons, List.length_nil, Nat.succ_eq_add_one,
          Nat.add_le_add_iff_right] using smaller

private theorem natBytesPack_of_pos (n : Nat) (positive : 0 < n) :
    n.toBytesPack = n.toBytes := by
  cases n with
  | zero => omega
  | succ => rfl

private theorem encode_bytes_many_length_strict {xs ys : Bytes}
    (many : 2 ≤ xs.length) (lt : xs.length < ys.length) :
    (BLT.bytes xs).toBytes.length < (BLT.bytes ys).toBytes.length := by
  rw [encode_bytes_many xs many, encode_bytes_many ys (by omega)]
  split <;> split
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons, List.length_append]; omega
  · omega
  · have width := nat_bytes_length_mono (Nat.le_of_lt lt)
    rw [natBytesPack_of_pos xs.length (by omega), natBytesPack_of_pos ys.length (by omega)]
    simp only [List.length_cons, List.length_append]
    omega

private theorem encode_bytes_many_length (xs : Bytes) (many : 2 ≤ xs.length) :
    3 ≤ (BLT.bytes xs).toBytes.length := by
  rw [encode_bytes_many xs many]
  split <;> simp only [List.length_cons, List.length_append] <;> omega

private theorem encode_bytes_many_inj {xs ys : Bytes}
    (hx : 2 ≤ xs.length) (hy : 2 ≤ ys.length)
    (same : (BLT.bytes xs).toBytes = (BLT.bytes ys).toBytes) : xs = ys := by
  have lengths : xs.length = ys.length := by
    have encodedLengths := congrArg List.length same
    rcases Nat.lt_trichotomy xs.length ys.length with lt | eq | gt
    · have := encode_bytes_many_length_strict hx lt; omega
    · exact eq
    · have := encode_bytes_many_length_strict hy gt; omega
  rw [encode_bytes_many xs hx, encode_bytes_many ys hy, lengths] at same
  split at same
  · exact (List.cons.inj same).2
  · exact List.append_cancel_left (List.cons.inj same).2

private theorem encode_bytes_nil : (BLT.bytes []).toBytes = [0x80] := by
  rw [BLT.toBytes] <;> simp only [reduceCtorEq, imp_self, implies_true]
  rfl

private theorem encode_bytes_singleton (b : UInt8) :
    (BLT.bytes [b]).toBytes = (if b < 0x80 then [b] else [0x81, b]) := by
  rw [BLT.toBytes]

/-- Jaune's byte-payload RLP encoder is injective, with no payload-size bound.
The proof uses total encoded lengths, not validity of a possibly wrapped tag. -/
theorem encode_bytes_injective {xs ys : Bytes}
    (same : (BLT.bytes xs).toBytes = (BLT.bytes ys).toBytes) : xs = ys := by
  rcases xs with _ | ⟨a, _ | ⟨b, xs⟩⟩ <;>
    rcases ys with _ | ⟨c, _ | ⟨d, ys⟩⟩
  · rfl
  · rw [encode_bytes_nil, encode_bytes_singleton] at same
    change [0x80] = (if c < 0x80 then [c] else [0x81, c]) at same
    split at same
    · have byte := (List.cons.inj same).1
      subst c
      contradiction
    · have := congrArg List.length same
      simp only [List.length_cons, List.length_nil] at this
      omega
  · have large := encode_bytes_many_length (c :: d :: ys) (by simp only [List.length_cons]; omega)
    have lengths := congrArg List.length same
    rw [encode_bytes_nil] at lengths
    change 1 = _ at lengths
    omega
  · rw [encode_bytes_singleton, encode_bytes_nil] at same
    change (if a < 0x80 then [a] else [0x81, a]) = [0x80] at same
    split at same
    · have byte := (List.cons.inj same).1
      subst a
      contradiction
    · have := congrArg List.length same
      simp only [List.length_cons, List.length_nil] at this
      omega
  · rw [BLT.toBytes, BLT.toBytes] at same
    split at same <;> split at same
    · exact same
    · have := congrArg List.length same
      simp only [List.length_cons, List.length_nil] at this
      omega
    · have := congrArg List.length same
      simp only [List.length_cons, List.length_nil] at this
      omega
    · exact (List.cons.inj same).2
  · have large := encode_bytes_many_length (c :: d :: ys) (by simp only [List.length_cons]; omega)
    have lengths := congrArg List.length same
    rw [BLT.toBytes] at lengths
    split at lengths <;> simp only [List.length_cons, List.length_nil] at lengths <;> omega
  · have large := encode_bytes_many_length (a :: b :: xs) (by simp only [List.length_cons]; omega)
    have lengths := congrArg List.length same
    rw [encode_bytes_nil] at lengths
    change _ = 1 at lengths
    omega
  · have large := encode_bytes_many_length (a :: b :: xs) (by simp only [List.length_cons]; omega)
    have lengths := congrArg List.length same
    rw [encode_bytes_singleton c] at lengths
    split at lengths <;> simp only [List.length_cons, List.length_nil] at lengths <;> omega
  · exact encode_bytes_many_inj (by simp only [List.length_cons]; omega)
      (by simp only [List.length_cons]; omega) same

/-- Every natural transaction index has a distinct actual receipt key,
including zero and indices at or above 128. This is not a decoder roundtrip. -/
theorem receipt_key_injective {index other : Nat}
    (same : (BLT.bytes index.toBytes).toBytes = (BLT.bytes other.toBytes).toBytes) :
    index = other := by
  have bytes := encode_bytes_injective same
  have numbers := congrArg Bytes.toNat bytes
  simpa only [nat_bytes_roundtrip] using numbers

theorem receipt_key_ne {index other : Nat} (different : index ≠ other) :
    (BLT.bytes index.toBytes).toBytes ≠ (BLT.bytes other.toBytes).toBytes := by
  intro same
  exact different (receipt_key_injective same)

end Blanc.RlpConcrete
