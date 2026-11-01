import Blanc.RlpBytesInjective
import Jaune.RlpEval

/-!
# RLP round trip

Jaune's parser inverts its encoder: `toBLT?_toBytes` states
`Bytes.toBLT? b.toBytes = some b` for every `BLT` whose encoding is shorter
than `2 ^ 64` bytes (the bound keeps every length-of-length tag below the
next tag range). Payloads stay abstract, so a signed transaction carrying a
large creation input is decoded from its canonical encoding without reducing
the input bytes.
-/

namespace Blanc.RlpConcrete

open Jaune

/-- A positive natural below `2 ^ 64` has a one-to-eight-byte encoding. -/
private theorem toBytes_width (n : Nat) (positive : 0 < n) (small : n < 2 ^ 64) :
    1 ≤ n.toBytes.length ∧ n.toBytes.length ≤ 8 := by
  have lo := nat_bytes_length_mono (show 1 ≤ n by omega)
  have hi := nat_bytes_length_mono (show n ≤ 2 ^ 64 - 1 by omega)
  have one : (Nat.toBytes 1).length = 1 := by
    rw [Nat.toBytes_eq_toBytesS]; decide +kernel
  have eight : (Nat.toBytes (2 ^ 64 - 1)).length = 8 := by
    rw [Nat.toBytes_eq_toBytesS]; decide +kernel
  omega

private theorem toBools_split (c : UInt8) :
    c.toBools = (c.toBools.1, c.toBools.2.1, c.toBools.2.2.1, c.toBools.2.2.2.1,
      c.toBools.2.2.2.2.1, c.toBools.2.2.2.2.2) := rfl

/-- A long-string tag with a one-to-eight-byte length consumes its payload. -/
theorem decode_bytes_long (k : Nat) (lbs bs tail : Bytes)
    (pos : 1 ≤ lbs.length) (wide : lbs.length ≤ 8) (hlen : lbs.toNat = bs.length) :
    Bytes.toBLTDiff? (k + 1) ((0xb7 + lbs.length.toUInt8) :: (lbs ++ (bs ++ tail))) =
      some (.bytes bs, tail) := by
  have tags : ∀ i : Fin 8,
      (0xb7 + (i.val + 1).toUInt8).toBools.1 = true ∧
      (0xb7 + (i.val + 1).toUInt8).toBools.2.1 = false ∧
      (0xb7 + (i.val + 1).toUInt8).toBools.2.2.1 = true ∧
      (0xb7 + (i.val + 1).toUInt8).toBools.2.2.2.1 = true ∧
      (0xb7 + (i.val + 1).toUInt8).toBools.2.2.2.2.1 = true ∧
      (0xb7 + (i.val + 1).toUInt8 - 0xb7).toNat = i.val + 1 := by decide +kernel
  obtain ⟨t0, t1, t2, t3, t4, hsize⟩ := tags ⟨lbs.length - 1, by omega⟩
  simp only [Nat.sub_add_cancel pos] at t0 t1 t2 t3 t4 hsize
  rw [Bytes.toBLTDiff?, toBools_split, t0, t1, t2, t3, t4]
  simp only [hsize, splitAt_append, Option.bind_some, hlen, bind, pure]

/-- A short-list tag consumes exactly its parsed body. -/
theorem decode_list_short (k n : Nat) (bs tail : Bytes) (children : List BLT)
    (hn : n < 56) (hlen : bs.length = n) (hparse : Bytes.toBLTs? k bs = some children) :
    Bytes.toBLTDiff? (k + 1) ((0xc0 + n.toUInt8) :: (bs ++ tail)) =
      some (.list children, tail) := by
  have tags : ∀ i : Fin 56,
      (0xc0 + i.val.toUInt8).toBools.1 = true ∧
      (0xc0 + i.val.toUInt8).toBools.2.1 = true ∧
      ((0xc0 + i.val.toUInt8).toBools.2.2.1 && (0xc0 + i.val.toUInt8).toBools.2.2.2.1 &&
        (0xc0 + i.val.toUInt8).toBools.2.2.2.2.1) = false ∧
      (0xc0 + i.val.toUInt8 - 0xc0).toNat = i.val := by decide +kernel
  obtain ⟨t0, t1, t234, hsize⟩ := tags ⟨n, hn⟩
  simp only at t0 t1 t234 hsize
  rw [Bytes.toBLTDiff?, toBools_split, t0, t1]
  generalize (0xc0 + n.toUInt8).toBools.2.2.1 = a2 at t234 ⊢
  generalize (0xc0 + n.toUInt8).toBools.2.2.2.1 = a3 at t234 ⊢
  generalize (0xc0 + n.toUInt8).toBools.2.2.2.2.1 = a4 at t234 ⊢
  subst hlen
  cases a2 <;> cases a3 <;> cases a4 <;>
    simp only [Bool.and_self, Bool.and_false, Bool.and_true, reduceCtorEq] at t234 <;>
    simp only [hsize, splitAt_append, Option.bind_some, hparse, bind, pure]

/-- A long-list tag with a one-to-eight-byte length consumes exactly its parsed body. -/
theorem decode_list_long (k : Nat) (lbs bs tail : Bytes) (children : List BLT)
    (pos : 1 ≤ lbs.length) (wide : lbs.length ≤ 8) (hlen : lbs.toNat = bs.length)
    (hparse : Bytes.toBLTs? k bs = some children) :
    Bytes.toBLTDiff? (k + 1) ((0xf7 + lbs.length.toUInt8) :: (lbs ++ (bs ++ tail))) =
      some (.list children, tail) := by
  have tags : ∀ i : Fin 8,
      (0xf7 + (i.val + 1).toUInt8).toBools.1 = true ∧
      (0xf7 + (i.val + 1).toUInt8).toBools.2.1 = true ∧
      (0xf7 + (i.val + 1).toUInt8).toBools.2.2.1 = true ∧
      (0xf7 + (i.val + 1).toUInt8).toBools.2.2.2.1 = true ∧
      (0xf7 + (i.val + 1).toUInt8).toBools.2.2.2.2.1 = true ∧
      (0xf7 + (i.val + 1).toUInt8 - 0xf7).toNat = i.val + 1 := by decide +kernel
  obtain ⟨t0, t1, t2, t3, t4, hsize⟩ := tags ⟨lbs.length - 1, by omega⟩
  simp only [Nat.sub_add_cancel pos] at t0 t1 t2 t3 t4 hsize
  rw [Bytes.toBLTDiff?, toBools_split, t0, t1, t2, t3, t4]
  simp only [hsize, splitAt_append, Option.bind_some, hlen, hparse, bind, pure]

private theorem highBit_of_lt (b : UInt8) (small : b < 0x80) : b.highBit = false := by
  have bytes : ∀ i : Fin 128, (i.val.toUInt8).highBit = false := by decide +kernel
  have hb : b.toNat < 128 := small
  simpa only [Nat.toUInt8_eq, UInt8.ofNat_toNat] using bytes ⟨b.toNat, hb⟩

/-- Every byte string below `2 ^ 64` bytes is recovered from its encoding. -/
theorem decode_bytes_encode (k : Nat) (bs tail : Bytes) (small : bs.length < 2 ^ 64) :
    Bytes.toBLTDiff? (k + 1) ((BLT.bytes bs).toBytes ++ tail) = some (.bytes bs, tail) := by
  rcases bs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rw [encode_bytes_nil]
    exact decode_empty_bytes k tail
  · rw [BLT.toBytes]
    split
    · exact decode_byte k a tail (highBit_of_lt a (by assumption))
    · exact decode_bytes_short k 1 [a] tail (by decide) rfl
  · rw [encode_bytes_many _ (by simp only [List.length_cons]; omega)]
    split
    · exact decode_bytes_short k _ _ tail (by assumption) rfl
    · have width := toBytes_width (a :: b :: rest).length (by simp only [List.length_cons]; omega)
        small
      rw [toBytesPack_of_pos _ (by simp only [List.length_cons]; omega)]
      simp only [List.cons_append, List.append_assoc]
      exact decode_bytes_long k _ _ tail width.1 width.2 (nat_bytes_roundtrip _)

/-- A list body below `2 ^ 64` bytes that parses to `children` is recovered
from the list encoding over it. -/
theorem decode_list_encode (k : Nat) (rs : List BLT) (tail : Bytes)
    (small : (BLTs.toBytesJoin rs).length < 2 ^ 64)
    (hparse : Bytes.toBLTs? k (BLTs.toBytesJoin rs) = some rs) :
    Bytes.toBLTDiff? (k + 1) ((BLT.list rs).toBytes ++ tail) = some (.list rs, tail) := by
  rw [BLT.toBytes, BLTs.toBytes]
  generalize BLTs.toBytesJoin rs = body at small hparse ⊢
  dsimp only
  split
  · exact decode_list_short k _ body tail rs (by assumption) rfl hparse
  · have width := toBytes_width body.length (by omega) small
    rw [toBytesPack_of_pos _ (by omega)]
    simp only [List.cons_append, List.append_assoc]
    exact decode_list_long k _ body tail rs width.1 width.2 (nat_bytes_roundtrip _) hparse

theorem length_le_toBytes_bytes (bs : Bytes) : bs.length ≤ (BLT.bytes bs).toBytes.length := by
  rcases bs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact Nat.zero_le _
  · rw [BLT.toBytes]; split <;> simp only [List.length_cons, List.length_nil] <;> omega
  · rw [encode_bytes_many _ (by simp only [List.length_cons]; omega)]
    split <;> simp only [List.length_cons, List.length_append] <;> omega

theorem length_lt_toBytes_list (rs : List BLT) :
    (BLTs.toBytesJoin rs).length < (BLT.list rs).toBytes.length := by
  rw [BLT.toBytes, BLTs.toBytes]
  dsimp only
  split <;> simp only [List.length_cons, List.length_append] <;> omega

theorem toBytes_ne_nil (b : BLT) : b.toBytes ≠ [] := by
  cases b with
  | bytes bs =>
    rcases bs with _ | ⟨a, _ | ⟨c, rest⟩⟩
    · rw [encode_bytes_nil]; exact List.cons_ne_nil _ _
    · rw [BLT.toBytes]; split <;> exact List.cons_ne_nil _ _
    · rw [encode_bytes_many _ (by simp only [List.length_cons]; omega)]
      split <;> exact List.cons_ne_nil _ _
  | list rs =>
    rw [BLT.toBytes, BLTs.toBytes]
    dsimp only
    split <;> exact List.cons_ne_nil _ _

mutual

/-- One item is recovered from its encoding, given fuel at least its length. -/
theorem decode_encode (b : BLT) (k : Nat) (tail : Bytes)
    (small : b.toBytes.length < 2 ^ 64) (fuel : b.toBytes.length ≤ k + 1) :
    Bytes.toBLTDiff? (k + 1) (b.toBytes ++ tail) = some (b, tail) :=
  match b with
  | .bytes bs =>
    decode_bytes_encode k bs tail (Nat.lt_of_le_of_lt (length_le_toBytes_bytes bs) small)
  | .list rs =>
    have hl := length_lt_toBytes_list rs
    decode_list_encode k rs tail (by omega) (parse_encode rs k (by omega) (by omega))

/-- A joint item encoding parses back to its items, given fuel at least its length. -/
theorem parse_encode (rs : List BLT) (k : Nat)
    (small : (BLTs.toBytesJoin rs).length < 2 ^ 64)
    (fuel : (BLTs.toBytesJoin rs).length ≤ k) :
    Bytes.toBLTs? k (BLTs.toBytesJoin rs) = some rs :=
  match rs, k with
  | [], k => by rw [BLTs.toBytesJoin, Bytes.toBLTs?]
  | r :: rs, k => by
    have hjoin : BLTs.toBytesJoin (r :: rs) = r.toBytes ++ BLTs.toBytesJoin rs := by
      rw [BLTs.toBytesJoin]
    have hne := toBytes_ne_nil r
    rw [hjoin, List.length_append] at small fuel
    have hpos : 1 ≤ r.toBytes.length := List.length_pos_iff.mpr hne
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c, rest, hcons⟩ := List.exists_cons_of_ne_nil hne
    have first := decode_encode r k (BLTs.toBytesJoin rs) (by omega) (by omega)
    have tailParse := parse_encode rs k (by omega) (by omega)
    rw [hjoin, hcons] at *
    exact parse_cons k c (rest ++ BLTs.toBytesJoin rs) _ r rs first tailParse

end

/-- Jaune's RLP parser inverts its encoder on every item encoded in fewer
than `2 ^ 64` bytes; payload bytes stay abstract. -/
theorem toBLT?_toBytes (b : BLT) (small : b.toBytes.length < 2 ^ 64) :
    Bytes.toBLT? b.toBytes = some b := by
  have hpos : 1 ≤ b.toBytes.length := List.length_pos_iff.mpr (toBytes_ne_nil b)
  have h := decode_encode b (b.toBytes.length - 1) [] small (by omega)
  rw [List.append_nil, Nat.sub_add_cancel hpos] at h
  unfold Bytes.toBLT?
  rw [h]

/-- Bytes proved to be the canonical encoding of `b` decode to `b`. -/
theorem toBLT?_of_encoded {b : BLT} {signed : Bytes} (encoded : b.toBytes = signed)
    (small : signed.length < 2 ^ 64) : Bytes.toBLT? signed = some b := by
  subst encoded
  exact toBLT?_toBytes b small

end Blanc.RlpConcrete
