import Jaune.Transaction

/-! Structural equations for concrete RLP proofs over Jaune's actual codec. -/

namespace Blanc.RlpConcrete

open Jaune

private theorem splitAt_aux_append (xs ys acc : List α) :
    Jaune.List.splitAt?.aux xs.length acc (xs ++ ys) =
      some (acc.reverse ++ xs, ys) := by
  induction xs generalizing acc with
  | nil => simp [Jaune.List.splitAt?.aux]
  | cons x xs ih =>
    simpa [Jaune.List.splitAt?.aux, List.reverse_cons, List.append_assoc] using ih (x :: acc)

/-- Splitting at a retained prefix's exact length preserves its suffix. -/
theorem splitAt_append (xs ys : List α) :
    Jaune.List.splitAt? xs.length (xs ++ ys) = some (xs, ys) := by
  simpa [Jaune.List.splitAt?] using splitAt_aux_append xs ys []

/-- A byte payload of at least two bytes uses the length-prefixed encoder arm. -/
theorem encode_bytes_many (bs : Bytes) (h : 2 ≤ bs.length) :
    (BLT.bytes bs).toBytes =
      if bs.length < 56 then (0x80 + bs.length.toUInt8) :: bs
      else let lbs := bs.length.toBytesPack
           (0xb7 + lbs.length.toUInt8) :: (lbs ++ bs) := by
  cases bs with
  | nil => simp at h
  | cons a bs =>
    cases bs with
    | nil => simp at h
    | cons b bs => rw [BLT.toBytes]; simp

/-- The two-byte long-string header consumes exactly its declared payload. -/
theorem decode_bytes_long_two (k : Nat) (hi lo : UInt8) (bs tail : Bytes)
    (hlen : Bytes.toNat [hi, lo] = bs.length) :
    Bytes.toBLTDiff? (k + 1) (0xb9 :: hi :: lo :: (bs ++ tail)) =
      some (.bytes bs, tail) := by
  have hb : (0xb9 : UInt8).toBools =
      (true, false, true, true, true, false, false, true) := by rfl
  rw [Bytes.toBLTDiff?]
  simp only [hb]
  change (do
    let p ← Jaune.List.splitAt? 2 ([hi, lo] ++ (bs ++ tail))
    let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
    pure (BLT.bytes q.1, q.2)) = some (.bytes bs, tail)
  rw [show Jaune.List.splitAt? 2 ([hi, lo] ++ (bs ++ tail)) =
      some ([hi, lo], bs ++ tail) from splitAt_append [hi, lo] (bs ++ tail)]
  change (do
    let q ← Jaune.List.splitAt? (Bytes.toNat [hi, lo]) (bs ++ tail)
    pure (BLT.bytes q.1, q.2)) = some (.bytes bs, tail)
  rw [hlen, splitAt_append]
  rfl

/-- The single-byte atom arm is selected by the byte's clear high bit. -/
theorem decode_byte (k : Nat) (b : UInt8) (tail : Bytes) (hb : b.highBit = false) :
    Bytes.toBLTDiff? (k + 1) (b :: tail) = some (.bytes [b], tail) := by
  rw [Bytes.toBLTDiff?]
  simp only [UInt8.toBools, hb]

theorem decode_empty_bytes (k : Nat) (tail : Bytes) :
    Bytes.toBLTDiff? (k + 1) (0x80 :: tail) = some (.bytes [], tail) := by
  have hb : (0x80 : UInt8).toBools =
      (true, false, false, false, false, false, false, false) := by rfl
  rw [Bytes.toBLTDiff?]
  simp only [hb]
  rfl

theorem decode_empty_list (k : Nat) (tail : Bytes) :
    Bytes.toBLTDiff? (k + 1) (0xc0 :: tail) = some (.list [], tail) := by
  have hb : (0xc0 : UInt8).toBools =
      (true, true, false, false, false, false, false, false) := by rfl
  rw [Bytes.toBLTDiff?]
  simp only [hb]
  change (do let rs ← Bytes.toBLTs? k []; pure (BLT.list rs, tail)) = _
  rw [Bytes.toBLTs?]
  rfl

theorem decode_bytes_three (k : Nat) (bs tail : Bytes) (hlen : bs.length = 3) :
    Bytes.toBLTDiff? (k + 1) (0x83 :: (bs ++ tail)) =
      some (.bytes bs, tail) := by
  have hb : (0x83 : UInt8).toBools =
      (true, false, false, false, false, false, true, true) := by rfl
  rw [Bytes.toBLTDiff?]
  simp only [hb]
  change Prod.map BLT.bytes id <$> Jaune.List.splitAt? 3 (bs ++ tail) = _
  rw [← hlen, splitAt_append]
  rfl

/-- A full-width scalar retains its exact thirty-two bytes and outer suffix. -/
theorem decode_bytes_32 (k : Nat) (bs tail : Bytes) (hlen : bs.length = 32) :
    Bytes.toBLTDiff? (k + 1) (0xa0 :: (bs ++ tail)) =
      some (.bytes bs, tail) := by
  have hb : (0xa0 : UInt8).toBools =
      (true, false, true, false, false, false, false, false) := by rfl
  rw [Bytes.toBLTDiff?]
  simp only [hb]
  change Prod.map BLT.bytes id <$> Jaune.List.splitAt? 32 (bs ++ tail) = _
  rw [← hlen, splitAt_append]
  rfl

/-- A two-byte long-list header retains exactly its payload and outer suffix. -/
theorem decode_list_long_two (k : Nat) (hi lo : UInt8) (bs tail : Bytes)
    (children : List BLT) (hlen : Bytes.toNat [hi, lo] = bs.length)
    (hparse : Bytes.toBLTs? k bs = some children) :
    Bytes.toBLTDiff? (k + 1) (0xf9 :: hi :: lo :: (bs ++ tail)) =
      some (.list children, tail) := by
  have hb : (0xf9 : UInt8).toBools =
      (true, true, true, true, true, false, false, true) := by rfl
  rw [Bytes.toBLTDiff?]
  simp only [hb]
  change (do
    let p ← Jaune.List.splitAt? 2 ([hi, lo] ++ (bs ++ tail))
    let q ← Jaune.List.splitAt? (Bytes.toNat p.1) p.2
    let rs ← Bytes.toBLTs? k q.1
    pure (BLT.list rs, q.2)) = some (.list children, tail)
  rw [show Jaune.List.splitAt? 2 ([hi, lo] ++ (bs ++ tail)) =
      some ([hi, lo], bs ++ tail) from splitAt_append [hi, lo] (bs ++ tail)]
  change (do
    let q ← Jaune.List.splitAt? (Bytes.toNat [hi, lo]) (bs ++ tail)
    let rs ← Bytes.toBLTs? k q.1
    pure (BLT.list rs, q.2)) = some (.list children, tail)
  rw [hlen, splitAt_append]
  change (do let rs ← Bytes.toBLTs? k bs; pure (BLT.list rs, tail)) = _
  rw [hparse]
  rfl

/-- Compose actual first-item and remaining-list parser equations. -/
theorem parse_cons (k : Nat) (b : UInt8) (bs tail : Bytes) (r : BLT) (rs : List BLT)
    (hfirst : Bytes.toBLTDiff? (k + 1) (b :: bs) = some (r, tail))
    (hrest : Bytes.toBLTs? k tail = some rs) :
    Bytes.toBLTs? (k + 1) (b :: bs) = some (r :: rs) := by
  rw [Bytes.toBLTs?, hfirst]
  change (do let rest ← Bytes.toBLTs? k tail; pure (r :: rest)) = _
  rw [hrest]
  rfl

end Blanc.RlpConcrete
