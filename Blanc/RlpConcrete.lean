import Jaune.Transaction

/-! Structural equations for concrete RLP proofs over Jaune's actual codec. -/

namespace Blanc.RlpConcrete

open Jaune

private theorem natBytes_aux_roundtrip (n : Nat) (acc : Bytes) :
    Bytes.toNat (Nat.toBytes.aux acc n) = Bytes.toNat.aux n acc := by
  induction n using Nat.strong_induction_on generalizing acc with
  | h n ih =>
    cases n with
    | zero => rw [Nat.toBytes.aux]; rfl
    | succ n =>
      rw [Nat.toBytes.aux]
      rw [ih ((n + 1) / 256) (by omega)]
      rw [Bytes.toNat.aux]
      have digit : ((n + 1) % 256).toUInt8.toNat = (n + 1) % 256 := by
        simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow,
          Nat.mod_mod]
      rw [digit, Nat.mul_comm ((n + 1) / 256), Nat.div_add_mod]

/-- Jaune's variable-width natural encoding retains the entire natural. -/
theorem nat_bytes_roundtrip (n : Nat) : n.toBytes.toNat = n := by
  exact natBytes_aux_roundtrip n []

private theorem splitAt_aux_append (xs ys acc : List α) :
    Jaune.List.splitAt?.aux xs.length acc (xs ++ ys) =
      some (acc.reverse ++ xs, ys) := by
  induction xs generalizing acc with
  | nil => simp only [List.length_nil, List.nil_append, List.splitAt?.aux, List.append_nil]
  | cons x xs ih =>
    simpa only [List.length_cons, List.cons_append, List.splitAt?.aux, List.reverse_cons,
      List.append_assoc, List.nil_append] using ih (x :: acc)

/-- Splitting at a retained prefix's exact length preserves its suffix. -/
theorem splitAt_append (xs ys : List α) :
    Jaune.List.splitAt? xs.length (xs ++ ys) = some (xs, ys) := by
  simpa only [List.splitAt?, List.reverse_nil, List.nil_append] using splitAt_aux_append xs ys []

/-- A byte payload of at least two bytes uses the length-prefixed encoder arm. -/
theorem encode_bytes_many (bs : Bytes) (h : 2 ≤ bs.length) :
    (BLT.bytes bs).toBytes =
      if bs.length < 56 then (0x80 + bs.length.toUInt8) :: bs
      else let lbs := bs.length.toBytesPack
           (0xb7 + lbs.length.toUInt8) :: (lbs ++ bs) := by
  cases bs with
  | nil => simp only [List.length_nil, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] at h
  | cons a bs =>
    cases bs with
    | nil => simp only [List.length_cons, List.length_nil, zero_add, Nat.not_ofNat_le_one] at h
    | cons b bs => rw [BLT.toBytes]; simp only [List.cons.injEq, reduceCtorEq, and_false, imp_self,
      implies_true]

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

/-- Any short-string tag consumes exactly the declared payload and retains
the following bytes. This proves parser acceptance; scalar canonicality is
checked by the enclosing field decoder. -/
theorem decode_bytes_short (k n : Nat) (bs tail : Bytes)
    (hn : n < 56) (hlen : bs.length = n) :
    Bytes.toBLTDiff? (k + 1) ((0x80 + n.toUInt8) :: (bs ++ tail)) =
      some (.bytes bs, tail) := by
  have tags : ∀ i : Fin 56,
      (match (0x80 + i.val.toUInt8).toBools with
       | (true, false, true, true, true, _, _, _) => false
       | (true, false, _, _, _, _, _, _) => true
       | _ => false) = true ∧
      (0x80 + i.val.toUInt8 - 0x80).toNat = i.val := by decide +kernel
  obtain ⟨htag, hsize⟩ := tags ⟨n, hn⟩
  rw [Bytes.toBLTDiff?]
  split <;> simp_all only [Nat.toUInt8_eq, add_sub_cancel_left, UInt8.toNat_ofNat', Nat.reducePow, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd, Bool.false_eq_true, imp_false, Bool.not_eq_true, Option.map_eq_map, Option.map_eq_some_iff, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq, BLT.bytes.injEq, exists_eq_right_right, exists_eq_right]
  rw [Nat.mod_eq_of_lt (by omega), ← hlen, splitAt_append]

/-- Compose actual first-item and remaining-list parser equations. -/
theorem parse_cons (k : Nat) (b : UInt8) (bs tail : Bytes) (r : BLT) (rs : List BLT)
    (hfirst : Bytes.toBLTDiff? (k + 1) (b :: bs) = some (r, tail))
    (hrest : Bytes.toBLTs? k tail = some rs) :
    Bytes.toBLTs? (k + 1) (b :: bs) = some (r :: rs) := by
  rw [Bytes.toBLTs?, hfirst]
  change (do let rest ← Bytes.toBLTs? k tail; pure (r :: rest)) = _
  rw [hrest]
  rfl

private theorem decode_b128_prefix (hi lo : UInt64) (tail : Bytes) :
    Bytes.toB128Diff (hi.toBytes ++ lo.toBytes ++ tail) = some ((hi, lo), tail) := by
  simp only [UInt64.toBytes, UInt32.toBytes, UInt16.toBytes,
    List.cons_append, List.nil_append, Bytes.toB128Diff]
  rw [UInt64.ofBytes_eq_toUInt64, UInt64.ofBytes_eq_toUInt64]
  change some ((hi.toBytes.toUInt64, lo.toBytes.toUInt64), tail) = _
  rw [UInt64.toUInt64_toBytes, UInt64.toUInt64_toBytes]

/-- A full-width header commitment decodes to the original word, including
words whose first byte is zero. -/
theorem decode_hash (name : String) (word : B256) :
    word.toBytes.toRlpHash name = .ok word := by
  have h : word.toBytes.toB256? = some word := by
    simp only [Bytes.toB256?, B256.toBytes, B128.toBytes, List.append_assoc]
    rw [show word.2.2.toBytes = word.2.2.toBytes ++ [] from (List.append_nil _).symm]
    rw [← List.append_assoc word.1.1.toBytes word.1.2.toBytes, decode_b128_prefix]
    simp only [bind, Option.bind]
    rw [← List.append_assoc, decode_b128_prefix]
    rfl
  simp only [Bytes.toRlpHash, h, Option.toExcept]

/-- A 21-field header returns from Jaune's structural decoder when its
variable-width scalar fields carry their exact decoder equations.  The
optional tail is deliberately restricted to a requests commitment alone:
the 20- and 23-field wire shapes have different parser branches. Every preceding
optional field must be present, so the encoder actually emits this 21-field tail. -/
theorem header21_roundtrip (header : Header) (requestsHash : B256)
    (hrequests : header.requestsHash = some requestsHash)
    (haccess : header.blockAccessListHash = none)
    (hslot : header.slotNumber = none)
    (baseFeePerGas : Nat) (withdrawalsRoot parentBeaconBlockRoot : B256)
    (hbaseFeePresent : header.baseFeePerGas = some baseFeePerGas)
    (hwithdrawals : header.withdrawalsRoot = some withdrawalsRoot)
    (hbeacon : header.parentBeaconBlockRoot = some parentBeaconBlockRoot)
    (hcoinbase : header.coinbase.toBytes.toRlpAdr "header coinbase" = .ok header.coinbase)
    (hbloom : header.bloom.toRlpFixed "header bloom" 256 = .ok header.bloom)
    (hdifficulty : header.difficulty.toBytes.toRlpNat "header difficulty" 32 =
      .ok header.difficulty)
    (hnumber : header.number.toBytes.toRlpNat "header number" 32 = .ok header.number)
    (hgasLimit : header.gasLimit.toBytes.toRlpNat "header gasLimit" 32 = .ok header.gasLimit)
    (hgasUsed : header.gasUsed.toBytes.toRlpNat "header gasUsed" 32 = .ok header.gasUsed)
    (htimestamp : header.timestamp.toBytes.toRlpNat "header timestamp" 32 =
      .ok header.timestamp)
    (hnonce : header.nonce.toBytes.toRlpFixedB64 "header nonce" = .ok header.nonce)
    (hbaseFee : baseFeePerGas.toBytes.toRlpNat "header baseFeePerGas" 32 =
      .ok baseFeePerGas)
    (blobGasUsed excessBlobGas : UInt64)
    (hblobGasUsed : blobGasUsed.toNat.toBytes.toRlpB64 "header blobGasUsed" =
      .ok blobGasUsed)
    (hblobGasUsedNat : header.blobGasUsed = some blobGasUsed.toNat)
    (hexcessBlobGas : excessBlobGas.toNat.toBytes.toRlpB64 "header excessBlobGas" =
      .ok excessBlobGas)
    (hexcessBlobGasNat : header.excessBlobGas = some excessBlobGas.toNat) :
    header.toBLT.toExHeader = .ok header := by
  rw [Header.toBLT, hrequests, haccess, hslot, hbaseFeePresent, hwithdrawals,
    hblobGasUsedNat, hexcessBlobGasNat, hbeacon]
  simp only [List.cons_append, List.nil_append, BLT.toExHeader, decode_hash,
    bind, Except.bind, hcoinbase, hbloom, hdifficulty, hnumber, hgasLimit, hgasUsed,
    htimestamp, hnonce]
  simp! only [hbaseFee, decode_hash, hblobGasUsed, hexcessBlobGas, bind, Except.bind]
  rw [← hbaseFeePresent, ← hwithdrawals, ← hblobGasUsedNat, ← hexcessBlobGasNat,
    ← hbeacon, ← hrequests, ← haccess, ← hslot]


end Blanc.RlpConcrete
