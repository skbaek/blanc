import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def d16F0 : Bytes := [0x4e, 0x42]

def d16F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d16F2 : Bytes := [0x01, 0x86, 0xa0]

def d16F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d16F4 : Bytes := []

def d16F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x15, 0xb8, 0x73, 0x14, 0xcb, 0x3c, 0xc4, 0xb4, 0x25, 0x47, 0x2b, 0xc9, 0x6f, 0xb5, 0xe2, 0x91, 0x83, 0x33, 0xe1, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x6d, 0x6a, 0x7c]

def d16F6 : Bytes := [0x1b]

def d16F7 : Bytes := [0xea, 0x74, 0x1c, 0x30, 0x97, 0x9f, 0x02, 0x69, 0x0f, 0xb4, 0xf0, 0x05, 0xe4, 0xbc, 0xdf, 0x05, 0x99, 0x1f, 0x15, 0x8b, 0x2c, 0xa3, 0x9b, 0x50, 0x6a, 0x10, 0xfa, 0x85, 0xee, 0xa0, 0x1a, 0x7c]

def d16F8 : Bytes := [0x0a, 0x1f, 0x0b, 0x99, 0xf1, 0x5c, 0x0f, 0x6f, 0xcf, 0x90, 0x0e, 0xbb, 0xe8, 0x5d, 0x2c, 0x89, 0xff, 0x6c, 0x93, 0xdd, 0xe2, 0x69, 0xfa, 0xca, 0xa5, 0xda, 0x54, 0x24, 0x15, 0x86, 0x83, 0x61]

def d16Fields : List BLT := [.bytes d16F0, .bytes d16F1, .bytes d16F2, .bytes d16F3, .bytes d16F4, .bytes d16F5, .bytes d16F6, .bytes d16F7, .bytes d16F8]

def d16Payload : Bytes := [0x82] ++ d16F0 ++ [0x85] ++ d16F1 ++ [0x83] ++ d16F2 ++ [0x94] ++ d16F3 ++ [0x80] ++ d16F4 ++ [0xb8, 0x44] ++ d16F5 ++ [] ++ d16F6 ++ [0xa0] ++ d16F7 ++ [0xa0] ++ d16F8

def d16Signed : Bytes := [0xf8, 0xac] ++ d16Payload

def d16Tx : Tx := { nonce := 20034, gas := 100000, value := 0, data := d16F5, v := 27, r := d16F7, s := d16F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d16_literal : d16Signed = [0xf8, 0xac, 0x82, 0x4e, 0x42, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x15, 0xb8, 0x73, 0x14, 0xcb, 0x3c, 0xc4, 0xb4, 0x25, 0x47, 0x2b, 0xc9, 0x6f, 0xb5, 0xe2, 0x91, 0x83, 0x33, 0xe1, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x6d, 0x6a, 0x7c, 0x1b, 0xa0, 0xea, 0x74, 0x1c, 0x30, 0x97, 0x9f, 0x02, 0x69, 0x0f, 0xb4, 0xf0, 0x05, 0xe4, 0xbc, 0xdf, 0x05, 0x99, 0x1f, 0x15, 0x8b, 0x2c, 0xa3, 0x9b, 0x50, 0x6a, 0x10, 0xfa, 0x85, 0xee, 0xa0, 0x1a, 0x7c, 0xa0, 0x0a, 0x1f, 0x0b, 0x99, 0xf1, 0x5c, 0x0f, 0x6f, 0xcf, 0x90, 0x0e, 0xbb, 0xe8, 0x5d, 0x2c, 0x89, 0xff, 0x6c, 0x93, 0xdd, 0xe2, 0x69, 0xfa, 0xca, 0xa5, 0xda, 0x54, 0x24, 0x15, 0x86, 0x83, 0x61] := by
  decide +kernel

theorem d16_payload_length : d16Payload.length = 172 := by
  decide +kernel

theorem d16_signed_length : d16Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d16_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d16Payload = some d16Fields := by
  unfold d16Payload d16Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d16F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d16F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d16F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d16F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d16F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d16F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d16F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d16_parse : d16Signed.toBLT? = some (.list d16Fields) := by
  have outer : Bytes.toBLTDiff? 174 d16Signed = some (.list d16Fields, []) := by
    simpa only [d16Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d16Payload [] d16Fields
        (by rw [d16_payload_length]; decide +kernel) (d16_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d16_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d16_decode :
    (d16Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d16Tx := by
  rw [d16_parse]
  decide +kernel

theorem d16_blt : d16Tx.toBLT = .list d16Fields := by
  norm_num only [d16Tx, d16Fields, d16F0, d16F1, d16F2, d16F3, d16F4, d16F6, d16F7, d16F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d16_encode0 : (BLT.bytes d16F0).toBytes = [0x82] ++ d16F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d16F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d16_encode1 : (BLT.bytes d16F1).toBytes = [0x85] ++ d16F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d16F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d16_encode2 : (BLT.bytes d16F2).toBytes = [0x83] ++ d16F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d16F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d16_encode3 : (BLT.bytes d16F3).toBytes = [0x94] ++ d16F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d16F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d16_encode4 : (BLT.bytes d16F4).toBytes = [0x80] ++ d16F4 := by
  unfold d16F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d16_encode5 : (BLT.bytes d16F5).toBytes = [0xb8, 0x44] ++ d16F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d16F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d16_encode6 : (BLT.bytes d16F6).toBytes = [] ++ d16F6 := by
  unfold d16F6
  rw [BLT.toBytes]
  decide +kernel

theorem d16_encode7 : (BLT.bytes d16F7).toBytes = [0xa0] ++ d16F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d16F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d16_encode8 : (BLT.bytes d16F8).toBytes = [0xa0] ++ d16F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d16F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d16_canonical : d16Tx.toBLT.toBytes = d16Signed := by
  have encoded : BLTs.toBytesJoin d16Fields = d16Payload := by
    simp only [d16Fields, BLTs.toBytesJoin,
      d16_encode0, d16_encode1, d16_encode2, d16_encode3, d16_encode4, d16_encode5, d16_encode6, d16_encode7, d16_encode8, d16Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d16_blt, BLT.toBytes, BLTs.toBytes, encoded, d16_payload_length]
  norm_num only [d16Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d17F0 : Bytes := [0x4e, 0x43]

def d17F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d17F2 : Bytes := [0x01, 0x86, 0xa0]

def d17F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d17F4 : Bytes := []

def d17F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x18, 0x17, 0xa1, 0xf5, 0x1c, 0xc0, 0x78, 0xdf, 0xe6, 0x13, 0xbf, 0xc8, 0x80, 0x1d, 0x22, 0x3e, 0x7d, 0xfc, 0x51, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe0, 0xd8, 0x8c]

def d17F6 : Bytes := [0x1c]

def d17F7 : Bytes := [0x90, 0x81, 0xce, 0xa2, 0xd4, 0x2a, 0xb3, 0x88, 0x37, 0x08, 0x67, 0x34, 0xcf, 0x00, 0x0e, 0xe9, 0x8f, 0x26, 0x66, 0x2a, 0xf2, 0xf4, 0x23, 0xf8, 0x64, 0x1d, 0x16, 0x8d, 0x0b, 0xdb, 0xe2, 0x6b]

def d17F8 : Bytes := [0x56, 0x28, 0xae, 0x28, 0x33, 0x1d, 0x49, 0x0d, 0x7c, 0x55, 0x3e, 0x94, 0xd8, 0x1c, 0xb4, 0x7b, 0x8f, 0xa3, 0x12, 0x96, 0x59, 0x09, 0x7c, 0x6e, 0xcb, 0x71, 0xfc, 0xcd, 0x17, 0xc0, 0x1b, 0xa4]

def d17Fields : List BLT := [.bytes d17F0, .bytes d17F1, .bytes d17F2, .bytes d17F3, .bytes d17F4, .bytes d17F5, .bytes d17F6, .bytes d17F7, .bytes d17F8]

def d17Payload : Bytes := [0x82] ++ d17F0 ++ [0x85] ++ d17F1 ++ [0x83] ++ d17F2 ++ [0x94] ++ d17F3 ++ [0x80] ++ d17F4 ++ [0xb8, 0x44] ++ d17F5 ++ [] ++ d17F6 ++ [0xa0] ++ d17F7 ++ [0xa0] ++ d17F8

def d17Signed : Bytes := [0xf8, 0xac] ++ d17Payload

def d17Tx : Tx := { nonce := 20035, gas := 100000, value := 0, data := d17F5, v := 28, r := d17F7, s := d17F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d17_literal : d17Signed = [0xf8, 0xac, 0x82, 0x4e, 0x43, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x18, 0x17, 0xa1, 0xf5, 0x1c, 0xc0, 0x78, 0xdf, 0xe6, 0x13, 0xbf, 0xc8, 0x80, 0x1d, 0x22, 0x3e, 0x7d, 0xfc, 0x51, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe0, 0xd8, 0x8c, 0x1c, 0xa0, 0x90, 0x81, 0xce, 0xa2, 0xd4, 0x2a, 0xb3, 0x88, 0x37, 0x08, 0x67, 0x34, 0xcf, 0x00, 0x0e, 0xe9, 0x8f, 0x26, 0x66, 0x2a, 0xf2, 0xf4, 0x23, 0xf8, 0x64, 0x1d, 0x16, 0x8d, 0x0b, 0xdb, 0xe2, 0x6b, 0xa0, 0x56, 0x28, 0xae, 0x28, 0x33, 0x1d, 0x49, 0x0d, 0x7c, 0x55, 0x3e, 0x94, 0xd8, 0x1c, 0xb4, 0x7b, 0x8f, 0xa3, 0x12, 0x96, 0x59, 0x09, 0x7c, 0x6e, 0xcb, 0x71, 0xfc, 0xcd, 0x17, 0xc0, 0x1b, 0xa4] := by
  decide +kernel

theorem d17_payload_length : d17Payload.length = 172 := by
  decide +kernel

theorem d17_signed_length : d17Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d17_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d17Payload = some d17Fields := by
  unfold d17Payload d17Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d17F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d17F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d17F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d17F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d17F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d17F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d17F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d17_parse : d17Signed.toBLT? = some (.list d17Fields) := by
  have outer : Bytes.toBLTDiff? 174 d17Signed = some (.list d17Fields, []) := by
    simpa only [d17Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d17Payload [] d17Fields
        (by rw [d17_payload_length]; decide +kernel) (d17_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d17_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d17_decode :
    (d17Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d17Tx := by
  rw [d17_parse]
  decide +kernel

theorem d17_blt : d17Tx.toBLT = .list d17Fields := by
  norm_num only [d17Tx, d17Fields, d17F0, d17F1, d17F2, d17F3, d17F4, d17F6, d17F7, d17F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d17_encode0 : (BLT.bytes d17F0).toBytes = [0x82] ++ d17F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d17F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d17_encode1 : (BLT.bytes d17F1).toBytes = [0x85] ++ d17F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d17F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d17_encode2 : (BLT.bytes d17F2).toBytes = [0x83] ++ d17F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d17F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d17_encode3 : (BLT.bytes d17F3).toBytes = [0x94] ++ d17F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d17F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d17_encode4 : (BLT.bytes d17F4).toBytes = [0x80] ++ d17F4 := by
  unfold d17F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d17_encode5 : (BLT.bytes d17F5).toBytes = [0xb8, 0x44] ++ d17F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d17F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d17_encode6 : (BLT.bytes d17F6).toBytes = [] ++ d17F6 := by
  unfold d17F6
  rw [BLT.toBytes]
  decide +kernel

theorem d17_encode7 : (BLT.bytes d17F7).toBytes = [0xa0] ++ d17F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d17F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d17_encode8 : (BLT.bytes d17F8).toBytes = [0xa0] ++ d17F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d17F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d17_canonical : d17Tx.toBLT.toBytes = d17Signed := by
  have encoded : BLTs.toBytesJoin d17Fields = d17Payload := by
    simp only [d17Fields, BLTs.toBytesJoin,
      d17_encode0, d17_encode1, d17_encode2, d17_encode3, d17_encode4, d17_encode5, d17_encode6, d17_encode7, d17_encode8, d17Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d17_blt, BLT.toBytes, BLTs.toBytes, encoded, d17_payload_length]
  norm_num only [d17Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d18F0 : Bytes := [0x4e, 0x44]

def d18F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d18F2 : Bytes := [0x01, 0x86, 0xa0]

def d18F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d18F4 : Bytes := []

def d18F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x1e, 0x44, 0xeb, 0xc8, 0x20, 0x42, 0xff, 0x1f, 0x0c, 0x02, 0x3c, 0x01, 0x76, 0xde, 0xac, 0xe4, 0x6e, 0xd2, 0xd2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x23, 0xdc, 0x68]

def d18F6 : Bytes := [0x1b]

def d18F7 : Bytes := [0x5a, 0x37, 0x2b, 0xbc, 0x6b, 0x78, 0x3a, 0x14, 0x2d, 0xb0, 0xb3, 0x84, 0x5f, 0xa9, 0x03, 0x2a, 0x4f, 0xad, 0xf4, 0xdf, 0xa5, 0x1a, 0x74, 0x0e, 0x75, 0xcc, 0x85, 0x7b, 0xb1, 0x27, 0x93]

def d18F8 : Bytes := [0x55, 0x14, 0x18, 0x0f, 0xc0, 0xb4, 0x8b, 0x52, 0x5c, 0xa8, 0xd6, 0x01, 0x4d, 0xe8, 0x40, 0xd4, 0xe3, 0xae, 0xfd, 0x34, 0xa6, 0x15, 0x95, 0xcf, 0x6f, 0x8a, 0xbb, 0xff, 0x26, 0xde, 0xb0, 0x78]

def d18Fields : List BLT := [.bytes d18F0, .bytes d18F1, .bytes d18F2, .bytes d18F3, .bytes d18F4, .bytes d18F5, .bytes d18F6, .bytes d18F7, .bytes d18F8]

def d18Payload : Bytes := [0x82] ++ d18F0 ++ [0x85] ++ d18F1 ++ [0x83] ++ d18F2 ++ [0x94] ++ d18F3 ++ [0x80] ++ d18F4 ++ [0xb8, 0x44] ++ d18F5 ++ [] ++ d18F6 ++ [0x9f] ++ d18F7 ++ [0xa0] ++ d18F8

def d18Signed : Bytes := [0xf8, 0xab] ++ d18Payload

def d18Tx : Tx := { nonce := 20036, gas := 100000, value := 0, data := d18F5, v := 27, r := d18F7, s := d18F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d18_literal : d18Signed = [0xf8, 0xab, 0x82, 0x4e, 0x44, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x1e, 0x44, 0xeb, 0xc8, 0x20, 0x42, 0xff, 0x1f, 0x0c, 0x02, 0x3c, 0x01, 0x76, 0xde, 0xac, 0xe4, 0x6e, 0xd2, 0xd2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x23, 0xdc, 0x68, 0x1b, 0x9f, 0x5a, 0x37, 0x2b, 0xbc, 0x6b, 0x78, 0x3a, 0x14, 0x2d, 0xb0, 0xb3, 0x84, 0x5f, 0xa9, 0x03, 0x2a, 0x4f, 0xad, 0xf4, 0xdf, 0xa5, 0x1a, 0x74, 0x0e, 0x75, 0xcc, 0x85, 0x7b, 0xb1, 0x27, 0x93, 0xa0, 0x55, 0x14, 0x18, 0x0f, 0xc0, 0xb4, 0x8b, 0x52, 0x5c, 0xa8, 0xd6, 0x01, 0x4d, 0xe8, 0x40, 0xd4, 0xe3, 0xae, 0xfd, 0x34, 0xa6, 0x15, 0x95, 0xcf, 0x6f, 0x8a, 0xbb, 0xff, 0x26, 0xde, 0xb0, 0x78] := by
  decide +kernel

theorem d18_payload_length : d18Payload.length = 171 := by
  decide +kernel

theorem d18_signed_length : d18Signed.length = 173 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d18_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d18Payload = some d18Fields := by
  unfold d18Payload d18Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d18F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d18F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d18F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d18F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d18F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 31 d18F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d18F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d18_parse : d18Signed.toBLT? = some (.list d18Fields) := by
  have outer : Bytes.toBLTDiff? 173 d18Signed = some (.list d18Fields, []) := by
    simpa only [d18Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 172 171 d18Payload [] d18Fields
        (by rw [d18_payload_length]; decide +kernel) (d18_payload_parse 163)
  unfold Bytes.toBLT?
  rw [d18_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d18_decode :
    (d18Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d18Tx := by
  rw [d18_parse]
  decide +kernel

theorem d18_blt : d18Tx.toBLT = .list d18Fields := by
  norm_num only [d18Tx, d18Fields, d18F0, d18F1, d18F2, d18F3, d18F4, d18F6, d18F7, d18F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d18_encode0 : (BLT.bytes d18F0).toBytes = [0x82] ++ d18F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d18F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d18_encode1 : (BLT.bytes d18F1).toBytes = [0x85] ++ d18F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d18F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d18_encode2 : (BLT.bytes d18F2).toBytes = [0x83] ++ d18F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d18F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d18_encode3 : (BLT.bytes d18F3).toBytes = [0x94] ++ d18F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d18F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d18_encode4 : (BLT.bytes d18F4).toBytes = [0x80] ++ d18F4 := by
  unfold d18F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d18_encode5 : (BLT.bytes d18F5).toBytes = [0xb8, 0x44] ++ d18F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d18F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d18_encode6 : (BLT.bytes d18F6).toBytes = [] ++ d18F6 := by
  unfold d18F6
  rw [BLT.toBytes]
  decide +kernel

theorem d18_encode7 : (BLT.bytes d18F7).toBytes = [0x9f] ++ d18F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d18F7.length = 31 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d18_encode8 : (BLT.bytes d18F8).toBytes = [0xa0] ++ d18F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d18F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d18_canonical : d18Tx.toBLT.toBytes = d18Signed := by
  have encoded : BLTs.toBytesJoin d18Fields = d18Payload := by
    simp only [d18Fields, BLTs.toBytesJoin,
      d18_encode0, d18_encode1, d18_encode2, d18_encode3, d18_encode4, d18_encode5, d18_encode6, d18_encode7, d18_encode8, d18Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d18_blt, BLT.toBytes, BLTs.toBytes, encoded, d18_payload_length]
  norm_num only [d18Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d19F0 : Bytes := [0x7a]

def d19F1 : Bytes := [0x01, 0x22, 0xae, 0x10, 0x14]

def d19F2 : Bytes := [0x52, 0x08]

def d19F3 : Bytes := [0xd7, 0xb9, 0xa9, 0xb2, 0xf6, 0x65, 0x84, 0x9c, 0x40, 0x71, 0xad, 0x5a, 0xf7, 0x7d, 0x8c, 0x76, 0xaa, 0x30, 0xfb, 0x32]

def d19F4 : Bytes := [0xb1, 0x5a, 0x61, 0x85, 0x10, 0xc6, 0xc4]

def d19F5 : Bytes := []

def d19F6 : Bytes := [0x26]

def d19F7 : Bytes := [0x11, 0x2b, 0x54, 0xfd, 0x63, 0x55, 0x0f, 0xc9, 0x0a, 0x88, 0xbd, 0xd0, 0xe9, 0x5d, 0xc4, 0x24, 0x0e, 0x63, 0x96, 0xc6, 0x7a, 0x4f, 0x89, 0x57, 0x81, 0xbb, 0x13, 0x9e, 0x8f, 0xe7, 0xa5, 0xcf]

def d19F8 : Bytes := [0x7e, 0x03, 0x2a, 0xa8, 0x17, 0x78, 0x5f, 0x56, 0xad, 0xdb, 0x6f, 0x9f, 0xf2, 0x98, 0x3d, 0x8f, 0xc5, 0xc6, 0x47, 0xc3, 0x45, 0x2c, 0xbf, 0x65, 0xbe, 0x69, 0x52, 0xdf, 0xac, 0xd1, 0x72, 0xdf]

def d19Fields : List BLT := [.bytes d19F0, .bytes d19F1, .bytes d19F2, .bytes d19F3, .bytes d19F4, .bytes d19F5, .bytes d19F6, .bytes d19F7, .bytes d19F8]

def d19Payload : Bytes := [] ++ d19F0 ++ [0x85] ++ d19F1 ++ [0x82] ++ d19F2 ++ [0x94] ++ d19F3 ++ [0x87] ++ d19F4 ++ [0x80] ++ d19F5 ++ [] ++ d19F6 ++ [0xa0] ++ d19F7 ++ [0xa0] ++ d19F8

def d19Signed : Bytes := [0xf8, 0x6b] ++ d19Payload

def d19Tx : Tx := { nonce := 122, gas := 21000, value := 49920445768582852, data := d19F5, v := 38, r := d19F7, s := d19F8, type := .zero 4876800020 (some 0xd7b9a9b2f665849c4071ad5af77d8c76aa30fb32) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d19_literal : d19Signed = [0xf8, 0x6b, 0x7a, 0x85, 0x01, 0x22, 0xae, 0x10, 0x14, 0x82, 0x52, 0x08, 0x94, 0xd7, 0xb9, 0xa9, 0xb2, 0xf6, 0x65, 0x84, 0x9c, 0x40, 0x71, 0xad, 0x5a, 0xf7, 0x7d, 0x8c, 0x76, 0xaa, 0x30, 0xfb, 0x32, 0x87, 0xb1, 0x5a, 0x61, 0x85, 0x10, 0xc6, 0xc4, 0x80, 0x26, 0xa0, 0x11, 0x2b, 0x54, 0xfd, 0x63, 0x55, 0x0f, 0xc9, 0x0a, 0x88, 0xbd, 0xd0, 0xe9, 0x5d, 0xc4, 0x24, 0x0e, 0x63, 0x96, 0xc6, 0x7a, 0x4f, 0x89, 0x57, 0x81, 0xbb, 0x13, 0x9e, 0x8f, 0xe7, 0xa5, 0xcf, 0xa0, 0x7e, 0x03, 0x2a, 0xa8, 0x17, 0x78, 0x5f, 0x56, 0xad, 0xdb, 0x6f, 0x9f, 0xf2, 0x98, 0x3d, 0x8f, 0xc5, 0xc6, 0x47, 0xc3, 0x45, 0x2c, 0xbf, 0x65, 0xbe, 0x69, 0x52, 0xdf, 0xac, 0xd1, 0x72, 0xdf] := by
  decide +kernel

theorem d19_payload_length : d19Payload.length = 107 := by
  decide +kernel

theorem d19_signed_length : d19Signed.length = 109 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d19_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d19Payload = some d19Fields := by
  unfold d19Payload d19Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d19F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d19F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d19F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 7 d19F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d19F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d19F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d19_parse : d19Signed.toBLT? = some (.list d19Fields) := by
  have outer : Bytes.toBLTDiff? 109 d19Signed = some (.list d19Fields, []) := by
    simpa only [d19Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 108 107 d19Payload [] d19Fields
        (by rw [d19_payload_length]; decide +kernel) (d19_payload_parse 99)
  unfold Bytes.toBLT?
  rw [d19_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d19_decode :
    (d19Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d19Tx := by
  rw [d19_parse]
  decide +kernel

theorem d19_blt : d19Tx.toBLT = .list d19Fields := by
  norm_num only [d19Tx, d19Fields, d19F0, d19F1, d19F2, d19F3, d19F4, d19F6, d19F7, d19F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d19_encode0 : (BLT.bytes d19F0).toBytes = [] ++ d19F0 := by
  unfold d19F0
  rw [BLT.toBytes]
  decide +kernel

theorem d19_encode1 : (BLT.bytes d19F1).toBytes = [0x85] ++ d19F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d19F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d19_encode2 : (BLT.bytes d19F2).toBytes = [0x82] ++ d19F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d19F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d19_encode3 : (BLT.bytes d19F3).toBytes = [0x94] ++ d19F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d19F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d19_encode4 : (BLT.bytes d19F4).toBytes = [0x87] ++ d19F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d19F4.length = 7 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d19_encode5 : (BLT.bytes d19F5).toBytes = [0x80] ++ d19F5 := by
  unfold d19F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d19_encode6 : (BLT.bytes d19F6).toBytes = [] ++ d19F6 := by
  unfold d19F6
  rw [BLT.toBytes]
  decide +kernel

theorem d19_encode7 : (BLT.bytes d19F7).toBytes = [0xa0] ++ d19F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d19F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d19_encode8 : (BLT.bytes d19F8).toBytes = [0xa0] ++ d19F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d19F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d19_canonical : d19Tx.toBLT.toBytes = d19Signed := by
  have encoded : BLTs.toBytesJoin d19Fields = d19Payload := by
    simp only [d19Fields, BLTs.toBytesJoin,
      d19_encode0, d19_encode1, d19_encode2, d19_encode3, d19_encode4, d19_encode5, d19_encode6, d19_encode7, d19_encode8, d19Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d19_blt, BLT.toBytes, BLTs.toBytes, encoded, d19_payload_length]
  norm_num only [d19Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d20F0 : Bytes := [0x13]

def d20F1 : Bytes := [0x01, 0x0c, 0xd1, 0x24, 0x69]

def d20F2 : Bytes := [0xea, 0x60]

def d20F3 : Bytes := [0x8e, 0x87, 0x0d, 0x67, 0xf6, 0x60, 0xd9, 0x5d, 0x5b, 0xe5, 0x30, 0x38, 0x0d, 0x0e, 0xc0, 0xbd, 0x38, 0x82, 0x89, 0xe1]

def d20F4 : Bytes := []

def d20F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1c, 0x3d, 0x91, 0x7b, 0x90, 0x91, 0xc3, 0x46, 0xf4, 0x42, 0x57, 0x00, 0x01, 0xc8, 0x82, 0x4d, 0x8d, 0x8e, 0x0f, 0xf3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05, 0x6b, 0xc7, 0x5e, 0x2d, 0x63, 0x10, 0x00, 0x00]

def d20F6 : Bytes := [0x26]

def d20F7 : Bytes := [0x8a, 0x5b, 0x14, 0x1d, 0x9c, 0xcf, 0xf0, 0x8e, 0x8b, 0x81, 0x96, 0x32, 0xaa, 0x55, 0x1b, 0xce, 0xd1, 0x1a, 0x36, 0xdc, 0xdb, 0x4c, 0x4f, 0x93, 0x50, 0x2d, 0x41, 0x21, 0x4f, 0xe9, 0x71, 0xb7]

def d20F8 : Bytes := [0x4a, 0x7c, 0xda, 0xeb, 0x61, 0xdb, 0xd7, 0xc5, 0x8c, 0xc3, 0x92, 0x10, 0xd8, 0xf5, 0x8b, 0xa6, 0x3a, 0x80, 0xe2, 0xd3, 0x68, 0x5f, 0xa5, 0x8e, 0x59, 0x5e, 0xc3, 0xa1, 0xd7, 0x95, 0xd1, 0x67]

def d20Fields : List BLT := [.bytes d20F0, .bytes d20F1, .bytes d20F2, .bytes d20F3, .bytes d20F4, .bytes d20F5, .bytes d20F6, .bytes d20F7, .bytes d20F8]

def d20Payload : Bytes := [] ++ d20F0 ++ [0x85] ++ d20F1 ++ [0x82] ++ d20F2 ++ [0x94] ++ d20F3 ++ [0x80] ++ d20F4 ++ [0xb8, 0x44] ++ d20F5 ++ [] ++ d20F6 ++ [0xa0] ++ d20F7 ++ [0xa0] ++ d20F8

def d20Signed : Bytes := [0xf8, 0xa9] ++ d20Payload

def d20Tx : Tx := { nonce := 19, gas := 60000, value := 0, data := d20F5, v := 38, r := d20F7, s := d20F8, type := .zero 4510000233 (some 0x8e870d67f660d95d5be530380d0ec0bd388289e1) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d20_literal : d20Signed = [0xf8, 0xa9, 0x13, 0x85, 0x01, 0x0c, 0xd1, 0x24, 0x69, 0x82, 0xea, 0x60, 0x94, 0x8e, 0x87, 0x0d, 0x67, 0xf6, 0x60, 0xd9, 0x5d, 0x5b, 0xe5, 0x30, 0x38, 0x0d, 0x0e, 0xc0, 0xbd, 0x38, 0x82, 0x89, 0xe1, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1c, 0x3d, 0x91, 0x7b, 0x90, 0x91, 0xc3, 0x46, 0xf4, 0x42, 0x57, 0x00, 0x01, 0xc8, 0x82, 0x4d, 0x8d, 0x8e, 0x0f, 0xf3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05, 0x6b, 0xc7, 0x5e, 0x2d, 0x63, 0x10, 0x00, 0x00, 0x26, 0xa0, 0x8a, 0x5b, 0x14, 0x1d, 0x9c, 0xcf, 0xf0, 0x8e, 0x8b, 0x81, 0x96, 0x32, 0xaa, 0x55, 0x1b, 0xce, 0xd1, 0x1a, 0x36, 0xdc, 0xdb, 0x4c, 0x4f, 0x93, 0x50, 0x2d, 0x41, 0x21, 0x4f, 0xe9, 0x71, 0xb7, 0xa0, 0x4a, 0x7c, 0xda, 0xeb, 0x61, 0xdb, 0xd7, 0xc5, 0x8c, 0xc3, 0x92, 0x10, 0xd8, 0xf5, 0x8b, 0xa6, 0x3a, 0x80, 0xe2, 0xd3, 0x68, 0x5f, 0xa5, 0x8e, 0x59, 0x5e, 0xc3, 0xa1, 0xd7, 0x95, 0xd1, 0x67] := by
  decide +kernel

theorem d20_payload_length : d20Payload.length = 169 := by
  decide +kernel

theorem d20_signed_length : d20Signed.length = 171 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d20_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d20Payload = some d20Fields := by
  unfold d20Payload d20Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d20F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d20F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d20F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d20F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d20F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d20F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d20_parse : d20Signed.toBLT? = some (.list d20Fields) := by
  have outer : Bytes.toBLTDiff? 171 d20Signed = some (.list d20Fields, []) := by
    simpa only [d20Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 170 169 d20Payload [] d20Fields
        (by rw [d20_payload_length]; decide +kernel) (d20_payload_parse 161)
  unfold Bytes.toBLT?
  rw [d20_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d20_decode :
    (d20Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d20Tx := by
  rw [d20_parse]
  decide +kernel

theorem d20_blt : d20Tx.toBLT = .list d20Fields := by
  norm_num only [d20Tx, d20Fields, d20F0, d20F1, d20F2, d20F3, d20F4, d20F6, d20F7, d20F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d20_encode0 : (BLT.bytes d20F0).toBytes = [] ++ d20F0 := by
  unfold d20F0
  rw [BLT.toBytes]
  decide +kernel

theorem d20_encode1 : (BLT.bytes d20F1).toBytes = [0x85] ++ d20F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d20F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d20_encode2 : (BLT.bytes d20F2).toBytes = [0x82] ++ d20F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d20F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d20_encode3 : (BLT.bytes d20F3).toBytes = [0x94] ++ d20F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d20F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d20_encode4 : (BLT.bytes d20F4).toBytes = [0x80] ++ d20F4 := by
  unfold d20F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d20_encode5 : (BLT.bytes d20F5).toBytes = [0xb8, 0x44] ++ d20F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d20F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d20_encode6 : (BLT.bytes d20F6).toBytes = [] ++ d20F6 := by
  unfold d20F6
  rw [BLT.toBytes]
  decide +kernel

theorem d20_encode7 : (BLT.bytes d20F7).toBytes = [0xa0] ++ d20F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d20F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d20_encode8 : (BLT.bytes d20F8).toBytes = [0xa0] ++ d20F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d20F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d20_canonical : d20Tx.toBLT.toBytes = d20Signed := by
  have encoded : BLTs.toBytesJoin d20Fields = d20Payload := by
    simp only [d20Fields, BLTs.toBytesJoin,
      d20_encode0, d20_encode1, d20_encode2, d20_encode3, d20_encode4, d20_encode5, d20_encode6, d20_encode7, d20_encode8, d20Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d20_blt, BLT.toBytes, BLTs.toBytes, encoded, d20_payload_length]
  norm_num only [d20Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d21F0 : Bytes := []

def d21F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d21F2 : Bytes := [0x1e, 0x84, 0x80]

def d21F3 : Bytes := [0xf9, 0x36, 0x98, 0x7b, 0x8c, 0x35, 0xd1, 0xf8, 0xdb, 0xb7, 0x6d, 0x11, 0x4a, 0x68, 0x92, 0x93, 0xb0, 0x08, 0xd5, 0x3e]

def d21F4 : Bytes := [0x01, 0x63, 0x45, 0x78, 0x5d, 0x8a, 0x00, 0x00]

def d21F5 : Bytes := [0x88, 0x53, 0xb5, 0x3e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x0a]

def d21F6 : Bytes := [0x25]

def d21F7 : Bytes := [0xb8, 0xe2, 0x54, 0x22, 0xb9, 0x5b, 0x09, 0x72, 0xa3, 0x4f, 0x3a, 0x76, 0x1e, 0xce, 0x62, 0xe7, 0x26, 0x16, 0x60, 0x2c, 0xc0, 0xaf, 0xf9, 0x83, 0x8e, 0xeb, 0x9d, 0xa6, 0xf8, 0xd2, 0x10, 0x57]

def d21F8 : Bytes := [0x36, 0x5b, 0x95, 0xb6, 0x18, 0x0d, 0x3d, 0x36, 0xe9, 0x81, 0x7f, 0x91, 0x92, 0xe8, 0x41, 0xef, 0x31, 0x78, 0x9f, 0x33, 0xa5, 0xc8, 0xea, 0xa3, 0x6f, 0x04, 0xf2, 0xd4, 0xa8, 0x38, 0x79, 0x6b]

def d21Fields : List BLT := [.bytes d21F0, .bytes d21F1, .bytes d21F2, .bytes d21F3, .bytes d21F4, .bytes d21F5, .bytes d21F6, .bytes d21F7, .bytes d21F8]

def d21Payload : Bytes := [0x80] ++ d21F0 ++ [0x84] ++ d21F1 ++ [0x83] ++ d21F2 ++ [0x94] ++ d21F3 ++ [0x88] ++ d21F4 ++ [0xa4] ++ d21F5 ++ [] ++ d21F6 ++ [0xa0] ++ d21F7 ++ [0xa0] ++ d21F8

def d21Signed : Bytes := [0xf8, 0x90] ++ d21Payload

def d21Tx : Tx := { nonce := 0, gas := 2000000, value := 100000000000000000, data := d21F5, v := 37, r := d21F7, s := d21F8, type := .zero 4000000000 (some 0xf936987b8c35d1f8dbb76d114a689293b008d53e) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d21_literal : d21Signed = [0xf8, 0x90, 0x80, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x1e, 0x84, 0x80, 0x94, 0xf9, 0x36, 0x98, 0x7b, 0x8c, 0x35, 0xd1, 0xf8, 0xdb, 0xb7, 0x6d, 0x11, 0x4a, 0x68, 0x92, 0x93, 0xb0, 0x08, 0xd5, 0x3e, 0x88, 0x01, 0x63, 0x45, 0x78, 0x5d, 0x8a, 0x00, 0x00, 0xa4, 0x88, 0x53, 0xb5, 0x3e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x0a, 0x25, 0xa0, 0xb8, 0xe2, 0x54, 0x22, 0xb9, 0x5b, 0x09, 0x72, 0xa3, 0x4f, 0x3a, 0x76, 0x1e, 0xce, 0x62, 0xe7, 0x26, 0x16, 0x60, 0x2c, 0xc0, 0xaf, 0xf9, 0x83, 0x8e, 0xeb, 0x9d, 0xa6, 0xf8, 0xd2, 0x10, 0x57, 0xa0, 0x36, 0x5b, 0x95, 0xb6, 0x18, 0x0d, 0x3d, 0x36, 0xe9, 0x81, 0x7f, 0x91, 0x92, 0xe8, 0x41, 0xef, 0x31, 0x78, 0x9f, 0x33, 0xa5, 0xc8, 0xea, 0xa3, 0x6f, 0x04, 0xf2, 0xd4, 0xa8, 0x38, 0x79, 0x6b] := by
  decide +kernel

theorem d21_payload_length : d21Payload.length = 144 := by
  decide +kernel

theorem d21_signed_length : d21Signed.length = 146 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d21_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d21Payload = some d21Fields := by
  unfold d21Payload d21Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d21F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d21F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d21F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 d21F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 36 d21F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d21F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d21F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d21_parse : d21Signed.toBLT? = some (.list d21Fields) := by
  have outer : Bytes.toBLTDiff? 146 d21Signed = some (.list d21Fields, []) := by
    simpa only [d21Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 145 144 d21Payload [] d21Fields
        (by rw [d21_payload_length]; decide +kernel) (d21_payload_parse 136)
  unfold Bytes.toBLT?
  rw [d21_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d21_decode :
    (d21Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d21Tx := by
  rw [d21_parse]
  decide +kernel

theorem d21_blt : d21Tx.toBLT = .list d21Fields := by
  norm_num only [d21Tx, d21Fields, d21F0, d21F1, d21F2, d21F3, d21F4, d21F6, d21F7, d21F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d21_encode0 : (BLT.bytes d21F0).toBytes = [0x80] ++ d21F0 := by
  unfold d21F0
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d21_encode1 : (BLT.bytes d21F1).toBytes = [0x84] ++ d21F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d21F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d21_encode2 : (BLT.bytes d21F2).toBytes = [0x83] ++ d21F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d21F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d21_encode3 : (BLT.bytes d21F3).toBytes = [0x94] ++ d21F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d21F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d21_encode4 : (BLT.bytes d21F4).toBytes = [0x88] ++ d21F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d21F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d21_encode5 : (BLT.bytes d21F5).toBytes = [0xa4] ++ d21F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d21F5.length = 36 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d21_encode6 : (BLT.bytes d21F6).toBytes = [] ++ d21F6 := by
  unfold d21F6
  rw [BLT.toBytes]
  decide +kernel

theorem d21_encode7 : (BLT.bytes d21F7).toBytes = [0xa0] ++ d21F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d21F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d21_encode8 : (BLT.bytes d21F8).toBytes = [0xa0] ++ d21F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d21F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d21_canonical : d21Tx.toBLT.toBytes = d21Signed := by
  have encoded : BLTs.toBytesJoin d21Fields = d21Payload := by
    simp only [d21Fields, BLTs.toBytesJoin,
      d21_encode0, d21_encode1, d21_encode2, d21_encode3, d21_encode4, d21_encode5, d21_encode6, d21_encode7, d21_encode8, d21Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d21_blt, BLT.toBytes, BLTs.toBytes, encoded, d21_payload_length]
  norm_num only [d21Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d22F0 : Bytes := [0x15, 0x75]

def d22F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d22F2 : Bytes := [0x04, 0xc8, 0x0f]

def d22F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d22F4 : Bytes := []

def d22F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d22F6 : Bytes := [0x1b]

def d22F7 : Bytes := [0x0f, 0x68, 0xa1, 0x48, 0xd4, 0x0f, 0x86, 0xd2, 0xfe, 0xb9, 0xdb, 0xc2, 0xaf, 0xdb, 0x24, 0x6e, 0xa7, 0x93, 0x8f, 0xcc, 0xd5, 0xa9, 0x02, 0x75, 0x4d, 0x55, 0xb2, 0x9d, 0x6c, 0xbf, 0xce, 0x78]

def d22F8 : Bytes := [0x50, 0x1a, 0xb9, 0xd8, 0xb7, 0xa1, 0xe2, 0xb2, 0x35, 0xe9, 0xa0, 0xaf, 0x7e, 0xa2, 0x92, 0x43, 0xbc, 0x3c, 0x7b, 0xa1, 0x41, 0xd5, 0xa0, 0xfc, 0xb4, 0xad, 0x3b, 0xf0, 0x5e, 0x4e, 0x4b, 0xec]

def d22Fields : List BLT := [.bytes d22F0, .bytes d22F1, .bytes d22F2, .bytes d22F3, .bytes d22F4, .bytes d22F5, .bytes d22F6, .bytes d22F7, .bytes d22F8]

def d22Payload : Bytes := [0x82] ++ d22F0 ++ [0x84] ++ d22F1 ++ [0x83] ++ d22F2 ++ [0x94] ++ d22F3 ++ [0x80] ++ d22F4 ++ [0x84] ++ d22F5 ++ [] ++ d22F6 ++ [0xa0] ++ d22F7 ++ [0xa0] ++ d22F8

def d22Signed : Bytes := [0xf8, 0x6a] ++ d22Payload

def d22Tx : Tx := { nonce := 5493, gas := 313359, value := 0, data := d22F5, v := 27, r := d22F7, s := d22F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d22_literal : d22Signed = [0xf8, 0x6a, 0x82, 0x15, 0x75, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x0f, 0x68, 0xa1, 0x48, 0xd4, 0x0f, 0x86, 0xd2, 0xfe, 0xb9, 0xdb, 0xc2, 0xaf, 0xdb, 0x24, 0x6e, 0xa7, 0x93, 0x8f, 0xcc, 0xd5, 0xa9, 0x02, 0x75, 0x4d, 0x55, 0xb2, 0x9d, 0x6c, 0xbf, 0xce, 0x78, 0xa0, 0x50, 0x1a, 0xb9, 0xd8, 0xb7, 0xa1, 0xe2, 0xb2, 0x35, 0xe9, 0xa0, 0xaf, 0x7e, 0xa2, 0x92, 0x43, 0xbc, 0x3c, 0x7b, 0xa1, 0x41, 0xd5, 0xa0, 0xfc, 0xb4, 0xad, 0x3b, 0xf0, 0x5e, 0x4e, 0x4b, 0xec] := by
  decide +kernel

theorem d22_payload_length : d22Payload.length = 106 := by
  decide +kernel

theorem d22_signed_length : d22Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d22_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d22Payload = some d22Fields := by
  unfold d22Payload d22Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d22F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d22F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d22F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d22F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d22F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d22F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d22F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d22_parse : d22Signed.toBLT? = some (.list d22Fields) := by
  have outer : Bytes.toBLTDiff? 108 d22Signed = some (.list d22Fields, []) := by
    simpa only [d22Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d22Payload [] d22Fields
        (by rw [d22_payload_length]; decide +kernel) (d22_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d22_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d22_decode :
    (d22Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d22Tx := by
  rw [d22_parse]
  decide +kernel

theorem d22_blt : d22Tx.toBLT = .list d22Fields := by
  norm_num only [d22Tx, d22Fields, d22F0, d22F1, d22F2, d22F3, d22F4, d22F6, d22F7, d22F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d22_encode0 : (BLT.bytes d22F0).toBytes = [0x82] ++ d22F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d22F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d22_encode1 : (BLT.bytes d22F1).toBytes = [0x84] ++ d22F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d22F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d22_encode2 : (BLT.bytes d22F2).toBytes = [0x83] ++ d22F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d22F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d22_encode3 : (BLT.bytes d22F3).toBytes = [0x94] ++ d22F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d22F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d22_encode4 : (BLT.bytes d22F4).toBytes = [0x80] ++ d22F4 := by
  unfold d22F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d22_encode5 : (BLT.bytes d22F5).toBytes = [0x84] ++ d22F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d22F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d22_encode6 : (BLT.bytes d22F6).toBytes = [] ++ d22F6 := by
  unfold d22F6
  rw [BLT.toBytes]
  decide +kernel

theorem d22_encode7 : (BLT.bytes d22F7).toBytes = [0xa0] ++ d22F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d22F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d22_encode8 : (BLT.bytes d22F8).toBytes = [0xa0] ++ d22F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d22F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d22_canonical : d22Tx.toBLT.toBytes = d22Signed := by
  have encoded : BLTs.toBytesJoin d22Fields = d22Payload := by
    simp only [d22Fields, BLTs.toBytesJoin,
      d22_encode0, d22_encode1, d22_encode2, d22_encode3, d22_encode4, d22_encode5, d22_encode6, d22_encode7, d22_encode8, d22Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d22_blt, BLT.toBytes, BLTs.toBytes, encoded, d22_payload_length]
  norm_num only [d22Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d23F0 : Bytes := [0x15, 0x76]

def d23F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d23F2 : Bytes := [0x04, 0xc8, 0x0f]

def d23F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d23F4 : Bytes := []

def d23F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d23F6 : Bytes := [0x1b]

def d23F7 : Bytes := [0x67, 0xa7, 0x66, 0xc4, 0x97, 0xff, 0x45, 0xa1, 0x9a, 0x5e, 0x2b, 0x76, 0x7d, 0x4f, 0xae, 0x02, 0xb1, 0xc0, 0x9e, 0x18, 0x11, 0xd9, 0x8b, 0x6b, 0x53, 0x24, 0x05, 0xb9, 0x06, 0x5b, 0xf0, 0xce]

def d23F8 : Bytes := [0x39, 0x87, 0x43, 0x73, 0x3e, 0x4d, 0x60, 0x7a, 0xec, 0x21, 0x7b, 0x92, 0x0b, 0x60, 0x2c, 0xba, 0xf7, 0xc6, 0x6d, 0xae, 0xcc, 0xe2, 0x3d, 0xb2, 0xc9, 0xcb, 0xdd, 0xbe, 0x03, 0xc5, 0x52, 0x49]

def d23Fields : List BLT := [.bytes d23F0, .bytes d23F1, .bytes d23F2, .bytes d23F3, .bytes d23F4, .bytes d23F5, .bytes d23F6, .bytes d23F7, .bytes d23F8]

def d23Payload : Bytes := [0x82] ++ d23F0 ++ [0x84] ++ d23F1 ++ [0x83] ++ d23F2 ++ [0x94] ++ d23F3 ++ [0x80] ++ d23F4 ++ [0x84] ++ d23F5 ++ [] ++ d23F6 ++ [0xa0] ++ d23F7 ++ [0xa0] ++ d23F8

def d23Signed : Bytes := [0xf8, 0x6a] ++ d23Payload

def d23Tx : Tx := { nonce := 5494, gas := 313359, value := 0, data := d23F5, v := 27, r := d23F7, s := d23F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d23_literal : d23Signed = [0xf8, 0x6a, 0x82, 0x15, 0x76, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x67, 0xa7, 0x66, 0xc4, 0x97, 0xff, 0x45, 0xa1, 0x9a, 0x5e, 0x2b, 0x76, 0x7d, 0x4f, 0xae, 0x02, 0xb1, 0xc0, 0x9e, 0x18, 0x11, 0xd9, 0x8b, 0x6b, 0x53, 0x24, 0x05, 0xb9, 0x06, 0x5b, 0xf0, 0xce, 0xa0, 0x39, 0x87, 0x43, 0x73, 0x3e, 0x4d, 0x60, 0x7a, 0xec, 0x21, 0x7b, 0x92, 0x0b, 0x60, 0x2c, 0xba, 0xf7, 0xc6, 0x6d, 0xae, 0xcc, 0xe2, 0x3d, 0xb2, 0xc9, 0xcb, 0xdd, 0xbe, 0x03, 0xc5, 0x52, 0x49] := by
  decide +kernel

theorem d23_payload_length : d23Payload.length = 106 := by
  decide +kernel

theorem d23_signed_length : d23Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d23_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d23Payload = some d23Fields := by
  unfold d23Payload d23Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d23F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d23F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d23F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d23F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d23F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d23F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d23F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d23_parse : d23Signed.toBLT? = some (.list d23Fields) := by
  have outer : Bytes.toBLTDiff? 108 d23Signed = some (.list d23Fields, []) := by
    simpa only [d23Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d23Payload [] d23Fields
        (by rw [d23_payload_length]; decide +kernel) (d23_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d23_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d23_decode :
    (d23Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d23Tx := by
  rw [d23_parse]
  decide +kernel

theorem d23_blt : d23Tx.toBLT = .list d23Fields := by
  norm_num only [d23Tx, d23Fields, d23F0, d23F1, d23F2, d23F3, d23F4, d23F6, d23F7, d23F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d23_encode0 : (BLT.bytes d23F0).toBytes = [0x82] ++ d23F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d23F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d23_encode1 : (BLT.bytes d23F1).toBytes = [0x84] ++ d23F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d23F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d23_encode2 : (BLT.bytes d23F2).toBytes = [0x83] ++ d23F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d23F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d23_encode3 : (BLT.bytes d23F3).toBytes = [0x94] ++ d23F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d23F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d23_encode4 : (BLT.bytes d23F4).toBytes = [0x80] ++ d23F4 := by
  unfold d23F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d23_encode5 : (BLT.bytes d23F5).toBytes = [0x84] ++ d23F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d23F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d23_encode6 : (BLT.bytes d23F6).toBytes = [] ++ d23F6 := by
  unfold d23F6
  rw [BLT.toBytes]
  decide +kernel

theorem d23_encode7 : (BLT.bytes d23F7).toBytes = [0xa0] ++ d23F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d23F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d23_encode8 : (BLT.bytes d23F8).toBytes = [0xa0] ++ d23F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d23F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d23_canonical : d23Tx.toBLT.toBytes = d23Signed := by
  have encoded : BLTs.toBytesJoin d23Fields = d23Payload := by
    simp only [d23Fields, BLTs.toBytesJoin,
      d23_encode0, d23_encode1, d23_encode2, d23_encode3, d23_encode4, d23_encode5, d23_encode6, d23_encode7, d23_encode8, d23Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d23_blt, BLT.toBytes, BLTs.toBytes, encoded, d23_payload_length]
  norm_num only [d23Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
