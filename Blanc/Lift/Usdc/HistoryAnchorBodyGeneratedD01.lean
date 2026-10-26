import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def d08F0 : Bytes := [0x4e, 0x3a]

def d08F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d08F2 : Bytes := [0x01, 0x86, 0xa0]

def d08F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d08F4 : Bytes := []

def d08F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xed, 0xb5, 0xbd, 0x5b, 0x3c, 0x46, 0x9f, 0x62, 0xa1, 0x9b, 0xc3, 0x70, 0x67, 0xab, 0x7b, 0x6e, 0x80, 0x04, 0xfa, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xef, 0xe5, 0x48]

def d08F6 : Bytes := [0x1b]

def d08F7 : Bytes := [0x7d, 0xb3, 0x7e, 0x97, 0x9e, 0x07, 0xdf, 0x85, 0x92, 0xa5, 0x77, 0xfa, 0xd2, 0x59, 0x5e, 0x15, 0x9c, 0xdb, 0x84, 0x4f, 0x40, 0x67, 0xf5, 0x26, 0xb0, 0x37, 0x90, 0x10, 0x39, 0xf6, 0xce, 0x44]

def d08F8 : Bytes := [0x6f, 0xa3, 0x63, 0x92, 0xca, 0xa3, 0xea, 0x4f, 0xa0, 0xf7, 0x66, 0x63, 0x93, 0xc4, 0x53, 0xee, 0xec, 0x96, 0x4d, 0x2d, 0x53, 0x78, 0x46, 0x26, 0x53, 0x9c, 0x74, 0xea, 0x73, 0xdb, 0x99, 0x90]

def d08Fields : List BLT := [.bytes d08F0, .bytes d08F1, .bytes d08F2, .bytes d08F3, .bytes d08F4, .bytes d08F5, .bytes d08F6, .bytes d08F7, .bytes d08F8]

def d08Payload : Bytes := [0x82] ++ d08F0 ++ [0x85] ++ d08F1 ++ [0x83] ++ d08F2 ++ [0x94] ++ d08F3 ++ [0x80] ++ d08F4 ++ [0xb8, 0x44] ++ d08F5 ++ [] ++ d08F6 ++ [0xa0] ++ d08F7 ++ [0xa0] ++ d08F8

def d08Signed : Bytes := [0xf8, 0xac] ++ d08Payload

def d08Tx : Tx := { nonce := 20026, gas := 100000, value := 0, data := d08F5, v := 27, r := d08F7, s := d08F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d08_literal : d08Signed = [0xf8, 0xac, 0x82, 0x4e, 0x3a, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xed, 0xb5, 0xbd, 0x5b, 0x3c, 0x46, 0x9f, 0x62, 0xa1, 0x9b, 0xc3, 0x70, 0x67, 0xab, 0x7b, 0x6e, 0x80, 0x04, 0xfa, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xef, 0xe5, 0x48, 0x1b, 0xa0, 0x7d, 0xb3, 0x7e, 0x97, 0x9e, 0x07, 0xdf, 0x85, 0x92, 0xa5, 0x77, 0xfa, 0xd2, 0x59, 0x5e, 0x15, 0x9c, 0xdb, 0x84, 0x4f, 0x40, 0x67, 0xf5, 0x26, 0xb0, 0x37, 0x90, 0x10, 0x39, 0xf6, 0xce, 0x44, 0xa0, 0x6f, 0xa3, 0x63, 0x92, 0xca, 0xa3, 0xea, 0x4f, 0xa0, 0xf7, 0x66, 0x63, 0x93, 0xc4, 0x53, 0xee, 0xec, 0x96, 0x4d, 0x2d, 0x53, 0x78, 0x46, 0x26, 0x53, 0x9c, 0x74, 0xea, 0x73, 0xdb, 0x99, 0x90] := by
  decide +kernel

theorem d08_payload_length : d08Payload.length = 172 := by
  decide +kernel

theorem d08_signed_length : d08Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d08_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d08Payload = some d08Fields := by
  unfold d08Payload d08Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d08F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d08F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d08F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d08F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d08F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d08F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d08F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d08_parse : d08Signed.toBLT? = some (.list d08Fields) := by
  have outer : Bytes.toBLTDiff? 174 d08Signed = some (.list d08Fields, []) := by
    simpa only [d08Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d08Payload [] d08Fields
        (by rw [d08_payload_length]; decide +kernel) (d08_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d08_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d08_decode :
    (d08Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d08Tx := by
  rw [d08_parse]
  decide +kernel

theorem d08_blt : d08Tx.toBLT = .list d08Fields := by
  norm_num only [d08Tx, d08Fields, d08F0, d08F1, d08F2, d08F3, d08F4, d08F6, d08F7, d08F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d08_encode0 : (BLT.bytes d08F0).toBytes = [0x82] ++ d08F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d08F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d08_encode1 : (BLT.bytes d08F1).toBytes = [0x85] ++ d08F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d08F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d08_encode2 : (BLT.bytes d08F2).toBytes = [0x83] ++ d08F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d08F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d08_encode3 : (BLT.bytes d08F3).toBytes = [0x94] ++ d08F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d08F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d08_encode4 : (BLT.bytes d08F4).toBytes = [0x80] ++ d08F4 := by
  unfold d08F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d08_encode5 : (BLT.bytes d08F5).toBytes = [0xb8, 0x44] ++ d08F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d08F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d08_encode6 : (BLT.bytes d08F6).toBytes = [] ++ d08F6 := by
  unfold d08F6
  rw [BLT.toBytes]
  decide +kernel

theorem d08_encode7 : (BLT.bytes d08F7).toBytes = [0xa0] ++ d08F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d08F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d08_encode8 : (BLT.bytes d08F8).toBytes = [0xa0] ++ d08F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d08F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d08_canonical : d08Tx.toBLT.toBytes = d08Signed := by
  have encoded : BLTs.toBytesJoin d08Fields = d08Payload := by
    simp only [d08Fields, BLTs.toBytesJoin,
      d08_encode0, d08_encode1, d08_encode2, d08_encode3, d08_encode4, d08_encode5, d08_encode6, d08_encode7, d08_encode8, d08Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d08_blt, BLT.toBytes, BLTs.toBytes, encoded, d08_payload_length]
  norm_num only [d08Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d09F0 : Bytes := [0x4e, 0x3b]

def d09F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d09F2 : Bytes := [0x01, 0x86, 0xa0]

def d09F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d09F4 : Bytes := []

def d09F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xf5, 0x78, 0x00, 0x9a, 0x5d, 0x19, 0x10, 0xcd, 0x69, 0x3e, 0x96, 0xc6, 0xf5, 0x57, 0x81, 0xe6, 0x33, 0xed, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe3, 0xb4, 0x94]

def d09F6 : Bytes := [0x1c]

def d09F7 : Bytes := [0xcd, 0xaa, 0x53, 0x9f, 0x1f, 0x38, 0xb9, 0x12, 0x72, 0xcf, 0x23, 0xf3, 0xc7, 0x25, 0x9b, 0x03, 0x21, 0x54, 0x0e, 0xcc, 0xa5, 0xde, 0x01, 0x09, 0xd8, 0xab, 0x51, 0xe9, 0xd0, 0x4a, 0xee, 0xe7]

def d09F8 : Bytes := [0x70, 0x27, 0x62, 0x0d, 0x8a, 0xc0, 0x4f, 0x7e, 0xf9, 0x7a, 0x65, 0x64, 0x88, 0xbf, 0x49, 0x36, 0xf2, 0x58, 0xa5, 0x27, 0x23, 0x3c, 0x90, 0xab, 0xe4, 0x78, 0x40, 0x36, 0x51, 0x8f, 0x8c, 0x0c]

def d09Fields : List BLT := [.bytes d09F0, .bytes d09F1, .bytes d09F2, .bytes d09F3, .bytes d09F4, .bytes d09F5, .bytes d09F6, .bytes d09F7, .bytes d09F8]

def d09Payload : Bytes := [0x82] ++ d09F0 ++ [0x85] ++ d09F1 ++ [0x83] ++ d09F2 ++ [0x94] ++ d09F3 ++ [0x80] ++ d09F4 ++ [0xb8, 0x44] ++ d09F5 ++ [] ++ d09F6 ++ [0xa0] ++ d09F7 ++ [0xa0] ++ d09F8

def d09Signed : Bytes := [0xf8, 0xac] ++ d09Payload

def d09Tx : Tx := { nonce := 20027, gas := 100000, value := 0, data := d09F5, v := 28, r := d09F7, s := d09F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d09_literal : d09Signed = [0xf8, 0xac, 0x82, 0x4e, 0x3b, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xf5, 0x78, 0x00, 0x9a, 0x5d, 0x19, 0x10, 0xcd, 0x69, 0x3e, 0x96, 0xc6, 0xf5, 0x57, 0x81, 0xe6, 0x33, 0xed, 0x6c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe3, 0xb4, 0x94, 0x1c, 0xa0, 0xcd, 0xaa, 0x53, 0x9f, 0x1f, 0x38, 0xb9, 0x12, 0x72, 0xcf, 0x23, 0xf3, 0xc7, 0x25, 0x9b, 0x03, 0x21, 0x54, 0x0e, 0xcc, 0xa5, 0xde, 0x01, 0x09, 0xd8, 0xab, 0x51, 0xe9, 0xd0, 0x4a, 0xee, 0xe7, 0xa0, 0x70, 0x27, 0x62, 0x0d, 0x8a, 0xc0, 0x4f, 0x7e, 0xf9, 0x7a, 0x65, 0x64, 0x88, 0xbf, 0x49, 0x36, 0xf2, 0x58, 0xa5, 0x27, 0x23, 0x3c, 0x90, 0xab, 0xe4, 0x78, 0x40, 0x36, 0x51, 0x8f, 0x8c, 0x0c] := by
  decide +kernel

theorem d09_payload_length : d09Payload.length = 172 := by
  decide +kernel

theorem d09_signed_length : d09Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d09_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d09Payload = some d09Fields := by
  unfold d09Payload d09Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d09F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d09F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d09F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d09F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d09F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d09F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d09F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d09_parse : d09Signed.toBLT? = some (.list d09Fields) := by
  have outer : Bytes.toBLTDiff? 174 d09Signed = some (.list d09Fields, []) := by
    simpa only [d09Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d09Payload [] d09Fields
        (by rw [d09_payload_length]; decide +kernel) (d09_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d09_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d09_decode :
    (d09Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d09Tx := by
  rw [d09_parse]
  decide +kernel

theorem d09_blt : d09Tx.toBLT = .list d09Fields := by
  norm_num only [d09Tx, d09Fields, d09F0, d09F1, d09F2, d09F3, d09F4, d09F6, d09F7, d09F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d09_encode0 : (BLT.bytes d09F0).toBytes = [0x82] ++ d09F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d09F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d09_encode1 : (BLT.bytes d09F1).toBytes = [0x85] ++ d09F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d09F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d09_encode2 : (BLT.bytes d09F2).toBytes = [0x83] ++ d09F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d09F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d09_encode3 : (BLT.bytes d09F3).toBytes = [0x94] ++ d09F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d09F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d09_encode4 : (BLT.bytes d09F4).toBytes = [0x80] ++ d09F4 := by
  unfold d09F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d09_encode5 : (BLT.bytes d09F5).toBytes = [0xb8, 0x44] ++ d09F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d09F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d09_encode6 : (BLT.bytes d09F6).toBytes = [] ++ d09F6 := by
  unfold d09F6
  rw [BLT.toBytes]
  decide +kernel

theorem d09_encode7 : (BLT.bytes d09F7).toBytes = [0xa0] ++ d09F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d09F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d09_encode8 : (BLT.bytes d09F8).toBytes = [0xa0] ++ d09F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d09F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d09_canonical : d09Tx.toBLT.toBytes = d09Signed := by
  have encoded : BLTs.toBytesJoin d09Fields = d09Payload := by
    simp only [d09Fields, BLTs.toBytesJoin,
      d09_encode0, d09_encode1, d09_encode2, d09_encode3, d09_encode4, d09_encode5, d09_encode6, d09_encode7, d09_encode8, d09Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d09_blt, BLT.toBytes, BLTs.toBytes, encoded, d09_payload_length]
  norm_num only [d09Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d10F0 : Bytes := [0x4e, 0x3c]

def d10F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d10F2 : Bytes := [0x01, 0x86, 0xa0]

def d10F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d10F4 : Bytes := []

def d10F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xf6, 0xb7, 0x09, 0xfc, 0xb2, 0xb1, 0x6f, 0xcc, 0xff, 0x48, 0x7e, 0x22, 0xf3, 0x3b, 0x69, 0x13, 0xe9, 0x5f, 0xc5, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x0b, 0xde, 0x6c]

def d10F6 : Bytes := [0x1b]

def d10F7 : Bytes := [0x76, 0xe8, 0x62, 0x61, 0xed, 0xea, 0xd8, 0x29, 0x6a, 0xba, 0x8c, 0x61, 0xb4, 0xd6, 0xd5, 0x6b, 0x70, 0xc0, 0x0f, 0xa6, 0xd1, 0x37, 0x5c, 0xa3, 0xd3, 0x92, 0x00, 0xea, 0xd8, 0xae, 0x33, 0x2b]

def d10F8 : Bytes := [0x78, 0x12, 0xed, 0xcc, 0xc4, 0x96, 0x15, 0x6d, 0x0b, 0x1c, 0x06, 0x76, 0xce, 0xf5, 0xef, 0x78, 0x94, 0xc4, 0x58, 0xaa, 0xcf, 0x4d, 0x26, 0x2f, 0x71, 0x4a, 0xce, 0xa6, 0xaa, 0xbb, 0x84, 0x30]

def d10Fields : List BLT := [.bytes d10F0, .bytes d10F1, .bytes d10F2, .bytes d10F3, .bytes d10F4, .bytes d10F5, .bytes d10F6, .bytes d10F7, .bytes d10F8]

def d10Payload : Bytes := [0x82] ++ d10F0 ++ [0x85] ++ d10F1 ++ [0x83] ++ d10F2 ++ [0x94] ++ d10F3 ++ [0x80] ++ d10F4 ++ [0xb8, 0x44] ++ d10F5 ++ [] ++ d10F6 ++ [0xa0] ++ d10F7 ++ [0xa0] ++ d10F8

def d10Signed : Bytes := [0xf8, 0xac] ++ d10Payload

def d10Tx : Tx := { nonce := 20028, gas := 100000, value := 0, data := d10F5, v := 27, r := d10F7, s := d10F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d10_literal : d10Signed = [0xf8, 0xac, 0x82, 0x4e, 0x3c, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xf6, 0xb7, 0x09, 0xfc, 0xb2, 0xb1, 0x6f, 0xcc, 0xff, 0x48, 0x7e, 0x22, 0xf3, 0x3b, 0x69, 0x13, 0xe9, 0x5f, 0xc5, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x0b, 0xde, 0x6c, 0x1b, 0xa0, 0x76, 0xe8, 0x62, 0x61, 0xed, 0xea, 0xd8, 0x29, 0x6a, 0xba, 0x8c, 0x61, 0xb4, 0xd6, 0xd5, 0x6b, 0x70, 0xc0, 0x0f, 0xa6, 0xd1, 0x37, 0x5c, 0xa3, 0xd3, 0x92, 0x00, 0xea, 0xd8, 0xae, 0x33, 0x2b, 0xa0, 0x78, 0x12, 0xed, 0xcc, 0xc4, 0x96, 0x15, 0x6d, 0x0b, 0x1c, 0x06, 0x76, 0xce, 0xf5, 0xef, 0x78, 0x94, 0xc4, 0x58, 0xaa, 0xcf, 0x4d, 0x26, 0x2f, 0x71, 0x4a, 0xce, 0xa6, 0xaa, 0xbb, 0x84, 0x30] := by
  decide +kernel

theorem d10_payload_length : d10Payload.length = 172 := by
  decide +kernel

theorem d10_signed_length : d10Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d10_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d10Payload = some d10Fields := by
  unfold d10Payload d10Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d10F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d10F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d10F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d10F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d10F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d10F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d10F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d10_parse : d10Signed.toBLT? = some (.list d10Fields) := by
  have outer : Bytes.toBLTDiff? 174 d10Signed = some (.list d10Fields, []) := by
    simpa only [d10Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d10Payload [] d10Fields
        (by rw [d10_payload_length]; decide +kernel) (d10_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d10_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d10_decode :
    (d10Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d10Tx := by
  rw [d10_parse]
  decide +kernel

theorem d10_blt : d10Tx.toBLT = .list d10Fields := by
  norm_num only [d10Tx, d10Fields, d10F0, d10F1, d10F2, d10F3, d10F4, d10F6, d10F7, d10F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d10_encode0 : (BLT.bytes d10F0).toBytes = [0x82] ++ d10F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d10F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d10_encode1 : (BLT.bytes d10F1).toBytes = [0x85] ++ d10F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d10F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d10_encode2 : (BLT.bytes d10F2).toBytes = [0x83] ++ d10F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d10F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d10_encode3 : (BLT.bytes d10F3).toBytes = [0x94] ++ d10F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d10F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d10_encode4 : (BLT.bytes d10F4).toBytes = [0x80] ++ d10F4 := by
  unfold d10F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d10_encode5 : (BLT.bytes d10F5).toBytes = [0xb8, 0x44] ++ d10F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d10F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d10_encode6 : (BLT.bytes d10F6).toBytes = [] ++ d10F6 := by
  unfold d10F6
  rw [BLT.toBytes]
  decide +kernel

theorem d10_encode7 : (BLT.bytes d10F7).toBytes = [0xa0] ++ d10F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d10F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d10_encode8 : (BLT.bytes d10F8).toBytes = [0xa0] ++ d10F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d10F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d10_canonical : d10Tx.toBLT.toBytes = d10Signed := by
  have encoded : BLTs.toBytesJoin d10Fields = d10Payload := by
    simp only [d10Fields, BLTs.toBytesJoin,
      d10_encode0, d10_encode1, d10_encode2, d10_encode3, d10_encode4, d10_encode5, d10_encode6, d10_encode7, d10_encode8, d10Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d10_blt, BLT.toBytes, BLTs.toBytes, encoded, d10_payload_length]
  norm_num only [d10Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d11F0 : Bytes := [0x4e, 0x3d]

def d11F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d11F2 : Bytes := [0x01, 0x86, 0xa0]

def d11F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d11F4 : Bytes := []

def d11F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x04, 0x5a, 0xa2, 0xa0, 0x22, 0x2c, 0xab, 0x33, 0xa1, 0xee, 0x2a, 0x39, 0x50, 0x7c, 0x0c, 0x53, 0xaf, 0x6f, 0x23, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb4, 0x74, 0x7c]

def d11F6 : Bytes := [0x1b]

def d11F7 : Bytes := [0xf3, 0x7b, 0xfb, 0xb6, 0xf8, 0xbe, 0x6e, 0x5c, 0x71, 0x8b, 0x76, 0xe1, 0xc8, 0x4e, 0x8e, 0x42, 0x5d, 0xd9, 0xb3, 0x5d, 0xbd, 0x2f, 0xb1, 0xc8, 0x10, 0xba, 0x84, 0x0c, 0x19, 0xa2, 0x06, 0x75]

def d11F8 : Bytes := [0x68, 0x66, 0x1a, 0x48, 0x0c, 0x1d, 0x96, 0x51, 0x75, 0x07, 0x6a, 0x8d, 0xd8, 0x58, 0x94, 0xab, 0x06, 0x07, 0x63, 0x7e, 0x6f, 0xab, 0x2f, 0xb6, 0x24, 0x9b, 0x54, 0x0a, 0x72, 0x3e, 0x4d, 0xeb]

def d11Fields : List BLT := [.bytes d11F0, .bytes d11F1, .bytes d11F2, .bytes d11F3, .bytes d11F4, .bytes d11F5, .bytes d11F6, .bytes d11F7, .bytes d11F8]

def d11Payload : Bytes := [0x82] ++ d11F0 ++ [0x85] ++ d11F1 ++ [0x83] ++ d11F2 ++ [0x94] ++ d11F3 ++ [0x80] ++ d11F4 ++ [0xb8, 0x44] ++ d11F5 ++ [] ++ d11F6 ++ [0xa0] ++ d11F7 ++ [0xa0] ++ d11F8

def d11Signed : Bytes := [0xf8, 0xac] ++ d11Payload

def d11Tx : Tx := { nonce := 20029, gas := 100000, value := 0, data := d11F5, v := 27, r := d11F7, s := d11F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d11_literal : d11Signed = [0xf8, 0xac, 0x82, 0x4e, 0x3d, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x04, 0x5a, 0xa2, 0xa0, 0x22, 0x2c, 0xab, 0x33, 0xa1, 0xee, 0x2a, 0x39, 0x50, 0x7c, 0x0c, 0x53, 0xaf, 0x6f, 0x23, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb4, 0x74, 0x7c, 0x1b, 0xa0, 0xf3, 0x7b, 0xfb, 0xb6, 0xf8, 0xbe, 0x6e, 0x5c, 0x71, 0x8b, 0x76, 0xe1, 0xc8, 0x4e, 0x8e, 0x42, 0x5d, 0xd9, 0xb3, 0x5d, 0xbd, 0x2f, 0xb1, 0xc8, 0x10, 0xba, 0x84, 0x0c, 0x19, 0xa2, 0x06, 0x75, 0xa0, 0x68, 0x66, 0x1a, 0x48, 0x0c, 0x1d, 0x96, 0x51, 0x75, 0x07, 0x6a, 0x8d, 0xd8, 0x58, 0x94, 0xab, 0x06, 0x07, 0x63, 0x7e, 0x6f, 0xab, 0x2f, 0xb6, 0x24, 0x9b, 0x54, 0x0a, 0x72, 0x3e, 0x4d, 0xeb] := by
  decide +kernel

theorem d11_payload_length : d11Payload.length = 172 := by
  decide +kernel

theorem d11_signed_length : d11Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d11_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d11Payload = some d11Fields := by
  unfold d11Payload d11Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d11F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d11F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d11F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d11F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d11F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d11F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d11F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d11_parse : d11Signed.toBLT? = some (.list d11Fields) := by
  have outer : Bytes.toBLTDiff? 174 d11Signed = some (.list d11Fields, []) := by
    simpa only [d11Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d11Payload [] d11Fields
        (by rw [d11_payload_length]; decide +kernel) (d11_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d11_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d11_decode :
    (d11Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d11Tx := by
  rw [d11_parse]
  decide +kernel

theorem d11_blt : d11Tx.toBLT = .list d11Fields := by
  norm_num only [d11Tx, d11Fields, d11F0, d11F1, d11F2, d11F3, d11F4, d11F6, d11F7, d11F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d11_encode0 : (BLT.bytes d11F0).toBytes = [0x82] ++ d11F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d11F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d11_encode1 : (BLT.bytes d11F1).toBytes = [0x85] ++ d11F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d11F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d11_encode2 : (BLT.bytes d11F2).toBytes = [0x83] ++ d11F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d11F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d11_encode3 : (BLT.bytes d11F3).toBytes = [0x94] ++ d11F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d11F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d11_encode4 : (BLT.bytes d11F4).toBytes = [0x80] ++ d11F4 := by
  unfold d11F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d11_encode5 : (BLT.bytes d11F5).toBytes = [0xb8, 0x44] ++ d11F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d11F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d11_encode6 : (BLT.bytes d11F6).toBytes = [] ++ d11F6 := by
  unfold d11F6
  rw [BLT.toBytes]
  decide +kernel

theorem d11_encode7 : (BLT.bytes d11F7).toBytes = [0xa0] ++ d11F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d11F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d11_encode8 : (BLT.bytes d11F8).toBytes = [0xa0] ++ d11F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d11F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d11_canonical : d11Tx.toBLT.toBytes = d11Signed := by
  have encoded : BLTs.toBytesJoin d11Fields = d11Payload := by
    simp only [d11Fields, BLTs.toBytesJoin,
      d11_encode0, d11_encode1, d11_encode2, d11_encode3, d11_encode4, d11_encode5, d11_encode6, d11_encode7, d11_encode8, d11Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d11_blt, BLT.toBytes, BLTs.toBytes, encoded, d11_payload_length]
  norm_num only [d11Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d12F0 : Bytes := [0x4e, 0x3e]

def d12F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d12F2 : Bytes := [0x01, 0x86, 0xa0]

def d12F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d12F4 : Bytes := []

def d12F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x0d, 0xaf, 0x1b, 0x06, 0x39, 0x25, 0xaa, 0x71, 0xa0, 0x96, 0xdd, 0xb2, 0x31, 0x3e, 0x08, 0x92, 0x58, 0xec, 0x5f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x19, 0x9d, 0x6c]

def d12F6 : Bytes := [0x1c]

def d12F7 : Bytes := [0xdb, 0x01, 0xc8, 0xfa, 0x36, 0xee, 0xee, 0x40, 0x90, 0xf8, 0xd1, 0xea, 0xa1, 0x7f, 0x18, 0xc7, 0x71, 0x64, 0xa2, 0x3d, 0x46, 0x80, 0x3a, 0xe8, 0x24, 0xcf, 0xd2, 0x01, 0x2a, 0x08, 0xb0, 0x62]

def d12F8 : Bytes := [0x59, 0x9e, 0x60, 0xa3, 0xa8, 0x99, 0x84, 0xa0, 0xf1, 0xce, 0x11, 0xec, 0xb4, 0xdd, 0xaf, 0x55, 0x6a, 0x6f, 0x35, 0x91, 0xf7, 0xfd, 0x14, 0xfe, 0x4b, 0x2f, 0x3d, 0x19, 0xa6, 0xf5, 0xfa, 0x6e]

def d12Fields : List BLT := [.bytes d12F0, .bytes d12F1, .bytes d12F2, .bytes d12F3, .bytes d12F4, .bytes d12F5, .bytes d12F6, .bytes d12F7, .bytes d12F8]

def d12Payload : Bytes := [0x82] ++ d12F0 ++ [0x85] ++ d12F1 ++ [0x83] ++ d12F2 ++ [0x94] ++ d12F3 ++ [0x80] ++ d12F4 ++ [0xb8, 0x44] ++ d12F5 ++ [] ++ d12F6 ++ [0xa0] ++ d12F7 ++ [0xa0] ++ d12F8

def d12Signed : Bytes := [0xf8, 0xac] ++ d12Payload

def d12Tx : Tx := { nonce := 20030, gas := 100000, value := 0, data := d12F5, v := 28, r := d12F7, s := d12F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d12_literal : d12Signed = [0xf8, 0xac, 0x82, 0x4e, 0x3e, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x0d, 0xaf, 0x1b, 0x06, 0x39, 0x25, 0xaa, 0x71, 0xa0, 0x96, 0xdd, 0xb2, 0x31, 0x3e, 0x08, 0x92, 0x58, 0xec, 0x5f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x19, 0x9d, 0x6c, 0x1c, 0xa0, 0xdb, 0x01, 0xc8, 0xfa, 0x36, 0xee, 0xee, 0x40, 0x90, 0xf8, 0xd1, 0xea, 0xa1, 0x7f, 0x18, 0xc7, 0x71, 0x64, 0xa2, 0x3d, 0x46, 0x80, 0x3a, 0xe8, 0x24, 0xcf, 0xd2, 0x01, 0x2a, 0x08, 0xb0, 0x62, 0xa0, 0x59, 0x9e, 0x60, 0xa3, 0xa8, 0x99, 0x84, 0xa0, 0xf1, 0xce, 0x11, 0xec, 0xb4, 0xdd, 0xaf, 0x55, 0x6a, 0x6f, 0x35, 0x91, 0xf7, 0xfd, 0x14, 0xfe, 0x4b, 0x2f, 0x3d, 0x19, 0xa6, 0xf5, 0xfa, 0x6e] := by
  decide +kernel

theorem d12_payload_length : d12Payload.length = 172 := by
  decide +kernel

theorem d12_signed_length : d12Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d12_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d12Payload = some d12Fields := by
  unfold d12Payload d12Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d12F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d12F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d12F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d12F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d12F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d12F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d12F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d12_parse : d12Signed.toBLT? = some (.list d12Fields) := by
  have outer : Bytes.toBLTDiff? 174 d12Signed = some (.list d12Fields, []) := by
    simpa only [d12Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d12Payload [] d12Fields
        (by rw [d12_payload_length]; decide +kernel) (d12_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d12_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d12_decode :
    (d12Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d12Tx := by
  rw [d12_parse]
  decide +kernel

theorem d12_blt : d12Tx.toBLT = .list d12Fields := by
  norm_num only [d12Tx, d12Fields, d12F0, d12F1, d12F2, d12F3, d12F4, d12F6, d12F7, d12F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d12_encode0 : (BLT.bytes d12F0).toBytes = [0x82] ++ d12F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d12F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d12_encode1 : (BLT.bytes d12F1).toBytes = [0x85] ++ d12F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d12F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d12_encode2 : (BLT.bytes d12F2).toBytes = [0x83] ++ d12F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d12F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d12_encode3 : (BLT.bytes d12F3).toBytes = [0x94] ++ d12F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d12F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d12_encode4 : (BLT.bytes d12F4).toBytes = [0x80] ++ d12F4 := by
  unfold d12F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d12_encode5 : (BLT.bytes d12F5).toBytes = [0xb8, 0x44] ++ d12F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d12F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d12_encode6 : (BLT.bytes d12F6).toBytes = [] ++ d12F6 := by
  unfold d12F6
  rw [BLT.toBytes]
  decide +kernel

theorem d12_encode7 : (BLT.bytes d12F7).toBytes = [0xa0] ++ d12F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d12F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d12_encode8 : (BLT.bytes d12F8).toBytes = [0xa0] ++ d12F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d12F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d12_canonical : d12Tx.toBLT.toBytes = d12Signed := by
  have encoded : BLTs.toBytesJoin d12Fields = d12Payload := by
    simp only [d12Fields, BLTs.toBytesJoin,
      d12_encode0, d12_encode1, d12_encode2, d12_encode3, d12_encode4, d12_encode5, d12_encode6, d12_encode7, d12_encode8, d12Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d12_blt, BLT.toBytes, BLTs.toBytes, encoded, d12_payload_length]
  norm_num only [d12Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d13F0 : Bytes := [0x4e, 0x3f]

def d13F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d13F2 : Bytes := [0x01, 0x86, 0xa0]

def d13F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d13F4 : Bytes := []

def d13F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x0f, 0x2c, 0x5e, 0xa8, 0x5c, 0x28, 0x74, 0x94, 0x4c, 0x23, 0x52, 0xeb, 0xb8, 0xa3, 0x59, 0xf6, 0x1b, 0x5e, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe5, 0xf7, 0x7b]

def d13F6 : Bytes := [0x1c]

def d13F7 : Bytes := [0xee, 0xa0, 0x93, 0xfe, 0xfb, 0x24, 0xfc, 0xbb, 0xbb, 0xbd, 0x13, 0x0d, 0x7a, 0x14, 0xd2, 0xa7, 0x91, 0x1b, 0x6b, 0x29, 0x87, 0x8b, 0x46, 0x72, 0xe6, 0xf3, 0x05, 0xc8, 0x09, 0x24, 0x1f, 0x8d]

def d13F8 : Bytes := [0x77, 0xd1, 0x61, 0xa4, 0xa9, 0xd5, 0xbc, 0xae, 0x9c, 0xc5, 0x58, 0x86, 0xf3, 0x23, 0xd1, 0xe9, 0x29, 0x74, 0xd5, 0xae, 0x3f, 0x69, 0x7c, 0x3c, 0xd8, 0xfb, 0x8e, 0x94, 0x0c, 0x3f, 0xb8, 0x4a]

def d13Fields : List BLT := [.bytes d13F0, .bytes d13F1, .bytes d13F2, .bytes d13F3, .bytes d13F4, .bytes d13F5, .bytes d13F6, .bytes d13F7, .bytes d13F8]

def d13Payload : Bytes := [0x82] ++ d13F0 ++ [0x85] ++ d13F1 ++ [0x83] ++ d13F2 ++ [0x94] ++ d13F3 ++ [0x80] ++ d13F4 ++ [0xb8, 0x44] ++ d13F5 ++ [] ++ d13F6 ++ [0xa0] ++ d13F7 ++ [0xa0] ++ d13F8

def d13Signed : Bytes := [0xf8, 0xac] ++ d13Payload

def d13Tx : Tx := { nonce := 20031, gas := 100000, value := 0, data := d13F5, v := 28, r := d13F7, s := d13F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d13_literal : d13Signed = [0xf8, 0xac, 0x82, 0x4e, 0x3f, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x0f, 0x2c, 0x5e, 0xa8, 0x5c, 0x28, 0x74, 0x94, 0x4c, 0x23, 0x52, 0xeb, 0xb8, 0xa3, 0x59, 0xf6, 0x1b, 0x5e, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe5, 0xf7, 0x7b, 0x1c, 0xa0, 0xee, 0xa0, 0x93, 0xfe, 0xfb, 0x24, 0xfc, 0xbb, 0xbb, 0xbd, 0x13, 0x0d, 0x7a, 0x14, 0xd2, 0xa7, 0x91, 0x1b, 0x6b, 0x29, 0x87, 0x8b, 0x46, 0x72, 0xe6, 0xf3, 0x05, 0xc8, 0x09, 0x24, 0x1f, 0x8d, 0xa0, 0x77, 0xd1, 0x61, 0xa4, 0xa9, 0xd5, 0xbc, 0xae, 0x9c, 0xc5, 0x58, 0x86, 0xf3, 0x23, 0xd1, 0xe9, 0x29, 0x74, 0xd5, 0xae, 0x3f, 0x69, 0x7c, 0x3c, 0xd8, 0xfb, 0x8e, 0x94, 0x0c, 0x3f, 0xb8, 0x4a] := by
  decide +kernel

theorem d13_payload_length : d13Payload.length = 172 := by
  decide +kernel

theorem d13_signed_length : d13Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d13_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d13Payload = some d13Fields := by
  unfold d13Payload d13Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d13F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d13F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d13F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d13F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d13F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d13F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d13F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d13_parse : d13Signed.toBLT? = some (.list d13Fields) := by
  have outer : Bytes.toBLTDiff? 174 d13Signed = some (.list d13Fields, []) := by
    simpa only [d13Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d13Payload [] d13Fields
        (by rw [d13_payload_length]; decide +kernel) (d13_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d13_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d13_decode :
    (d13Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d13Tx := by
  rw [d13_parse]
  decide +kernel

theorem d13_blt : d13Tx.toBLT = .list d13Fields := by
  norm_num only [d13Tx, d13Fields, d13F0, d13F1, d13F2, d13F3, d13F4, d13F6, d13F7, d13F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d13_encode0 : (BLT.bytes d13F0).toBytes = [0x82] ++ d13F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d13F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d13_encode1 : (BLT.bytes d13F1).toBytes = [0x85] ++ d13F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d13F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d13_encode2 : (BLT.bytes d13F2).toBytes = [0x83] ++ d13F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d13F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d13_encode3 : (BLT.bytes d13F3).toBytes = [0x94] ++ d13F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d13F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d13_encode4 : (BLT.bytes d13F4).toBytes = [0x80] ++ d13F4 := by
  unfold d13F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d13_encode5 : (BLT.bytes d13F5).toBytes = [0xb8, 0x44] ++ d13F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d13F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d13_encode6 : (BLT.bytes d13F6).toBytes = [] ++ d13F6 := by
  unfold d13F6
  rw [BLT.toBytes]
  decide +kernel

theorem d13_encode7 : (BLT.bytes d13F7).toBytes = [0xa0] ++ d13F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d13F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d13_encode8 : (BLT.bytes d13F8).toBytes = [0xa0] ++ d13F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d13F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d13_canonical : d13Tx.toBLT.toBytes = d13Signed := by
  have encoded : BLTs.toBytesJoin d13Fields = d13Payload := by
    simp only [d13Fields, BLTs.toBytesJoin,
      d13_encode0, d13_encode1, d13_encode2, d13_encode3, d13_encode4, d13_encode5, d13_encode6, d13_encode7, d13_encode8, d13Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d13_blt, BLT.toBytes, BLTs.toBytes, encoded, d13_payload_length]
  norm_num only [d13Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d14F0 : Bytes := [0x4e, 0x40]

def d14F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d14F2 : Bytes := [0x01, 0x86, 0xa0]

def d14F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d14F4 : Bytes := []

def d14F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x0c, 0x20, 0x1e, 0xb3, 0xab, 0x51, 0x99, 0x6a, 0x01, 0x09, 0x5a, 0x34, 0xc1, 0x6f, 0x30, 0x97, 0x3f, 0xfd, 0x77, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x09, 0xf7, 0x8f]

def d14F6 : Bytes := [0x1b]

def d14F7 : Bytes := [0x8b, 0xaf, 0x92, 0xce, 0xa0, 0x50, 0x92, 0xaa, 0x0a, 0x5c, 0xea, 0xff, 0xba, 0x68, 0xb7, 0x84, 0xbb, 0x1c, 0x5f, 0x2c, 0x14, 0x75, 0x07, 0x6c, 0xda, 0xe1, 0x27, 0xba, 0x1e, 0x1e, 0x3a, 0x9c]

def d14F8 : Bytes := [0x4a, 0x96, 0x20, 0x30, 0x81, 0x7c, 0xa5, 0x80, 0x7e, 0x87, 0xfb, 0x66, 0xd3, 0x8b, 0x44, 0xf0, 0x53, 0xcb, 0xfe, 0x34, 0xd8, 0x59, 0xb3, 0xf0, 0x7d, 0xab, 0xe8, 0x25, 0x1f, 0xff, 0x24, 0x2f]

def d14Fields : List BLT := [.bytes d14F0, .bytes d14F1, .bytes d14F2, .bytes d14F3, .bytes d14F4, .bytes d14F5, .bytes d14F6, .bytes d14F7, .bytes d14F8]

def d14Payload : Bytes := [0x82] ++ d14F0 ++ [0x85] ++ d14F1 ++ [0x83] ++ d14F2 ++ [0x94] ++ d14F3 ++ [0x80] ++ d14F4 ++ [0xb8, 0x44] ++ d14F5 ++ [] ++ d14F6 ++ [0xa0] ++ d14F7 ++ [0xa0] ++ d14F8

def d14Signed : Bytes := [0xf8, 0xac] ++ d14Payload

def d14Tx : Tx := { nonce := 20032, gas := 100000, value := 0, data := d14F5, v := 27, r := d14F7, s := d14F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d14_literal : d14Signed = [0xf8, 0xac, 0x82, 0x4e, 0x40, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x0c, 0x20, 0x1e, 0xb3, 0xab, 0x51, 0x99, 0x6a, 0x01, 0x09, 0x5a, 0x34, 0xc1, 0x6f, 0x30, 0x97, 0x3f, 0xfd, 0x77, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x09, 0xf7, 0x8f, 0x1b, 0xa0, 0x8b, 0xaf, 0x92, 0xce, 0xa0, 0x50, 0x92, 0xaa, 0x0a, 0x5c, 0xea, 0xff, 0xba, 0x68, 0xb7, 0x84, 0xbb, 0x1c, 0x5f, 0x2c, 0x14, 0x75, 0x07, 0x6c, 0xda, 0xe1, 0x27, 0xba, 0x1e, 0x1e, 0x3a, 0x9c, 0xa0, 0x4a, 0x96, 0x20, 0x30, 0x81, 0x7c, 0xa5, 0x80, 0x7e, 0x87, 0xfb, 0x66, 0xd3, 0x8b, 0x44, 0xf0, 0x53, 0xcb, 0xfe, 0x34, 0xd8, 0x59, 0xb3, 0xf0, 0x7d, 0xab, 0xe8, 0x25, 0x1f, 0xff, 0x24, 0x2f] := by
  decide +kernel

theorem d14_payload_length : d14Payload.length = 172 := by
  decide +kernel

theorem d14_signed_length : d14Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d14_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d14Payload = some d14Fields := by
  unfold d14Payload d14Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d14F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d14F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d14F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d14F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d14F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d14F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d14F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d14_parse : d14Signed.toBLT? = some (.list d14Fields) := by
  have outer : Bytes.toBLTDiff? 174 d14Signed = some (.list d14Fields, []) := by
    simpa only [d14Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d14Payload [] d14Fields
        (by rw [d14_payload_length]; decide +kernel) (d14_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d14_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d14_decode :
    (d14Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d14Tx := by
  rw [d14_parse]
  decide +kernel

theorem d14_blt : d14Tx.toBLT = .list d14Fields := by
  norm_num only [d14Tx, d14Fields, d14F0, d14F1, d14F2, d14F3, d14F4, d14F6, d14F7, d14F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d14_encode0 : (BLT.bytes d14F0).toBytes = [0x82] ++ d14F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d14F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d14_encode1 : (BLT.bytes d14F1).toBytes = [0x85] ++ d14F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d14F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d14_encode2 : (BLT.bytes d14F2).toBytes = [0x83] ++ d14F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d14F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d14_encode3 : (BLT.bytes d14F3).toBytes = [0x94] ++ d14F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d14F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d14_encode4 : (BLT.bytes d14F4).toBytes = [0x80] ++ d14F4 := by
  unfold d14F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d14_encode5 : (BLT.bytes d14F5).toBytes = [0xb8, 0x44] ++ d14F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d14F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d14_encode6 : (BLT.bytes d14F6).toBytes = [] ++ d14F6 := by
  unfold d14F6
  rw [BLT.toBytes]
  decide +kernel

theorem d14_encode7 : (BLT.bytes d14F7).toBytes = [0xa0] ++ d14F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d14F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d14_encode8 : (BLT.bytes d14F8).toBytes = [0xa0] ++ d14F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d14F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d14_canonical : d14Tx.toBLT.toBytes = d14Signed := by
  have encoded : BLTs.toBytesJoin d14Fields = d14Payload := by
    simp only [d14Fields, BLTs.toBytesJoin,
      d14_encode0, d14_encode1, d14_encode2, d14_encode3, d14_encode4, d14_encode5, d14_encode6, d14_encode7, d14_encode8, d14Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d14_blt, BLT.toBytes, BLTs.toBytes, encoded, d14_payload_length]
  norm_num only [d14Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d15F0 : Bytes := [0x4e, 0x41]

def d15F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d15F2 : Bytes := [0x01, 0x86, 0xa0]

def d15F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d15F4 : Bytes := []

def d15F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x10, 0x68, 0xc6, 0xb1, 0x35, 0x10, 0x28, 0xc1, 0x28, 0x1a, 0x7e, 0x92, 0x62, 0x12, 0x07, 0xbe, 0x63, 0xff, 0x96, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4d, 0x8f, 0x14]

def d15F6 : Bytes := [0x1b]

def d15F7 : Bytes := [0x7e, 0xb2, 0x51, 0x10, 0x6e, 0x64, 0xaa, 0xcf, 0x6a, 0xef, 0xca, 0x58, 0x74, 0xf6, 0xd6, 0x4f, 0x21, 0xed, 0xeb, 0x81, 0x80, 0x69, 0x80, 0xff, 0xcb, 0xea, 0x3c, 0x45, 0xed, 0x38, 0x57, 0x0d]

def d15F8 : Bytes := [0x1f, 0x60, 0xee, 0xa8, 0x48, 0x23, 0x40, 0x38, 0x97, 0x58, 0x82, 0x05, 0xfe, 0x4d, 0x04, 0x18, 0x50, 0xff, 0x57, 0xfc, 0x6c, 0x78, 0x60, 0x7f, 0xa2, 0xe6, 0x2f, 0x41, 0x19, 0x44, 0xe2, 0xf0]

def d15Fields : List BLT := [.bytes d15F0, .bytes d15F1, .bytes d15F2, .bytes d15F3, .bytes d15F4, .bytes d15F5, .bytes d15F6, .bytes d15F7, .bytes d15F8]

def d15Payload : Bytes := [0x82] ++ d15F0 ++ [0x85] ++ d15F1 ++ [0x83] ++ d15F2 ++ [0x94] ++ d15F3 ++ [0x80] ++ d15F4 ++ [0xb8, 0x44] ++ d15F5 ++ [] ++ d15F6 ++ [0xa0] ++ d15F7 ++ [0xa0] ++ d15F8

def d15Signed : Bytes := [0xf8, 0xac] ++ d15Payload

def d15Tx : Tx := { nonce := 20033, gas := 100000, value := 0, data := d15F5, v := 27, r := d15F7, s := d15F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d15_literal : d15Signed = [0xf8, 0xac, 0x82, 0x4e, 0x41, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0x10, 0x68, 0xc6, 0xb1, 0x35, 0x10, 0x28, 0xc1, 0x28, 0x1a, 0x7e, 0x92, 0x62, 0x12, 0x07, 0xbe, 0x63, 0xff, 0x96, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4d, 0x8f, 0x14, 0x1b, 0xa0, 0x7e, 0xb2, 0x51, 0x10, 0x6e, 0x64, 0xaa, 0xcf, 0x6a, 0xef, 0xca, 0x58, 0x74, 0xf6, 0xd6, 0x4f, 0x21, 0xed, 0xeb, 0x81, 0x80, 0x69, 0x80, 0xff, 0xcb, 0xea, 0x3c, 0x45, 0xed, 0x38, 0x57, 0x0d, 0xa0, 0x1f, 0x60, 0xee, 0xa8, 0x48, 0x23, 0x40, 0x38, 0x97, 0x58, 0x82, 0x05, 0xfe, 0x4d, 0x04, 0x18, 0x50, 0xff, 0x57, 0xfc, 0x6c, 0x78, 0x60, 0x7f, 0xa2, 0xe6, 0x2f, 0x41, 0x19, 0x44, 0xe2, 0xf0] := by
  decide +kernel

theorem d15_payload_length : d15Payload.length = 172 := by
  decide +kernel

theorem d15_signed_length : d15Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d15_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d15Payload = some d15Fields := by
  unfold d15Payload d15Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d15F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d15F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d15F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d15F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d15F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d15F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d15F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d15_parse : d15Signed.toBLT? = some (.list d15Fields) := by
  have outer : Bytes.toBLTDiff? 174 d15Signed = some (.list d15Fields, []) := by
    simpa only [d15Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d15Payload [] d15Fields
        (by rw [d15_payload_length]; decide +kernel) (d15_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d15_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d15_decode :
    (d15Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d15Tx := by
  rw [d15_parse]
  decide +kernel

theorem d15_blt : d15Tx.toBLT = .list d15Fields := by
  norm_num only [d15Tx, d15Fields, d15F0, d15F1, d15F2, d15F3, d15F4, d15F6, d15F7, d15F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d15_encode0 : (BLT.bytes d15F0).toBytes = [0x82] ++ d15F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d15F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d15_encode1 : (BLT.bytes d15F1).toBytes = [0x85] ++ d15F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d15F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d15_encode2 : (BLT.bytes d15F2).toBytes = [0x83] ++ d15F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d15F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d15_encode3 : (BLT.bytes d15F3).toBytes = [0x94] ++ d15F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d15F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d15_encode4 : (BLT.bytes d15F4).toBytes = [0x80] ++ d15F4 := by
  unfold d15F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d15_encode5 : (BLT.bytes d15F5).toBytes = [0xb8, 0x44] ++ d15F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d15F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d15_encode6 : (BLT.bytes d15F6).toBytes = [] ++ d15F6 := by
  unfold d15F6
  rw [BLT.toBytes]
  decide +kernel

theorem d15_encode7 : (BLT.bytes d15F7).toBytes = [0xa0] ++ d15F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d15F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d15_encode8 : (BLT.bytes d15F8).toBytes = [0xa0] ++ d15F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d15F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d15_canonical : d15Tx.toBLT.toBytes = d15Signed := by
  have encoded : BLTs.toBytesJoin d15Fields = d15Payload := by
    simp only [d15Fields, BLTs.toBytesJoin,
      d15_encode0, d15_encode1, d15_encode2, d15_encode3, d15_encode4, d15_encode5, d15_encode6, d15_encode7, d15_encode8, d15Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d15_blt, BLT.toBytes, BLTs.toBytes, encoded, d15_payload_length]
  norm_num only [d15Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
