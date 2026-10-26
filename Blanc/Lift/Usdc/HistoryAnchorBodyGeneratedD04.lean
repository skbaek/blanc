import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def d32F0 : Bytes := [0x15, 0x7f]

def d32F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d32F2 : Bytes := [0x04, 0xc8, 0x0f]

def d32F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d32F4 : Bytes := []

def d32F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d32F6 : Bytes := [0x1b]

def d32F7 : Bytes := [0x1f, 0x9b, 0xe6, 0x83, 0x44, 0x43, 0x70, 0x98, 0xc4, 0x13, 0xd0, 0xf6, 0x6c, 0x40, 0x57, 0xce, 0x2a, 0x8c, 0x38, 0x04, 0x47, 0xd2, 0xd3, 0x11, 0x93, 0xa6, 0x73, 0x3f, 0x9f, 0x46, 0xa3, 0x7b]

def d32F8 : Bytes := [0x3b, 0xdc, 0x23, 0xb0, 0xf3, 0xac, 0x7d, 0xe0, 0xc8, 0x9c, 0x76, 0x32, 0x60, 0xa5, 0x02, 0x1b, 0xdf, 0xd6, 0xe6, 0xdf, 0x70, 0xba, 0x35, 0x27, 0xa6, 0xf0, 0x8e, 0xda, 0x4b, 0x8c, 0xeb, 0x07]

def d32Fields : List BLT := [.bytes d32F0, .bytes d32F1, .bytes d32F2, .bytes d32F3, .bytes d32F4, .bytes d32F5, .bytes d32F6, .bytes d32F7, .bytes d32F8]

def d32Payload : Bytes := [0x82] ++ d32F0 ++ [0x84] ++ d32F1 ++ [0x83] ++ d32F2 ++ [0x94] ++ d32F3 ++ [0x80] ++ d32F4 ++ [0x84] ++ d32F5 ++ [] ++ d32F6 ++ [0xa0] ++ d32F7 ++ [0xa0] ++ d32F8

def d32Signed : Bytes := [0xf8, 0x6a] ++ d32Payload

def d32Tx : Tx := { nonce := 5503, gas := 313359, value := 0, data := d32F5, v := 27, r := d32F7, s := d32F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d32_literal : d32Signed = [0xf8, 0x6a, 0x82, 0x15, 0x7f, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x1f, 0x9b, 0xe6, 0x83, 0x44, 0x43, 0x70, 0x98, 0xc4, 0x13, 0xd0, 0xf6, 0x6c, 0x40, 0x57, 0xce, 0x2a, 0x8c, 0x38, 0x04, 0x47, 0xd2, 0xd3, 0x11, 0x93, 0xa6, 0x73, 0x3f, 0x9f, 0x46, 0xa3, 0x7b, 0xa0, 0x3b, 0xdc, 0x23, 0xb0, 0xf3, 0xac, 0x7d, 0xe0, 0xc8, 0x9c, 0x76, 0x32, 0x60, 0xa5, 0x02, 0x1b, 0xdf, 0xd6, 0xe6, 0xdf, 0x70, 0xba, 0x35, 0x27, 0xa6, 0xf0, 0x8e, 0xda, 0x4b, 0x8c, 0xeb, 0x07] := by
  decide +kernel

theorem d32_payload_length : d32Payload.length = 106 := by
  decide +kernel

theorem d32_signed_length : d32Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d32_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d32Payload = some d32Fields := by
  unfold d32Payload d32Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d32F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d32F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d32F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d32F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d32F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d32F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d32F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d32_parse : d32Signed.toBLT? = some (.list d32Fields) := by
  have outer : Bytes.toBLTDiff? 108 d32Signed = some (.list d32Fields, []) := by
    simpa only [d32Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d32Payload [] d32Fields
        (by rw [d32_payload_length]; decide +kernel) (d32_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d32_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d32_decode :
    (d32Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d32Tx := by
  rw [d32_parse]
  decide +kernel

theorem d32_blt : d32Tx.toBLT = .list d32Fields := by
  norm_num only [d32Tx, d32Fields, d32F0, d32F1, d32F2, d32F3, d32F4, d32F6, d32F7, d32F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d32_encode0 : (BLT.bytes d32F0).toBytes = [0x82] ++ d32F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d32F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d32_encode1 : (BLT.bytes d32F1).toBytes = [0x84] ++ d32F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d32F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d32_encode2 : (BLT.bytes d32F2).toBytes = [0x83] ++ d32F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d32F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d32_encode3 : (BLT.bytes d32F3).toBytes = [0x94] ++ d32F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d32F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d32_encode4 : (BLT.bytes d32F4).toBytes = [0x80] ++ d32F4 := by
  unfold d32F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d32_encode5 : (BLT.bytes d32F5).toBytes = [0x84] ++ d32F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d32F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d32_encode6 : (BLT.bytes d32F6).toBytes = [] ++ d32F6 := by
  unfold d32F6
  rw [BLT.toBytes]
  decide +kernel

theorem d32_encode7 : (BLT.bytes d32F7).toBytes = [0xa0] ++ d32F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d32F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d32_encode8 : (BLT.bytes d32F8).toBytes = [0xa0] ++ d32F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d32F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d32_canonical : d32Tx.toBLT.toBytes = d32Signed := by
  have encoded : BLTs.toBytesJoin d32Fields = d32Payload := by
    simp only [d32Fields, BLTs.toBytesJoin,
      d32_encode0, d32_encode1, d32_encode2, d32_encode3, d32_encode4, d32_encode5, d32_encode6, d32_encode7, d32_encode8, d32Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d32_blt, BLT.toBytes, BLTs.toBytes, encoded, d32_payload_length]
  norm_num only [d32Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d33F0 : Bytes := [0x15, 0x80]

def d33F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d33F2 : Bytes := [0x04, 0xc8, 0x0f]

def d33F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d33F4 : Bytes := []

def d33F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d33F6 : Bytes := [0x1b]

def d33F7 : Bytes := [0x2a, 0x5f, 0x3a, 0xff, 0x41, 0x77, 0x3c, 0xf6, 0x80, 0xb2, 0xfb, 0x7f, 0xa0, 0x29, 0x53, 0xb1, 0xda, 0xbc, 0xd3, 0x2b, 0x8a, 0xb2, 0x8c, 0x79, 0x68, 0x1f, 0x1b, 0x4a, 0xf5, 0xf7, 0xb9, 0x66]

def d33F8 : Bytes := [0x0c, 0x7e, 0xec, 0xd8, 0x34, 0xb3, 0xdb, 0xba, 0x0f, 0x75, 0xe0, 0xd2, 0xed, 0xb7, 0xe1, 0x08, 0x02, 0x4b, 0x93, 0x44, 0x83, 0xff, 0x22, 0x46, 0x95, 0xe9, 0x08, 0x55, 0x80, 0x70, 0x37, 0x2a]

def d33Fields : List BLT := [.bytes d33F0, .bytes d33F1, .bytes d33F2, .bytes d33F3, .bytes d33F4, .bytes d33F5, .bytes d33F6, .bytes d33F7, .bytes d33F8]

def d33Payload : Bytes := [0x82] ++ d33F0 ++ [0x84] ++ d33F1 ++ [0x83] ++ d33F2 ++ [0x94] ++ d33F3 ++ [0x80] ++ d33F4 ++ [0x84] ++ d33F5 ++ [] ++ d33F6 ++ [0xa0] ++ d33F7 ++ [0xa0] ++ d33F8

def d33Signed : Bytes := [0xf8, 0x6a] ++ d33Payload

def d33Tx : Tx := { nonce := 5504, gas := 313359, value := 0, data := d33F5, v := 27, r := d33F7, s := d33F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d33_literal : d33Signed = [0xf8, 0x6a, 0x82, 0x15, 0x80, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x2a, 0x5f, 0x3a, 0xff, 0x41, 0x77, 0x3c, 0xf6, 0x80, 0xb2, 0xfb, 0x7f, 0xa0, 0x29, 0x53, 0xb1, 0xda, 0xbc, 0xd3, 0x2b, 0x8a, 0xb2, 0x8c, 0x79, 0x68, 0x1f, 0x1b, 0x4a, 0xf5, 0xf7, 0xb9, 0x66, 0xa0, 0x0c, 0x7e, 0xec, 0xd8, 0x34, 0xb3, 0xdb, 0xba, 0x0f, 0x75, 0xe0, 0xd2, 0xed, 0xb7, 0xe1, 0x08, 0x02, 0x4b, 0x93, 0x44, 0x83, 0xff, 0x22, 0x46, 0x95, 0xe9, 0x08, 0x55, 0x80, 0x70, 0x37, 0x2a] := by
  decide +kernel

theorem d33_payload_length : d33Payload.length = 106 := by
  decide +kernel

theorem d33_signed_length : d33Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d33_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d33Payload = some d33Fields := by
  unfold d33Payload d33Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d33F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d33F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d33F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d33F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d33F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d33F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d33F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d33_parse : d33Signed.toBLT? = some (.list d33Fields) := by
  have outer : Bytes.toBLTDiff? 108 d33Signed = some (.list d33Fields, []) := by
    simpa only [d33Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d33Payload [] d33Fields
        (by rw [d33_payload_length]; decide +kernel) (d33_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d33_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d33_decode :
    (d33Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d33Tx := by
  rw [d33_parse]
  decide +kernel

theorem d33_blt : d33Tx.toBLT = .list d33Fields := by
  norm_num only [d33Tx, d33Fields, d33F0, d33F1, d33F2, d33F3, d33F4, d33F6, d33F7, d33F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d33_encode0 : (BLT.bytes d33F0).toBytes = [0x82] ++ d33F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d33F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d33_encode1 : (BLT.bytes d33F1).toBytes = [0x84] ++ d33F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d33F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d33_encode2 : (BLT.bytes d33F2).toBytes = [0x83] ++ d33F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d33F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d33_encode3 : (BLT.bytes d33F3).toBytes = [0x94] ++ d33F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d33F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d33_encode4 : (BLT.bytes d33F4).toBytes = [0x80] ++ d33F4 := by
  unfold d33F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d33_encode5 : (BLT.bytes d33F5).toBytes = [0x84] ++ d33F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d33F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d33_encode6 : (BLT.bytes d33F6).toBytes = [] ++ d33F6 := by
  unfold d33F6
  rw [BLT.toBytes]
  decide +kernel

theorem d33_encode7 : (BLT.bytes d33F7).toBytes = [0xa0] ++ d33F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d33F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d33_encode8 : (BLT.bytes d33F8).toBytes = [0xa0] ++ d33F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d33F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d33_canonical : d33Tx.toBLT.toBytes = d33Signed := by
  have encoded : BLTs.toBytesJoin d33Fields = d33Payload := by
    simp only [d33Fields, BLTs.toBytesJoin,
      d33_encode0, d33_encode1, d33_encode2, d33_encode3, d33_encode4, d33_encode5, d33_encode6, d33_encode7, d33_encode8, d33Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d33_blt, BLT.toBytes, BLTs.toBytes, encoded, d33_payload_length]
  norm_num only [d33Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d34F0 : Bytes := [0x15, 0x81]

def d34F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d34F2 : Bytes := [0x04, 0xc8, 0x0f]

def d34F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d34F4 : Bytes := []

def d34F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d34F6 : Bytes := [0x1c]

def d34F7 : Bytes := [0x3d, 0x44, 0x63, 0xf1, 0x02, 0x2e, 0xc1, 0xc5, 0x22, 0x4d, 0x54, 0xd8, 0xbd, 0xd8, 0x59, 0x7b, 0x07, 0x74, 0xae, 0xd2, 0x09, 0x20, 0x91, 0x31, 0xf9, 0x93, 0x35, 0x17, 0x64, 0xe1, 0xd8, 0x3a]

def d34F8 : Bytes := [0x28, 0x0e, 0x61, 0x4d, 0x5b, 0xda, 0xb6, 0xa4, 0x9c, 0x1c, 0xe2, 0x1f, 0x74, 0x8e, 0x2f, 0x47, 0xa7, 0x18, 0x4f, 0x41, 0x8f, 0xf8, 0x85, 0x52, 0x63, 0xb2, 0xf4, 0xb4, 0xe0, 0x89, 0x8d, 0x39]

def d34Fields : List BLT := [.bytes d34F0, .bytes d34F1, .bytes d34F2, .bytes d34F3, .bytes d34F4, .bytes d34F5, .bytes d34F6, .bytes d34F7, .bytes d34F8]

def d34Payload : Bytes := [0x82] ++ d34F0 ++ [0x84] ++ d34F1 ++ [0x83] ++ d34F2 ++ [0x94] ++ d34F3 ++ [0x80] ++ d34F4 ++ [0x84] ++ d34F5 ++ [] ++ d34F6 ++ [0xa0] ++ d34F7 ++ [0xa0] ++ d34F8

def d34Signed : Bytes := [0xf8, 0x6a] ++ d34Payload

def d34Tx : Tx := { nonce := 5505, gas := 313359, value := 0, data := d34F5, v := 28, r := d34F7, s := d34F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d34_literal : d34Signed = [0xf8, 0x6a, 0x82, 0x15, 0x81, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1c, 0xa0, 0x3d, 0x44, 0x63, 0xf1, 0x02, 0x2e, 0xc1, 0xc5, 0x22, 0x4d, 0x54, 0xd8, 0xbd, 0xd8, 0x59, 0x7b, 0x07, 0x74, 0xae, 0xd2, 0x09, 0x20, 0x91, 0x31, 0xf9, 0x93, 0x35, 0x17, 0x64, 0xe1, 0xd8, 0x3a, 0xa0, 0x28, 0x0e, 0x61, 0x4d, 0x5b, 0xda, 0xb6, 0xa4, 0x9c, 0x1c, 0xe2, 0x1f, 0x74, 0x8e, 0x2f, 0x47, 0xa7, 0x18, 0x4f, 0x41, 0x8f, 0xf8, 0x85, 0x52, 0x63, 0xb2, 0xf4, 0xb4, 0xe0, 0x89, 0x8d, 0x39] := by
  decide +kernel

theorem d34_payload_length : d34Payload.length = 106 := by
  decide +kernel

theorem d34_signed_length : d34Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d34_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d34Payload = some d34Fields := by
  unfold d34Payload d34Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d34F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d34F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d34F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d34F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d34F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d34F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d34F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d34_parse : d34Signed.toBLT? = some (.list d34Fields) := by
  have outer : Bytes.toBLTDiff? 108 d34Signed = some (.list d34Fields, []) := by
    simpa only [d34Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d34Payload [] d34Fields
        (by rw [d34_payload_length]; decide +kernel) (d34_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d34_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d34_decode :
    (d34Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d34Tx := by
  rw [d34_parse]
  decide +kernel

theorem d34_blt : d34Tx.toBLT = .list d34Fields := by
  norm_num only [d34Tx, d34Fields, d34F0, d34F1, d34F2, d34F3, d34F4, d34F6, d34F7, d34F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d34_encode0 : (BLT.bytes d34F0).toBytes = [0x82] ++ d34F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d34F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d34_encode1 : (BLT.bytes d34F1).toBytes = [0x84] ++ d34F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d34F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d34_encode2 : (BLT.bytes d34F2).toBytes = [0x83] ++ d34F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d34F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d34_encode3 : (BLT.bytes d34F3).toBytes = [0x94] ++ d34F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d34F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d34_encode4 : (BLT.bytes d34F4).toBytes = [0x80] ++ d34F4 := by
  unfold d34F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d34_encode5 : (BLT.bytes d34F5).toBytes = [0x84] ++ d34F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d34F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d34_encode6 : (BLT.bytes d34F6).toBytes = [] ++ d34F6 := by
  unfold d34F6
  rw [BLT.toBytes]
  decide +kernel

theorem d34_encode7 : (BLT.bytes d34F7).toBytes = [0xa0] ++ d34F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d34F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d34_encode8 : (BLT.bytes d34F8).toBytes = [0xa0] ++ d34F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d34F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d34_canonical : d34Tx.toBLT.toBytes = d34Signed := by
  have encoded : BLTs.toBytesJoin d34Fields = d34Payload := by
    simp only [d34Fields, BLTs.toBytesJoin,
      d34_encode0, d34_encode1, d34_encode2, d34_encode3, d34_encode4, d34_encode5, d34_encode6, d34_encode7, d34_encode8, d34Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d34_blt, BLT.toBytes, BLTs.toBytes, encoded, d34_payload_length]
  norm_num only [d34Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d35F0 : Bytes := [0x15, 0x82]

def d35F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d35F2 : Bytes := [0x04, 0xc8, 0x0f]

def d35F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d35F4 : Bytes := []

def d35F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d35F6 : Bytes := [0x1c]

def d35F7 : Bytes := [0x76, 0xfb, 0xdd, 0x87, 0x0a, 0x93, 0xcf, 0x8f, 0x34, 0xb5, 0xb9, 0xdc, 0x1d, 0x41, 0xc9, 0x35, 0x83, 0xbb, 0x6a, 0x53, 0x5a, 0x6e, 0x02, 0x16, 0x2b, 0x2b, 0x3c, 0xe5, 0x23, 0xa4, 0xed, 0x0c]

def d35F8 : Bytes := [0x20, 0xf9, 0xeb, 0x6a, 0x1f, 0x2e, 0xc0, 0xd3, 0x13, 0x9d, 0xbb, 0x33, 0xe0, 0xee, 0xce, 0x8d, 0xf9, 0x74, 0x09, 0xf5, 0x93, 0x75, 0xcc, 0x65, 0x8e, 0x59, 0x01, 0xce, 0xf2, 0xf6, 0x2f, 0xec]

def d35Fields : List BLT := [.bytes d35F0, .bytes d35F1, .bytes d35F2, .bytes d35F3, .bytes d35F4, .bytes d35F5, .bytes d35F6, .bytes d35F7, .bytes d35F8]

def d35Payload : Bytes := [0x82] ++ d35F0 ++ [0x84] ++ d35F1 ++ [0x83] ++ d35F2 ++ [0x94] ++ d35F3 ++ [0x80] ++ d35F4 ++ [0x84] ++ d35F5 ++ [] ++ d35F6 ++ [0xa0] ++ d35F7 ++ [0xa0] ++ d35F8

def d35Signed : Bytes := [0xf8, 0x6a] ++ d35Payload

def d35Tx : Tx := { nonce := 5506, gas := 313359, value := 0, data := d35F5, v := 28, r := d35F7, s := d35F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d35_literal : d35Signed = [0xf8, 0x6a, 0x82, 0x15, 0x82, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1c, 0xa0, 0x76, 0xfb, 0xdd, 0x87, 0x0a, 0x93, 0xcf, 0x8f, 0x34, 0xb5, 0xb9, 0xdc, 0x1d, 0x41, 0xc9, 0x35, 0x83, 0xbb, 0x6a, 0x53, 0x5a, 0x6e, 0x02, 0x16, 0x2b, 0x2b, 0x3c, 0xe5, 0x23, 0xa4, 0xed, 0x0c, 0xa0, 0x20, 0xf9, 0xeb, 0x6a, 0x1f, 0x2e, 0xc0, 0xd3, 0x13, 0x9d, 0xbb, 0x33, 0xe0, 0xee, 0xce, 0x8d, 0xf9, 0x74, 0x09, 0xf5, 0x93, 0x75, 0xcc, 0x65, 0x8e, 0x59, 0x01, 0xce, 0xf2, 0xf6, 0x2f, 0xec] := by
  decide +kernel

theorem d35_payload_length : d35Payload.length = 106 := by
  decide +kernel

theorem d35_signed_length : d35Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d35_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d35Payload = some d35Fields := by
  unfold d35Payload d35Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d35F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d35F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d35F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d35F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d35F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d35F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d35F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d35_parse : d35Signed.toBLT? = some (.list d35Fields) := by
  have outer : Bytes.toBLTDiff? 108 d35Signed = some (.list d35Fields, []) := by
    simpa only [d35Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d35Payload [] d35Fields
        (by rw [d35_payload_length]; decide +kernel) (d35_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d35_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d35_decode :
    (d35Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d35Tx := by
  rw [d35_parse]
  decide +kernel

theorem d35_blt : d35Tx.toBLT = .list d35Fields := by
  norm_num only [d35Tx, d35Fields, d35F0, d35F1, d35F2, d35F3, d35F4, d35F6, d35F7, d35F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d35_encode0 : (BLT.bytes d35F0).toBytes = [0x82] ++ d35F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d35F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d35_encode1 : (BLT.bytes d35F1).toBytes = [0x84] ++ d35F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d35F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d35_encode2 : (BLT.bytes d35F2).toBytes = [0x83] ++ d35F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d35F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d35_encode3 : (BLT.bytes d35F3).toBytes = [0x94] ++ d35F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d35F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d35_encode4 : (BLT.bytes d35F4).toBytes = [0x80] ++ d35F4 := by
  unfold d35F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d35_encode5 : (BLT.bytes d35F5).toBytes = [0x84] ++ d35F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d35F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d35_encode6 : (BLT.bytes d35F6).toBytes = [] ++ d35F6 := by
  unfold d35F6
  rw [BLT.toBytes]
  decide +kernel

theorem d35_encode7 : (BLT.bytes d35F7).toBytes = [0xa0] ++ d35F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d35F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d35_encode8 : (BLT.bytes d35F8).toBytes = [0xa0] ++ d35F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d35F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d35_canonical : d35Tx.toBLT.toBytes = d35Signed := by
  have encoded : BLTs.toBytesJoin d35Fields = d35Payload := by
    simp only [d35Fields, BLTs.toBytesJoin,
      d35_encode0, d35_encode1, d35_encode2, d35_encode3, d35_encode4, d35_encode5, d35_encode6, d35_encode7, d35_encode8, d35Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d35_blt, BLT.toBytes, BLTs.toBytes, encoded, d35_payload_length]
  norm_num only [d35Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d36F0 : Bytes := [0x01]

def d36F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d36F2 : Bytes := [0x2d, 0xc6, 0xc0]

def d36F3 : Bytes := [0xf0, 0x54, 0x2e, 0xd4, 0x4d, 0x26, 0x8c, 0x85, 0x87, 0x5b, 0x3b, 0x84, 0xb0, 0xe7, 0xce, 0x07, 0x73, 0xe9, 0xae, 0xef]

def d36F4 : Bytes := [0x01, 0x63, 0x45, 0x78, 0x5d, 0x8a, 0x00, 0x00]

def d36F5 : Bytes := [0x32, 0x2f, 0x62, 0xba, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

def d36F6 : Bytes := [0x25]

def d36F7 : Bytes := [0x3b, 0x63, 0x75, 0xd8, 0xe4, 0x55, 0x9c, 0x5f, 0x20, 0xf1, 0x6e, 0xb0, 0x2b, 0x56, 0x6b, 0x3c, 0x5e, 0x38, 0x4c, 0x92, 0x37, 0x03, 0xb9, 0x5c, 0xb1, 0x43, 0x00, 0x67, 0xce, 0x7d, 0x23, 0x6d]

def d36F8 : Bytes := [0x30, 0x2c, 0xff, 0x58, 0xe7, 0x94, 0x69, 0x0f, 0xb9, 0x26, 0x57, 0xb9, 0xd7, 0x35, 0x18, 0x03, 0xb9, 0xc3, 0x3d, 0x26, 0x06, 0x9e, 0xeb, 0x6b, 0xb8, 0x95, 0xb2, 0x42, 0x63, 0xe4, 0xff, 0xbe]

def d36Fields : List BLT := [.bytes d36F0, .bytes d36F1, .bytes d36F2, .bytes d36F3, .bytes d36F4, .bytes d36F5, .bytes d36F6, .bytes d36F7, .bytes d36F8]

def d36Payload : Bytes := [] ++ d36F0 ++ [0x84] ++ d36F1 ++ [0x83] ++ d36F2 ++ [0x94] ++ d36F3 ++ [0x88] ++ d36F4 ++ [0xa4] ++ d36F5 ++ [] ++ d36F6 ++ [0xa0] ++ d36F7 ++ [0xa0] ++ d36F8

def d36Signed : Bytes := [0xf8, 0x90] ++ d36Payload

def d36Tx : Tx := { nonce := 1, gas := 3000000, value := 100000000000000000, data := d36F5, v := 37, r := d36F7, s := d36F8, type := .zero 4000000000 (some 0xf0542ed44d268c85875b3b84b0e7ce0773e9aeef) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d36_literal : d36Signed = [0xf8, 0x90, 0x01, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x2d, 0xc6, 0xc0, 0x94, 0xf0, 0x54, 0x2e, 0xd4, 0x4d, 0x26, 0x8c, 0x85, 0x87, 0x5b, 0x3b, 0x84, 0xb0, 0xe7, 0xce, 0x07, 0x73, 0xe9, 0xae, 0xef, 0x88, 0x01, 0x63, 0x45, 0x78, 0x5d, 0x8a, 0x00, 0x00, 0xa4, 0x32, 0x2f, 0x62, 0xba, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0xa0, 0x3b, 0x63, 0x75, 0xd8, 0xe4, 0x55, 0x9c, 0x5f, 0x20, 0xf1, 0x6e, 0xb0, 0x2b, 0x56, 0x6b, 0x3c, 0x5e, 0x38, 0x4c, 0x92, 0x37, 0x03, 0xb9, 0x5c, 0xb1, 0x43, 0x00, 0x67, 0xce, 0x7d, 0x23, 0x6d, 0xa0, 0x30, 0x2c, 0xff, 0x58, 0xe7, 0x94, 0x69, 0x0f, 0xb9, 0x26, 0x57, 0xb9, 0xd7, 0x35, 0x18, 0x03, 0xb9, 0xc3, 0x3d, 0x26, 0x06, 0x9e, 0xeb, 0x6b, 0xb8, 0x95, 0xb2, 0x42, 0x63, 0xe4, 0xff, 0xbe] := by
  decide +kernel

theorem d36_payload_length : d36Payload.length = 144 := by
  decide +kernel

theorem d36_signed_length : d36Signed.length = 146 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d36_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d36Payload = some d36Fields := by
  unfold d36Payload d36Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d36F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d36F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d36F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 d36F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 36 d36F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d36F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d36F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d36_parse : d36Signed.toBLT? = some (.list d36Fields) := by
  have outer : Bytes.toBLTDiff? 146 d36Signed = some (.list d36Fields, []) := by
    simpa only [d36Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 145 144 d36Payload [] d36Fields
        (by rw [d36_payload_length]; decide +kernel) (d36_payload_parse 136)
  unfold Bytes.toBLT?
  rw [d36_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d36_decode :
    (d36Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d36Tx := by
  rw [d36_parse]
  decide +kernel

theorem d36_blt : d36Tx.toBLT = .list d36Fields := by
  norm_num only [d36Tx, d36Fields, d36F0, d36F1, d36F2, d36F3, d36F4, d36F6, d36F7, d36F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d36_encode0 : (BLT.bytes d36F0).toBytes = [] ++ d36F0 := by
  unfold d36F0
  rw [BLT.toBytes]
  decide +kernel

theorem d36_encode1 : (BLT.bytes d36F1).toBytes = [0x84] ++ d36F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d36F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d36_encode2 : (BLT.bytes d36F2).toBytes = [0x83] ++ d36F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d36F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d36_encode3 : (BLT.bytes d36F3).toBytes = [0x94] ++ d36F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d36F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d36_encode4 : (BLT.bytes d36F4).toBytes = [0x88] ++ d36F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d36F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d36_encode5 : (BLT.bytes d36F5).toBytes = [0xa4] ++ d36F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d36F5.length = 36 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d36_encode6 : (BLT.bytes d36F6).toBytes = [] ++ d36F6 := by
  unfold d36F6
  rw [BLT.toBytes]
  decide +kernel

theorem d36_encode7 : (BLT.bytes d36F7).toBytes = [0xa0] ++ d36F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d36F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d36_encode8 : (BLT.bytes d36F8).toBytes = [0xa0] ++ d36F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d36F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d36_canonical : d36Tx.toBLT.toBytes = d36Signed := by
  have encoded : BLTs.toBytesJoin d36Fields = d36Payload := by
    simp only [d36Fields, BLTs.toBytesJoin,
      d36_encode0, d36_encode1, d36_encode2, d36_encode3, d36_encode4, d36_encode5, d36_encode6, d36_encode7, d36_encode8, d36Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d36_blt, BLT.toBytes, BLTs.toBytes, encoded, d36_payload_length]
  norm_num only [d36Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d37F0 : Bytes := [0x09]

def d37F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d37F2 : Bytes := [0x20, 0x0b, 0x20]

def d37F3 : Bytes := [0xf9, 0x36, 0x98, 0x7b, 0x8c, 0x35, 0xd1, 0xf8, 0xdb, 0xb7, 0x6d, 0x11, 0x4a, 0x68, 0x92, 0x93, 0xb0, 0x08, 0xd5, 0x3e]

def d37F4 : Bytes := [0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00]

def d37F5 : Bytes := [0x0c, 0x7c, 0x0c, 0x0f]

def d37F6 : Bytes := [0x25]

def d37F7 : Bytes := [0x1d, 0xdd, 0x3f, 0x5e, 0x65, 0xcf, 0xca, 0xbd, 0x55, 0x32, 0xe9, 0x9a, 0x45, 0x96, 0x6e, 0x04, 0x6a, 0xf8, 0xf3, 0x8c, 0x34, 0xd7, 0x01, 0x50, 0x86, 0x5b, 0x32, 0x8d, 0xab, 0xf6, 0x1a, 0xcc]

def d37F8 : Bytes := [0x7c, 0x05, 0x27, 0x0c, 0xeb, 0x06, 0xc7, 0x6a, 0x1d, 0x4f, 0x8c, 0x81, 0x94, 0x3a, 0xb3, 0x86, 0xf4, 0xdf, 0xbd, 0x8f, 0x8d, 0x74, 0x3b, 0x10, 0xea, 0x33, 0xf1, 0x00, 0x99, 0xad, 0x79, 0x79]

def d37Fields : List BLT := [.bytes d37F0, .bytes d37F1, .bytes d37F2, .bytes d37F3, .bytes d37F4, .bytes d37F5, .bytes d37F6, .bytes d37F7, .bytes d37F8]

def d37Payload : Bytes := [] ++ d37F0 ++ [0x84] ++ d37F1 ++ [0x83] ++ d37F2 ++ [0x94] ++ d37F3 ++ [0x88] ++ d37F4 ++ [0x84] ++ d37F5 ++ [] ++ d37F6 ++ [0xa0] ++ d37F7 ++ [0xa0] ++ d37F8

def d37Signed : Bytes := [0xf8, 0x70] ++ d37Payload

def d37Tx : Tx := { nonce := 9, gas := 2100000, value := 1000000000000000000, data := d37F5, v := 37, r := d37F7, s := d37F8, type := .zero 4000000000 (some 0xf936987b8c35d1f8dbb76d114a689293b008d53e) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d37_literal : d37Signed = [0xf8, 0x70, 0x09, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x20, 0x0b, 0x20, 0x94, 0xf9, 0x36, 0x98, 0x7b, 0x8c, 0x35, 0xd1, 0xf8, 0xdb, 0xb7, 0x6d, 0x11, 0x4a, 0x68, 0x92, 0x93, 0xb0, 0x08, 0xd5, 0x3e, 0x88, 0x0d, 0xe0, 0xb6, 0xb3, 0xa7, 0x64, 0x00, 0x00, 0x84, 0x0c, 0x7c, 0x0c, 0x0f, 0x25, 0xa0, 0x1d, 0xdd, 0x3f, 0x5e, 0x65, 0xcf, 0xca, 0xbd, 0x55, 0x32, 0xe9, 0x9a, 0x45, 0x96, 0x6e, 0x04, 0x6a, 0xf8, 0xf3, 0x8c, 0x34, 0xd7, 0x01, 0x50, 0x86, 0x5b, 0x32, 0x8d, 0xab, 0xf6, 0x1a, 0xcc, 0xa0, 0x7c, 0x05, 0x27, 0x0c, 0xeb, 0x06, 0xc7, 0x6a, 0x1d, 0x4f, 0x8c, 0x81, 0x94, 0x3a, 0xb3, 0x86, 0xf4, 0xdf, 0xbd, 0x8f, 0x8d, 0x74, 0x3b, 0x10, 0xea, 0x33, 0xf1, 0x00, 0x99, 0xad, 0x79, 0x79] := by
  decide +kernel

theorem d37_payload_length : d37Payload.length = 112 := by
  decide +kernel

theorem d37_signed_length : d37Signed.length = 114 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d37_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d37Payload = some d37Fields := by
  unfold d37Payload d37Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d37F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d37F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d37F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 d37F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d37F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d37F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d37F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d37_parse : d37Signed.toBLT? = some (.list d37Fields) := by
  have outer : Bytes.toBLTDiff? 114 d37Signed = some (.list d37Fields, []) := by
    simpa only [d37Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 113 112 d37Payload [] d37Fields
        (by rw [d37_payload_length]; decide +kernel) (d37_payload_parse 104)
  unfold Bytes.toBLT?
  rw [d37_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d37_decode :
    (d37Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d37Tx := by
  rw [d37_parse]
  decide +kernel

theorem d37_blt : d37Tx.toBLT = .list d37Fields := by
  norm_num only [d37Tx, d37Fields, d37F0, d37F1, d37F2, d37F3, d37F4, d37F6, d37F7, d37F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d37_encode0 : (BLT.bytes d37F0).toBytes = [] ++ d37F0 := by
  unfold d37F0
  rw [BLT.toBytes]
  decide +kernel

theorem d37_encode1 : (BLT.bytes d37F1).toBytes = [0x84] ++ d37F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d37F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d37_encode2 : (BLT.bytes d37F2).toBytes = [0x83] ++ d37F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d37F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d37_encode3 : (BLT.bytes d37F3).toBytes = [0x94] ++ d37F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d37F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d37_encode4 : (BLT.bytes d37F4).toBytes = [0x88] ++ d37F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d37F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d37_encode5 : (BLT.bytes d37F5).toBytes = [0x84] ++ d37F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d37F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d37_encode6 : (BLT.bytes d37F6).toBytes = [] ++ d37F6 := by
  unfold d37F6
  rw [BLT.toBytes]
  decide +kernel

theorem d37_encode7 : (BLT.bytes d37F7).toBytes = [0xa0] ++ d37F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d37F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d37_encode8 : (BLT.bytes d37F8).toBytes = [0xa0] ++ d37F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d37F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d37_canonical : d37Tx.toBLT.toBytes = d37Signed := by
  have encoded : BLTs.toBytesJoin d37Fields = d37Payload := by
    simp only [d37Fields, BLTs.toBytesJoin,
      d37_encode0, d37_encode1, d37_encode2, d37_encode3, d37_encode4, d37_encode5, d37_encode6, d37_encode7, d37_encode8, d37Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d37_blt, BLT.toBytes, BLTs.toBytes, encoded, d37_payload_length]
  norm_num only [d37Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d38F0 : Bytes := [0xcd]

def d38F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d38F2 : Bytes := [0x39, 0x86, 0xdf]

def d38F3 : Bytes := [0x5c, 0x69, 0xbe, 0xe7, 0x01, 0xef, 0x81, 0x4a, 0x2b, 0x6a, 0x3e, 0xdd, 0x4b, 0x16, 0x52, 0xcb, 0x9c, 0xc5, 0xaa, 0x6f]

def d38F4 : Bytes := []

def d38F5 : Bytes := [0xc9, 0xc6, 0x53, 0x96, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x2a, 0xaa, 0x39, 0xb2, 0x23, 0xfe, 0x8d, 0x0a, 0x0e, 0x5c, 0x4f, 0x27, 0xea, 0xd9, 0x08, 0x3c, 0x75, 0x6c, 0xc2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0xb8, 0x69, 0x91, 0xc6, 0x21, 0x8b, 0x36, 0xc1, 0xd1, 0x9d, 0x4a, 0x2e, 0x9e, 0xb0, 0xce, 0x36, 0x06, 0xeb, 0x48]

def d38F6 : Bytes := [0x26]

def d38F7 : Bytes := [0xf9, 0xe4, 0x6c, 0x09, 0xc6, 0xb6, 0x2c, 0x90, 0x02, 0xdb, 0x7c, 0x13, 0xfd, 0x17, 0x35, 0xaf, 0xc9, 0x2a, 0x2c, 0x47, 0xea, 0x32, 0xf5, 0x2b, 0xb9, 0x27, 0x26, 0x8b, 0x0d, 0xd5, 0x58, 0x68]

def d38F8 : Bytes := [0x19, 0xcf, 0xf6, 0xfa, 0xf4, 0x68, 0xa7, 0xcb, 0x27, 0xe4, 0xcb, 0x45, 0x43, 0xc3, 0xc5, 0x9e, 0x03, 0xef, 0xd9, 0xb4, 0x82, 0x7b, 0x09, 0x66, 0x0e, 0xd8, 0x97, 0x5c, 0x3b, 0x68, 0xf0, 0x7e]

def d38Fields : List BLT := [.bytes d38F0, .bytes d38F1, .bytes d38F2, .bytes d38F3, .bytes d38F4, .bytes d38F5, .bytes d38F6, .bytes d38F7, .bytes d38F8]

def d38Payload : Bytes := [0x81] ++ d38F0 ++ [0x84] ++ d38F1 ++ [0x83] ++ d38F2 ++ [0x94] ++ d38F3 ++ [0x80] ++ d38F4 ++ [0xb8, 0x44] ++ d38F5 ++ [] ++ d38F6 ++ [0xa0] ++ d38F7 ++ [0xa0] ++ d38F8

def d38Signed : Bytes := [0xf8, 0xaa] ++ d38Payload

def d38Tx : Tx := { nonce := 205, gas := 3770079, value := 0, data := d38F5, v := 38, r := d38F7, s := d38F8, type := .zero 4000000000 (some 0x5c69bee701ef814a2b6a3edd4b1652cb9cc5aa6f) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d38_literal : d38Signed = [0xf8, 0xaa, 0x81, 0xcd, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x39, 0x86, 0xdf, 0x94, 0x5c, 0x69, 0xbe, 0xe7, 0x01, 0xef, 0x81, 0x4a, 0x2b, 0x6a, 0x3e, 0xdd, 0x4b, 0x16, 0x52, 0xcb, 0x9c, 0xc5, 0xaa, 0x6f, 0x80, 0xb8, 0x44, 0xc9, 0xc6, 0x53, 0x96, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x2a, 0xaa, 0x39, 0xb2, 0x23, 0xfe, 0x8d, 0x0a, 0x0e, 0x5c, 0x4f, 0x27, 0xea, 0xd9, 0x08, 0x3c, 0x75, 0x6c, 0xc2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa0, 0xb8, 0x69, 0x91, 0xc6, 0x21, 0x8b, 0x36, 0xc1, 0xd1, 0x9d, 0x4a, 0x2e, 0x9e, 0xb0, 0xce, 0x36, 0x06, 0xeb, 0x48, 0x26, 0xa0, 0xf9, 0xe4, 0x6c, 0x09, 0xc6, 0xb6, 0x2c, 0x90, 0x02, 0xdb, 0x7c, 0x13, 0xfd, 0x17, 0x35, 0xaf, 0xc9, 0x2a, 0x2c, 0x47, 0xea, 0x32, 0xf5, 0x2b, 0xb9, 0x27, 0x26, 0x8b, 0x0d, 0xd5, 0x58, 0x68, 0xa0, 0x19, 0xcf, 0xf6, 0xfa, 0xf4, 0x68, 0xa7, 0xcb, 0x27, 0xe4, 0xcb, 0x45, 0x43, 0xc3, 0xc5, 0x9e, 0x03, 0xef, 0xd9, 0xb4, 0x82, 0x7b, 0x09, 0x66, 0x0e, 0xd8, 0x97, 0x5c, 0x3b, 0x68, 0xf0, 0x7e] := by
  decide +kernel

theorem d38_payload_length : d38Payload.length = 170 := by
  decide +kernel

theorem d38_signed_length : d38Signed.length = 172 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d38_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d38Payload = some d38Fields := by
  unfold d38Payload d38Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 1 d38F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d38F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d38F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d38F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d38F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d38F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d38F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d38_parse : d38Signed.toBLT? = some (.list d38Fields) := by
  have outer : Bytes.toBLTDiff? 172 d38Signed = some (.list d38Fields, []) := by
    simpa only [d38Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 171 170 d38Payload [] d38Fields
        (by rw [d38_payload_length]; decide +kernel) (d38_payload_parse 162)
  unfold Bytes.toBLT?
  rw [d38_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d38_decode :
    (d38Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d38Tx := by
  rw [d38_parse]
  decide +kernel

theorem d38_blt : d38Tx.toBLT = .list d38Fields := by
  norm_num only [d38Tx, d38Fields, d38F0, d38F1, d38F2, d38F3, d38F4, d38F6, d38F7, d38F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d38_encode0 : (BLT.bytes d38F0).toBytes = [0x81] ++ d38F0 := by
  unfold d38F0
  rw [BLT.toBytes]
  decide +kernel

theorem d38_encode1 : (BLT.bytes d38F1).toBytes = [0x84] ++ d38F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d38F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d38_encode2 : (BLT.bytes d38F2).toBytes = [0x83] ++ d38F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d38F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d38_encode3 : (BLT.bytes d38F3).toBytes = [0x94] ++ d38F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d38F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d38_encode4 : (BLT.bytes d38F4).toBytes = [0x80] ++ d38F4 := by
  unfold d38F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d38_encode5 : (BLT.bytes d38F5).toBytes = [0xb8, 0x44] ++ d38F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d38F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d38_encode6 : (BLT.bytes d38F6).toBytes = [] ++ d38F6 := by
  unfold d38F6
  rw [BLT.toBytes]
  decide +kernel

theorem d38_encode7 : (BLT.bytes d38F7).toBytes = [0xa0] ++ d38F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d38F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d38_encode8 : (BLT.bytes d38F8).toBytes = [0xa0] ++ d38F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d38F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d38_canonical : d38Tx.toBLT.toBytes = d38Signed := by
  have encoded : BLTs.toBytesJoin d38Fields = d38Payload := by
    simp only [d38Fields, BLTs.toBytesJoin,
      d38_encode0, d38_encode1, d38_encode2, d38_encode3, d38_encode4, d38_encode5, d38_encode6, d38_encode7, d38_encode8, d38Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d38_blt, BLT.toBytes, BLTs.toBytes, encoded, d38_payload_length]
  norm_num only [d38Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d39F0 : Bytes := [0x02]

def d39F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d39F2 : Bytes := [0x20, 0x0b, 0x20]

def d39F3 : Bytes := [0xf9, 0x36, 0x98, 0x7b, 0x8c, 0x35, 0xd1, 0xf8, 0xdb, 0xb7, 0x6d, 0x11, 0x4a, 0x68, 0x92, 0x93, 0xb0, 0x08, 0xd5, 0x3e]

def d39F4 : Bytes := [0x02, 0xc6, 0x8a, 0xf0, 0xbb, 0x14, 0x00, 0x00]

def d39F5 : Bytes := [0xed, 0x3b, 0xb9, 0xfa]

def d39F6 : Bytes := [0x25]

def d39F7 : Bytes := [0xcb, 0x75, 0xeb, 0x46, 0x57, 0x6d, 0x5e, 0x03, 0xcd, 0x1a, 0x61, 0x4f, 0xbe, 0x81, 0xff, 0xe9, 0x5f, 0x26, 0xd2, 0x43, 0x56, 0x2c, 0x67, 0xdf, 0xfb, 0xcf, 0x1e, 0xce, 0x3e, 0x61, 0xd7, 0xdd]

def d39F8 : Bytes := [0x41, 0xe8, 0x15, 0xc8, 0xd3, 0x74, 0xd9, 0x73, 0x45, 0x62, 0xcd, 0x48, 0x5a, 0xdc, 0x60, 0x8c, 0x2c, 0x7c, 0xde, 0x25, 0x62, 0x90, 0x91, 0x19, 0xd3, 0xa0, 0xe7, 0xbc, 0x04, 0xa6, 0xfb, 0x43]

def d39Fields : List BLT := [.bytes d39F0, .bytes d39F1, .bytes d39F2, .bytes d39F3, .bytes d39F4, .bytes d39F5, .bytes d39F6, .bytes d39F7, .bytes d39F8]

def d39Payload : Bytes := [] ++ d39F0 ++ [0x84] ++ d39F1 ++ [0x83] ++ d39F2 ++ [0x94] ++ d39F3 ++ [0x88] ++ d39F4 ++ [0x84] ++ d39F5 ++ [] ++ d39F6 ++ [0xa0] ++ d39F7 ++ [0xa0] ++ d39F8

def d39Signed : Bytes := [0xf8, 0x70] ++ d39Payload

def d39Tx : Tx := { nonce := 2, gas := 2100000, value := 200000000000000000, data := d39F5, v := 37, r := d39F7, s := d39F8, type := .zero 4000000000 (some 0xf936987b8c35d1f8dbb76d114a689293b008d53e) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d39_literal : d39Signed = [0xf8, 0x70, 0x02, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x20, 0x0b, 0x20, 0x94, 0xf9, 0x36, 0x98, 0x7b, 0x8c, 0x35, 0xd1, 0xf8, 0xdb, 0xb7, 0x6d, 0x11, 0x4a, 0x68, 0x92, 0x93, 0xb0, 0x08, 0xd5, 0x3e, 0x88, 0x02, 0xc6, 0x8a, 0xf0, 0xbb, 0x14, 0x00, 0x00, 0x84, 0xed, 0x3b, 0xb9, 0xfa, 0x25, 0xa0, 0xcb, 0x75, 0xeb, 0x46, 0x57, 0x6d, 0x5e, 0x03, 0xcd, 0x1a, 0x61, 0x4f, 0xbe, 0x81, 0xff, 0xe9, 0x5f, 0x26, 0xd2, 0x43, 0x56, 0x2c, 0x67, 0xdf, 0xfb, 0xcf, 0x1e, 0xce, 0x3e, 0x61, 0xd7, 0xdd, 0xa0, 0x41, 0xe8, 0x15, 0xc8, 0xd3, 0x74, 0xd9, 0x73, 0x45, 0x62, 0xcd, 0x48, 0x5a, 0xdc, 0x60, 0x8c, 0x2c, 0x7c, 0xde, 0x25, 0x62, 0x90, 0x91, 0x19, 0xd3, 0xa0, 0xe7, 0xbc, 0x04, 0xa6, 0xfb, 0x43] := by
  decide +kernel

theorem d39_payload_length : d39Payload.length = 112 := by
  decide +kernel

theorem d39_signed_length : d39Signed.length = 114 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d39_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d39Payload = some d39Fields := by
  unfold d39Payload d39Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d39F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d39F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d39F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 d39F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d39F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d39F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d39F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d39_parse : d39Signed.toBLT? = some (.list d39Fields) := by
  have outer : Bytes.toBLTDiff? 114 d39Signed = some (.list d39Fields, []) := by
    simpa only [d39Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 113 112 d39Payload [] d39Fields
        (by rw [d39_payload_length]; decide +kernel) (d39_payload_parse 104)
  unfold Bytes.toBLT?
  rw [d39_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d39_decode :
    (d39Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d39Tx := by
  rw [d39_parse]
  decide +kernel

theorem d39_blt : d39Tx.toBLT = .list d39Fields := by
  norm_num only [d39Tx, d39Fields, d39F0, d39F1, d39F2, d39F3, d39F4, d39F6, d39F7, d39F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d39_encode0 : (BLT.bytes d39F0).toBytes = [] ++ d39F0 := by
  unfold d39F0
  rw [BLT.toBytes]
  decide +kernel

theorem d39_encode1 : (BLT.bytes d39F1).toBytes = [0x84] ++ d39F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d39F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d39_encode2 : (BLT.bytes d39F2).toBytes = [0x83] ++ d39F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d39F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d39_encode3 : (BLT.bytes d39F3).toBytes = [0x94] ++ d39F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d39F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d39_encode4 : (BLT.bytes d39F4).toBytes = [0x88] ++ d39F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d39F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d39_encode5 : (BLT.bytes d39F5).toBytes = [0x84] ++ d39F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d39F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d39_encode6 : (BLT.bytes d39F6).toBytes = [] ++ d39F6 := by
  unfold d39F6
  rw [BLT.toBytes]
  decide +kernel

theorem d39_encode7 : (BLT.bytes d39F7).toBytes = [0xa0] ++ d39F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d39F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d39_encode8 : (BLT.bytes d39F8).toBytes = [0xa0] ++ d39F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d39F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d39_canonical : d39Tx.toBLT.toBytes = d39Signed := by
  have encoded : BLTs.toBytesJoin d39Fields = d39Payload := by
    simp only [d39Fields, BLTs.toBytesJoin,
      d39_encode0, d39_encode1, d39_encode2, d39_encode3, d39_encode4, d39_encode5, d39_encode6, d39_encode7, d39_encode8, d39Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d39_blt, BLT.toBytes, BLTs.toBytes, encoded, d39_payload_length]
  norm_num only [d39Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
