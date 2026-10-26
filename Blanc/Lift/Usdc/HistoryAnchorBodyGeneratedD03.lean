import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def d24F0 : Bytes := [0x15, 0x77]

def d24F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d24F2 : Bytes := [0x04, 0xc8, 0x0f]

def d24F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d24F4 : Bytes := []

def d24F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d24F6 : Bytes := [0x1b]

def d24F7 : Bytes := [0x25, 0xa4, 0xa2, 0x43, 0x99, 0x05, 0x0b, 0xd4, 0x8e, 0xde, 0x42, 0xfe, 0x3f, 0x63, 0x3f, 0xfa, 0xb4, 0xe5, 0xc3, 0x0f, 0x92, 0xae, 0xa3, 0x94, 0xbe, 0x11, 0x42, 0x5f, 0x7e, 0x6e, 0xc6, 0x1b]

def d24F8 : Bytes := [0x4d, 0xb6, 0x1c, 0x5d, 0x31, 0x8f, 0xcc, 0xb3, 0xaf, 0x40, 0xec, 0xbe, 0xbf, 0xf9, 0x7b, 0x78, 0x52, 0x82, 0xb2, 0x4b, 0xba, 0xda, 0x73, 0x48, 0xd3, 0x59, 0x48, 0xb8, 0xf9, 0x46, 0x45, 0xb8]

def d24Fields : List BLT := [.bytes d24F0, .bytes d24F1, .bytes d24F2, .bytes d24F3, .bytes d24F4, .bytes d24F5, .bytes d24F6, .bytes d24F7, .bytes d24F8]

def d24Payload : Bytes := [0x82] ++ d24F0 ++ [0x84] ++ d24F1 ++ [0x83] ++ d24F2 ++ [0x94] ++ d24F3 ++ [0x80] ++ d24F4 ++ [0x84] ++ d24F5 ++ [] ++ d24F6 ++ [0xa0] ++ d24F7 ++ [0xa0] ++ d24F8

def d24Signed : Bytes := [0xf8, 0x6a] ++ d24Payload

def d24Tx : Tx := { nonce := 5495, gas := 313359, value := 0, data := d24F5, v := 27, r := d24F7, s := d24F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d24_literal : d24Signed = [0xf8, 0x6a, 0x82, 0x15, 0x77, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x25, 0xa4, 0xa2, 0x43, 0x99, 0x05, 0x0b, 0xd4, 0x8e, 0xde, 0x42, 0xfe, 0x3f, 0x63, 0x3f, 0xfa, 0xb4, 0xe5, 0xc3, 0x0f, 0x92, 0xae, 0xa3, 0x94, 0xbe, 0x11, 0x42, 0x5f, 0x7e, 0x6e, 0xc6, 0x1b, 0xa0, 0x4d, 0xb6, 0x1c, 0x5d, 0x31, 0x8f, 0xcc, 0xb3, 0xaf, 0x40, 0xec, 0xbe, 0xbf, 0xf9, 0x7b, 0x78, 0x52, 0x82, 0xb2, 0x4b, 0xba, 0xda, 0x73, 0x48, 0xd3, 0x59, 0x48, 0xb8, 0xf9, 0x46, 0x45, 0xb8] := by
  decide +kernel

theorem d24_payload_length : d24Payload.length = 106 := by
  decide +kernel

theorem d24_signed_length : d24Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d24_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d24Payload = some d24Fields := by
  unfold d24Payload d24Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d24F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d24F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d24F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d24F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d24F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d24F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d24F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d24_parse : d24Signed.toBLT? = some (.list d24Fields) := by
  have outer : Bytes.toBLTDiff? 108 d24Signed = some (.list d24Fields, []) := by
    simpa only [d24Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d24Payload [] d24Fields
        (by rw [d24_payload_length]; decide +kernel) (d24_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d24_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d24_decode :
    (d24Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d24Tx := by
  rw [d24_parse]
  decide +kernel

theorem d24_blt : d24Tx.toBLT = .list d24Fields := by
  norm_num only [d24Tx, d24Fields, d24F0, d24F1, d24F2, d24F3, d24F4, d24F6, d24F7, d24F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d24_encode0 : (BLT.bytes d24F0).toBytes = [0x82] ++ d24F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d24F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d24_encode1 : (BLT.bytes d24F1).toBytes = [0x84] ++ d24F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d24F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d24_encode2 : (BLT.bytes d24F2).toBytes = [0x83] ++ d24F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d24F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d24_encode3 : (BLT.bytes d24F3).toBytes = [0x94] ++ d24F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d24F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d24_encode4 : (BLT.bytes d24F4).toBytes = [0x80] ++ d24F4 := by
  unfold d24F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d24_encode5 : (BLT.bytes d24F5).toBytes = [0x84] ++ d24F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d24F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d24_encode6 : (BLT.bytes d24F6).toBytes = [] ++ d24F6 := by
  unfold d24F6
  rw [BLT.toBytes]
  decide +kernel

theorem d24_encode7 : (BLT.bytes d24F7).toBytes = [0xa0] ++ d24F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d24F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d24_encode8 : (BLT.bytes d24F8).toBytes = [0xa0] ++ d24F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d24F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d24_canonical : d24Tx.toBLT.toBytes = d24Signed := by
  have encoded : BLTs.toBytesJoin d24Fields = d24Payload := by
    simp only [d24Fields, BLTs.toBytesJoin,
      d24_encode0, d24_encode1, d24_encode2, d24_encode3, d24_encode4, d24_encode5, d24_encode6, d24_encode7, d24_encode8, d24Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d24_blt, BLT.toBytes, BLTs.toBytes, encoded, d24_payload_length]
  norm_num only [d24Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d25F0 : Bytes := [0x15, 0x78]

def d25F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d25F2 : Bytes := [0x04, 0xc8, 0x0f]

def d25F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d25F4 : Bytes := []

def d25F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d25F6 : Bytes := [0x1b]

def d25F7 : Bytes := [0x6a, 0x53, 0xf9, 0x20, 0x63, 0x22, 0xfb, 0x9a, 0x29, 0x67, 0x55, 0x1b, 0x53, 0x5a, 0xc2, 0xf5, 0x1b, 0x2a, 0xf4, 0xff, 0x5b, 0xf2, 0x0b, 0xf7, 0x56, 0x97, 0xb1, 0x5a, 0xea, 0xba, 0x96, 0x4c]

def d25F8 : Bytes := [0x28, 0x9b, 0x78, 0x24, 0x2d, 0x03, 0x8b, 0x8a, 0x1b, 0xb5, 0xc0, 0x65, 0xaf, 0xfe, 0xa6, 0xaf, 0xfe, 0x6d, 0xad, 0x32, 0x13, 0x4d, 0x85, 0x89, 0x6d, 0xc0, 0x9d, 0x8d, 0xbf, 0xcb, 0xe8, 0x4d]

def d25Fields : List BLT := [.bytes d25F0, .bytes d25F1, .bytes d25F2, .bytes d25F3, .bytes d25F4, .bytes d25F5, .bytes d25F6, .bytes d25F7, .bytes d25F8]

def d25Payload : Bytes := [0x82] ++ d25F0 ++ [0x84] ++ d25F1 ++ [0x83] ++ d25F2 ++ [0x94] ++ d25F3 ++ [0x80] ++ d25F4 ++ [0x84] ++ d25F5 ++ [] ++ d25F6 ++ [0xa0] ++ d25F7 ++ [0xa0] ++ d25F8

def d25Signed : Bytes := [0xf8, 0x6a] ++ d25Payload

def d25Tx : Tx := { nonce := 5496, gas := 313359, value := 0, data := d25F5, v := 27, r := d25F7, s := d25F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d25_literal : d25Signed = [0xf8, 0x6a, 0x82, 0x15, 0x78, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x6a, 0x53, 0xf9, 0x20, 0x63, 0x22, 0xfb, 0x9a, 0x29, 0x67, 0x55, 0x1b, 0x53, 0x5a, 0xc2, 0xf5, 0x1b, 0x2a, 0xf4, 0xff, 0x5b, 0xf2, 0x0b, 0xf7, 0x56, 0x97, 0xb1, 0x5a, 0xea, 0xba, 0x96, 0x4c, 0xa0, 0x28, 0x9b, 0x78, 0x24, 0x2d, 0x03, 0x8b, 0x8a, 0x1b, 0xb5, 0xc0, 0x65, 0xaf, 0xfe, 0xa6, 0xaf, 0xfe, 0x6d, 0xad, 0x32, 0x13, 0x4d, 0x85, 0x89, 0x6d, 0xc0, 0x9d, 0x8d, 0xbf, 0xcb, 0xe8, 0x4d] := by
  decide +kernel

theorem d25_payload_length : d25Payload.length = 106 := by
  decide +kernel

theorem d25_signed_length : d25Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d25_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d25Payload = some d25Fields := by
  unfold d25Payload d25Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d25F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d25F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d25F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d25F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d25F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d25F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d25F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d25_parse : d25Signed.toBLT? = some (.list d25Fields) := by
  have outer : Bytes.toBLTDiff? 108 d25Signed = some (.list d25Fields, []) := by
    simpa only [d25Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d25Payload [] d25Fields
        (by rw [d25_payload_length]; decide +kernel) (d25_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d25_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d25_decode :
    (d25Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d25Tx := by
  rw [d25_parse]
  decide +kernel

theorem d25_blt : d25Tx.toBLT = .list d25Fields := by
  norm_num only [d25Tx, d25Fields, d25F0, d25F1, d25F2, d25F3, d25F4, d25F6, d25F7, d25F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d25_encode0 : (BLT.bytes d25F0).toBytes = [0x82] ++ d25F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d25F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d25_encode1 : (BLT.bytes d25F1).toBytes = [0x84] ++ d25F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d25F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d25_encode2 : (BLT.bytes d25F2).toBytes = [0x83] ++ d25F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d25F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d25_encode3 : (BLT.bytes d25F3).toBytes = [0x94] ++ d25F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d25F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d25_encode4 : (BLT.bytes d25F4).toBytes = [0x80] ++ d25F4 := by
  unfold d25F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d25_encode5 : (BLT.bytes d25F5).toBytes = [0x84] ++ d25F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d25F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d25_encode6 : (BLT.bytes d25F6).toBytes = [] ++ d25F6 := by
  unfold d25F6
  rw [BLT.toBytes]
  decide +kernel

theorem d25_encode7 : (BLT.bytes d25F7).toBytes = [0xa0] ++ d25F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d25F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d25_encode8 : (BLT.bytes d25F8).toBytes = [0xa0] ++ d25F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d25F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d25_canonical : d25Tx.toBLT.toBytes = d25Signed := by
  have encoded : BLTs.toBytesJoin d25Fields = d25Payload := by
    simp only [d25Fields, BLTs.toBytesJoin,
      d25_encode0, d25_encode1, d25_encode2, d25_encode3, d25_encode4, d25_encode5, d25_encode6, d25_encode7, d25_encode8, d25Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d25_blt, BLT.toBytes, BLTs.toBytes, encoded, d25_payload_length]
  norm_num only [d25Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d26F0 : Bytes := [0x15, 0x79]

def d26F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d26F2 : Bytes := [0x04, 0xc8, 0x0f]

def d26F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d26F4 : Bytes := []

def d26F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d26F6 : Bytes := [0x1c]

def d26F7 : Bytes := [0x61, 0x7c, 0x33, 0xe6, 0xfd, 0xae, 0x7d, 0xed, 0x7c, 0xc8, 0xd8, 0x75, 0x80, 0x5f, 0x6b, 0x83, 0x78, 0x86, 0x7c, 0x98, 0x37, 0x65, 0x62, 0xa6, 0xc6, 0xa8, 0xff, 0x21, 0x43, 0x86, 0xe3, 0xd2]

def d26F8 : Bytes := [0x7b, 0xf9, 0x1f, 0x18, 0xb4, 0x41, 0x60, 0x3d, 0x36, 0xcb, 0x89, 0xbc, 0x0c, 0x7e, 0xba, 0xe4, 0x60, 0xb5, 0x90, 0xa7, 0x43, 0xaa, 0x1f, 0xf8, 0x0a, 0xd9, 0x6f, 0x6f, 0x42, 0x97, 0xef, 0x02]

def d26Fields : List BLT := [.bytes d26F0, .bytes d26F1, .bytes d26F2, .bytes d26F3, .bytes d26F4, .bytes d26F5, .bytes d26F6, .bytes d26F7, .bytes d26F8]

def d26Payload : Bytes := [0x82] ++ d26F0 ++ [0x84] ++ d26F1 ++ [0x83] ++ d26F2 ++ [0x94] ++ d26F3 ++ [0x80] ++ d26F4 ++ [0x84] ++ d26F5 ++ [] ++ d26F6 ++ [0xa0] ++ d26F7 ++ [0xa0] ++ d26F8

def d26Signed : Bytes := [0xf8, 0x6a] ++ d26Payload

def d26Tx : Tx := { nonce := 5497, gas := 313359, value := 0, data := d26F5, v := 28, r := d26F7, s := d26F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d26_literal : d26Signed = [0xf8, 0x6a, 0x82, 0x15, 0x79, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1c, 0xa0, 0x61, 0x7c, 0x33, 0xe6, 0xfd, 0xae, 0x7d, 0xed, 0x7c, 0xc8, 0xd8, 0x75, 0x80, 0x5f, 0x6b, 0x83, 0x78, 0x86, 0x7c, 0x98, 0x37, 0x65, 0x62, 0xa6, 0xc6, 0xa8, 0xff, 0x21, 0x43, 0x86, 0xe3, 0xd2, 0xa0, 0x7b, 0xf9, 0x1f, 0x18, 0xb4, 0x41, 0x60, 0x3d, 0x36, 0xcb, 0x89, 0xbc, 0x0c, 0x7e, 0xba, 0xe4, 0x60, 0xb5, 0x90, 0xa7, 0x43, 0xaa, 0x1f, 0xf8, 0x0a, 0xd9, 0x6f, 0x6f, 0x42, 0x97, 0xef, 0x02] := by
  decide +kernel

theorem d26_payload_length : d26Payload.length = 106 := by
  decide +kernel

theorem d26_signed_length : d26Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d26_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d26Payload = some d26Fields := by
  unfold d26Payload d26Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d26F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d26F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d26F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d26F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d26F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d26F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d26F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d26_parse : d26Signed.toBLT? = some (.list d26Fields) := by
  have outer : Bytes.toBLTDiff? 108 d26Signed = some (.list d26Fields, []) := by
    simpa only [d26Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d26Payload [] d26Fields
        (by rw [d26_payload_length]; decide +kernel) (d26_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d26_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d26_decode :
    (d26Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d26Tx := by
  rw [d26_parse]
  decide +kernel

theorem d26_blt : d26Tx.toBLT = .list d26Fields := by
  norm_num only [d26Tx, d26Fields, d26F0, d26F1, d26F2, d26F3, d26F4, d26F6, d26F7, d26F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d26_encode0 : (BLT.bytes d26F0).toBytes = [0x82] ++ d26F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d26F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d26_encode1 : (BLT.bytes d26F1).toBytes = [0x84] ++ d26F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d26F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d26_encode2 : (BLT.bytes d26F2).toBytes = [0x83] ++ d26F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d26F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d26_encode3 : (BLT.bytes d26F3).toBytes = [0x94] ++ d26F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d26F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d26_encode4 : (BLT.bytes d26F4).toBytes = [0x80] ++ d26F4 := by
  unfold d26F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d26_encode5 : (BLT.bytes d26F5).toBytes = [0x84] ++ d26F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d26F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d26_encode6 : (BLT.bytes d26F6).toBytes = [] ++ d26F6 := by
  unfold d26F6
  rw [BLT.toBytes]
  decide +kernel

theorem d26_encode7 : (BLT.bytes d26F7).toBytes = [0xa0] ++ d26F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d26F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d26_encode8 : (BLT.bytes d26F8).toBytes = [0xa0] ++ d26F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d26F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d26_canonical : d26Tx.toBLT.toBytes = d26Signed := by
  have encoded : BLTs.toBytesJoin d26Fields = d26Payload := by
    simp only [d26Fields, BLTs.toBytesJoin,
      d26_encode0, d26_encode1, d26_encode2, d26_encode3, d26_encode4, d26_encode5, d26_encode6, d26_encode7, d26_encode8, d26Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d26_blt, BLT.toBytes, BLTs.toBytes, encoded, d26_payload_length]
  norm_num only [d26Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d27F0 : Bytes := [0x15, 0x7a]

def d27F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d27F2 : Bytes := [0x04, 0xc8, 0x0f]

def d27F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d27F4 : Bytes := []

def d27F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d27F6 : Bytes := [0x1b]

def d27F7 : Bytes := [0x1f, 0x31, 0xc6, 0x1f, 0x9c, 0x67, 0x1b, 0xc5, 0x1b, 0x7d, 0xf5, 0x69, 0x94, 0x03, 0x07, 0xcb, 0x0c, 0x37, 0xe0, 0x96, 0x24, 0xa9, 0x2f, 0xf2, 0xc2, 0xce, 0x26, 0x60, 0xf5, 0x33, 0xcf, 0x41]

def d27F8 : Bytes := [0x6c, 0x13, 0x83, 0xe6, 0x21, 0x54, 0x58, 0x13, 0x63, 0xca, 0x12, 0xc0, 0xe3, 0x6c, 0x48, 0xb9, 0x89, 0x63, 0x7b, 0x2e, 0x31, 0x53, 0x2a, 0x59, 0x1f, 0xb7, 0xea, 0x57, 0x35, 0x03, 0x26, 0x3b]

def d27Fields : List BLT := [.bytes d27F0, .bytes d27F1, .bytes d27F2, .bytes d27F3, .bytes d27F4, .bytes d27F5, .bytes d27F6, .bytes d27F7, .bytes d27F8]

def d27Payload : Bytes := [0x82] ++ d27F0 ++ [0x84] ++ d27F1 ++ [0x83] ++ d27F2 ++ [0x94] ++ d27F3 ++ [0x80] ++ d27F4 ++ [0x84] ++ d27F5 ++ [] ++ d27F6 ++ [0xa0] ++ d27F7 ++ [0xa0] ++ d27F8

def d27Signed : Bytes := [0xf8, 0x6a] ++ d27Payload

def d27Tx : Tx := { nonce := 5498, gas := 313359, value := 0, data := d27F5, v := 27, r := d27F7, s := d27F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d27_literal : d27Signed = [0xf8, 0x6a, 0x82, 0x15, 0x7a, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x1f, 0x31, 0xc6, 0x1f, 0x9c, 0x67, 0x1b, 0xc5, 0x1b, 0x7d, 0xf5, 0x69, 0x94, 0x03, 0x07, 0xcb, 0x0c, 0x37, 0xe0, 0x96, 0x24, 0xa9, 0x2f, 0xf2, 0xc2, 0xce, 0x26, 0x60, 0xf5, 0x33, 0xcf, 0x41, 0xa0, 0x6c, 0x13, 0x83, 0xe6, 0x21, 0x54, 0x58, 0x13, 0x63, 0xca, 0x12, 0xc0, 0xe3, 0x6c, 0x48, 0xb9, 0x89, 0x63, 0x7b, 0x2e, 0x31, 0x53, 0x2a, 0x59, 0x1f, 0xb7, 0xea, 0x57, 0x35, 0x03, 0x26, 0x3b] := by
  decide +kernel

theorem d27_payload_length : d27Payload.length = 106 := by
  decide +kernel

theorem d27_signed_length : d27Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d27_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d27Payload = some d27Fields := by
  unfold d27Payload d27Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d27F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d27F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d27F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d27F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d27F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d27F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d27F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d27_parse : d27Signed.toBLT? = some (.list d27Fields) := by
  have outer : Bytes.toBLTDiff? 108 d27Signed = some (.list d27Fields, []) := by
    simpa only [d27Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d27Payload [] d27Fields
        (by rw [d27_payload_length]; decide +kernel) (d27_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d27_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d27_decode :
    (d27Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d27Tx := by
  rw [d27_parse]
  decide +kernel

theorem d27_blt : d27Tx.toBLT = .list d27Fields := by
  norm_num only [d27Tx, d27Fields, d27F0, d27F1, d27F2, d27F3, d27F4, d27F6, d27F7, d27F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d27_encode0 : (BLT.bytes d27F0).toBytes = [0x82] ++ d27F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d27F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d27_encode1 : (BLT.bytes d27F1).toBytes = [0x84] ++ d27F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d27F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d27_encode2 : (BLT.bytes d27F2).toBytes = [0x83] ++ d27F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d27F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d27_encode3 : (BLT.bytes d27F3).toBytes = [0x94] ++ d27F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d27F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d27_encode4 : (BLT.bytes d27F4).toBytes = [0x80] ++ d27F4 := by
  unfold d27F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d27_encode5 : (BLT.bytes d27F5).toBytes = [0x84] ++ d27F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d27F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d27_encode6 : (BLT.bytes d27F6).toBytes = [] ++ d27F6 := by
  unfold d27F6
  rw [BLT.toBytes]
  decide +kernel

theorem d27_encode7 : (BLT.bytes d27F7).toBytes = [0xa0] ++ d27F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d27F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d27_encode8 : (BLT.bytes d27F8).toBytes = [0xa0] ++ d27F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d27F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d27_canonical : d27Tx.toBLT.toBytes = d27Signed := by
  have encoded : BLTs.toBytesJoin d27Fields = d27Payload := by
    simp only [d27Fields, BLTs.toBytesJoin,
      d27_encode0, d27_encode1, d27_encode2, d27_encode3, d27_encode4, d27_encode5, d27_encode6, d27_encode7, d27_encode8, d27Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d27_blt, BLT.toBytes, BLTs.toBytes, encoded, d27_payload_length]
  norm_num only [d27Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d28F0 : Bytes := [0x15, 0x7b]

def d28F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d28F2 : Bytes := [0x04, 0xc8, 0x0f]

def d28F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d28F4 : Bytes := []

def d28F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d28F6 : Bytes := [0x1b]

def d28F7 : Bytes := [0x3a, 0x6b, 0xe9, 0xe2, 0xbe, 0x46, 0xe0, 0xfa, 0xa5, 0x05, 0x78, 0x80, 0x35, 0x25, 0x1a, 0x6b, 0xc7, 0x78, 0x56, 0x22, 0x11, 0x64, 0x0d, 0xb3, 0x14, 0xfa, 0xe3, 0x54, 0xd5, 0x3a, 0x8f, 0x43]

def d28F8 : Bytes := [0x28, 0x6b, 0x80, 0x79, 0xbe, 0xe7, 0x1b, 0x69, 0x73, 0x8a, 0x37, 0xc3, 0xf9, 0x45, 0x1b, 0x10, 0x7a, 0xe3, 0x66, 0xaa, 0x64, 0x59, 0x0c, 0x23, 0xaa, 0x76, 0x27, 0x9e, 0x01, 0x4b, 0x1b, 0x86]

def d28Fields : List BLT := [.bytes d28F0, .bytes d28F1, .bytes d28F2, .bytes d28F3, .bytes d28F4, .bytes d28F5, .bytes d28F6, .bytes d28F7, .bytes d28F8]

def d28Payload : Bytes := [0x82] ++ d28F0 ++ [0x84] ++ d28F1 ++ [0x83] ++ d28F2 ++ [0x94] ++ d28F3 ++ [0x80] ++ d28F4 ++ [0x84] ++ d28F5 ++ [] ++ d28F6 ++ [0xa0] ++ d28F7 ++ [0xa0] ++ d28F8

def d28Signed : Bytes := [0xf8, 0x6a] ++ d28Payload

def d28Tx : Tx := { nonce := 5499, gas := 313359, value := 0, data := d28F5, v := 27, r := d28F7, s := d28F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d28_literal : d28Signed = [0xf8, 0x6a, 0x82, 0x15, 0x7b, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x3a, 0x6b, 0xe9, 0xe2, 0xbe, 0x46, 0xe0, 0xfa, 0xa5, 0x05, 0x78, 0x80, 0x35, 0x25, 0x1a, 0x6b, 0xc7, 0x78, 0x56, 0x22, 0x11, 0x64, 0x0d, 0xb3, 0x14, 0xfa, 0xe3, 0x54, 0xd5, 0x3a, 0x8f, 0x43, 0xa0, 0x28, 0x6b, 0x80, 0x79, 0xbe, 0xe7, 0x1b, 0x69, 0x73, 0x8a, 0x37, 0xc3, 0xf9, 0x45, 0x1b, 0x10, 0x7a, 0xe3, 0x66, 0xaa, 0x64, 0x59, 0x0c, 0x23, 0xaa, 0x76, 0x27, 0x9e, 0x01, 0x4b, 0x1b, 0x86] := by
  decide +kernel

theorem d28_payload_length : d28Payload.length = 106 := by
  decide +kernel

theorem d28_signed_length : d28Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d28_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d28Payload = some d28Fields := by
  unfold d28Payload d28Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d28F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d28F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d28F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d28F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d28F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d28F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d28F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d28_parse : d28Signed.toBLT? = some (.list d28Fields) := by
  have outer : Bytes.toBLTDiff? 108 d28Signed = some (.list d28Fields, []) := by
    simpa only [d28Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d28Payload [] d28Fields
        (by rw [d28_payload_length]; decide +kernel) (d28_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d28_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d28_decode :
    (d28Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d28Tx := by
  rw [d28_parse]
  decide +kernel

theorem d28_blt : d28Tx.toBLT = .list d28Fields := by
  norm_num only [d28Tx, d28Fields, d28F0, d28F1, d28F2, d28F3, d28F4, d28F6, d28F7, d28F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d28_encode0 : (BLT.bytes d28F0).toBytes = [0x82] ++ d28F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d28F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d28_encode1 : (BLT.bytes d28F1).toBytes = [0x84] ++ d28F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d28F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d28_encode2 : (BLT.bytes d28F2).toBytes = [0x83] ++ d28F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d28F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d28_encode3 : (BLT.bytes d28F3).toBytes = [0x94] ++ d28F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d28F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d28_encode4 : (BLT.bytes d28F4).toBytes = [0x80] ++ d28F4 := by
  unfold d28F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d28_encode5 : (BLT.bytes d28F5).toBytes = [0x84] ++ d28F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d28F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d28_encode6 : (BLT.bytes d28F6).toBytes = [] ++ d28F6 := by
  unfold d28F6
  rw [BLT.toBytes]
  decide +kernel

theorem d28_encode7 : (BLT.bytes d28F7).toBytes = [0xa0] ++ d28F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d28F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d28_encode8 : (BLT.bytes d28F8).toBytes = [0xa0] ++ d28F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d28F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d28_canonical : d28Tx.toBLT.toBytes = d28Signed := by
  have encoded : BLTs.toBytesJoin d28Fields = d28Payload := by
    simp only [d28Fields, BLTs.toBytesJoin,
      d28_encode0, d28_encode1, d28_encode2, d28_encode3, d28_encode4, d28_encode5, d28_encode6, d28_encode7, d28_encode8, d28Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d28_blt, BLT.toBytes, BLTs.toBytes, encoded, d28_payload_length]
  norm_num only [d28Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d29F0 : Bytes := [0x15, 0x7c]

def d29F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d29F2 : Bytes := [0x04, 0xc8, 0x0f]

def d29F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d29F4 : Bytes := []

def d29F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d29F6 : Bytes := [0x1c]

def d29F7 : Bytes := [0x4d, 0x34, 0xc3, 0xd7, 0x49, 0x04, 0x55, 0xc5, 0x84, 0xfd, 0x0d, 0x2e, 0x43, 0xf6, 0xc5, 0x6e, 0xaf, 0x63, 0x16, 0xa8, 0xc9, 0x5f, 0x61, 0x71, 0x3c, 0xbe, 0xd8, 0x9c, 0xd8, 0xd6, 0xc4, 0x55]

def d29F8 : Bytes := [0x05, 0x3c, 0x8a, 0x0f, 0x00, 0xf0, 0x66, 0x79, 0x96, 0xdb, 0x32, 0x45, 0x86, 0xe3, 0xb0, 0xe8, 0xf1, 0xeb, 0xeb, 0x99, 0x8c, 0x35, 0xd4, 0x90, 0x03, 0x5a, 0x11, 0xb2, 0x87, 0x0b, 0x4d, 0x84]

def d29Fields : List BLT := [.bytes d29F0, .bytes d29F1, .bytes d29F2, .bytes d29F3, .bytes d29F4, .bytes d29F5, .bytes d29F6, .bytes d29F7, .bytes d29F8]

def d29Payload : Bytes := [0x82] ++ d29F0 ++ [0x84] ++ d29F1 ++ [0x83] ++ d29F2 ++ [0x94] ++ d29F3 ++ [0x80] ++ d29F4 ++ [0x84] ++ d29F5 ++ [] ++ d29F6 ++ [0xa0] ++ d29F7 ++ [0xa0] ++ d29F8

def d29Signed : Bytes := [0xf8, 0x6a] ++ d29Payload

def d29Tx : Tx := { nonce := 5500, gas := 313359, value := 0, data := d29F5, v := 28, r := d29F7, s := d29F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d29_literal : d29Signed = [0xf8, 0x6a, 0x82, 0x15, 0x7c, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1c, 0xa0, 0x4d, 0x34, 0xc3, 0xd7, 0x49, 0x04, 0x55, 0xc5, 0x84, 0xfd, 0x0d, 0x2e, 0x43, 0xf6, 0xc5, 0x6e, 0xaf, 0x63, 0x16, 0xa8, 0xc9, 0x5f, 0x61, 0x71, 0x3c, 0xbe, 0xd8, 0x9c, 0xd8, 0xd6, 0xc4, 0x55, 0xa0, 0x05, 0x3c, 0x8a, 0x0f, 0x00, 0xf0, 0x66, 0x79, 0x96, 0xdb, 0x32, 0x45, 0x86, 0xe3, 0xb0, 0xe8, 0xf1, 0xeb, 0xeb, 0x99, 0x8c, 0x35, 0xd4, 0x90, 0x03, 0x5a, 0x11, 0xb2, 0x87, 0x0b, 0x4d, 0x84] := by
  decide +kernel

theorem d29_payload_length : d29Payload.length = 106 := by
  decide +kernel

theorem d29_signed_length : d29Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d29_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d29Payload = some d29Fields := by
  unfold d29Payload d29Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d29F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d29F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d29F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d29F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d29F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d29F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d29F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d29_parse : d29Signed.toBLT? = some (.list d29Fields) := by
  have outer : Bytes.toBLTDiff? 108 d29Signed = some (.list d29Fields, []) := by
    simpa only [d29Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d29Payload [] d29Fields
        (by rw [d29_payload_length]; decide +kernel) (d29_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d29_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d29_decode :
    (d29Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d29Tx := by
  rw [d29_parse]
  decide +kernel

theorem d29_blt : d29Tx.toBLT = .list d29Fields := by
  norm_num only [d29Tx, d29Fields, d29F0, d29F1, d29F2, d29F3, d29F4, d29F6, d29F7, d29F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d29_encode0 : (BLT.bytes d29F0).toBytes = [0x82] ++ d29F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d29F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d29_encode1 : (BLT.bytes d29F1).toBytes = [0x84] ++ d29F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d29F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d29_encode2 : (BLT.bytes d29F2).toBytes = [0x83] ++ d29F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d29F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d29_encode3 : (BLT.bytes d29F3).toBytes = [0x94] ++ d29F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d29F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d29_encode4 : (BLT.bytes d29F4).toBytes = [0x80] ++ d29F4 := by
  unfold d29F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d29_encode5 : (BLT.bytes d29F5).toBytes = [0x84] ++ d29F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d29F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d29_encode6 : (BLT.bytes d29F6).toBytes = [] ++ d29F6 := by
  unfold d29F6
  rw [BLT.toBytes]
  decide +kernel

theorem d29_encode7 : (BLT.bytes d29F7).toBytes = [0xa0] ++ d29F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d29F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d29_encode8 : (BLT.bytes d29F8).toBytes = [0xa0] ++ d29F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d29F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d29_canonical : d29Tx.toBLT.toBytes = d29Signed := by
  have encoded : BLTs.toBytesJoin d29Fields = d29Payload := by
    simp only [d29Fields, BLTs.toBytesJoin,
      d29_encode0, d29_encode1, d29_encode2, d29_encode3, d29_encode4, d29_encode5, d29_encode6, d29_encode7, d29_encode8, d29Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d29_blt, BLT.toBytes, BLTs.toBytes, encoded, d29_payload_length]
  norm_num only [d29Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d30F0 : Bytes := [0x15, 0x7d]

def d30F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d30F2 : Bytes := [0x04, 0xc8, 0x0f]

def d30F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d30F4 : Bytes := []

def d30F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d30F6 : Bytes := [0x1b]

def d30F7 : Bytes := [0x75, 0x2a, 0xdd, 0x0a, 0x44, 0x66, 0xd0, 0xfa, 0x05, 0x14, 0x89, 0xa1, 0xb0, 0xe6, 0x28, 0x41, 0x74, 0x5a, 0x82, 0x33, 0x1c, 0x58, 0xd2, 0x09, 0xbf, 0x1a, 0x56, 0x14, 0x65, 0xe4, 0x26, 0x72]

def d30F8 : Bytes := [0x6f, 0x5e, 0xb1, 0xe7, 0x88, 0xfc, 0x2b, 0x6e, 0xb2, 0xca, 0x97, 0x10, 0x15, 0x79, 0xf3, 0x03, 0x99, 0x29, 0x02, 0x6a, 0x32, 0x5c, 0xa8, 0x4f, 0x46, 0x87, 0x60, 0xea, 0x72, 0x8a, 0x33, 0x16]

def d30Fields : List BLT := [.bytes d30F0, .bytes d30F1, .bytes d30F2, .bytes d30F3, .bytes d30F4, .bytes d30F5, .bytes d30F6, .bytes d30F7, .bytes d30F8]

def d30Payload : Bytes := [0x82] ++ d30F0 ++ [0x84] ++ d30F1 ++ [0x83] ++ d30F2 ++ [0x94] ++ d30F3 ++ [0x80] ++ d30F4 ++ [0x84] ++ d30F5 ++ [] ++ d30F6 ++ [0xa0] ++ d30F7 ++ [0xa0] ++ d30F8

def d30Signed : Bytes := [0xf8, 0x6a] ++ d30Payload

def d30Tx : Tx := { nonce := 5501, gas := 313359, value := 0, data := d30F5, v := 27, r := d30F7, s := d30F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d30_literal : d30Signed = [0xf8, 0x6a, 0x82, 0x15, 0x7d, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1b, 0xa0, 0x75, 0x2a, 0xdd, 0x0a, 0x44, 0x66, 0xd0, 0xfa, 0x05, 0x14, 0x89, 0xa1, 0xb0, 0xe6, 0x28, 0x41, 0x74, 0x5a, 0x82, 0x33, 0x1c, 0x58, 0xd2, 0x09, 0xbf, 0x1a, 0x56, 0x14, 0x65, 0xe4, 0x26, 0x72, 0xa0, 0x6f, 0x5e, 0xb1, 0xe7, 0x88, 0xfc, 0x2b, 0x6e, 0xb2, 0xca, 0x97, 0x10, 0x15, 0x79, 0xf3, 0x03, 0x99, 0x29, 0x02, 0x6a, 0x32, 0x5c, 0xa8, 0x4f, 0x46, 0x87, 0x60, 0xea, 0x72, 0x8a, 0x33, 0x16] := by
  decide +kernel

theorem d30_payload_length : d30Payload.length = 106 := by
  decide +kernel

theorem d30_signed_length : d30Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d30_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d30Payload = some d30Fields := by
  unfold d30Payload d30Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d30F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d30F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d30F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d30F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d30F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d30F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d30F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d30_parse : d30Signed.toBLT? = some (.list d30Fields) := by
  have outer : Bytes.toBLTDiff? 108 d30Signed = some (.list d30Fields, []) := by
    simpa only [d30Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d30Payload [] d30Fields
        (by rw [d30_payload_length]; decide +kernel) (d30_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d30_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d30_decode :
    (d30Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d30Tx := by
  rw [d30_parse]
  decide +kernel

theorem d30_blt : d30Tx.toBLT = .list d30Fields := by
  norm_num only [d30Tx, d30Fields, d30F0, d30F1, d30F2, d30F3, d30F4, d30F6, d30F7, d30F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d30_encode0 : (BLT.bytes d30F0).toBytes = [0x82] ++ d30F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d30F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d30_encode1 : (BLT.bytes d30F1).toBytes = [0x84] ++ d30F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d30F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d30_encode2 : (BLT.bytes d30F2).toBytes = [0x83] ++ d30F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d30F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d30_encode3 : (BLT.bytes d30F3).toBytes = [0x94] ++ d30F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d30F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d30_encode4 : (BLT.bytes d30F4).toBytes = [0x80] ++ d30F4 := by
  unfold d30F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d30_encode5 : (BLT.bytes d30F5).toBytes = [0x84] ++ d30F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d30F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d30_encode6 : (BLT.bytes d30F6).toBytes = [] ++ d30F6 := by
  unfold d30F6
  rw [BLT.toBytes]
  decide +kernel

theorem d30_encode7 : (BLT.bytes d30F7).toBytes = [0xa0] ++ d30F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d30F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d30_encode8 : (BLT.bytes d30F8).toBytes = [0xa0] ++ d30F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d30F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d30_canonical : d30Tx.toBLT.toBytes = d30Signed := by
  have encoded : BLTs.toBytesJoin d30Fields = d30Payload := by
    simp only [d30Fields, BLTs.toBytesJoin,
      d30_encode0, d30_encode1, d30_encode2, d30_encode3, d30_encode4, d30_encode5, d30_encode6, d30_encode7, d30_encode8, d30Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d30_blt, BLT.toBytes, BLTs.toBytes, encoded, d30_payload_length]
  norm_num only [d30Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d31F0 : Bytes := [0x15, 0x7e]

def d31F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def d31F2 : Bytes := [0x04, 0xc8, 0x0f]

def d31F3 : Bytes := [0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b]

def d31F4 : Bytes := []

def d31F5 : Bytes := [0xa6, 0x8a, 0x76, 0xcc]

def d31F6 : Bytes := [0x1c]

def d31F7 : Bytes := [0x13, 0x4e, 0xcd, 0x0d, 0xd5, 0xbb, 0xeb, 0x8e, 0x50, 0x0c, 0x1c, 0x3c, 0xa9, 0x40, 0x34, 0xcd, 0x99, 0x29, 0x18, 0xc5, 0xa0, 0x55, 0x65, 0x8a, 0x4b, 0xdc, 0x2d, 0xb6, 0xd9, 0xca, 0x34, 0xda]

def d31F8 : Bytes := [0x20, 0xcc, 0x84, 0x1d, 0x1d, 0x9e, 0xc7, 0x7a, 0x22, 0xe1, 0x18, 0xf8, 0xfe, 0x43, 0x60, 0xdb, 0xe2, 0x71, 0xc4, 0xac, 0x92, 0xe3, 0x57, 0x2d, 0x94, 0x4e, 0x49, 0x4e, 0xe6, 0xb2, 0x1d, 0x99]

def d31Fields : List BLT := [.bytes d31F0, .bytes d31F1, .bytes d31F2, .bytes d31F3, .bytes d31F4, .bytes d31F5, .bytes d31F6, .bytes d31F7, .bytes d31F8]

def d31Payload : Bytes := [0x82] ++ d31F0 ++ [0x84] ++ d31F1 ++ [0x83] ++ d31F2 ++ [0x94] ++ d31F3 ++ [0x80] ++ d31F4 ++ [0x84] ++ d31F5 ++ [] ++ d31F6 ++ [0xa0] ++ d31F7 ++ [0xa0] ++ d31F8

def d31Signed : Bytes := [0xf8, 0x6a] ++ d31Payload

def d31Tx : Tx := { nonce := 5502, gas := 313359, value := 0, data := d31F5, v := 28, r := d31F7, s := d31F8, type := .zero 4000000000 (some 0xb6ecc1c41720bdb6ca1d6d84435c1c479d6dd89b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d31_literal : d31Signed = [0xf8, 0x6a, 0x82, 0x15, 0x7e, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x04, 0xc8, 0x0f, 0x94, 0xb6, 0xec, 0xc1, 0xc4, 0x17, 0x20, 0xbd, 0xb6, 0xca, 0x1d, 0x6d, 0x84, 0x43, 0x5c, 0x1c, 0x47, 0x9d, 0x6d, 0xd8, 0x9b, 0x80, 0x84, 0xa6, 0x8a, 0x76, 0xcc, 0x1c, 0xa0, 0x13, 0x4e, 0xcd, 0x0d, 0xd5, 0xbb, 0xeb, 0x8e, 0x50, 0x0c, 0x1c, 0x3c, 0xa9, 0x40, 0x34, 0xcd, 0x99, 0x29, 0x18, 0xc5, 0xa0, 0x55, 0x65, 0x8a, 0x4b, 0xdc, 0x2d, 0xb6, 0xd9, 0xca, 0x34, 0xda, 0xa0, 0x20, 0xcc, 0x84, 0x1d, 0x1d, 0x9e, 0xc7, 0x7a, 0x22, 0xe1, 0x18, 0xf8, 0xfe, 0x43, 0x60, 0xdb, 0xe2, 0x71, 0xc4, 0xac, 0x92, 0xe3, 0x57, 0x2d, 0x94, 0x4e, 0x49, 0x4e, 0xe6, 0xb2, 0x1d, 0x99] := by
  decide +kernel

theorem d31_payload_length : d31Payload.length = 106 := by
  decide +kernel

theorem d31_signed_length : d31Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d31_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d31Payload = some d31Fields := by
  unfold d31Payload d31Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d31F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d31F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d31F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d31F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d31F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d31F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d31F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d31_parse : d31Signed.toBLT? = some (.list d31Fields) := by
  have outer : Bytes.toBLTDiff? 108 d31Signed = some (.list d31Fields, []) := by
    simpa only [d31Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 d31Payload [] d31Fields
        (by rw [d31_payload_length]; decide +kernel) (d31_payload_parse 98)
  unfold Bytes.toBLT?
  rw [d31_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d31_decode :
    (d31Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d31Tx := by
  rw [d31_parse]
  decide +kernel

theorem d31_blt : d31Tx.toBLT = .list d31Fields := by
  norm_num only [d31Tx, d31Fields, d31F0, d31F1, d31F2, d31F3, d31F4, d31F6, d31F7, d31F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d31_encode0 : (BLT.bytes d31F0).toBytes = [0x82] ++ d31F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d31F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d31_encode1 : (BLT.bytes d31F1).toBytes = [0x84] ++ d31F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d31F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d31_encode2 : (BLT.bytes d31F2).toBytes = [0x83] ++ d31F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d31F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d31_encode3 : (BLT.bytes d31F3).toBytes = [0x94] ++ d31F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d31F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d31_encode4 : (BLT.bytes d31F4).toBytes = [0x80] ++ d31F4 := by
  unfold d31F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d31_encode5 : (BLT.bytes d31F5).toBytes = [0x84] ++ d31F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d31F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d31_encode6 : (BLT.bytes d31F6).toBytes = [] ++ d31F6 := by
  unfold d31F6
  rw [BLT.toBytes]
  decide +kernel

theorem d31_encode7 : (BLT.bytes d31F7).toBytes = [0xa0] ++ d31F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d31F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d31_encode8 : (BLT.bytes d31F8).toBytes = [0xa0] ++ d31F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d31F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d31_canonical : d31Tx.toBLT.toBytes = d31Signed := by
  have encoded : BLTs.toBytesJoin d31Fields = d31Payload := by
    simp only [d31Fields, BLTs.toBytesJoin,
      d31_encode0, d31_encode1, d31_encode2, d31_encode3, d31_encode4, d31_encode5, d31_encode6, d31_encode7, d31_encode8, d31Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d31_blt, BLT.toBytes, BLTs.toBytes, encoded, d31_payload_length]
  norm_num only [d31Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
