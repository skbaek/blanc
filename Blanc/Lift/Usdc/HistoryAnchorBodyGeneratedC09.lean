import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def c72F0 : Bytes := [0x02]

def c72F1 : Bytes := [0x5f, 0x5e, 0x10, 0x00]

def c72F2 : Bytes := [0x52, 0x08]

def c72F3 : Bytes := [0x3d, 0x92, 0x85, 0xa3, 0x30, 0xa3, 0x50, 0xae, 0x57, 0xf4, 0x66, 0xc3, 0x16, 0x71, 0x6a, 0x1f, 0xb4, 0xd3, 0x77, 0x3d]

def c72F4 : Bytes := [0x05, 0x85, 0xd9, 0x46, 0xc0, 0xef, 0x40, 0x00]

def c72F5 : Bytes := []

def c72F6 : Bytes := [0x25]

def c72F7 : Bytes := [0x9e, 0xb9, 0x94, 0xa2, 0x62, 0xaf, 0xbf, 0x5c, 0xbb, 0xc6, 0xc6, 0x83, 0x7e, 0xcf, 0xf4, 0x01, 0x0c, 0xb8, 0xd8, 0xac, 0x3b, 0x49, 0x78, 0x22, 0xae, 0xf6, 0xbc, 0x8c, 0x37, 0xeb, 0xa3, 0x3c]

def c72F8 : Bytes := [0x77, 0xd1, 0xf3, 0x93, 0x8b, 0xb2, 0xa1, 0x90, 0x78, 0xec, 0x0b, 0x95, 0x43, 0x6a, 0xb1, 0x2d, 0x60, 0x80, 0x1a, 0x71, 0x88, 0xd8, 0xfd, 0x0f, 0x76, 0xe5, 0xc7, 0x8a, 0x06, 0x0d, 0xa1, 0xd4]

def c72Fields : List BLT := [.bytes c72F0, .bytes c72F1, .bytes c72F2, .bytes c72F3, .bytes c72F4, .bytes c72F5, .bytes c72F6, .bytes c72F7, .bytes c72F8]

def c72Payload : Bytes := [] ++ c72F0 ++ [0x84] ++ c72F1 ++ [0x82] ++ c72F2 ++ [0x94] ++ c72F3 ++ [0x88] ++ c72F4 ++ [0x80] ++ c72F5 ++ [] ++ c72F6 ++ [0xa0] ++ c72F7 ++ [0xa0] ++ c72F8

def c72Signed : Bytes := [0xf8, 0x6b] ++ c72Payload

def c72Tx : Tx := { nonce := 2, gas := 21000, value := 397963040000000000, data := c72F5, v := 37, r := c72F7, s := c72F8, type := .zero 1600000000 (some 0x3d9285a330a350ae57f466c316716a1fb4d3773d) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c72_literal : c72Signed = [0xf8, 0x6b, 0x02, 0x84, 0x5f, 0x5e, 0x10, 0x00, 0x82, 0x52, 0x08, 0x94, 0x3d, 0x92, 0x85, 0xa3, 0x30, 0xa3, 0x50, 0xae, 0x57, 0xf4, 0x66, 0xc3, 0x16, 0x71, 0x6a, 0x1f, 0xb4, 0xd3, 0x77, 0x3d, 0x88, 0x05, 0x85, 0xd9, 0x46, 0xc0, 0xef, 0x40, 0x00, 0x80, 0x25, 0xa0, 0x9e, 0xb9, 0x94, 0xa2, 0x62, 0xaf, 0xbf, 0x5c, 0xbb, 0xc6, 0xc6, 0x83, 0x7e, 0xcf, 0xf4, 0x01, 0x0c, 0xb8, 0xd8, 0xac, 0x3b, 0x49, 0x78, 0x22, 0xae, 0xf6, 0xbc, 0x8c, 0x37, 0xeb, 0xa3, 0x3c, 0xa0, 0x77, 0xd1, 0xf3, 0x93, 0x8b, 0xb2, 0xa1, 0x90, 0x78, 0xec, 0x0b, 0x95, 0x43, 0x6a, 0xb1, 0x2d, 0x60, 0x80, 0x1a, 0x71, 0x88, 0xd8, 0xfd, 0x0f, 0x76, 0xe5, 0xc7, 0x8a, 0x06, 0x0d, 0xa1, 0xd4] := by
  decide +kernel

theorem c72_payload_length : c72Payload.length = 107 := by
  decide +kernel

theorem c72_signed_length : c72Signed.length = 109 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c72_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c72Payload = some c72Fields := by
  unfold c72Payload c72Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c72F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c72F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c72F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c72F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c72F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c72F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c72_parse : c72Signed.toBLT? = some (.list c72Fields) := by
  have outer : Bytes.toBLTDiff? 109 c72Signed = some (.list c72Fields, []) := by
    simpa only [c72Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 108 107 c72Payload [] c72Fields
        (by rw [c72_payload_length]; decide +kernel) (c72_payload_parse 99)
  unfold Bytes.toBLT?
  rw [c72_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c72_decode :
    (c72Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c72Tx := by
  rw [c72_parse]
  decide +kernel

theorem c72_blt : c72Tx.toBLT = .list c72Fields := by
  norm_num only [c72Tx, c72Fields, c72F0, c72F1, c72F2, c72F3, c72F4, c72F6, c72F7, c72F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c72_encode0 : (BLT.bytes c72F0).toBytes = [] ++ c72F0 := by
  unfold c72F0
  rw [BLT.toBytes]
  decide +kernel

theorem c72_encode1 : (BLT.bytes c72F1).toBytes = [0x84] ++ c72F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c72F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c72_encode2 : (BLT.bytes c72F2).toBytes = [0x82] ++ c72F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c72F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c72_encode3 : (BLT.bytes c72F3).toBytes = [0x94] ++ c72F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c72F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c72_encode4 : (BLT.bytes c72F4).toBytes = [0x88] ++ c72F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c72F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c72_encode5 : (BLT.bytes c72F5).toBytes = [0x80] ++ c72F5 := by
  unfold c72F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c72_encode6 : (BLT.bytes c72F6).toBytes = [] ++ c72F6 := by
  unfold c72F6
  rw [BLT.toBytes]
  decide +kernel

theorem c72_encode7 : (BLT.bytes c72F7).toBytes = [0xa0] ++ c72F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c72F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c72_encode8 : (BLT.bytes c72F8).toBytes = [0xa0] ++ c72F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c72F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c72_canonical : c72Tx.toBLT.toBytes = c72Signed := by
  have encoded : BLTs.toBytesJoin c72Fields = c72Payload := by
    simp only [c72Fields, BLTs.toBytesJoin,
      c72_encode0, c72_encode1, c72_encode2, c72_encode3, c72_encode4, c72_encode5, c72_encode6, c72_encode7, c72_encode8, c72Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c72_blt, BLT.toBytes, BLTs.toBytes, encoded, c72_payload_length]
  norm_num only [c72Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c73F0 : Bytes := [0x1a]

def c73F1 : Bytes := [0x5f, 0x5e, 0x10, 0x00]

def c73F2 : Bytes := [0x52, 0x08]

def c73F3 : Bytes := [0xdb, 0x5f, 0x12, 0xa1, 0x56, 0x70, 0xcd, 0x3a, 0xbb, 0x77, 0x4d, 0xf3, 0xdb, 0x39, 0x7d, 0x08, 0x73, 0x42, 0xf7, 0x33]

def c73F4 : Bytes := [0x01, 0x53, 0x59, 0x67, 0xed, 0x24, 0x60, 0x00]

def c73F5 : Bytes := []

def c73F6 : Bytes := [0x25]

def c73F7 : Bytes := [0xd9, 0xfc, 0x91, 0xa7, 0x02, 0xa9, 0xb9, 0x81, 0x71, 0xcd, 0x00, 0xf3, 0x0f, 0x9f, 0xbc, 0x90, 0x33, 0xb2, 0xc9, 0xa1, 0x20, 0x95, 0x13, 0x01, 0x5e, 0xe6, 0x35, 0x83, 0x29, 0x94, 0xf3, 0xfc]

def c73F8 : Bytes := [0x68, 0x1c, 0xfb, 0xa1, 0x4a, 0x39, 0x66, 0xc1, 0xfe, 0xcf, 0xf5, 0x63, 0x4b, 0xe7, 0x7a, 0x2d, 0x52, 0x79, 0xe1, 0xb1, 0x8d, 0x90, 0x87, 0xa9, 0x26, 0x29, 0xe4, 0xd4, 0x4f, 0x9e, 0x90, 0x57]

def c73Fields : List BLT := [.bytes c73F0, .bytes c73F1, .bytes c73F2, .bytes c73F3, .bytes c73F4, .bytes c73F5, .bytes c73F6, .bytes c73F7, .bytes c73F8]

def c73Payload : Bytes := [] ++ c73F0 ++ [0x84] ++ c73F1 ++ [0x82] ++ c73F2 ++ [0x94] ++ c73F3 ++ [0x88] ++ c73F4 ++ [0x80] ++ c73F5 ++ [] ++ c73F6 ++ [0xa0] ++ c73F7 ++ [0xa0] ++ c73F8

def c73Signed : Bytes := [0xf8, 0x6b] ++ c73Payload

def c73Tx : Tx := { nonce := 26, gas := 21000, value := 95518320000000000, data := c73F5, v := 37, r := c73F7, s := c73F8, type := .zero 1600000000 (some 0xdb5f12a15670cd3abb774df3db397d087342f733) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c73_literal : c73Signed = [0xf8, 0x6b, 0x1a, 0x84, 0x5f, 0x5e, 0x10, 0x00, 0x82, 0x52, 0x08, 0x94, 0xdb, 0x5f, 0x12, 0xa1, 0x56, 0x70, 0xcd, 0x3a, 0xbb, 0x77, 0x4d, 0xf3, 0xdb, 0x39, 0x7d, 0x08, 0x73, 0x42, 0xf7, 0x33, 0x88, 0x01, 0x53, 0x59, 0x67, 0xed, 0x24, 0x60, 0x00, 0x80, 0x25, 0xa0, 0xd9, 0xfc, 0x91, 0xa7, 0x02, 0xa9, 0xb9, 0x81, 0x71, 0xcd, 0x00, 0xf3, 0x0f, 0x9f, 0xbc, 0x90, 0x33, 0xb2, 0xc9, 0xa1, 0x20, 0x95, 0x13, 0x01, 0x5e, 0xe6, 0x35, 0x83, 0x29, 0x94, 0xf3, 0xfc, 0xa0, 0x68, 0x1c, 0xfb, 0xa1, 0x4a, 0x39, 0x66, 0xc1, 0xfe, 0xcf, 0xf5, 0x63, 0x4b, 0xe7, 0x7a, 0x2d, 0x52, 0x79, 0xe1, 0xb1, 0x8d, 0x90, 0x87, 0xa9, 0x26, 0x29, 0xe4, 0xd4, 0x4f, 0x9e, 0x90, 0x57] := by
  decide +kernel

theorem c73_payload_length : c73Payload.length = 107 := by
  decide +kernel

theorem c73_signed_length : c73Signed.length = 109 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c73_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c73Payload = some c73Fields := by
  unfold c73Payload c73Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c73F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c73F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c73F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c73F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c73F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c73F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c73_parse : c73Signed.toBLT? = some (.list c73Fields) := by
  have outer : Bytes.toBLTDiff? 109 c73Signed = some (.list c73Fields, []) := by
    simpa only [c73Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 108 107 c73Payload [] c73Fields
        (by rw [c73_payload_length]; decide +kernel) (c73_payload_parse 99)
  unfold Bytes.toBLT?
  rw [c73_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c73_decode :
    (c73Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c73Tx := by
  rw [c73_parse]
  decide +kernel

theorem c73_blt : c73Tx.toBLT = .list c73Fields := by
  norm_num only [c73Tx, c73Fields, c73F0, c73F1, c73F2, c73F3, c73F4, c73F6, c73F7, c73F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c73_encode0 : (BLT.bytes c73F0).toBytes = [] ++ c73F0 := by
  unfold c73F0
  rw [BLT.toBytes]
  decide +kernel

theorem c73_encode1 : (BLT.bytes c73F1).toBytes = [0x84] ++ c73F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c73F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c73_encode2 : (BLT.bytes c73F2).toBytes = [0x82] ++ c73F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c73F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c73_encode3 : (BLT.bytes c73F3).toBytes = [0x94] ++ c73F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c73F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c73_encode4 : (BLT.bytes c73F4).toBytes = [0x88] ++ c73F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c73F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c73_encode5 : (BLT.bytes c73F5).toBytes = [0x80] ++ c73F5 := by
  unfold c73F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c73_encode6 : (BLT.bytes c73F6).toBytes = [] ++ c73F6 := by
  unfold c73F6
  rw [BLT.toBytes]
  decide +kernel

theorem c73_encode7 : (BLT.bytes c73F7).toBytes = [0xa0] ++ c73F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c73F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c73_encode8 : (BLT.bytes c73F8).toBytes = [0xa0] ++ c73F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c73F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c73_canonical : c73Tx.toBLT.toBytes = c73Signed := by
  have encoded : BLTs.toBytesJoin c73Fields = c73Payload := by
    simp only [c73Fields, BLTs.toBytesJoin,
      c73_encode0, c73_encode1, c73_encode2, c73_encode3, c73_encode4, c73_encode5, c73_encode6, c73_encode7, c73_encode8, c73Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c73_blt, BLT.toBytes, BLTs.toBytes, encoded, c73_payload_length]
  norm_num only [c73Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
