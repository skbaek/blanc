import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def c24F0 : Bytes := [0x6e]

def c24F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def c24F2 : Bytes := [0x03, 0xd0, 0x90]

def c24F3 : Bytes := [0x2a, 0x0c, 0x0d, 0xbe, 0xcc, 0x7e, 0x4d, 0x65, 0x8f, 0x48, 0xe0, 0x1e, 0x3f, 0xa3, 0x53, 0xf4, 0x40, 0x50, 0xc2, 0x08]

def c24F4 : Bytes := []

def c24F5 : Bytes := [0x33, 0x8b, 0x5d, 0xea, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd0, 0x35, 0x2a, 0x01, 0x9e, 0x9a, 0xb9, 0xd7, 0x57, 0x77, 0x6f, 0x53, 0x23, 0x77, 0xaa, 0xeb, 0xd3, 0x6f, 0xd5, 0x41, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x10, 0x24, 0xcb, 0xcd, 0x20, 0xa5, 0x71, 0xe8, 0x3e]

def c24F6 : Bytes := [0x26]

def c24F7 : Bytes := [0xc9, 0x4f, 0xaf, 0x74, 0x9d, 0x4f, 0xa3, 0xbc, 0xa2, 0xc0, 0x17, 0x93, 0x9e, 0x24, 0x10, 0xe1, 0x46, 0x2a, 0xe4, 0x93, 0x64, 0x1b, 0x32, 0x0f, 0x45, 0x3c, 0x95, 0xc7, 0x76, 0xed, 0x25, 0x89]

def c24F8 : Bytes := [0x5c, 0x93, 0x55, 0x03, 0xe5, 0x79, 0x34, 0x22, 0x5f, 0xca, 0xa9, 0x30, 0x3a, 0xff, 0x63, 0xcb, 0x90, 0x17, 0x6c, 0x88, 0x6c, 0x87, 0xbc, 0xac, 0x4b, 0xac, 0x98, 0x06, 0xc4, 0x61, 0x5f, 0x6e]

def c24Fields : List BLT := [.bytes c24F0, .bytes c24F1, .bytes c24F2, .bytes c24F3, .bytes c24F4, .bytes c24F5, .bytes c24F6, .bytes c24F7, .bytes c24F8]

def c24Payload : Bytes := [] ++ c24F0 ++ [0x84] ++ c24F1 ++ [0x83] ++ c24F2 ++ [0x94] ++ c24F3 ++ [0x80] ++ c24F4 ++ [0xb8, 0x44] ++ c24F5 ++ [] ++ c24F6 ++ [0xa0] ++ c24F7 ++ [0xa0] ++ c24F8

def c24Signed : Bytes := [0xf8, 0xa9] ++ c24Payload

def c24Tx : Tx := { nonce := 110, gas := 250000, value := 0, data := c24F5, v := 38, r := c24F7, s := c24F8, type := .zero 4000000000 (some 0x2a0c0dbecc7e4d658f48e01e3fa353f44050c208) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c24_literal : c24Signed = [0xf8, 0xa9, 0x6e, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x03, 0xd0, 0x90, 0x94, 0x2a, 0x0c, 0x0d, 0xbe, 0xcc, 0x7e, 0x4d, 0x65, 0x8f, 0x48, 0xe0, 0x1e, 0x3f, 0xa3, 0x53, 0xf4, 0x40, 0x50, 0xc2, 0x08, 0x80, 0xb8, 0x44, 0x33, 0x8b, 0x5d, 0xea, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd0, 0x35, 0x2a, 0x01, 0x9e, 0x9a, 0xb9, 0xd7, 0x57, 0x77, 0x6f, 0x53, 0x23, 0x77, 0xaa, 0xeb, 0xd3, 0x6f, 0xd5, 0x41, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x10, 0x24, 0xcb, 0xcd, 0x20, 0xa5, 0x71, 0xe8, 0x3e, 0x26, 0xa0, 0xc9, 0x4f, 0xaf, 0x74, 0x9d, 0x4f, 0xa3, 0xbc, 0xa2, 0xc0, 0x17, 0x93, 0x9e, 0x24, 0x10, 0xe1, 0x46, 0x2a, 0xe4, 0x93, 0x64, 0x1b, 0x32, 0x0f, 0x45, 0x3c, 0x95, 0xc7, 0x76, 0xed, 0x25, 0x89, 0xa0, 0x5c, 0x93, 0x55, 0x03, 0xe5, 0x79, 0x34, 0x22, 0x5f, 0xca, 0xa9, 0x30, 0x3a, 0xff, 0x63, 0xcb, 0x90, 0x17, 0x6c, 0x88, 0x6c, 0x87, 0xbc, 0xac, 0x4b, 0xac, 0x98, 0x06, 0xc4, 0x61, 0x5f, 0x6e] := by
  decide +kernel

theorem c24_payload_length : c24Payload.length = 169 := by
  decide +kernel

theorem c24_signed_length : c24Signed.length = 171 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c24_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c24Payload = some c24Fields := by
  unfold c24Payload c24Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c24F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c24F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c24F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c24F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c24F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c24F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c24_parse : c24Signed.toBLT? = some (.list c24Fields) := by
  have outer : Bytes.toBLTDiff? 171 c24Signed = some (.list c24Fields, []) := by
    simpa only [c24Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 170 169 c24Payload [] c24Fields
        (by rw [c24_payload_length]; decide +kernel) (c24_payload_parse 161)
  unfold Bytes.toBLT?
  rw [c24_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c24_decode :
    (c24Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c24Tx := by
  rw [c24_parse]
  decide +kernel

theorem c24_blt : c24Tx.toBLT = .list c24Fields := by
  norm_num only [c24Tx, c24Fields, c24F0, c24F1, c24F2, c24F3, c24F4, c24F6, c24F7, c24F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c24_encode0 : (BLT.bytes c24F0).toBytes = [] ++ c24F0 := by
  unfold c24F0
  rw [BLT.toBytes]
  decide +kernel

theorem c24_encode1 : (BLT.bytes c24F1).toBytes = [0x84] ++ c24F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c24F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c24_encode2 : (BLT.bytes c24F2).toBytes = [0x83] ++ c24F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c24F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c24_encode3 : (BLT.bytes c24F3).toBytes = [0x94] ++ c24F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c24F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c24_encode4 : (BLT.bytes c24F4).toBytes = [0x80] ++ c24F4 := by
  unfold c24F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c24_encode5 : (BLT.bytes c24F5).toBytes = [0xb8, 0x44] ++ c24F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c24F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c24_encode6 : (BLT.bytes c24F6).toBytes = [] ++ c24F6 := by
  unfold c24F6
  rw [BLT.toBytes]
  decide +kernel

theorem c24_encode7 : (BLT.bytes c24F7).toBytes = [0xa0] ++ c24F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c24F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c24_encode8 : (BLT.bytes c24F8).toBytes = [0xa0] ++ c24F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c24F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c24_canonical : c24Tx.toBLT.toBytes = c24Signed := by
  have encoded : BLTs.toBytesJoin c24Fields = c24Payload := by
    simp only [c24Fields, BLTs.toBytesJoin,
      c24_encode0, c24_encode1, c24_encode2, c24_encode3, c24_encode4, c24_encode5, c24_encode6, c24_encode7, c24_encode8, c24Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c24_blt, BLT.toBytes, BLTs.toBytes, encoded, c24_payload_length]
  norm_num only [c24Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c25F0 : Bytes := [0x01, 0x9c]

def c25F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def c25F2 : Bytes := [0x03, 0xc2, 0x04]

def c25F3 : Bytes := [0xd4, 0x8b, 0x63, 0x30, 0x45, 0xaf, 0x65, 0xff, 0x63, 0x6f, 0x3c, 0x6e, 0xdd, 0x74, 0x47, 0x48, 0x35, 0x1e, 0x02, 0x0d]

def c25F4 : Bytes := []

def c25F5 : Bytes := [0xfd, 0xb5, 0xa0, 0x3e]

def c25F6 : Bytes := [0x26]

def c25F7 : Bytes := [0x6b, 0x84, 0x2c, 0xbe, 0x1d, 0x2c, 0x43, 0x33, 0xb2, 0xe8, 0x7c, 0x9a, 0xa0, 0xf8, 0xb9, 0xcd, 0xf0, 0x1c, 0xdc, 0x79, 0xb0, 0x0e, 0x9e, 0x8b, 0x01, 0x14, 0xbe, 0x37, 0xb2, 0x68, 0x82, 0x8e]

def c25F8 : Bytes := [0x77, 0x0b, 0xba, 0x85, 0x2d, 0x9e, 0x96, 0xb0, 0x3e, 0xa1, 0x5e, 0xe0, 0x33, 0x83, 0xd0, 0x0b, 0x7c, 0x8c, 0x58, 0x91, 0xf1, 0x12, 0x03, 0xd8, 0x2e, 0x5e, 0xe6, 0x3f, 0xc8, 0x19, 0xe2, 0x4e]

def c25Fields : List BLT := [.bytes c25F0, .bytes c25F1, .bytes c25F2, .bytes c25F3, .bytes c25F4, .bytes c25F5, .bytes c25F6, .bytes c25F7, .bytes c25F8]

def c25Payload : Bytes := [0x82] ++ c25F0 ++ [0x84] ++ c25F1 ++ [0x83] ++ c25F2 ++ [0x94] ++ c25F3 ++ [0x80] ++ c25F4 ++ [0x84] ++ c25F5 ++ [] ++ c25F6 ++ [0xa0] ++ c25F7 ++ [0xa0] ++ c25F8

def c25Signed : Bytes := [0xf8, 0x6a] ++ c25Payload

def c25Tx : Tx := { nonce := 412, gas := 246276, value := 0, data := c25F5, v := 38, r := c25F7, s := c25F8, type := .zero 4000000000 (some 0xd48b633045af65ff636f3c6edd744748351e020d) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c25_literal : c25Signed = [0xf8, 0x6a, 0x82, 0x01, 0x9c, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x83, 0x03, 0xc2, 0x04, 0x94, 0xd4, 0x8b, 0x63, 0x30, 0x45, 0xaf, 0x65, 0xff, 0x63, 0x6f, 0x3c, 0x6e, 0xdd, 0x74, 0x47, 0x48, 0x35, 0x1e, 0x02, 0x0d, 0x80, 0x84, 0xfd, 0xb5, 0xa0, 0x3e, 0x26, 0xa0, 0x6b, 0x84, 0x2c, 0xbe, 0x1d, 0x2c, 0x43, 0x33, 0xb2, 0xe8, 0x7c, 0x9a, 0xa0, 0xf8, 0xb9, 0xcd, 0xf0, 0x1c, 0xdc, 0x79, 0xb0, 0x0e, 0x9e, 0x8b, 0x01, 0x14, 0xbe, 0x37, 0xb2, 0x68, 0x82, 0x8e, 0xa0, 0x77, 0x0b, 0xba, 0x85, 0x2d, 0x9e, 0x96, 0xb0, 0x3e, 0xa1, 0x5e, 0xe0, 0x33, 0x83, 0xd0, 0x0b, 0x7c, 0x8c, 0x58, 0x91, 0xf1, 0x12, 0x03, 0xd8, 0x2e, 0x5e, 0xe6, 0x3f, 0xc8, 0x19, 0xe2, 0x4e] := by
  decide +kernel

theorem c25_payload_length : c25Payload.length = 106 := by
  decide +kernel

theorem c25_signed_length : c25Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c25_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c25Payload = some c25Fields := by
  unfold c25Payload c25Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c25F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c25F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c25F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c25F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c25F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c25F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c25F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c25_parse : c25Signed.toBLT? = some (.list c25Fields) := by
  have outer : Bytes.toBLTDiff? 108 c25Signed = some (.list c25Fields, []) := by
    simpa only [c25Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 c25Payload [] c25Fields
        (by rw [c25_payload_length]; decide +kernel) (c25_payload_parse 98)
  unfold Bytes.toBLT?
  rw [c25_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c25_decode :
    (c25Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c25Tx := by
  rw [c25_parse]
  decide +kernel

theorem c25_blt : c25Tx.toBLT = .list c25Fields := by
  norm_num only [c25Tx, c25Fields, c25F0, c25F1, c25F2, c25F3, c25F4, c25F6, c25F7, c25F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c25_encode0 : (BLT.bytes c25F0).toBytes = [0x82] ++ c25F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c25F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c25_encode1 : (BLT.bytes c25F1).toBytes = [0x84] ++ c25F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c25F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c25_encode2 : (BLT.bytes c25F2).toBytes = [0x83] ++ c25F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c25F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c25_encode3 : (BLT.bytes c25F3).toBytes = [0x94] ++ c25F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c25F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c25_encode4 : (BLT.bytes c25F4).toBytes = [0x80] ++ c25F4 := by
  unfold c25F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c25_encode5 : (BLT.bytes c25F5).toBytes = [0x84] ++ c25F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c25F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c25_encode6 : (BLT.bytes c25F6).toBytes = [] ++ c25F6 := by
  unfold c25F6
  rw [BLT.toBytes]
  decide +kernel

theorem c25_encode7 : (BLT.bytes c25F7).toBytes = [0xa0] ++ c25F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c25F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c25_encode8 : (BLT.bytes c25F8).toBytes = [0xa0] ++ c25F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c25F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c25_canonical : c25Tx.toBLT.toBytes = c25Signed := by
  have encoded : BLTs.toBytesJoin c25Fields = c25Payload := by
    simp only [c25Fields, BLTs.toBytesJoin,
      c25_encode0, c25_encode1, c25_encode2, c25_encode3, c25_encode4, c25_encode5, c25_encode6, c25_encode7, c25_encode8, c25Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c25_blt, BLT.toBytes, BLTs.toBytes, encoded, c25_payload_length]
  norm_num only [c25Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c26F0 : Bytes := []

def c26F1 : Bytes := [0xee, 0x6b, 0x28, 0x00]

def c26F2 : Bytes := [0x52, 0x08]

def c26F3 : Bytes := [0xf7, 0x7d, 0xf9, 0x82, 0x9e, 0x79, 0x01, 0xab, 0x30, 0x75, 0xd5, 0x56, 0xb8, 0x4a, 0xd7, 0x25, 0x89, 0xbf, 0xa4, 0xe2]

def c26F4 : Bytes := [0x23, 0x3a, 0x8c, 0xa9, 0x97, 0xc0, 0x00]

def c26F5 : Bytes := []

def c26F6 : Bytes := [0x25]

def c26F7 : Bytes := [0x13, 0xa5, 0xc5, 0xea, 0x10, 0x03, 0x57, 0xea, 0xca, 0x81, 0x3f, 0x3d, 0xd4, 0x52, 0x40, 0xd2, 0xdb, 0x15, 0x30, 0x32, 0xac, 0xd3, 0xdf, 0x79, 0x2f, 0xfd, 0xc6, 0x61, 0xa6, 0x63, 0x6d, 0x93]

def c26F8 : Bytes := [0x27, 0x56, 0x72, 0xdb, 0x2b, 0xb3, 0xcd, 0x3d, 0xab, 0x41, 0xf3, 0x55, 0xd7, 0x0a, 0x1c, 0x60, 0xc4, 0x34, 0x0a, 0x29, 0xdd, 0x78, 0x87, 0x50, 0x2f, 0xb1, 0x58, 0xaf, 0x95, 0xe3, 0x94, 0x27]

def c26Fields : List BLT := [.bytes c26F0, .bytes c26F1, .bytes c26F2, .bytes c26F3, .bytes c26F4, .bytes c26F5, .bytes c26F6, .bytes c26F7, .bytes c26F8]

def c26Payload : Bytes := [0x80] ++ c26F0 ++ [0x84] ++ c26F1 ++ [0x82] ++ c26F2 ++ [0x94] ++ c26F3 ++ [0x87] ++ c26F4 ++ [0x80] ++ c26F5 ++ [] ++ c26F6 ++ [0xa0] ++ c26F7 ++ [0xa0] ++ c26F8

def c26Signed : Bytes := [0xf8, 0x6a] ++ c26Payload

def c26Tx : Tx := { nonce := 0, gas := 21000, value := 9916000000000000, data := c26F5, v := 37, r := c26F7, s := c26F8, type := .zero 4000000000 (some 0xf77df9829e7901ab3075d556b84ad72589bfa4e2) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c26_literal : c26Signed = [0xf8, 0x6a, 0x80, 0x84, 0xee, 0x6b, 0x28, 0x00, 0x82, 0x52, 0x08, 0x94, 0xf7, 0x7d, 0xf9, 0x82, 0x9e, 0x79, 0x01, 0xab, 0x30, 0x75, 0xd5, 0x56, 0xb8, 0x4a, 0xd7, 0x25, 0x89, 0xbf, 0xa4, 0xe2, 0x87, 0x23, 0x3a, 0x8c, 0xa9, 0x97, 0xc0, 0x00, 0x80, 0x25, 0xa0, 0x13, 0xa5, 0xc5, 0xea, 0x10, 0x03, 0x57, 0xea, 0xca, 0x81, 0x3f, 0x3d, 0xd4, 0x52, 0x40, 0xd2, 0xdb, 0x15, 0x30, 0x32, 0xac, 0xd3, 0xdf, 0x79, 0x2f, 0xfd, 0xc6, 0x61, 0xa6, 0x63, 0x6d, 0x93, 0xa0, 0x27, 0x56, 0x72, 0xdb, 0x2b, 0xb3, 0xcd, 0x3d, 0xab, 0x41, 0xf3, 0x55, 0xd7, 0x0a, 0x1c, 0x60, 0xc4, 0x34, 0x0a, 0x29, 0xdd, 0x78, 0x87, 0x50, 0x2f, 0xb1, 0x58, 0xaf, 0x95, 0xe3, 0x94, 0x27] := by
  decide +kernel

theorem c26_payload_length : c26Payload.length = 106 := by
  decide +kernel

theorem c26_signed_length : c26Signed.length = 108 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c26_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c26Payload = some c26Fields := by
  unfold c26Payload c26Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c26F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c26F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c26F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 7 c26F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c26F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c26F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c26_parse : c26Signed.toBLT? = some (.list c26Fields) := by
  have outer : Bytes.toBLTDiff? 108 c26Signed = some (.list c26Fields, []) := by
    simpa only [c26Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 107 106 c26Payload [] c26Fields
        (by rw [c26_payload_length]; decide +kernel) (c26_payload_parse 98)
  unfold Bytes.toBLT?
  rw [c26_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c26_decode :
    (c26Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c26Tx := by
  rw [c26_parse]
  decide +kernel

theorem c26_blt : c26Tx.toBLT = .list c26Fields := by
  norm_num only [c26Tx, c26Fields, c26F0, c26F1, c26F2, c26F3, c26F4, c26F6, c26F7, c26F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c26_encode0 : (BLT.bytes c26F0).toBytes = [0x80] ++ c26F0 := by
  unfold c26F0
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c26_encode1 : (BLT.bytes c26F1).toBytes = [0x84] ++ c26F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c26F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c26_encode2 : (BLT.bytes c26F2).toBytes = [0x82] ++ c26F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c26F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c26_encode3 : (BLT.bytes c26F3).toBytes = [0x94] ++ c26F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c26F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c26_encode4 : (BLT.bytes c26F4).toBytes = [0x87] ++ c26F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c26F4.length = 7 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c26_encode5 : (BLT.bytes c26F5).toBytes = [0x80] ++ c26F5 := by
  unfold c26F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c26_encode6 : (BLT.bytes c26F6).toBytes = [] ++ c26F6 := by
  unfold c26F6
  rw [BLT.toBytes]
  decide +kernel

theorem c26_encode7 : (BLT.bytes c26F7).toBytes = [0xa0] ++ c26F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c26F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c26_encode8 : (BLT.bytes c26F8).toBytes = [0xa0] ++ c26F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c26F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c26_canonical : c26Tx.toBLT.toBytes = c26Signed := by
  have encoded : BLTs.toBytesJoin c26Fields = c26Payload := by
    simp only [c26Fields, BLTs.toBytesJoin,
      c26_encode0, c26_encode1, c26_encode2, c26_encode3, c26_encode4, c26_encode5, c26_encode6, c26_encode7, c26_encode8, c26Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c26_blt, BLT.toBytes, BLTs.toBytes, encoded, c26_payload_length]
  norm_num only [c26Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c27F0 : Bytes := [0x46, 0x16]

def c27F1 : Bytes := [0xd6, 0x93, 0xa4, 0x00]

def c27F2 : Bytes := [0x01, 0x5f, 0x90]

def c27F3 : Bytes := [0x15, 0x24, 0xde, 0xf7, 0xae, 0x94, 0x29, 0x59, 0xdd, 0xe0, 0xd1, 0x1b, 0x36, 0x1f, 0xa2, 0x94, 0x02, 0xf2, 0x92, 0xc6]

def c27F4 : Bytes := [0x23, 0x6b, 0xb9, 0xd0, 0xbc, 0x5c, 0x00]

def c27F5 : Bytes := []

def c27F6 : Bytes := [0x25]

def c27F7 : Bytes := [0xd4, 0x5c, 0x06, 0x06, 0xe8, 0xbe, 0x9d, 0xdb, 0x11, 0x56, 0xbf, 0x38, 0xd2, 0x3d, 0xbd, 0x23, 0x26, 0x26, 0x72, 0x61, 0xa9, 0x2d, 0x7d, 0xcd, 0xc3, 0x3c, 0x98, 0x5d, 0xad, 0x69, 0xca, 0x36]

def c27F8 : Bytes := [0x0b, 0x2d, 0xd5, 0x0d, 0x26, 0xbb, 0xbc, 0xeb, 0xa2, 0x85, 0xa1, 0x72, 0xb1, 0xdf, 0xb2, 0x1a, 0xaf, 0xd7, 0x92, 0x44, 0xea, 0x16, 0xe8, 0x2c, 0x8b, 0xed, 0x35, 0xa7, 0x78, 0xdb, 0x9d, 0x51]

def c27Fields : List BLT := [.bytes c27F0, .bytes c27F1, .bytes c27F2, .bytes c27F3, .bytes c27F4, .bytes c27F5, .bytes c27F6, .bytes c27F7, .bytes c27F8]

def c27Payload : Bytes := [0x82] ++ c27F0 ++ [0x84] ++ c27F1 ++ [0x83] ++ c27F2 ++ [0x94] ++ c27F3 ++ [0x87] ++ c27F4 ++ [0x80] ++ c27F5 ++ [] ++ c27F6 ++ [0xa0] ++ c27F7 ++ [0xa0] ++ c27F8

def c27Signed : Bytes := [0xf8, 0x6d] ++ c27Payload

def c27Tx : Tx := { nonce := 17942, gas := 90000, value := 9970070000000000, data := c27F5, v := 37, r := c27F7, s := c27F8, type := .zero 3600000000 (some 0x1524def7ae942959dde0d11b361fa29402f292c6) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c27_literal : c27Signed = [0xf8, 0x6d, 0x82, 0x46, 0x16, 0x84, 0xd6, 0x93, 0xa4, 0x00, 0x83, 0x01, 0x5f, 0x90, 0x94, 0x15, 0x24, 0xde, 0xf7, 0xae, 0x94, 0x29, 0x59, 0xdd, 0xe0, 0xd1, 0x1b, 0x36, 0x1f, 0xa2, 0x94, 0x02, 0xf2, 0x92, 0xc6, 0x87, 0x23, 0x6b, 0xb9, 0xd0, 0xbc, 0x5c, 0x00, 0x80, 0x25, 0xa0, 0xd4, 0x5c, 0x06, 0x06, 0xe8, 0xbe, 0x9d, 0xdb, 0x11, 0x56, 0xbf, 0x38, 0xd2, 0x3d, 0xbd, 0x23, 0x26, 0x26, 0x72, 0x61, 0xa9, 0x2d, 0x7d, 0xcd, 0xc3, 0x3c, 0x98, 0x5d, 0xad, 0x69, 0xca, 0x36, 0xa0, 0x0b, 0x2d, 0xd5, 0x0d, 0x26, 0xbb, 0xbc, 0xeb, 0xa2, 0x85, 0xa1, 0x72, 0xb1, 0xdf, 0xb2, 0x1a, 0xaf, 0xd7, 0x92, 0x44, 0xea, 0x16, 0xe8, 0x2c, 0x8b, 0xed, 0x35, 0xa7, 0x78, 0xdb, 0x9d, 0x51] := by
  decide +kernel

theorem c27_payload_length : c27Payload.length = 109 := by
  decide +kernel

theorem c27_signed_length : c27Signed.length = 111 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c27_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c27Payload = some c27Fields := by
  unfold c27Payload c27Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c27F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c27F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c27F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c27F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 7 c27F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c27F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c27F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c27_parse : c27Signed.toBLT? = some (.list c27Fields) := by
  have outer : Bytes.toBLTDiff? 111 c27Signed = some (.list c27Fields, []) := by
    simpa only [c27Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 110 109 c27Payload [] c27Fields
        (by rw [c27_payload_length]; decide +kernel) (c27_payload_parse 101)
  unfold Bytes.toBLT?
  rw [c27_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c27_decode :
    (c27Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c27Tx := by
  rw [c27_parse]
  decide +kernel

theorem c27_blt : c27Tx.toBLT = .list c27Fields := by
  norm_num only [c27Tx, c27Fields, c27F0, c27F1, c27F2, c27F3, c27F4, c27F6, c27F7, c27F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c27_encode0 : (BLT.bytes c27F0).toBytes = [0x82] ++ c27F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c27F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c27_encode1 : (BLT.bytes c27F1).toBytes = [0x84] ++ c27F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c27F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c27_encode2 : (BLT.bytes c27F2).toBytes = [0x83] ++ c27F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c27F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c27_encode3 : (BLT.bytes c27F3).toBytes = [0x94] ++ c27F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c27F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c27_encode4 : (BLT.bytes c27F4).toBytes = [0x87] ++ c27F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c27F4.length = 7 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c27_encode5 : (BLT.bytes c27F5).toBytes = [0x80] ++ c27F5 := by
  unfold c27F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c27_encode6 : (BLT.bytes c27F6).toBytes = [] ++ c27F6 := by
  unfold c27F6
  rw [BLT.toBytes]
  decide +kernel

theorem c27_encode7 : (BLT.bytes c27F7).toBytes = [0xa0] ++ c27F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c27F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c27_encode8 : (BLT.bytes c27F8).toBytes = [0xa0] ++ c27F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c27F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c27_canonical : c27Tx.toBLT.toBytes = c27Signed := by
  have encoded : BLTs.toBytesJoin c27Fields = c27Payload := by
    simp only [c27Fields, BLTs.toBytesJoin,
      c27_encode0, c27_encode1, c27_encode2, c27_encode3, c27_encode4, c27_encode5, c27_encode6, c27_encode7, c27_encode8, c27Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c27_blt, BLT.toBytes, BLTs.toBytes, encoded, c27_payload_length]
  norm_num only [c27Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c28F0 : Bytes := [0x02, 0x23]

def c28F1 : Bytes := [0xd6, 0x93, 0xa4, 0x00]

def c28F2 : Bytes := [0x03, 0xe8, 0x2a]

def c28F3 : Bytes := [0xd4, 0x8b, 0x63, 0x30, 0x45, 0xaf, 0x65, 0xff, 0x63, 0x6f, 0x3c, 0x6e, 0xdd, 0x74, 0x47, 0x48, 0x35, 0x1e, 0x02, 0x0d]

def c28F4 : Bytes := []

def c28F5 : Bytes := [0x19, 0xfb, 0x36, 0x1f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2f, 0xe8, 0xe1, 0x06, 0x33, 0xea, 0xe7, 0x1b, 0x50, 0x3c, 0x60, 0x18, 0x0c, 0x41, 0x90, 0x71, 0x0a, 0x13, 0x22, 0x37, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb7, 0xe5, 0xf4, 0x73, 0xe5, 0x55, 0x0d, 0x7c, 0xa9, 0x85, 0x75, 0x61, 0x26, 0x95, 0x31, 0x78, 0x70, 0x94, 0xb7, 0x15, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0xa0, 0x55, 0x69, 0x0d, 0x9d, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

def c28F6 : Bytes := [0x25]

def c28F7 : Bytes := [0x2a, 0xdb, 0x59, 0xfb, 0x33, 0x3e, 0x7e, 0x59, 0x7a, 0x99, 0xba, 0xb4, 0x9f, 0x22, 0x27, 0xed, 0xa9, 0x7f, 0x21, 0x7d, 0xfe, 0x16, 0x95, 0x95, 0x8a, 0x46, 0x22, 0x0c, 0x87, 0xa1, 0xbb, 0x7d]

def c28F8 : Bytes := [0x22, 0xf1, 0x63, 0xd5, 0xef, 0x7c, 0x80, 0x5d, 0x58, 0xe6, 0x33, 0x51, 0xcd, 0x11, 0x9c, 0xf3, 0x7a, 0x16, 0xf5, 0xfb, 0x9c, 0x8b, 0xe4, 0xb8, 0x0b, 0x4b, 0x92, 0x83, 0xad, 0x7c, 0x54, 0x60]

def c28Fields : List BLT := [.bytes c28F0, .bytes c28F1, .bytes c28F2, .bytes c28F3, .bytes c28F4, .bytes c28F5, .bytes c28F6, .bytes c28F7, .bytes c28F8]

def c28Payload : Bytes := [0x82] ++ c28F0 ++ [0x84] ++ c28F1 ++ [0x83] ++ c28F2 ++ [0x94] ++ c28F3 ++ [0x80] ++ c28F4 ++ [0xb8, 0xc4] ++ c28F5 ++ [] ++ c28F6 ++ [0xa0] ++ c28F7 ++ [0xa0] ++ c28F8

def c28Signed : Bytes := [0xf9, 0x01, 0x2b] ++ c28Payload

def c28Tx : Tx := { nonce := 547, gas := 256042, value := 0, data := c28F5, v := 37, r := c28F7, s := c28F8, type := .zero 3600000000 (some 0xd48b633045af65ff636f3c6edd744748351e020d) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c28_literal : c28Signed = [0xf9, 0x01, 0x2b, 0x82, 0x02, 0x23, 0x84, 0xd6, 0x93, 0xa4, 0x00, 0x83, 0x03, 0xe8, 0x2a, 0x94, 0xd4, 0x8b, 0x63, 0x30, 0x45, 0xaf, 0x65, 0xff, 0x63, 0x6f, 0x3c, 0x6e, 0xdd, 0x74, 0x47, 0x48, 0x35, 0x1e, 0x02, 0x0d, 0x80, 0xb8, 0xc4, 0x19, 0xfb, 0x36, 0x1f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2f, 0xe8, 0xe1, 0x06, 0x33, 0xea, 0xe7, 0x1b, 0x50, 0x3c, 0x60, 0x18, 0x0c, 0x41, 0x90, 0x71, 0x0a, 0x13, 0x22, 0x37, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb7, 0xe5, 0xf4, 0x73, 0xe5, 0x55, 0x0d, 0x7c, 0xa9, 0x85, 0x75, 0x61, 0x26, 0x95, 0x31, 0x78, 0x70, 0x94, 0xb7, 0x15, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0xa0, 0x55, 0x69, 0x0d, 0x9d, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25, 0xa0, 0x2a, 0xdb, 0x59, 0xfb, 0x33, 0x3e, 0x7e, 0x59, 0x7a, 0x99, 0xba, 0xb4, 0x9f, 0x22, 0x27, 0xed, 0xa9, 0x7f, 0x21, 0x7d, 0xfe, 0x16, 0x95, 0x95, 0x8a, 0x46, 0x22, 0x0c, 0x87, 0xa1, 0xbb, 0x7d, 0xa0, 0x22, 0xf1, 0x63, 0xd5, 0xef, 0x7c, 0x80, 0x5d, 0x58, 0xe6, 0x33, 0x51, 0xcd, 0x11, 0x9c, 0xf3, 0x7a, 0x16, 0xf5, 0xfb, 0x9c, 0x8b, 0xe4, 0xb8, 0x0b, 0x4b, 0x92, 0x83, 0xad, 0x7c, 0x54, 0x60] := by
  decide +kernel

theorem c28_payload_length : c28Payload.length = 299 := by
  decide +kernel

theorem c28_signed_length : c28Signed.length = 302 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c28_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c28Payload = some c28Fields := by
  unfold c28Payload c28Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c28F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c28F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c28F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c28F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 196 c28F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c28F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c28F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c28_parse : c28Signed.toBLT? = some (.list c28Fields) := by
  have outer : Bytes.toBLTDiff? 302 c28Signed = some (.list c28Fields, []) := by
    simpa only [c28Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_two 301 1 43 c28Payload [] c28Fields
        (by rw [c28_payload_length]; decide +kernel) (c28_payload_parse 292)
  unfold Bytes.toBLT?
  rw [c28_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c28_decode :
    (c28Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c28Tx := by
  rw [c28_parse]
  decide +kernel

theorem c28_blt : c28Tx.toBLT = .list c28Fields := by
  norm_num only [c28Tx, c28Fields, c28F0, c28F1, c28F2, c28F3, c28F4, c28F6, c28F7, c28F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c28_encode0 : (BLT.bytes c28F0).toBytes = [0x82] ++ c28F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c28F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c28_encode1 : (BLT.bytes c28F1).toBytes = [0x84] ++ c28F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c28F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c28_encode2 : (BLT.bytes c28F2).toBytes = [0x83] ++ c28F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c28F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c28_encode3 : (BLT.bytes c28F3).toBytes = [0x94] ++ c28F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c28F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c28_encode4 : (BLT.bytes c28F4).toBytes = [0x80] ++ c28F4 := by
  unfold c28F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c28_encode5 : (BLT.bytes c28F5).toBytes = [0xb8, 0xc4] ++ c28F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c28F5.length = 196 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c28_encode6 : (BLT.bytes c28F6).toBytes = [] ++ c28F6 := by
  unfold c28F6
  rw [BLT.toBytes]
  decide +kernel

theorem c28_encode7 : (BLT.bytes c28F7).toBytes = [0xa0] ++ c28F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c28F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c28_encode8 : (BLT.bytes c28F8).toBytes = [0xa0] ++ c28F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c28F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c28_canonical : c28Tx.toBLT.toBytes = c28Signed := by
  have encoded : BLTs.toBytesJoin c28Fields = c28Payload := by
    simp only [c28Fields, BLTs.toBytesJoin,
      c28_encode0, c28_encode1, c28_encode2, c28_encode3, c28_encode4, c28_encode5, c28_encode6, c28_encode7, c28_encode8, c28Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c28_blt, BLT.toBytes, BLTs.toBytes, encoded, c28_payload_length]
  norm_num only [c28Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c29F0 : Bytes := [0x0a, 0xf6]

def c29F1 : Bytes := [0xd6, 0x93, 0xa4, 0x00]

def c29F2 : Bytes := [0x01, 0xaa, 0x6d]

def c29F3 : Bytes := [0xb1, 0x69, 0x0c, 0x08, 0xe2, 0x13, 0xa3, 0x5e, 0xd9, 0xba, 0xb7, 0xb3, 0x18, 0xde, 0x14, 0x42, 0x0f, 0xb5, 0x7d, 0x8c]

def c29F4 : Bytes := []

def c29F5 : Bytes := [0x96, 0xb5, 0xa7, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0a, 0xa0, 0x4e]

def c29F6 : Bytes := [0x25]

def c29F7 : Bytes := [0xb8, 0xda, 0xd2, 0x85, 0x18, 0x2a, 0x0a, 0xdb, 0x82, 0xc5, 0x28, 0x52, 0x2c, 0xd9, 0x0c, 0xc7, 0xc8, 0xd8, 0xe7, 0x14, 0x3d, 0x3e, 0x2b, 0xf8, 0x06, 0x5f, 0x5e, 0x1f, 0x53, 0x55, 0xac, 0x7b]

def c29F8 : Bytes := [0x24, 0x36, 0x8b, 0x4e, 0x9c, 0xdb, 0x91, 0xff, 0x08, 0xe9, 0xc5, 0xc3, 0x51, 0xf8, 0x59, 0xb9, 0x49, 0x9b, 0xb8, 0xd4, 0x49, 0xe0, 0xda, 0x40, 0x1a, 0x9b, 0xf5, 0x50, 0x3a, 0xa6, 0xf9, 0x8b]

def c29Fields : List BLT := [.bytes c29F0, .bytes c29F1, .bytes c29F2, .bytes c29F3, .bytes c29F4, .bytes c29F5, .bytes c29F6, .bytes c29F7, .bytes c29F8]

def c29Payload : Bytes := [0x82] ++ c29F0 ++ [0x84] ++ c29F1 ++ [0x83] ++ c29F2 ++ [0x94] ++ c29F3 ++ [0x80] ++ c29F4 ++ [0xa4] ++ c29F5 ++ [] ++ c29F6 ++ [0xa0] ++ c29F7 ++ [0xa0] ++ c29F8

def c29Signed : Bytes := [0xf8, 0x8a] ++ c29Payload

def c29Tx : Tx := { nonce := 2806, gas := 109165, value := 0, data := c29F5, v := 37, r := c29F7, s := c29F8, type := .zero 3600000000 (some 0xb1690c08e213a35ed9bab7b318de14420fb57d8c) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c29_literal : c29Signed = [0xf8, 0x8a, 0x82, 0x0a, 0xf6, 0x84, 0xd6, 0x93, 0xa4, 0x00, 0x83, 0x01, 0xaa, 0x6d, 0x94, 0xb1, 0x69, 0x0c, 0x08, 0xe2, 0x13, 0xa3, 0x5e, 0xd9, 0xba, 0xb7, 0xb3, 0x18, 0xde, 0x14, 0x42, 0x0f, 0xb5, 0x7d, 0x8c, 0x80, 0xa4, 0x96, 0xb5, 0xa7, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0a, 0xa0, 0x4e, 0x25, 0xa0, 0xb8, 0xda, 0xd2, 0x85, 0x18, 0x2a, 0x0a, 0xdb, 0x82, 0xc5, 0x28, 0x52, 0x2c, 0xd9, 0x0c, 0xc7, 0xc8, 0xd8, 0xe7, 0x14, 0x3d, 0x3e, 0x2b, 0xf8, 0x06, 0x5f, 0x5e, 0x1f, 0x53, 0x55, 0xac, 0x7b, 0xa0, 0x24, 0x36, 0x8b, 0x4e, 0x9c, 0xdb, 0x91, 0xff, 0x08, 0xe9, 0xc5, 0xc3, 0x51, 0xf8, 0x59, 0xb9, 0x49, 0x9b, 0xb8, 0xd4, 0x49, 0xe0, 0xda, 0x40, 0x1a, 0x9b, 0xf5, 0x50, 0x3a, 0xa6, 0xf9, 0x8b] := by
  decide +kernel

theorem c29_payload_length : c29Payload.length = 138 := by
  decide +kernel

theorem c29_signed_length : c29Signed.length = 140 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c29_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c29Payload = some c29Fields := by
  unfold c29Payload c29Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c29F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c29F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c29F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c29F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 36 c29F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c29F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c29F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c29_parse : c29Signed.toBLT? = some (.list c29Fields) := by
  have outer : Bytes.toBLTDiff? 140 c29Signed = some (.list c29Fields, []) := by
    simpa only [c29Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 139 138 c29Payload [] c29Fields
        (by rw [c29_payload_length]; decide +kernel) (c29_payload_parse 130)
  unfold Bytes.toBLT?
  rw [c29_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c29_decode :
    (c29Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c29Tx := by
  rw [c29_parse]
  decide +kernel

theorem c29_blt : c29Tx.toBLT = .list c29Fields := by
  norm_num only [c29Tx, c29Fields, c29F0, c29F1, c29F2, c29F3, c29F4, c29F6, c29F7, c29F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c29_encode0 : (BLT.bytes c29F0).toBytes = [0x82] ++ c29F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c29F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c29_encode1 : (BLT.bytes c29F1).toBytes = [0x84] ++ c29F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c29F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c29_encode2 : (BLT.bytes c29F2).toBytes = [0x83] ++ c29F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c29F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c29_encode3 : (BLT.bytes c29F3).toBytes = [0x94] ++ c29F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c29F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c29_encode4 : (BLT.bytes c29F4).toBytes = [0x80] ++ c29F4 := by
  unfold c29F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c29_encode5 : (BLT.bytes c29F5).toBytes = [0xa4] ++ c29F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c29F5.length = 36 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c29_encode6 : (BLT.bytes c29F6).toBytes = [] ++ c29F6 := by
  unfold c29F6
  rw [BLT.toBytes]
  decide +kernel

theorem c29_encode7 : (BLT.bytes c29F7).toBytes = [0xa0] ++ c29F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c29F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c29_encode8 : (BLT.bytes c29F8).toBytes = [0xa0] ++ c29F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c29F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c29_canonical : c29Tx.toBLT.toBytes = c29Signed := by
  have encoded : BLTs.toBytesJoin c29Fields = c29Payload := by
    simp only [c29Fields, BLTs.toBytesJoin,
      c29_encode0, c29_encode1, c29_encode2, c29_encode3, c29_encode4, c29_encode5, c29_encode6, c29_encode7, c29_encode8, c29Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c29_blt, BLT.toBytes, BLTs.toBytes, encoded, c29_payload_length]
  norm_num only [c29Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c30F0 : Bytes := [0xfb, 0xe6]

def c30F1 : Bytes := [0xd0, 0xcb, 0x89, 0xc0]

def c30F2 : Bytes := [0x02, 0xc3, 0x08]

def c30F3 : Bytes := [0x76, 0x00, 0x97, 0x7e, 0xb9, 0xef, 0xfa, 0x62, 0x7d, 0x6b, 0xd0, 0xda, 0x2e, 0x5b, 0xe3, 0x5e, 0x11, 0x56, 0x63, 0x41]

def c30F4 : Bytes := []

def c30F5 : Bytes := [0x72, 0x2d, 0xed, 0x24, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x64, 0xac, 0x8c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0xd5, 0xba, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x01, 0x65, 0x01, 0x42, 0x05, 0x23, 0xb8, 0x09, 0x71, 0xfb, 0xd7, 0x86, 0xb0, 0x3e, 0x19, 0x47, 0x29, 0x7e, 0xa1, 0x84, 0xa3, 0xbf, 0x0b, 0x93, 0xa2, 0x76, 0x1c, 0xde, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x64, 0xba, 0x9c, 0x00, 0x00, 0x01, 0x01, 0xb9, 0x66, 0x85, 0x49, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x33, 0xc8, 0x00, 0x01, 0x00, 0x00, 0x00, 0x7c, 0x08, 0x2d, 0x31, 0x8b, 0x42, 0x3b, 0x94, 0xec, 0x5a, 0x4f, 0xf9, 0xc9, 0xe6, 0xab, 0xcf, 0xa9, 0x1e, 0x89, 0xa5, 0x1c, 0x50, 0xcf, 0xea, 0x75, 0x60, 0xf6, 0x5f, 0x53, 0x1c, 0x85, 0x61, 0xfc, 0x21, 0x91, 0x77, 0x66, 0xfe, 0x18, 0x90, 0xea, 0xe0, 0x70, 0x1a, 0xef, 0x6a, 0x51, 0xfe, 0xd0, 0x9a, 0x67, 0x5e, 0x49, 0x83, 0x1c, 0x35, 0x72, 0x64, 0xb3, 0x73, 0x54, 0xe6, 0x16, 0xe2, 0x7d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x65, 0x01, 0x42, 0x05, 0x71, 0x94, 0x86, 0x7c, 0xfd, 0x17, 0xe5, 0x4f, 0xaa, 0xcc, 0x9c, 0x89, 0xc1, 0x80, 0xc7, 0xa8, 0x02, 0x79, 0x13, 0x68, 0xc0, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x64, 0xba, 0x9c, 0x00, 0x00, 0x01, 0x01, 0xb9, 0x66, 0x85, 0x49, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x33, 0xc8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7c, 0x1e, 0xd8, 0x5d, 0x80, 0x2e, 0xe3, 0x59, 0xbc, 0xca, 0x9d, 0xa9, 0x01, 0xc8, 0x0a, 0xdd, 0x3a, 0x5f, 0xa4, 0xe5, 0x99, 0xf6, 0x00, 0x87, 0x94, 0x82, 0xd4, 0x62, 0xfd, 0x04, 0x9f, 0xca, 0x06, 0x55, 0x8f, 0x27, 0xab, 0x05, 0x4d, 0xb2, 0xe6, 0x2a, 0x47, 0xc0, 0x39, 0x00, 0x71, 0xe3, 0x7f, 0x9f, 0x7f, 0xf0, 0xb0, 0xdd, 0xc0, 0x7a, 0x8f, 0x9d, 0x35, 0x02, 0xb4, 0xd8, 0x57, 0x66, 0xa5]

def c30F6 : Bytes := [0x26]

def c30F7 : Bytes := [0xca, 0xfb, 0xc7, 0xb3, 0x4e, 0xd3, 0x24, 0xb1, 0x70, 0x2f, 0x2a, 0xa8, 0x77, 0x71, 0xa9, 0x78, 0xbc, 0xc2, 0x14, 0x5c, 0x23, 0xf1, 0x26, 0x72, 0x03, 0xbe, 0xed, 0x9e, 0xf8, 0x6f, 0xce, 0x36]

def c30F8 : Bytes := [0x22, 0x33, 0xd0, 0xb6, 0xa0, 0xb1, 0x7e, 0x2c, 0xf9, 0x4b, 0x6b, 0xa6, 0xce, 0x30, 0xf8, 0xc8, 0x9e, 0x13, 0x19, 0x8c, 0x29, 0x17, 0xca, 0x89, 0x0d, 0xe6, 0x86, 0x64, 0x2b, 0xf9, 0x9b, 0xca]

def c30Fields : List BLT := [.bytes c30F0, .bytes c30F1, .bytes c30F2, .bytes c30F3, .bytes c30F4, .bytes c30F5, .bytes c30F6, .bytes c30F7, .bytes c30F8]

def c30Payload : Bytes := [0x82] ++ c30F0 ++ [0x84] ++ c30F1 ++ [0x83] ++ c30F2 ++ [0x94] ++ c30F3 ++ [0x80] ++ c30F4 ++ [0xb9, 0x01, 0x64] ++ c30F5 ++ [] ++ c30F6 ++ [0xa0] ++ c30F7 ++ [0xa0] ++ c30F8

def c30Signed : Bytes := [0xf9, 0x01, 0xcc] ++ c30Payload

def c30Tx : Tx := { nonce := 64486, gas := 181000, value := 0, data := c30F5, v := 38, r := c30F7, s := c30F8, type := .zero 3503000000 (some 0x7600977eb9effa627d6bd0da2e5be35e11566341) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c30_literal : c30Signed = [0xf9, 0x01, 0xcc, 0x82, 0xfb, 0xe6, 0x84, 0xd0, 0xcb, 0x89, 0xc0, 0x83, 0x02, 0xc3, 0x08, 0x94, 0x76, 0x00, 0x97, 0x7e, 0xb9, 0xef, 0xfa, 0x62, 0x7d, 0x6b, 0xd0, 0xda, 0x2e, 0x5b, 0xe3, 0x5e, 0x11, 0x56, 0x63, 0x41, 0x80, 0xb9, 0x01, 0x64, 0x72, 0x2d, 0xed, 0x24, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x64, 0xac, 0x8c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0xd5, 0xba, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x01, 0x65, 0x01, 0x42, 0x05, 0x23, 0xb8, 0x09, 0x71, 0xfb, 0xd7, 0x86, 0xb0, 0x3e, 0x19, 0x47, 0x29, 0x7e, 0xa1, 0x84, 0xa3, 0xbf, 0x0b, 0x93, 0xa2, 0x76, 0x1c, 0xde, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x64, 0xba, 0x9c, 0x00, 0x00, 0x01, 0x01, 0xb9, 0x66, 0x85, 0x49, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x33, 0xc8, 0x00, 0x01, 0x00, 0x00, 0x00, 0x7c, 0x08, 0x2d, 0x31, 0x8b, 0x42, 0x3b, 0x94, 0xec, 0x5a, 0x4f, 0xf9, 0xc9, 0xe6, 0xab, 0xcf, 0xa9, 0x1e, 0x89, 0xa5, 0x1c, 0x50, 0xcf, 0xea, 0x75, 0x60, 0xf6, 0x5f, 0x53, 0x1c, 0x85, 0x61, 0xfc, 0x21, 0x91, 0x77, 0x66, 0xfe, 0x18, 0x90, 0xea, 0xe0, 0x70, 0x1a, 0xef, 0x6a, 0x51, 0xfe, 0xd0, 0x9a, 0x67, 0x5e, 0x49, 0x83, 0x1c, 0x35, 0x72, 0x64, 0xb3, 0x73, 0x54, 0xe6, 0x16, 0xe2, 0x7d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x65, 0x01, 0x42, 0x05, 0x71, 0x94, 0x86, 0x7c, 0xfd, 0x17, 0xe5, 0x4f, 0xaa, 0xcc, 0x9c, 0x89, 0xc1, 0x80, 0xc7, 0xa8, 0x02, 0x79, 0x13, 0x68, 0xc0, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x64, 0xba, 0x9c, 0x00, 0x00, 0x01, 0x01, 0xb9, 0x66, 0x85, 0x49, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x33, 0xc8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7c, 0x1e, 0xd8, 0x5d, 0x80, 0x2e, 0xe3, 0x59, 0xbc, 0xca, 0x9d, 0xa9, 0x01, 0xc8, 0x0a, 0xdd, 0x3a, 0x5f, 0xa4, 0xe5, 0x99, 0xf6, 0x00, 0x87, 0x94, 0x82, 0xd4, 0x62, 0xfd, 0x04, 0x9f, 0xca, 0x06, 0x55, 0x8f, 0x27, 0xab, 0x05, 0x4d, 0xb2, 0xe6, 0x2a, 0x47, 0xc0, 0x39, 0x00, 0x71, 0xe3, 0x7f, 0x9f, 0x7f, 0xf0, 0xb0, 0xdd, 0xc0, 0x7a, 0x8f, 0x9d, 0x35, 0x02, 0xb4, 0xd8, 0x57, 0x66, 0xa5, 0x26, 0xa0, 0xca, 0xfb, 0xc7, 0xb3, 0x4e, 0xd3, 0x24, 0xb1, 0x70, 0x2f, 0x2a, 0xa8, 0x77, 0x71, 0xa9, 0x78, 0xbc, 0xc2, 0x14, 0x5c, 0x23, 0xf1, 0x26, 0x72, 0x03, 0xbe, 0xed, 0x9e, 0xf8, 0x6f, 0xce, 0x36, 0xa0, 0x22, 0x33, 0xd0, 0xb6, 0xa0, 0xb1, 0x7e, 0x2c, 0xf9, 0x4b, 0x6b, 0xa6, 0xce, 0x30, 0xf8, 0xc8, 0x9e, 0x13, 0x19, 0x8c, 0x29, 0x17, 0xca, 0x89, 0x0d, 0xe6, 0x86, 0x64, 0x2b, 0xf9, 0x9b, 0xca] := by
  decide +kernel

theorem c30_payload_length : c30Payload.length = 460 := by
  decide +kernel

theorem c30_signed_length : c30Signed.length = 463 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c30_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c30Payload = some c30Fields := by
  unfold c30Payload c30Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c30F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c30F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c30F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c30F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_two _ 1 100 c30F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c30F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c30F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c30_parse : c30Signed.toBLT? = some (.list c30Fields) := by
  have outer : Bytes.toBLTDiff? 463 c30Signed = some (.list c30Fields, []) := by
    simpa only [c30Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_two 462 1 204 c30Payload [] c30Fields
        (by rw [c30_payload_length]; decide +kernel) (c30_payload_parse 453)
  unfold Bytes.toBLT?
  rw [c30_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c30_decode :
    (c30Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c30Tx := by
  rw [c30_parse]
  decide +kernel

theorem c30_blt : c30Tx.toBLT = .list c30Fields := by
  norm_num only [c30Tx, c30Fields, c30F0, c30F1, c30F2, c30F3, c30F4, c30F6, c30F7, c30F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c30_encode0 : (BLT.bytes c30F0).toBytes = [0x82] ++ c30F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c30F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c30_encode1 : (BLT.bytes c30F1).toBytes = [0x84] ++ c30F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c30F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c30_encode2 : (BLT.bytes c30F2).toBytes = [0x83] ++ c30F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c30F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c30_encode3 : (BLT.bytes c30F3).toBytes = [0x94] ++ c30F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c30F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c30_encode4 : (BLT.bytes c30F4).toBytes = [0x80] ++ c30F4 := by
  unfold c30F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c30_encode5 : (BLT.bytes c30F5).toBytes = [0xb9, 0x01, 0x64] ++ c30F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c30F5.length = 356 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c30_encode6 : (BLT.bytes c30F6).toBytes = [] ++ c30F6 := by
  unfold c30F6
  rw [BLT.toBytes]
  decide +kernel

theorem c30_encode7 : (BLT.bytes c30F7).toBytes = [0xa0] ++ c30F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c30F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c30_encode8 : (BLT.bytes c30F8).toBytes = [0xa0] ++ c30F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c30F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c30_canonical : c30Tx.toBLT.toBytes = c30Signed := by
  have encoded : BLTs.toBytesJoin c30Fields = c30Payload := by
    simp only [c30Fields, BLTs.toBytesJoin,
      c30_encode0, c30_encode1, c30_encode2, c30_encode3, c30_encode4, c30_encode5, c30_encode6, c30_encode7, c30_encode8, c30Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c30_blt, BLT.toBytes, BLTs.toBytes, encoded, c30_payload_length]
  norm_num only [c30Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c31F0 : Bytes := [0x01, 0xae, 0x70]

def c31F1 : Bytes := [0xc4, 0xb2, 0x01, 0x00]

def c31F2 : Bytes := [0x03, 0x71, 0x2e]

def c31F3 : Bytes := [0x14, 0xfb, 0xca, 0x95, 0xbe, 0x7e, 0x99, 0xc1, 0x5c, 0xc2, 0x99, 0x6c, 0x6c, 0x9d, 0x84, 0x1e, 0x54, 0xb7, 0x94, 0x25]

def c31F4 : Bytes := []

def c31F5 : Bytes := [0xb4, 0xf9, 0xb6, 0xc8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x64, 0xe3]

def c31F6 : Bytes := [0x25]

def c31F7 : Bytes := [0x7b, 0x3d, 0xac, 0x7e, 0x33, 0xf6, 0x67, 0x19, 0x54, 0x11, 0xda, 0x6e, 0xac, 0xbe, 0x85, 0xf9, 0x28, 0xb0, 0xea, 0xa2, 0xa2, 0x14, 0xec, 0xd7, 0x48, 0x08, 0x6c, 0xbc, 0x30, 0xf8, 0x56, 0x35]

def c31F8 : Bytes := [0x5b, 0xb6, 0x61, 0xd8, 0x92, 0x35, 0x50, 0x07, 0x5a, 0x31, 0xf7, 0xd0, 0x76, 0x12, 0x29, 0xcb, 0xed, 0x62, 0xcb, 0xc5, 0x29, 0x8e, 0x36, 0x8d, 0xdb, 0x93, 0x2e, 0xca, 0x76, 0xc6, 0x05, 0x51]

def c31Fields : List BLT := [.bytes c31F0, .bytes c31F1, .bytes c31F2, .bytes c31F3, .bytes c31F4, .bytes c31F5, .bytes c31F6, .bytes c31F7, .bytes c31F8]

def c31Payload : Bytes := [0x83] ++ c31F0 ++ [0x84] ++ c31F1 ++ [0x83] ++ c31F2 ++ [0x94] ++ c31F3 ++ [0x80] ++ c31F4 ++ [0xa4] ++ c31F5 ++ [] ++ c31F6 ++ [0xa0] ++ c31F7 ++ [0xa0] ++ c31F8

def c31Signed : Bytes := [0xf8, 0x8b] ++ c31Payload

def c31Tx : Tx := { nonce := 110192, gas := 225582, value := 0, data := c31F5, v := 37, r := c31F7, s := c31F8, type := .zero 3300000000 (some 0x14fbca95be7e99c15cc2996c6c9d841e54b79425) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c31_literal : c31Signed = [0xf8, 0x8b, 0x83, 0x01, 0xae, 0x70, 0x84, 0xc4, 0xb2, 0x01, 0x00, 0x83, 0x03, 0x71, 0x2e, 0x94, 0x14, 0xfb, 0xca, 0x95, 0xbe, 0x7e, 0x99, 0xc1, 0x5c, 0xc2, 0x99, 0x6c, 0x6c, 0x9d, 0x84, 0x1e, 0x54, 0xb7, 0x94, 0x25, 0x80, 0xa4, 0xb4, 0xf9, 0xb6, 0xc8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x64, 0xe3, 0x25, 0xa0, 0x7b, 0x3d, 0xac, 0x7e, 0x33, 0xf6, 0x67, 0x19, 0x54, 0x11, 0xda, 0x6e, 0xac, 0xbe, 0x85, 0xf9, 0x28, 0xb0, 0xea, 0xa2, 0xa2, 0x14, 0xec, 0xd7, 0x48, 0x08, 0x6c, 0xbc, 0x30, 0xf8, 0x56, 0x35, 0xa0, 0x5b, 0xb6, 0x61, 0xd8, 0x92, 0x35, 0x50, 0x07, 0x5a, 0x31, 0xf7, 0xd0, 0x76, 0x12, 0x29, 0xcb, 0xed, 0x62, 0xcb, 0xc5, 0x29, 0x8e, 0x36, 0x8d, 0xdb, 0x93, 0x2e, 0xca, 0x76, 0xc6, 0x05, 0x51] := by
  decide +kernel

theorem c31_payload_length : c31Payload.length = 139 := by
  decide +kernel

theorem c31_signed_length : c31Signed.length = 141 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c31_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c31Payload = some c31Fields := by
  unfold c31Payload c31Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c31F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c31F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c31F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c31F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 36 c31F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c31F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c31F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c31_parse : c31Signed.toBLT? = some (.list c31Fields) := by
  have outer : Bytes.toBLTDiff? 141 c31Signed = some (.list c31Fields, []) := by
    simpa only [c31Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 140 139 c31Payload [] c31Fields
        (by rw [c31_payload_length]; decide +kernel) (c31_payload_parse 131)
  unfold Bytes.toBLT?
  rw [c31_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c31_decode :
    (c31Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c31Tx := by
  rw [c31_parse]
  decide +kernel

theorem c31_blt : c31Tx.toBLT = .list c31Fields := by
  norm_num only [c31Tx, c31Fields, c31F0, c31F1, c31F2, c31F3, c31F4, c31F6, c31F7, c31F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c31_encode0 : (BLT.bytes c31F0).toBytes = [0x83] ++ c31F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c31F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c31_encode1 : (BLT.bytes c31F1).toBytes = [0x84] ++ c31F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c31F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c31_encode2 : (BLT.bytes c31F2).toBytes = [0x83] ++ c31F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c31F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c31_encode3 : (BLT.bytes c31F3).toBytes = [0x94] ++ c31F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c31F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c31_encode4 : (BLT.bytes c31F4).toBytes = [0x80] ++ c31F4 := by
  unfold c31F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c31_encode5 : (BLT.bytes c31F5).toBytes = [0xa4] ++ c31F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c31F5.length = 36 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c31_encode6 : (BLT.bytes c31F6).toBytes = [] ++ c31F6 := by
  unfold c31F6
  rw [BLT.toBytes]
  decide +kernel

theorem c31_encode7 : (BLT.bytes c31F7).toBytes = [0xa0] ++ c31F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c31F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c31_encode8 : (BLT.bytes c31F8).toBytes = [0xa0] ++ c31F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c31F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c31_canonical : c31Tx.toBLT.toBytes = c31Signed := by
  have encoded : BLTs.toBytesJoin c31Fields = c31Payload := by
    simp only [c31Fields, BLTs.toBytesJoin,
      c31_encode0, c31_encode1, c31_encode2, c31_encode3, c31_encode4, c31_encode5, c31_encode6, c31_encode7, c31_encode8, c31Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c31_blt, BLT.toBytes, BLTs.toBytes, encoded, c31_payload_length]
  norm_num only [c31Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
