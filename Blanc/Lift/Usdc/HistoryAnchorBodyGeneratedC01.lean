import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def c08F0 : Bytes := [0x51]

def c08F1 : Bytes := [0x06, 0xfc, 0x23, 0xac, 0x00]

def c08F2 : Bytes := [0x03, 0x34, 0x50]

def c08F3 : Bytes := [0x74, 0xee, 0xb7, 0xa4, 0x53, 0x83, 0x16, 0x2f, 0x06, 0x59, 0x1f, 0xe5, 0x8e, 0xc5, 0xd6, 0x82, 0x5a, 0x81, 0x83, 0x7e]

def c08F4 : Bytes := [0x27, 0xd4, 0x49, 0xcb, 0x49, 0x5f, 0x00, 0x00]

def c08F5 : Bytes := []

def c08F6 : Bytes := [0x25]

def c08F7 : Bytes := [0x7e, 0x3b, 0xc3, 0xfa, 0xb1, 0x41, 0xb5, 0xd1, 0x1d, 0xda, 0x96, 0x03, 0x1d, 0xd5, 0x36, 0x90, 0xa7, 0x08, 0x96, 0xf4, 0xfc, 0xce, 0x20, 0x86, 0x0e, 0x12, 0x0a, 0x5d, 0x06, 0xcc, 0x20, 0xbc]

def c08F8 : Bytes := [0x0b, 0xd7, 0xb9, 0x55, 0xb6, 0xeb, 0xeb, 0xd4, 0x72, 0xf9, 0x3a, 0x42, 0x15, 0x2a, 0x14, 0x32, 0x15, 0xf0, 0x04, 0x90, 0x83, 0x48, 0x27, 0xc6, 0x86, 0xf3, 0x95, 0xf9, 0x39, 0xba, 0x3d, 0x2f]

def c08Fields : List BLT := [.bytes c08F0, .bytes c08F1, .bytes c08F2, .bytes c08F3, .bytes c08F4, .bytes c08F5, .bytes c08F6, .bytes c08F7, .bytes c08F8]

def c08Payload : Bytes := [] ++ c08F0 ++ [0x85] ++ c08F1 ++ [0x83] ++ c08F2 ++ [0x94] ++ c08F3 ++ [0x88] ++ c08F4 ++ [0x80] ++ c08F5 ++ [] ++ c08F6 ++ [0xa0] ++ c08F7 ++ [0xa0] ++ c08F8

def c08Signed : Bytes := [0xf8, 0x6d] ++ c08Payload

def c08Tx : Tx := { nonce := 81, gas := 210000, value := 2870000000000000000, data := c08F5, v := 37, r := c08F7, s := c08F8, type := .zero 30000000000 (some 0x74eeb7a45383162f06591fe58ec5d6825a81837e) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c08_literal : c08Signed = [0xf8, 0x6d, 0x51, 0x85, 0x06, 0xfc, 0x23, 0xac, 0x00, 0x83, 0x03, 0x34, 0x50, 0x94, 0x74, 0xee, 0xb7, 0xa4, 0x53, 0x83, 0x16, 0x2f, 0x06, 0x59, 0x1f, 0xe5, 0x8e, 0xc5, 0xd6, 0x82, 0x5a, 0x81, 0x83, 0x7e, 0x88, 0x27, 0xd4, 0x49, 0xcb, 0x49, 0x5f, 0x00, 0x00, 0x80, 0x25, 0xa0, 0x7e, 0x3b, 0xc3, 0xfa, 0xb1, 0x41, 0xb5, 0xd1, 0x1d, 0xda, 0x96, 0x03, 0x1d, 0xd5, 0x36, 0x90, 0xa7, 0x08, 0x96, 0xf4, 0xfc, 0xce, 0x20, 0x86, 0x0e, 0x12, 0x0a, 0x5d, 0x06, 0xcc, 0x20, 0xbc, 0xa0, 0x0b, 0xd7, 0xb9, 0x55, 0xb6, 0xeb, 0xeb, 0xd4, 0x72, 0xf9, 0x3a, 0x42, 0x15, 0x2a, 0x14, 0x32, 0x15, 0xf0, 0x04, 0x90, 0x83, 0x48, 0x27, 0xc6, 0x86, 0xf3, 0x95, 0xf9, 0x39, 0xba, 0x3d, 0x2f] := by
  decide +kernel

theorem c08_payload_length : c08Payload.length = 109 := by
  decide +kernel

theorem c08_signed_length : c08Signed.length = 111 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c08_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c08Payload = some c08Fields := by
  unfold c08Payload c08Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c08F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c08F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c08F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c08F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c08F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c08F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c08_parse : c08Signed.toBLT? = some (.list c08Fields) := by
  have outer : Bytes.toBLTDiff? 111 c08Signed = some (.list c08Fields, []) := by
    simpa only [c08Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 110 109 c08Payload [] c08Fields
        (by rw [c08_payload_length]; decide +kernel) (c08_payload_parse 101)
  unfold Bytes.toBLT?
  rw [c08_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c08_decode :
    (c08Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c08Tx := by
  rw [c08_parse]
  decide +kernel

theorem c08_blt : c08Tx.toBLT = .list c08Fields := by
  norm_num only [c08Tx, c08Fields, c08F0, c08F1, c08F2, c08F3, c08F4, c08F6, c08F7, c08F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c08_encode0 : (BLT.bytes c08F0).toBytes = [] ++ c08F0 := by
  unfold c08F0
  rw [BLT.toBytes]
  decide +kernel

theorem c08_encode1 : (BLT.bytes c08F1).toBytes = [0x85] ++ c08F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c08F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c08_encode2 : (BLT.bytes c08F2).toBytes = [0x83] ++ c08F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c08F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c08_encode3 : (BLT.bytes c08F3).toBytes = [0x94] ++ c08F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c08F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c08_encode4 : (BLT.bytes c08F4).toBytes = [0x88] ++ c08F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c08F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c08_encode5 : (BLT.bytes c08F5).toBytes = [0x80] ++ c08F5 := by
  unfold c08F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c08_encode6 : (BLT.bytes c08F6).toBytes = [] ++ c08F6 := by
  unfold c08F6
  rw [BLT.toBytes]
  decide +kernel

theorem c08_encode7 : (BLT.bytes c08F7).toBytes = [0xa0] ++ c08F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c08F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c08_encode8 : (BLT.bytes c08F8).toBytes = [0xa0] ++ c08F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c08F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c08_canonical : c08Tx.toBLT.toBytes = c08Signed := by
  have encoded : BLTs.toBytesJoin c08Fields = c08Payload := by
    simp only [c08Fields, BLTs.toBytesJoin,
      c08_encode0, c08_encode1, c08_encode2, c08_encode3, c08_encode4, c08_encode5, c08_encode6, c08_encode7, c08_encode8, c08Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c08_blt, BLT.toBytes, BLTs.toBytes, encoded, c08_payload_length]
  norm_num only [c08Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c09F0 : Bytes := [0x11, 0xf6]

def c09F1 : Bytes := [0x04, 0xa8, 0x17, 0xc8, 0x00]

def c09F2 : Bytes := [0x01, 0x26, 0x7e]

def c09F3 : Bytes := [0xdc, 0x17, 0xe8, 0xa8, 0x4f, 0xee, 0x8b, 0x52, 0xe4, 0xde, 0x7a, 0x85, 0x16, 0x0f, 0x8c, 0xdb, 0xb3, 0xbb, 0x24, 0x94]

def c09F4 : Bytes := []

def c09F5 : Bytes := [0xc8, 0x51, 0x06, 0xa4, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x18, 0x1f, 0xd6, 0x97, 0x40, 0x00, 0x13, 0xad, 0x5c, 0x87, 0x04, 0x66, 0xd5, 0x93, 0xa0, 0x6c, 0xf1, 0xa1, 0x48, 0x2f, 0xb4, 0x6a, 0x1a, 0x8d, 0xa2, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x19, 0x37, 0x3c, 0x2a, 0x20, 0x00, 0xc4, 0x33, 0xcf, 0x10, 0xab, 0xcd, 0xcc, 0xfc, 0xbc, 0xfe, 0x34, 0x31, 0x52, 0xa8, 0x92, 0xe9, 0x8f, 0x08, 0xb7, 0xe2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb5, 0xe6, 0x20, 0xf4, 0x80, 0x00, 0xc2, 0x08, 0x52, 0xe1, 0x91, 0xbd, 0xba, 0xba, 0xd0, 0xab, 0x0a, 0xa4, 0x7a, 0x27, 0x12, 0xb8, 0x79, 0x6c, 0x9f, 0xe0]

def c09F6 : Bytes := [0x26]

def c09F7 : Bytes := [0x67, 0x8a, 0x84, 0x24, 0xa1, 0x08, 0xb6, 0x87, 0xdf, 0x67, 0xb3, 0xe6, 0x05, 0x5a, 0x05, 0xb2, 0xb5, 0x6e, 0x65, 0x7a, 0xc6, 0x25, 0xfb, 0x03, 0xe6, 0x3d, 0x77, 0x85, 0x82, 0xc4, 0x35, 0x9d]

def c09F8 : Bytes := [0x7b, 0xab, 0xe4, 0x9d, 0x73, 0xf1, 0x06, 0x26, 0x67, 0xbe, 0xdc, 0xe4, 0xa4, 0x1f, 0x90, 0xe1, 0x13, 0xaf, 0x17, 0x0e, 0x5b, 0xe2, 0x16, 0x7e, 0x28, 0x12, 0x64, 0x19, 0x9f, 0x79, 0x38, 0xfb]

def c09Fields : List BLT := [.bytes c09F0, .bytes c09F1, .bytes c09F2, .bytes c09F3, .bytes c09F4, .bytes c09F5, .bytes c09F6, .bytes c09F7, .bytes c09F8]

def c09Payload : Bytes := [0x82] ++ c09F0 ++ [0x85] ++ c09F1 ++ [0x83] ++ c09F2 ++ [0x94] ++ c09F3 ++ [0x80] ++ c09F4 ++ [0xb8, 0xa4] ++ c09F5 ++ [] ++ c09F6 ++ [0xa0] ++ c09F7 ++ [0xa0] ++ c09F8

def c09Signed : Bytes := [0xf9, 0x01, 0x0c] ++ c09Payload

def c09Tx : Tx := { nonce := 4598, gas := 75390, value := 0, data := c09F5, v := 38, r := c09F7, s := c09F8, type := .zero 20000000000 (some 0xdc17e8a84fee8b52e4de7a85160f8cdbb3bb2494) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c09_literal : c09Signed = [0xf9, 0x01, 0x0c, 0x82, 0x11, 0xf6, 0x85, 0x04, 0xa8, 0x17, 0xc8, 0x00, 0x83, 0x01, 0x26, 0x7e, 0x94, 0xdc, 0x17, 0xe8, 0xa8, 0x4f, 0xee, 0x8b, 0x52, 0xe4, 0xde, 0x7a, 0x85, 0x16, 0x0f, 0x8c, 0xdb, 0xb3, 0xbb, 0x24, 0x94, 0x80, 0xb8, 0xa4, 0xc8, 0x51, 0x06, 0xa4, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x18, 0x1f, 0xd6, 0x97, 0x40, 0x00, 0x13, 0xad, 0x5c, 0x87, 0x04, 0x66, 0xd5, 0x93, 0xa0, 0x6c, 0xf1, 0xa1, 0x48, 0x2f, 0xb4, 0x6a, 0x1a, 0x8d, 0xa2, 0x54, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x19, 0x37, 0x3c, 0x2a, 0x20, 0x00, 0xc4, 0x33, 0xcf, 0x10, 0xab, 0xcd, 0xcc, 0xfc, 0xbc, 0xfe, 0x34, 0x31, 0x52, 0xa8, 0x92, 0xe9, 0x8f, 0x08, 0xb7, 0xe2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb5, 0xe6, 0x20, 0xf4, 0x80, 0x00, 0xc2, 0x08, 0x52, 0xe1, 0x91, 0xbd, 0xba, 0xba, 0xd0, 0xab, 0x0a, 0xa4, 0x7a, 0x27, 0x12, 0xb8, 0x79, 0x6c, 0x9f, 0xe0, 0x26, 0xa0, 0x67, 0x8a, 0x84, 0x24, 0xa1, 0x08, 0xb6, 0x87, 0xdf, 0x67, 0xb3, 0xe6, 0x05, 0x5a, 0x05, 0xb2, 0xb5, 0x6e, 0x65, 0x7a, 0xc6, 0x25, 0xfb, 0x03, 0xe6, 0x3d, 0x77, 0x85, 0x82, 0xc4, 0x35, 0x9d, 0xa0, 0x7b, 0xab, 0xe4, 0x9d, 0x73, 0xf1, 0x06, 0x26, 0x67, 0xbe, 0xdc, 0xe4, 0xa4, 0x1f, 0x90, 0xe1, 0x13, 0xaf, 0x17, 0x0e, 0x5b, 0xe2, 0x16, 0x7e, 0x28, 0x12, 0x64, 0x19, 0x9f, 0x79, 0x38, 0xfb] := by
  decide +kernel

theorem c09_payload_length : c09Payload.length = 268 := by
  decide +kernel

theorem c09_signed_length : c09Signed.length = 271 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c09_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c09Payload = some c09Fields := by
  unfold c09Payload c09Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c09F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c09F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c09F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c09F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 164 c09F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c09F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c09F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c09_parse : c09Signed.toBLT? = some (.list c09Fields) := by
  have outer : Bytes.toBLTDiff? 271 c09Signed = some (.list c09Fields, []) := by
    simpa only [c09Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_two 270 1 12 c09Payload [] c09Fields
        (by rw [c09_payload_length]; decide +kernel) (c09_payload_parse 261)
  unfold Bytes.toBLT?
  rw [c09_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c09_decode :
    (c09Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c09Tx := by
  rw [c09_parse]
  decide +kernel

theorem c09_blt : c09Tx.toBLT = .list c09Fields := by
  norm_num only [c09Tx, c09Fields, c09F0, c09F1, c09F2, c09F3, c09F4, c09F6, c09F7, c09F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c09_encode0 : (BLT.bytes c09F0).toBytes = [0x82] ++ c09F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c09F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c09_encode1 : (BLT.bytes c09F1).toBytes = [0x85] ++ c09F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c09F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c09_encode2 : (BLT.bytes c09F2).toBytes = [0x83] ++ c09F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c09F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c09_encode3 : (BLT.bytes c09F3).toBytes = [0x94] ++ c09F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c09F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c09_encode4 : (BLT.bytes c09F4).toBytes = [0x80] ++ c09F4 := by
  unfold c09F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c09_encode5 : (BLT.bytes c09F5).toBytes = [0xb8, 0xa4] ++ c09F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c09F5.length = 164 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c09_encode6 : (BLT.bytes c09F6).toBytes = [] ++ c09F6 := by
  unfold c09F6
  rw [BLT.toBytes]
  decide +kernel

theorem c09_encode7 : (BLT.bytes c09F7).toBytes = [0xa0] ++ c09F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c09F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c09_encode8 : (BLT.bytes c09F8).toBytes = [0xa0] ++ c09F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c09F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c09_canonical : c09Tx.toBLT.toBytes = c09Signed := by
  have encoded : BLTs.toBytesJoin c09Fields = c09Payload := by
    simp only [c09Fields, BLTs.toBytesJoin,
      c09_encode0, c09_encode1, c09_encode2, c09_encode3, c09_encode4, c09_encode5, c09_encode6, c09_encode7, c09_encode8, c09Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c09_blt, BLT.toBytes, BLTs.toBytes, encoded, c09_payload_length]
  norm_num only [c09Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c10F0 : Bytes := [0x03, 0xd0, 0x1c]

def c10F1 : Bytes := [0x03, 0x7e, 0x11, 0xd6, 0x00]

def c10F2 : Bytes := [0x01, 0x5f, 0x90]

def c10F3 : Bytes := [0xaf, 0x31, 0x14, 0x97, 0x4a, 0x50, 0xd9, 0x08, 0xaf, 0x93, 0xea, 0x7f, 0xd4, 0x70, 0xc5, 0x7d, 0x30, 0x74, 0x39, 0x6f]

def c10F4 : Bytes := []

def c10F5 : Bytes := [0xff, 0x03, 0xad, 0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x98, 0x62, 0xd0, 0x74, 0xe3, 0x30, 0x03, 0x72, 0x6f, 0xa0, 0x5c, 0x74, 0xf0, 0x14, 0x29, 0x95, 0xf3, 0x3a, 0x32, 0x50, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x23, 0x86, 0xf2, 0x6f, 0xc1, 0x00, 0x00]

def c10F6 : Bytes := [0x26]

def c10F7 : Bytes := [0xe0, 0x47, 0x65, 0xb2, 0x19, 0x0f, 0xa3, 0xd7, 0xbf, 0x7e, 0xbe, 0xeb, 0xa1, 0xf3, 0x9d, 0xc6, 0xef, 0xe6, 0xfb, 0x28, 0xed, 0x5f, 0x60, 0xdf, 0x4b, 0xfd, 0x93, 0x0c, 0xcd, 0xab, 0x5b, 0x7f]

def c10F8 : Bytes := [0x77, 0x3f, 0x91, 0x28, 0xd9, 0xc2, 0x75, 0x08, 0xf2, 0x87, 0x68, 0x6c, 0xaf, 0xc2, 0xec, 0x26, 0xb1, 0x55, 0x2a, 0xd8, 0xd9, 0xaa, 0xdb, 0x37, 0x7d, 0x5e, 0x1d, 0x16, 0xae, 0x27, 0x42, 0xf5]

def c10Fields : List BLT := [.bytes c10F0, .bytes c10F1, .bytes c10F2, .bytes c10F3, .bytes c10F4, .bytes c10F5, .bytes c10F6, .bytes c10F7, .bytes c10F8]

def c10Payload : Bytes := [0x83] ++ c10F0 ++ [0x85] ++ c10F1 ++ [0x83] ++ c10F2 ++ [0x94] ++ c10F3 ++ [0x80] ++ c10F4 ++ [0xb8, 0x44] ++ c10F5 ++ [] ++ c10F6 ++ [0xa0] ++ c10F7 ++ [0xa0] ++ c10F8

def c10Signed : Bytes := [0xf8, 0xad] ++ c10Payload

def c10Tx : Tx := { nonce := 249884, gas := 90000, value := 0, data := c10F5, v := 38, r := c10F7, s := c10F8, type := .zero 15000000000 (some 0xaf3114974a50d908af93ea7fd470c57d3074396f) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c10_literal : c10Signed = [0xf8, 0xad, 0x83, 0x03, 0xd0, 0x1c, 0x85, 0x03, 0x7e, 0x11, 0xd6, 0x00, 0x83, 0x01, 0x5f, 0x90, 0x94, 0xaf, 0x31, 0x14, 0x97, 0x4a, 0x50, 0xd9, 0x08, 0xaf, 0x93, 0xea, 0x7f, 0xd4, 0x70, 0xc5, 0x7d, 0x30, 0x74, 0x39, 0x6f, 0x80, 0xb8, 0x44, 0xff, 0x03, 0xad, 0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x98, 0x62, 0xd0, 0x74, 0xe3, 0x30, 0x03, 0x72, 0x6f, 0xa0, 0x5c, 0x74, 0xf0, 0x14, 0x29, 0x95, 0xf3, 0x3a, 0x32, 0x50, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x23, 0x86, 0xf2, 0x6f, 0xc1, 0x00, 0x00, 0x26, 0xa0, 0xe0, 0x47, 0x65, 0xb2, 0x19, 0x0f, 0xa3, 0xd7, 0xbf, 0x7e, 0xbe, 0xeb, 0xa1, 0xf3, 0x9d, 0xc6, 0xef, 0xe6, 0xfb, 0x28, 0xed, 0x5f, 0x60, 0xdf, 0x4b, 0xfd, 0x93, 0x0c, 0xcd, 0xab, 0x5b, 0x7f, 0xa0, 0x77, 0x3f, 0x91, 0x28, 0xd9, 0xc2, 0x75, 0x08, 0xf2, 0x87, 0x68, 0x6c, 0xaf, 0xc2, 0xec, 0x26, 0xb1, 0x55, 0x2a, 0xd8, 0xd9, 0xaa, 0xdb, 0x37, 0x7d, 0x5e, 0x1d, 0x16, 0xae, 0x27, 0x42, 0xf5] := by
  decide +kernel

theorem c10_payload_length : c10Payload.length = 173 := by
  decide +kernel

theorem c10_signed_length : c10Signed.length = 175 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c10_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c10Payload = some c10Fields := by
  unfold c10Payload c10Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c10F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c10F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c10F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c10F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c10F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c10F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c10F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c10_parse : c10Signed.toBLT? = some (.list c10Fields) := by
  have outer : Bytes.toBLTDiff? 175 c10Signed = some (.list c10Fields, []) := by
    simpa only [c10Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 174 173 c10Payload [] c10Fields
        (by rw [c10_payload_length]; decide +kernel) (c10_payload_parse 165)
  unfold Bytes.toBLT?
  rw [c10_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c10_decode :
    (c10Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c10Tx := by
  rw [c10_parse]
  decide +kernel

theorem c10_blt : c10Tx.toBLT = .list c10Fields := by
  norm_num only [c10Tx, c10Fields, c10F0, c10F1, c10F2, c10F3, c10F4, c10F6, c10F7, c10F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c10_encode0 : (BLT.bytes c10F0).toBytes = [0x83] ++ c10F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c10F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c10_encode1 : (BLT.bytes c10F1).toBytes = [0x85] ++ c10F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c10F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c10_encode2 : (BLT.bytes c10F2).toBytes = [0x83] ++ c10F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c10F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c10_encode3 : (BLT.bytes c10F3).toBytes = [0x94] ++ c10F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c10F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c10_encode4 : (BLT.bytes c10F4).toBytes = [0x80] ++ c10F4 := by
  unfold c10F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c10_encode5 : (BLT.bytes c10F5).toBytes = [0xb8, 0x44] ++ c10F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c10F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c10_encode6 : (BLT.bytes c10F6).toBytes = [] ++ c10F6 := by
  unfold c10F6
  rw [BLT.toBytes]
  decide +kernel

theorem c10_encode7 : (BLT.bytes c10F7).toBytes = [0xa0] ++ c10F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c10F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c10_encode8 : (BLT.bytes c10F8).toBytes = [0xa0] ++ c10F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c10F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c10_canonical : c10Tx.toBLT.toBytes = c10Signed := by
  have encoded : BLTs.toBytesJoin c10Fields = c10Payload := by
    simp only [c10Fields, BLTs.toBytesJoin,
      c10_encode0, c10_encode1, c10_encode2, c10_encode3, c10_encode4, c10_encode5, c10_encode6, c10_encode7, c10_encode8, c10Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c10_blt, BLT.toBytes, BLTs.toBytes, encoded, c10_payload_length]
  norm_num only [c10Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c11F0 : Bytes := [0x10, 0x8a, 0xde]

def c11F1 : Bytes := [0x03, 0x7e, 0x11, 0xd6, 0x00]

def c11F2 : Bytes := [0x01, 0x5f, 0x90]

def c11F3 : Bytes := [0x0b, 0xdc, 0xfc, 0x70, 0xb4, 0x4c, 0x64, 0x97, 0x08, 0x01, 0xd8, 0x30, 0xb2, 0x21, 0xe4, 0x5c, 0xed, 0xef, 0x64, 0x38]

def c11F4 : Bytes := [0x35, 0xda, 0xdc, 0xfb, 0x1c, 0x22, 0x10, 0x00]

def c11F5 : Bytes := []

def c11F6 : Bytes := [0x25]

def c11F7 : Bytes := [0x8f, 0x3a, 0x77, 0xa1, 0x6d, 0xcc, 0x0b, 0xc9, 0xfc, 0x9f, 0xd9, 0x23, 0x8d, 0xf9, 0xff, 0x1b, 0xfe, 0xa6, 0xd0, 0xf6, 0x6a, 0xdc, 0x37, 0xef, 0x79, 0xd7, 0x7e, 0x1d, 0xd9, 0x14, 0x41, 0x76]

def c11F8 : Bytes := [0x05, 0xa8, 0xd8, 0x01, 0x3a, 0xc2, 0xb4, 0x5b, 0x2f, 0x89, 0xc0, 0xde, 0x4e, 0x9e, 0xc3, 0x35, 0x9c, 0xa5, 0x4d, 0xc0, 0x98, 0x27, 0x0c, 0x42, 0x62, 0xc2, 0xf7, 0x75, 0x9b, 0x01, 0x73, 0x73]

def c11Fields : List BLT := [.bytes c11F0, .bytes c11F1, .bytes c11F2, .bytes c11F3, .bytes c11F4, .bytes c11F5, .bytes c11F6, .bytes c11F7, .bytes c11F8]

def c11Payload : Bytes := [0x83] ++ c11F0 ++ [0x85] ++ c11F1 ++ [0x83] ++ c11F2 ++ [0x94] ++ c11F3 ++ [0x88] ++ c11F4 ++ [0x80] ++ c11F5 ++ [] ++ c11F6 ++ [0xa0] ++ c11F7 ++ [0xa0] ++ c11F8

def c11Signed : Bytes := [0xf8, 0x70] ++ c11Payload

def c11Tx : Tx := { nonce := 1084126, gas := 90000, value := 3880657000000000000, data := c11F5, v := 37, r := c11F7, s := c11F8, type := .zero 15000000000 (some 0x0bdcfc70b44c64970801d830b221e45cedef6438) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c11_literal : c11Signed = [0xf8, 0x70, 0x83, 0x10, 0x8a, 0xde, 0x85, 0x03, 0x7e, 0x11, 0xd6, 0x00, 0x83, 0x01, 0x5f, 0x90, 0x94, 0x0b, 0xdc, 0xfc, 0x70, 0xb4, 0x4c, 0x64, 0x97, 0x08, 0x01, 0xd8, 0x30, 0xb2, 0x21, 0xe4, 0x5c, 0xed, 0xef, 0x64, 0x38, 0x88, 0x35, 0xda, 0xdc, 0xfb, 0x1c, 0x22, 0x10, 0x00, 0x80, 0x25, 0xa0, 0x8f, 0x3a, 0x77, 0xa1, 0x6d, 0xcc, 0x0b, 0xc9, 0xfc, 0x9f, 0xd9, 0x23, 0x8d, 0xf9, 0xff, 0x1b, 0xfe, 0xa6, 0xd0, 0xf6, 0x6a, 0xdc, 0x37, 0xef, 0x79, 0xd7, 0x7e, 0x1d, 0xd9, 0x14, 0x41, 0x76, 0xa0, 0x05, 0xa8, 0xd8, 0x01, 0x3a, 0xc2, 0xb4, 0x5b, 0x2f, 0x89, 0xc0, 0xde, 0x4e, 0x9e, 0xc3, 0x35, 0x9c, 0xa5, 0x4d, 0xc0, 0x98, 0x27, 0x0c, 0x42, 0x62, 0xc2, 0xf7, 0x75, 0x9b, 0x01, 0x73, 0x73] := by
  decide +kernel

theorem c11_payload_length : c11Payload.length = 112 := by
  decide +kernel

theorem c11_signed_length : c11Signed.length = 114 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c11_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c11Payload = some c11Fields := by
  unfold c11Payload c11Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c11F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c11F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c11F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c11F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c11F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c11F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c11F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c11_parse : c11Signed.toBLT? = some (.list c11Fields) := by
  have outer : Bytes.toBLTDiff? 114 c11Signed = some (.list c11Fields, []) := by
    simpa only [c11Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 113 112 c11Payload [] c11Fields
        (by rw [c11_payload_length]; decide +kernel) (c11_payload_parse 104)
  unfold Bytes.toBLT?
  rw [c11_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c11_decode :
    (c11Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c11Tx := by
  rw [c11_parse]
  decide +kernel

theorem c11_blt : c11Tx.toBLT = .list c11Fields := by
  norm_num only [c11Tx, c11Fields, c11F0, c11F1, c11F2, c11F3, c11F4, c11F6, c11F7, c11F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c11_encode0 : (BLT.bytes c11F0).toBytes = [0x83] ++ c11F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c11F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c11_encode1 : (BLT.bytes c11F1).toBytes = [0x85] ++ c11F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c11F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c11_encode2 : (BLT.bytes c11F2).toBytes = [0x83] ++ c11F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c11F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c11_encode3 : (BLT.bytes c11F3).toBytes = [0x94] ++ c11F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c11F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c11_encode4 : (BLT.bytes c11F4).toBytes = [0x88] ++ c11F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c11F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c11_encode5 : (BLT.bytes c11F5).toBytes = [0x80] ++ c11F5 := by
  unfold c11F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c11_encode6 : (BLT.bytes c11F6).toBytes = [] ++ c11F6 := by
  unfold c11F6
  rw [BLT.toBytes]
  decide +kernel

theorem c11_encode7 : (BLT.bytes c11F7).toBytes = [0xa0] ++ c11F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c11F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c11_encode8 : (BLT.bytes c11F8).toBytes = [0xa0] ++ c11F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c11F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c11_canonical : c11Tx.toBLT.toBytes = c11Signed := by
  have encoded : BLTs.toBytesJoin c11Fields = c11Payload := by
    simp only [c11Fields, BLTs.toBytesJoin,
      c11_encode0, c11_encode1, c11_encode2, c11_encode3, c11_encode4, c11_encode5, c11_encode6, c11_encode7, c11_encode8, c11Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c11_blt, BLT.toBytes, BLTs.toBytes, encoded, c11_payload_length]
  norm_num only [c11Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c12F0 : Bytes := [0x01, 0xbc, 0x89]

def c12F1 : Bytes := [0x03, 0x7e, 0x11, 0xd6, 0x00]

def c12F2 : Bytes := [0x9c, 0x40]

def c12F3 : Bytes := [0xf2, 0x3f, 0x00, 0xf6, 0x87, 0xfa, 0x96, 0xb5, 0x87, 0x20, 0xa7, 0xd0, 0xdc, 0x7e, 0xe2, 0x94, 0x17, 0x61, 0xa8, 0xd1]

def c12F4 : Bytes := [0x01, 0xe2, 0xfa, 0x67, 0x37, 0xd7, 0xc8, 0x10]

def c12F5 : Bytes := []

def c12F6 : Bytes := [0x26]

def c12F7 : Bytes := [0xb8, 0x4e, 0x30, 0x82, 0x27, 0xb6, 0x33, 0x5a, 0x62, 0xc4, 0x39, 0x5b, 0x03, 0xc6, 0xe6, 0xfe, 0xdb, 0xa4, 0x44, 0xb5, 0x0d, 0x90, 0x14, 0x59, 0x1c, 0x4b, 0x71, 0x30, 0x89, 0xd8, 0x80, 0xea]

def c12F8 : Bytes := [0x0d, 0x7d, 0xc8, 0x96, 0xab, 0x60, 0x9c, 0x88, 0xac, 0xeb, 0x90, 0x5a, 0x4d, 0xb7, 0x4a, 0xf5, 0x4b, 0x14, 0xd1, 0x3c, 0x6d, 0xc4, 0xd2, 0x6d, 0xfd, 0x20, 0x77, 0xe4, 0x98, 0x8e, 0xa1, 0x4c]

def c12Fields : List BLT := [.bytes c12F0, .bytes c12F1, .bytes c12F2, .bytes c12F3, .bytes c12F4, .bytes c12F5, .bytes c12F6, .bytes c12F7, .bytes c12F8]

def c12Payload : Bytes := [0x83] ++ c12F0 ++ [0x85] ++ c12F1 ++ [0x82] ++ c12F2 ++ [0x94] ++ c12F3 ++ [0x88] ++ c12F4 ++ [0x80] ++ c12F5 ++ [] ++ c12F6 ++ [0xa0] ++ c12F7 ++ [0xa0] ++ c12F8

def c12Signed : Bytes := [0xf8, 0x6f] ++ c12Payload

def c12Tx : Tx := { nonce := 113801, gas := 40000, value := 135946260000000016, data := c12F5, v := 38, r := c12F7, s := c12F8, type := .zero 15000000000 (some 0xf23f00f687fa96b58720a7d0dc7ee2941761a8d1) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c12_literal : c12Signed = [0xf8, 0x6f, 0x83, 0x01, 0xbc, 0x89, 0x85, 0x03, 0x7e, 0x11, 0xd6, 0x00, 0x82, 0x9c, 0x40, 0x94, 0xf2, 0x3f, 0x00, 0xf6, 0x87, 0xfa, 0x96, 0xb5, 0x87, 0x20, 0xa7, 0xd0, 0xdc, 0x7e, 0xe2, 0x94, 0x17, 0x61, 0xa8, 0xd1, 0x88, 0x01, 0xe2, 0xfa, 0x67, 0x37, 0xd7, 0xc8, 0x10, 0x80, 0x26, 0xa0, 0xb8, 0x4e, 0x30, 0x82, 0x27, 0xb6, 0x33, 0x5a, 0x62, 0xc4, 0x39, 0x5b, 0x03, 0xc6, 0xe6, 0xfe, 0xdb, 0xa4, 0x44, 0xb5, 0x0d, 0x90, 0x14, 0x59, 0x1c, 0x4b, 0x71, 0x30, 0x89, 0xd8, 0x80, 0xea, 0xa0, 0x0d, 0x7d, 0xc8, 0x96, 0xab, 0x60, 0x9c, 0x88, 0xac, 0xeb, 0x90, 0x5a, 0x4d, 0xb7, 0x4a, 0xf5, 0x4b, 0x14, 0xd1, 0x3c, 0x6d, 0xc4, 0xd2, 0x6d, 0xfd, 0x20, 0x77, 0xe4, 0x98, 0x8e, 0xa1, 0x4c] := by
  decide +kernel

theorem c12_payload_length : c12Payload.length = 111 := by
  decide +kernel

theorem c12_signed_length : c12Signed.length = 113 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c12_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c12Payload = some c12Fields := by
  unfold c12Payload c12Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c12F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c12F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c12F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c12F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c12F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c12F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c12F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c12_parse : c12Signed.toBLT? = some (.list c12Fields) := by
  have outer : Bytes.toBLTDiff? 113 c12Signed = some (.list c12Fields, []) := by
    simpa only [c12Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 112 111 c12Payload [] c12Fields
        (by rw [c12_payload_length]; decide +kernel) (c12_payload_parse 103)
  unfold Bytes.toBLT?
  rw [c12_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c12_decode :
    (c12Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c12Tx := by
  rw [c12_parse]
  decide +kernel

theorem c12_blt : c12Tx.toBLT = .list c12Fields := by
  norm_num only [c12Tx, c12Fields, c12F0, c12F1, c12F2, c12F3, c12F4, c12F6, c12F7, c12F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c12_encode0 : (BLT.bytes c12F0).toBytes = [0x83] ++ c12F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c12F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c12_encode1 : (BLT.bytes c12F1).toBytes = [0x85] ++ c12F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c12F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c12_encode2 : (BLT.bytes c12F2).toBytes = [0x82] ++ c12F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c12F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c12_encode3 : (BLT.bytes c12F3).toBytes = [0x94] ++ c12F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c12F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c12_encode4 : (BLT.bytes c12F4).toBytes = [0x88] ++ c12F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c12F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c12_encode5 : (BLT.bytes c12F5).toBytes = [0x80] ++ c12F5 := by
  unfold c12F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c12_encode6 : (BLT.bytes c12F6).toBytes = [] ++ c12F6 := by
  unfold c12F6
  rw [BLT.toBytes]
  decide +kernel

theorem c12_encode7 : (BLT.bytes c12F7).toBytes = [0xa0] ++ c12F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c12F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c12_encode8 : (BLT.bytes c12F8).toBytes = [0xa0] ++ c12F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c12F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c12_canonical : c12Tx.toBLT.toBytes = c12Signed := by
  have encoded : BLTs.toBytesJoin c12Fields = c12Payload := by
    simp only [c12Fields, BLTs.toBytesJoin,
      c12_encode0, c12_encode1, c12_encode2, c12_encode3, c12_encode4, c12_encode5, c12_encode6, c12_encode7, c12_encode8, c12Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c12_blt, BLT.toBytes, BLTs.toBytes, encoded, c12_payload_length]
  norm_num only [c12Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c13F0 : Bytes := [0x01, 0xcd, 0xf2]

def c13F1 : Bytes := [0x03, 0x32, 0x12, 0xe1, 0x40]

def c13F2 : Bytes := [0x01, 0x7d, 0xb0]

def c13F3 : Bytes := [0x79, 0x8a, 0xbd, 0xa6, 0xcc, 0x24, 0x6d, 0x0e, 0xdb, 0xa9, 0x12, 0x09, 0x2a, 0x2a, 0x3d, 0xbd, 0x3d, 0x11, 0x19, 0x1b]

def c13F4 : Bytes := []

def c13F5 : Bytes := [0x64, 0x88, 0x73, 0x34, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5c, 0xcf, 0x9f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x21, 0x06, 0x00, 0xf8, 0x16, 0x43, 0x08, 0xe3, 0xc2, 0x15, 0x04, 0xf0, 0xc1, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xe5, 0x55, 0x24, 0x0a, 0xd3, 0x10, 0x5a, 0x32, 0xe7, 0x65, 0xb0, 0x2f, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xeb, 0x16, 0x1c, 0xd0, 0xf2, 0x3e, 0xc8, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xe1, 0xfc, 0x00, 0x10, 0xeb, 0xc1, 0xf8, 0x1f, 0x4a, 0xf1, 0x03, 0x13, 0x3c, 0xf2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x1b, 0xb4, 0xd8, 0xf6, 0x40, 0xf9, 0xbc, 0xd9, 0x16, 0xa5, 0x54, 0xd5, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11, 0xed, 0xe3, 0x28, 0x16, 0xc0, 0x3d, 0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02]

def c13F6 : Bytes := [0x1b]

def c13F7 : Bytes := [0xbe, 0x80, 0xe0, 0xe5, 0x4c, 0x87, 0xa9, 0x7c, 0x14, 0xbf, 0x34, 0x18, 0x1c, 0x27, 0x88, 0xe0, 0x73, 0x15, 0x5c, 0x51, 0x3a, 0xba, 0xc6, 0xef, 0x9e, 0x97, 0x22, 0x8b, 0xa0, 0xaa, 0x1e, 0x63]

def c13F8 : Bytes := [0x3c, 0xf9, 0x16, 0x52, 0xf4, 0x1e, 0x49, 0x20, 0x05, 0xdb, 0x94, 0x3e, 0xdd, 0x47, 0x45, 0x25, 0xd0, 0xd1, 0xf4, 0xf6, 0xad, 0x1e, 0xf0, 0x2c, 0xc7, 0x56, 0xc9, 0xcb, 0x32, 0x0e, 0xb6, 0xb9]

def c13Fields : List BLT := [.bytes c13F0, .bytes c13F1, .bytes c13F2, .bytes c13F3, .bytes c13F4, .bytes c13F5, .bytes c13F6, .bytes c13F7, .bytes c13F8]

def c13Payload : Bytes := [0x83] ++ c13F0 ++ [0x85] ++ c13F1 ++ [0x83] ++ c13F2 ++ [0x94] ++ c13F3 ++ [0x80] ++ c13F4 ++ [0xb9, 0x02, 0x04] ++ c13F5 ++ [] ++ c13F6 ++ [0xa0] ++ c13F7 ++ [0xa0] ++ c13F8

def c13Signed : Bytes := [0xf9, 0x02, 0x6e] ++ c13Payload

def c13Tx : Tx := { nonce := 118258, gas := 97712, value := 0, data := c13F5, v := 27, r := c13F7, s := c13F8, type := .zero 13725000000 (some 0x798abda6cc246d0edba912092a2a3dbd3d11191b) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c13_literal : c13Signed = [0xf9, 0x02, 0x6e, 0x83, 0x01, 0xcd, 0xf2, 0x85, 0x03, 0x32, 0x12, 0xe1, 0x40, 0x83, 0x01, 0x7d, 0xb0, 0x94, 0x79, 0x8a, 0xbd, 0xa6, 0xcc, 0x24, 0x6d, 0x0e, 0xdb, 0xa9, 0x12, 0x09, 0x2a, 0x2a, 0x3d, 0xbd, 0x3d, 0x11, 0x19, 0x1b, 0x80, 0xb9, 0x02, 0x04, 0x64, 0x88, 0x73, 0x34, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5c, 0xcf, 0x9f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x21, 0x06, 0x00, 0xf8, 0x16, 0x43, 0x08, 0xe3, 0xc2, 0x15, 0x04, 0xf0, 0xc1, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xe5, 0x55, 0x24, 0x0a, 0xd3, 0x10, 0x5a, 0x32, 0xe7, 0x65, 0xb0, 0x2f, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xeb, 0x16, 0x1c, 0xd0, 0xf2, 0x3e, 0xc8, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0xe1, 0xfc, 0x00, 0x10, 0xeb, 0xc1, 0xf8, 0x1f, 0x4a, 0xf1, 0x03, 0x13, 0x3c, 0xf2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x1b, 0xb4, 0xd8, 0xf6, 0x40, 0xf9, 0xbc, 0xd9, 0x16, 0xa5, 0x54, 0xd5, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11, 0xed, 0xe3, 0x28, 0x16, 0xc0, 0x3d, 0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x1b, 0xa0, 0xbe, 0x80, 0xe0, 0xe5, 0x4c, 0x87, 0xa9, 0x7c, 0x14, 0xbf, 0x34, 0x18, 0x1c, 0x27, 0x88, 0xe0, 0x73, 0x15, 0x5c, 0x51, 0x3a, 0xba, 0xc6, 0xef, 0x9e, 0x97, 0x22, 0x8b, 0xa0, 0xaa, 0x1e, 0x63, 0xa0, 0x3c, 0xf9, 0x16, 0x52, 0xf4, 0x1e, 0x49, 0x20, 0x05, 0xdb, 0x94, 0x3e, 0xdd, 0x47, 0x45, 0x25, 0xd0, 0xd1, 0xf4, 0xf6, 0xad, 0x1e, 0xf0, 0x2c, 0xc7, 0x56, 0xc9, 0xcb, 0x32, 0x0e, 0xb6, 0xb9] := by
  decide +kernel

theorem c13_payload_length : c13Payload.length = 622 := by
  decide +kernel

theorem c13_signed_length : c13Signed.length = 625 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c13_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c13Payload = some c13Fields := by
  unfold c13Payload c13Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c13F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c13F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c13F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c13F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_two _ 2 4 c13F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c13F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c13F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c13_parse : c13Signed.toBLT? = some (.list c13Fields) := by
  have outer : Bytes.toBLTDiff? 625 c13Signed = some (.list c13Fields, []) := by
    simpa only [c13Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_two 624 2 110 c13Payload [] c13Fields
        (by rw [c13_payload_length]; decide +kernel) (c13_payload_parse 615)
  unfold Bytes.toBLT?
  rw [c13_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c13_decode :
    (c13Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c13Tx := by
  rw [c13_parse]
  decide +kernel

theorem c13_blt : c13Tx.toBLT = .list c13Fields := by
  norm_num only [c13Tx, c13Fields, c13F0, c13F1, c13F2, c13F3, c13F4, c13F6, c13F7, c13F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c13_encode0 : (BLT.bytes c13F0).toBytes = [0x83] ++ c13F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c13F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c13_encode1 : (BLT.bytes c13F1).toBytes = [0x85] ++ c13F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c13F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c13_encode2 : (BLT.bytes c13F2).toBytes = [0x83] ++ c13F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c13F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c13_encode3 : (BLT.bytes c13F3).toBytes = [0x94] ++ c13F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c13F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c13_encode4 : (BLT.bytes c13F4).toBytes = [0x80] ++ c13F4 := by
  unfold c13F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c13_encode5 : (BLT.bytes c13F5).toBytes = [0xb9, 0x02, 0x04] ++ c13F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c13F5.length = 516 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c13_encode6 : (BLT.bytes c13F6).toBytes = [] ++ c13F6 := by
  unfold c13F6
  rw [BLT.toBytes]
  decide +kernel

theorem c13_encode7 : (BLT.bytes c13F7).toBytes = [0xa0] ++ c13F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c13F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c13_encode8 : (BLT.bytes c13F8).toBytes = [0xa0] ++ c13F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c13F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c13_canonical : c13Tx.toBLT.toBytes = c13Signed := by
  have encoded : BLTs.toBytesJoin c13Fields = c13Payload := by
    simp only [c13Fields, BLTs.toBytesJoin,
      c13_encode0, c13_encode1, c13_encode2, c13_encode3, c13_encode4, c13_encode5, c13_encode6, c13_encode7, c13_encode8, c13Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c13_blt, BLT.toBytes, BLTs.toBytes, encoded, c13_payload_length]
  norm_num only [c13Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c14F0 : Bytes := [0x0f, 0x85]

def c14F1 : Bytes := [0x02, 0x77, 0x30, 0x79, 0xad]

def c14F2 : Bytes := [0x02, 0x71, 0x00]

def c14F3 : Bytes := [0x12, 0x45, 0x9c, 0x95, 0x11, 0x27, 0xe0, 0xc3, 0x74, 0xff, 0x91, 0x05, 0xdd, 0xa0, 0x97, 0x66, 0x2a, 0x02, 0x70, 0x93]

def c14F4 : Bytes := []

def c14F5 : Bytes := [0x39, 0x4c, 0x21, 0xe7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5a, 0x61, 0x69, 0x23, 0x3f, 0x02, 0x63, 0x1f, 0x7f, 0x3d, 0x82, 0x24, 0x86, 0x35, 0x7a, 0x1b, 0x9b, 0x48, 0xb4, 0xb9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x2a, 0xaa, 0x39, 0xb2, 0x23, 0xfe, 0x8d, 0x0a, 0x0e, 0x5c, 0x4f, 0x27, 0xea, 0xd9, 0x08, 0x3c, 0x75, 0x6c, 0xc2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8f, 0x82, 0x21, 0xaf, 0xbb, 0x33, 0x99, 0x8d, 0x85, 0x84, 0xa2, 0xb0, 0x57, 0x49, 0xba, 0x73, 0xc3, 0x7a, 0x93, 0x8a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa2, 0x58, 0xb3, 0x99, 0x54, 0xce, 0xf5, 0xcb, 0x14, 0x2f, 0xd5, 0x67, 0xa4, 0x6c, 0xdd, 0xb3, 0x1a, 0x67, 0x01, 0x24, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1a, 0x5c, 0xa8, 0x42, 0xf0, 0x25, 0xe5, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x5a, 0x83, 0x88, 0xbb, 0x74, 0x0c, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x64, 0xad, 0x1e, 0x26, 0x90, 0x4a, 0xd1, 0x2c, 0xf3, 0x4f, 0x07, 0x3b, 0x6d, 0x4e, 0x93, 0x88, 0x2f, 0x03, 0x3b, 0x25, 0xe1, 0xbe, 0x4c, 0xac, 0x67, 0x47, 0xf1, 0x87, 0xc5, 0xc0, 0x42, 0xbd, 0xc2, 0x0e, 0x7c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x5a, 0x83, 0x88, 0xbb, 0x74, 0x0c, 0xa0, 0x00, 0x00]

def c14F6 : Bytes := [0x1b]

def c14F7 : Bytes := [0xe5, 0x6c, 0xfe, 0x71, 0xb7, 0x44, 0x8b, 0xf1, 0xc8, 0xf8, 0x6b, 0x50, 0xb5, 0xbc, 0x30, 0xe6, 0x06, 0xa3, 0x9d, 0x75, 0x09, 0x8e, 0xa0, 0x5e, 0x53, 0xf5, 0xc4, 0x6e, 0x81, 0xfa, 0x30, 0x6c]

def c14F8 : Bytes := [0x0b, 0xf7, 0x22, 0x61, 0xe3, 0xf3, 0x75, 0x88, 0x79, 0x02, 0x8e, 0xad, 0x94, 0x3b, 0x8f, 0x57, 0x59, 0x1e, 0x0e, 0x7b, 0xa5, 0x48, 0x18, 0xe3, 0xc3, 0xdf, 0x1e, 0x91, 0xf3, 0x91, 0xf8, 0xb4]

def c14Fields : List BLT := [.bytes c14F0, .bytes c14F1, .bytes c14F2, .bytes c14F3, .bytes c14F4, .bytes c14F5, .bytes c14F6, .bytes c14F7, .bytes c14F8]

def c14Payload : Bytes := [0x82] ++ c14F0 ++ [0x85] ++ c14F1 ++ [0x83] ++ c14F2 ++ [0x94] ++ c14F3 ++ [0x80] ++ c14F4 ++ [0xb9, 0x01, 0x84] ++ c14F5 ++ [] ++ c14F6 ++ [0xa0] ++ c14F7 ++ [0xa0] ++ c14F8

def c14Signed : Bytes := [0xf9, 0x01, 0xed] ++ c14Payload

def c14Tx : Tx := { nonce := 3973, gas := 160000, value := 0, data := c14F5, v := 27, r := c14F7, s := c14F8, type := .zero 10589600173 (some 0x12459c951127e0c374ff9105dda097662a027093) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c14_literal : c14Signed = [0xf9, 0x01, 0xed, 0x82, 0x0f, 0x85, 0x85, 0x02, 0x77, 0x30, 0x79, 0xad, 0x83, 0x02, 0x71, 0x00, 0x94, 0x12, 0x45, 0x9c, 0x95, 0x11, 0x27, 0xe0, 0xc3, 0x74, 0xff, 0x91, 0x05, 0xdd, 0xa0, 0x97, 0x66, 0x2a, 0x02, 0x70, 0x93, 0x80, 0xb9, 0x01, 0x84, 0x39, 0x4c, 0x21, 0xe7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5a, 0x61, 0x69, 0x23, 0x3f, 0x02, 0x63, 0x1f, 0x7f, 0x3d, 0x82, 0x24, 0x86, 0x35, 0x7a, 0x1b, 0x9b, 0x48, 0xb4, 0xb9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x2a, 0xaa, 0x39, 0xb2, 0x23, 0xfe, 0x8d, 0x0a, 0x0e, 0x5c, 0x4f, 0x27, 0xea, 0xd9, 0x08, 0x3c, 0x75, 0x6c, 0xc2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8f, 0x82, 0x21, 0xaf, 0xbb, 0x33, 0x99, 0x8d, 0x85, 0x84, 0xa2, 0xb0, 0x57, 0x49, 0xba, 0x73, 0xc3, 0x7a, 0x93, 0x8a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa2, 0x58, 0xb3, 0x99, 0x54, 0xce, 0xf5, 0xcb, 0x14, 0x2f, 0xd5, 0x67, 0xa4, 0x6c, 0xdd, 0xb3, 0x1a, 0x67, 0x01, 0x24, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1a, 0x5c, 0xa8, 0x42, 0xf0, 0x25, 0xe5, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x5a, 0x83, 0x88, 0xbb, 0x74, 0x0c, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x64, 0xad, 0x1e, 0x26, 0x90, 0x4a, 0xd1, 0x2c, 0xf3, 0x4f, 0x07, 0x3b, 0x6d, 0x4e, 0x93, 0x88, 0x2f, 0x03, 0x3b, 0x25, 0xe1, 0xbe, 0x4c, 0xac, 0x67, 0x47, 0xf1, 0x87, 0xc5, 0xc0, 0x42, 0xbd, 0xc2, 0x0e, 0x7c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x5a, 0x83, 0x88, 0xbb, 0x74, 0x0c, 0xa0, 0x00, 0x00, 0x1b, 0xa0, 0xe5, 0x6c, 0xfe, 0x71, 0xb7, 0x44, 0x8b, 0xf1, 0xc8, 0xf8, 0x6b, 0x50, 0xb5, 0xbc, 0x30, 0xe6, 0x06, 0xa3, 0x9d, 0x75, 0x09, 0x8e, 0xa0, 0x5e, 0x53, 0xf5, 0xc4, 0x6e, 0x81, 0xfa, 0x30, 0x6c, 0xa0, 0x0b, 0xf7, 0x22, 0x61, 0xe3, 0xf3, 0x75, 0x88, 0x79, 0x02, 0x8e, 0xad, 0x94, 0x3b, 0x8f, 0x57, 0x59, 0x1e, 0x0e, 0x7b, 0xa5, 0x48, 0x18, 0xe3, 0xc3, 0xdf, 0x1e, 0x91, 0xf3, 0x91, 0xf8, 0xb4] := by
  decide +kernel

theorem c14_payload_length : c14Payload.length = 493 := by
  decide +kernel

theorem c14_signed_length : c14Signed.length = 496 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c14_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c14Payload = some c14Fields := by
  unfold c14Payload c14Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c14F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c14F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c14F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c14F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_two _ 1 132 c14F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c14F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c14F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c14_parse : c14Signed.toBLT? = some (.list c14Fields) := by
  have outer : Bytes.toBLTDiff? 496 c14Signed = some (.list c14Fields, []) := by
    simpa only [c14Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_two 495 1 237 c14Payload [] c14Fields
        (by rw [c14_payload_length]; decide +kernel) (c14_payload_parse 486)
  unfold Bytes.toBLT?
  rw [c14_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c14_decode :
    (c14Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c14Tx := by
  rw [c14_parse]
  decide +kernel

theorem c14_blt : c14Tx.toBLT = .list c14Fields := by
  norm_num only [c14Tx, c14Fields, c14F0, c14F1, c14F2, c14F3, c14F4, c14F6, c14F7, c14F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c14_encode0 : (BLT.bytes c14F0).toBytes = [0x82] ++ c14F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c14F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c14_encode1 : (BLT.bytes c14F1).toBytes = [0x85] ++ c14F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c14F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c14_encode2 : (BLT.bytes c14F2).toBytes = [0x83] ++ c14F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c14F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c14_encode3 : (BLT.bytes c14F3).toBytes = [0x94] ++ c14F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c14F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c14_encode4 : (BLT.bytes c14F4).toBytes = [0x80] ++ c14F4 := by
  unfold c14F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c14_encode5 : (BLT.bytes c14F5).toBytes = [0xb9, 0x01, 0x84] ++ c14F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c14F5.length = 388 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c14_encode6 : (BLT.bytes c14F6).toBytes = [] ++ c14F6 := by
  unfold c14F6
  rw [BLT.toBytes]
  decide +kernel

theorem c14_encode7 : (BLT.bytes c14F7).toBytes = [0xa0] ++ c14F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c14F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c14_encode8 : (BLT.bytes c14F8).toBytes = [0xa0] ++ c14F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c14F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c14_canonical : c14Tx.toBLT.toBytes = c14Signed := by
  have encoded : BLTs.toBytesJoin c14Fields = c14Payload := by
    simp only [c14Fields, BLTs.toBytesJoin,
      c14_encode0, c14_encode1, c14_encode2, c14_encode3, c14_encode4, c14_encode5, c14_encode6, c14_encode7, c14_encode8, c14Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c14_blt, BLT.toBytes, BLTs.toBytes, encoded, c14_payload_length]
  norm_num only [c14Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c15F0 : Bytes := [0x31]

def c15F1 : Bytes := [0x02, 0x54, 0x0b, 0xe4, 0x00]

def c15F2 : Bytes := [0x52, 0x08]

def c15F3 : Bytes := [0xbf, 0x79, 0xe9, 0xe3, 0x1b, 0x53, 0x04, 0x41, 0xdc, 0x3c, 0x9d, 0xae, 0xb9, 0x85, 0xa0, 0xf2, 0xf6, 0x43, 0x92, 0xb1]

def c15F4 : Bytes := [0x08, 0x52, 0xe1, 0xd3, 0xc1, 0xd4, 0xe0, 0x00]

def c15F5 : Bytes := []

def c15F6 : Bytes := [0x25]

def c15F7 : Bytes := [0xc1, 0x8e, 0x02, 0xc6, 0xca, 0xdb, 0xd0, 0x8b, 0x93, 0xc3, 0xb7, 0x8e, 0xc7, 0x74, 0x12, 0xfd, 0x5f, 0x06, 0x68, 0xa3, 0xc0, 0x2b, 0xaa, 0x28, 0xa0, 0x8d, 0xa2, 0x07, 0x0c, 0xc6, 0x0f, 0x75]

def c15F8 : Bytes := [0x01, 0x9b, 0xc1, 0xf5, 0xe5, 0x4f, 0xe4, 0x6a, 0xab, 0x14, 0xac, 0x44, 0x8c, 0x5d, 0xaf, 0xc4, 0x95, 0x3c, 0x54, 0x16, 0x40, 0xd2, 0x61, 0xf6, 0x94, 0x44, 0x18, 0xa8, 0x26, 0xc3, 0x75, 0x95]

def c15Fields : List BLT := [.bytes c15F0, .bytes c15F1, .bytes c15F2, .bytes c15F3, .bytes c15F4, .bytes c15F5, .bytes c15F6, .bytes c15F7, .bytes c15F8]

def c15Payload : Bytes := [] ++ c15F0 ++ [0x85] ++ c15F1 ++ [0x82] ++ c15F2 ++ [0x94] ++ c15F3 ++ [0x88] ++ c15F4 ++ [0x80] ++ c15F5 ++ [] ++ c15F6 ++ [0xa0] ++ c15F7 ++ [0xa0] ++ c15F8

def c15Signed : Bytes := [0xf8, 0x6c] ++ c15Payload

def c15Tx : Tx := { nonce := 49, gas := 21000, value := 599790000000000000, data := c15F5, v := 37, r := c15F7, s := c15F8, type := .zero 10000000000 (some 0xbf79e9e31b530441dc3c9daeb985a0f2f64392b1) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c15_literal : c15Signed = [0xf8, 0x6c, 0x31, 0x85, 0x02, 0x54, 0x0b, 0xe4, 0x00, 0x82, 0x52, 0x08, 0x94, 0xbf, 0x79, 0xe9, 0xe3, 0x1b, 0x53, 0x04, 0x41, 0xdc, 0x3c, 0x9d, 0xae, 0xb9, 0x85, 0xa0, 0xf2, 0xf6, 0x43, 0x92, 0xb1, 0x88, 0x08, 0x52, 0xe1, 0xd3, 0xc1, 0xd4, 0xe0, 0x00, 0x80, 0x25, 0xa0, 0xc1, 0x8e, 0x02, 0xc6, 0xca, 0xdb, 0xd0, 0x8b, 0x93, 0xc3, 0xb7, 0x8e, 0xc7, 0x74, 0x12, 0xfd, 0x5f, 0x06, 0x68, 0xa3, 0xc0, 0x2b, 0xaa, 0x28, 0xa0, 0x8d, 0xa2, 0x07, 0x0c, 0xc6, 0x0f, 0x75, 0xa0, 0x01, 0x9b, 0xc1, 0xf5, 0xe5, 0x4f, 0xe4, 0x6a, 0xab, 0x14, 0xac, 0x44, 0x8c, 0x5d, 0xaf, 0xc4, 0x95, 0x3c, 0x54, 0x16, 0x40, 0xd2, 0x61, 0xf6, 0x94, 0x44, 0x18, 0xa8, 0x26, 0xc3, 0x75, 0x95] := by
  decide +kernel

theorem c15_payload_length : c15Payload.length = 108 := by
  decide +kernel

theorem c15_signed_length : c15Signed.length = 110 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c15_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c15Payload = some c15Fields := by
  unfold c15Payload c15Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c15F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c15F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c15F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c15F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c15F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c15F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c15_parse : c15Signed.toBLT? = some (.list c15Fields) := by
  have outer : Bytes.toBLTDiff? 110 c15Signed = some (.list c15Fields, []) := by
    simpa only [c15Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 109 108 c15Payload [] c15Fields
        (by rw [c15_payload_length]; decide +kernel) (c15_payload_parse 100)
  unfold Bytes.toBLT?
  rw [c15_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c15_decode :
    (c15Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c15Tx := by
  rw [c15_parse]
  decide +kernel

theorem c15_blt : c15Tx.toBLT = .list c15Fields := by
  norm_num only [c15Tx, c15Fields, c15F0, c15F1, c15F2, c15F3, c15F4, c15F6, c15F7, c15F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c15_encode0 : (BLT.bytes c15F0).toBytes = [] ++ c15F0 := by
  unfold c15F0
  rw [BLT.toBytes]
  decide +kernel

theorem c15_encode1 : (BLT.bytes c15F1).toBytes = [0x85] ++ c15F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c15F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c15_encode2 : (BLT.bytes c15F2).toBytes = [0x82] ++ c15F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c15F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c15_encode3 : (BLT.bytes c15F3).toBytes = [0x94] ++ c15F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c15F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c15_encode4 : (BLT.bytes c15F4).toBytes = [0x88] ++ c15F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c15F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c15_encode5 : (BLT.bytes c15F5).toBytes = [0x80] ++ c15F5 := by
  unfold c15F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c15_encode6 : (BLT.bytes c15F6).toBytes = [] ++ c15F6 := by
  unfold c15F6
  rw [BLT.toBytes]
  decide +kernel

theorem c15_encode7 : (BLT.bytes c15F7).toBytes = [0xa0] ++ c15F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c15F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c15_encode8 : (BLT.bytes c15F8).toBytes = [0xa0] ++ c15F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c15F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c15_canonical : c15Tx.toBLT.toBytes = c15Signed := by
  have encoded : BLTs.toBytesJoin c15Fields = c15Payload := by
    simp only [c15Fields, BLTs.toBytesJoin,
      c15_encode0, c15_encode1, c15_encode2, c15_encode3, c15_encode4, c15_encode5, c15_encode6, c15_encode7, c15_encode8, c15Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c15_blt, BLT.toBytes, BLTs.toBytes, encoded, c15_payload_length]
  norm_num only [c15Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
