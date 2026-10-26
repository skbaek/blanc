import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def c64F0 : Bytes := [0x07]

def c64F1 : Bytes := [0x77, 0x35, 0x94, 0x00]

def c64F2 : Bytes := [0x01, 0x86, 0xa0]

def c64F3 : Bytes := [0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04]

def c64F4 : Bytes := []

def c64F5 : Bytes := []

def c64F6 : Bytes := [0x1c]

def c64F7 : Bytes := [0x8d, 0xb2, 0x2f, 0xe4, 0x03, 0xbb, 0x76, 0xf7, 0xaf, 0x3e, 0x4d, 0x99, 0x85, 0x71, 0xa2, 0x7c, 0x34, 0x22, 0x54, 0x0e, 0x75, 0x21, 0xca, 0x80, 0x01, 0x0c, 0x85, 0x95, 0x42, 0xe3, 0x93, 0x01]

def c64F8 : Bytes := [0x67, 0x85, 0xbc, 0x22, 0x9c, 0x27, 0x27, 0xeb, 0x53, 0xcb, 0x39, 0xae, 0xd9, 0x3b, 0x6e, 0x3e, 0xbf, 0x7a, 0xf3, 0x81, 0xad, 0x97, 0x78, 0xa3, 0x7b, 0x72, 0x3e, 0xc2, 0x2b, 0xe7, 0xa9, 0xcc]

def c64Fields : List BLT := [.bytes c64F0, .bytes c64F1, .bytes c64F2, .bytes c64F3, .bytes c64F4, .bytes c64F5, .bytes c64F6, .bytes c64F7, .bytes c64F8]

def c64Payload : Bytes := [] ++ c64F0 ++ [0x84] ++ c64F1 ++ [0x83] ++ c64F2 ++ [0x94] ++ c64F3 ++ [0x80] ++ c64F4 ++ [0x80] ++ c64F5 ++ [] ++ c64F6 ++ [0xa0] ++ c64F7 ++ [0xa0] ++ c64F8

def c64Signed : Bytes := [0xf8, 0x64] ++ c64Payload

def c64Tx : Tx := { nonce := 7, gas := 100000, value := 0, data := c64F5, v := 28, r := c64F7, s := c64F8, type := .zero 2000000000 (some 0x3cd9024168e6240b4f18b466d9bea9f8efc66004) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c64_literal : c64Signed = [0xf8, 0x64, 0x07, 0x84, 0x77, 0x35, 0x94, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04, 0x80, 0x80, 0x1c, 0xa0, 0x8d, 0xb2, 0x2f, 0xe4, 0x03, 0xbb, 0x76, 0xf7, 0xaf, 0x3e, 0x4d, 0x99, 0x85, 0x71, 0xa2, 0x7c, 0x34, 0x22, 0x54, 0x0e, 0x75, 0x21, 0xca, 0x80, 0x01, 0x0c, 0x85, 0x95, 0x42, 0xe3, 0x93, 0x01, 0xa0, 0x67, 0x85, 0xbc, 0x22, 0x9c, 0x27, 0x27, 0xeb, 0x53, 0xcb, 0x39, 0xae, 0xd9, 0x3b, 0x6e, 0x3e, 0xbf, 0x7a, 0xf3, 0x81, 0xad, 0x97, 0x78, 0xa3, 0x7b, 0x72, 0x3e, 0xc2, 0x2b, 0xe7, 0xa9, 0xcc] := by
  decide +kernel

theorem c64_payload_length : c64Payload.length = 100 := by
  decide +kernel

theorem c64_signed_length : c64Signed.length = 102 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c64_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c64Payload = some c64Fields := by
  unfold c64Payload c64Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c64F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c64F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c64F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c64F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c64F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c64_parse : c64Signed.toBLT? = some (.list c64Fields) := by
  have outer : Bytes.toBLTDiff? 102 c64Signed = some (.list c64Fields, []) := by
    simpa only [c64Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 101 100 c64Payload [] c64Fields
        (by rw [c64_payload_length]; decide +kernel) (c64_payload_parse 92)
  unfold Bytes.toBLT?
  rw [c64_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c64_decode :
    (c64Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c64Tx := by
  rw [c64_parse]
  decide +kernel

theorem c64_blt : c64Tx.toBLT = .list c64Fields := by
  norm_num only [c64Tx, c64Fields, c64F0, c64F1, c64F2, c64F3, c64F4, c64F6, c64F7, c64F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c64_encode0 : (BLT.bytes c64F0).toBytes = [] ++ c64F0 := by
  unfold c64F0
  rw [BLT.toBytes]
  decide +kernel

theorem c64_encode1 : (BLT.bytes c64F1).toBytes = [0x84] ++ c64F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c64F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c64_encode2 : (BLT.bytes c64F2).toBytes = [0x83] ++ c64F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c64F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c64_encode3 : (BLT.bytes c64F3).toBytes = [0x94] ++ c64F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c64F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c64_encode4 : (BLT.bytes c64F4).toBytes = [0x80] ++ c64F4 := by
  unfold c64F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c64_encode5 : (BLT.bytes c64F5).toBytes = [0x80] ++ c64F5 := by
  unfold c64F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c64_encode6 : (BLT.bytes c64F6).toBytes = [] ++ c64F6 := by
  unfold c64F6
  rw [BLT.toBytes]
  decide +kernel

theorem c64_encode7 : (BLT.bytes c64F7).toBytes = [0xa0] ++ c64F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c64F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c64_encode8 : (BLT.bytes c64F8).toBytes = [0xa0] ++ c64F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c64F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c64_canonical : c64Tx.toBLT.toBytes = c64Signed := by
  have encoded : BLTs.toBytesJoin c64Fields = c64Payload := by
    simp only [c64Fields, BLTs.toBytesJoin,
      c64_encode0, c64_encode1, c64_encode2, c64_encode3, c64_encode4, c64_encode5, c64_encode6, c64_encode7, c64_encode8, c64Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c64_blt, BLT.toBytes, BLTs.toBytes, encoded, c64_payload_length]
  norm_num only [c64Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c65F0 : Bytes := [0x07]

def c65F1 : Bytes := [0x77, 0x35, 0x94, 0x00]

def c65F2 : Bytes := [0x01, 0x86, 0xa0]

def c65F3 : Bytes := [0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04]

def c65F4 : Bytes := []

def c65F5 : Bytes := []

def c65F6 : Bytes := [0x1b]

def c65F7 : Bytes := [0xf8, 0x7c, 0xec, 0x19, 0xaf, 0x4b, 0x50, 0x30, 0x8b, 0xc0, 0xf7, 0x86, 0x95, 0x28, 0x85, 0x12, 0xa8, 0x62, 0xfe, 0xe2, 0xb2, 0xc9, 0xe1, 0xaf, 0xe4, 0x24, 0x89, 0xe8, 0x73, 0x0d, 0xc7, 0x12]

def c65F8 : Bytes := [0x5d, 0x54, 0xf8, 0xa3, 0xd2, 0x81, 0x59, 0x37, 0x21, 0xef, 0x36, 0x39, 0xb4, 0xab, 0xcd, 0x40, 0xe6, 0x36, 0x87, 0x06, 0x1e, 0x55, 0xf1, 0x63, 0x02, 0x0c, 0x2f, 0xda, 0xb1, 0xa8, 0x30, 0x26]

def c65Fields : List BLT := [.bytes c65F0, .bytes c65F1, .bytes c65F2, .bytes c65F3, .bytes c65F4, .bytes c65F5, .bytes c65F6, .bytes c65F7, .bytes c65F8]

def c65Payload : Bytes := [] ++ c65F0 ++ [0x84] ++ c65F1 ++ [0x83] ++ c65F2 ++ [0x94] ++ c65F3 ++ [0x80] ++ c65F4 ++ [0x80] ++ c65F5 ++ [] ++ c65F6 ++ [0xa0] ++ c65F7 ++ [0xa0] ++ c65F8

def c65Signed : Bytes := [0xf8, 0x64] ++ c65Payload

def c65Tx : Tx := { nonce := 7, gas := 100000, value := 0, data := c65F5, v := 27, r := c65F7, s := c65F8, type := .zero 2000000000 (some 0x3cd9024168e6240b4f18b466d9bea9f8efc66004) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c65_literal : c65Signed = [0xf8, 0x64, 0x07, 0x84, 0x77, 0x35, 0x94, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04, 0x80, 0x80, 0x1b, 0xa0, 0xf8, 0x7c, 0xec, 0x19, 0xaf, 0x4b, 0x50, 0x30, 0x8b, 0xc0, 0xf7, 0x86, 0x95, 0x28, 0x85, 0x12, 0xa8, 0x62, 0xfe, 0xe2, 0xb2, 0xc9, 0xe1, 0xaf, 0xe4, 0x24, 0x89, 0xe8, 0x73, 0x0d, 0xc7, 0x12, 0xa0, 0x5d, 0x54, 0xf8, 0xa3, 0xd2, 0x81, 0x59, 0x37, 0x21, 0xef, 0x36, 0x39, 0xb4, 0xab, 0xcd, 0x40, 0xe6, 0x36, 0x87, 0x06, 0x1e, 0x55, 0xf1, 0x63, 0x02, 0x0c, 0x2f, 0xda, 0xb1, 0xa8, 0x30, 0x26] := by
  decide +kernel

theorem c65_payload_length : c65Payload.length = 100 := by
  decide +kernel

theorem c65_signed_length : c65Signed.length = 102 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c65_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c65Payload = some c65Fields := by
  unfold c65Payload c65Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c65F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c65F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c65F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c65F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c65F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c65_parse : c65Signed.toBLT? = some (.list c65Fields) := by
  have outer : Bytes.toBLTDiff? 102 c65Signed = some (.list c65Fields, []) := by
    simpa only [c65Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 101 100 c65Payload [] c65Fields
        (by rw [c65_payload_length]; decide +kernel) (c65_payload_parse 92)
  unfold Bytes.toBLT?
  rw [c65_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c65_decode :
    (c65Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c65Tx := by
  rw [c65_parse]
  decide +kernel

theorem c65_blt : c65Tx.toBLT = .list c65Fields := by
  norm_num only [c65Tx, c65Fields, c65F0, c65F1, c65F2, c65F3, c65F4, c65F6, c65F7, c65F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c65_encode0 : (BLT.bytes c65F0).toBytes = [] ++ c65F0 := by
  unfold c65F0
  rw [BLT.toBytes]
  decide +kernel

theorem c65_encode1 : (BLT.bytes c65F1).toBytes = [0x84] ++ c65F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c65F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c65_encode2 : (BLT.bytes c65F2).toBytes = [0x83] ++ c65F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c65F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c65_encode3 : (BLT.bytes c65F3).toBytes = [0x94] ++ c65F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c65F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c65_encode4 : (BLT.bytes c65F4).toBytes = [0x80] ++ c65F4 := by
  unfold c65F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c65_encode5 : (BLT.bytes c65F5).toBytes = [0x80] ++ c65F5 := by
  unfold c65F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c65_encode6 : (BLT.bytes c65F6).toBytes = [] ++ c65F6 := by
  unfold c65F6
  rw [BLT.toBytes]
  decide +kernel

theorem c65_encode7 : (BLT.bytes c65F7).toBytes = [0xa0] ++ c65F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c65F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c65_encode8 : (BLT.bytes c65F8).toBytes = [0xa0] ++ c65F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c65F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c65_canonical : c65Tx.toBLT.toBytes = c65Signed := by
  have encoded : BLTs.toBytesJoin c65Fields = c65Payload := by
    simp only [c65Fields, BLTs.toBytesJoin,
      c65_encode0, c65_encode1, c65_encode2, c65_encode3, c65_encode4, c65_encode5, c65_encode6, c65_encode7, c65_encode8, c65Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c65_blt, BLT.toBytes, BLTs.toBytes, encoded, c65_payload_length]
  norm_num only [c65Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c66F0 : Bytes := [0x07]

def c66F1 : Bytes := [0x77, 0x35, 0x94, 0x00]

def c66F2 : Bytes := [0x01, 0x86, 0xa0]

def c66F3 : Bytes := [0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04]

def c66F4 : Bytes := []

def c66F5 : Bytes := []

def c66F6 : Bytes := [0x1c]

def c66F7 : Bytes := [0x59, 0x7c, 0xa4, 0x27, 0xd3, 0xd4, 0x74, 0x04, 0x06, 0x0e, 0x9c, 0x8b, 0x97, 0x7d, 0x74, 0x18, 0x36, 0xf0, 0x2b, 0xb6, 0xe1, 0x0c, 0x37, 0x76, 0xf4, 0xc7, 0x3d, 0x48, 0x8b, 0x80, 0x0b, 0x64]

def c66F8 : Bytes := [0x78, 0xb6, 0x20, 0x39, 0xcf, 0x10, 0xdd, 0x0c, 0x39, 0xa2, 0x7d, 0x99, 0x8f, 0xff, 0x6c, 0x0f, 0x09, 0xb9, 0x6d, 0x37, 0x10, 0x64, 0xc6, 0xb8, 0xca, 0x4c, 0x4d, 0xa1, 0x7d, 0x92, 0xfc, 0x5d]

def c66Fields : List BLT := [.bytes c66F0, .bytes c66F1, .bytes c66F2, .bytes c66F3, .bytes c66F4, .bytes c66F5, .bytes c66F6, .bytes c66F7, .bytes c66F8]

def c66Payload : Bytes := [] ++ c66F0 ++ [0x84] ++ c66F1 ++ [0x83] ++ c66F2 ++ [0x94] ++ c66F3 ++ [0x80] ++ c66F4 ++ [0x80] ++ c66F5 ++ [] ++ c66F6 ++ [0xa0] ++ c66F7 ++ [0xa0] ++ c66F8

def c66Signed : Bytes := [0xf8, 0x64] ++ c66Payload

def c66Tx : Tx := { nonce := 7, gas := 100000, value := 0, data := c66F5, v := 28, r := c66F7, s := c66F8, type := .zero 2000000000 (some 0x3cd9024168e6240b4f18b466d9bea9f8efc66004) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c66_literal : c66Signed = [0xf8, 0x64, 0x07, 0x84, 0x77, 0x35, 0x94, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04, 0x80, 0x80, 0x1c, 0xa0, 0x59, 0x7c, 0xa4, 0x27, 0xd3, 0xd4, 0x74, 0x04, 0x06, 0x0e, 0x9c, 0x8b, 0x97, 0x7d, 0x74, 0x18, 0x36, 0xf0, 0x2b, 0xb6, 0xe1, 0x0c, 0x37, 0x76, 0xf4, 0xc7, 0x3d, 0x48, 0x8b, 0x80, 0x0b, 0x64, 0xa0, 0x78, 0xb6, 0x20, 0x39, 0xcf, 0x10, 0xdd, 0x0c, 0x39, 0xa2, 0x7d, 0x99, 0x8f, 0xff, 0x6c, 0x0f, 0x09, 0xb9, 0x6d, 0x37, 0x10, 0x64, 0xc6, 0xb8, 0xca, 0x4c, 0x4d, 0xa1, 0x7d, 0x92, 0xfc, 0x5d] := by
  decide +kernel

theorem c66_payload_length : c66Payload.length = 100 := by
  decide +kernel

theorem c66_signed_length : c66Signed.length = 102 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c66_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c66Payload = some c66Fields := by
  unfold c66Payload c66Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c66F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c66F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c66F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c66F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c66F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c66_parse : c66Signed.toBLT? = some (.list c66Fields) := by
  have outer : Bytes.toBLTDiff? 102 c66Signed = some (.list c66Fields, []) := by
    simpa only [c66Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 101 100 c66Payload [] c66Fields
        (by rw [c66_payload_length]; decide +kernel) (c66_payload_parse 92)
  unfold Bytes.toBLT?
  rw [c66_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c66_decode :
    (c66Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c66Tx := by
  rw [c66_parse]
  decide +kernel

theorem c66_blt : c66Tx.toBLT = .list c66Fields := by
  norm_num only [c66Tx, c66Fields, c66F0, c66F1, c66F2, c66F3, c66F4, c66F6, c66F7, c66F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c66_encode0 : (BLT.bytes c66F0).toBytes = [] ++ c66F0 := by
  unfold c66F0
  rw [BLT.toBytes]
  decide +kernel

theorem c66_encode1 : (BLT.bytes c66F1).toBytes = [0x84] ++ c66F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c66F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c66_encode2 : (BLT.bytes c66F2).toBytes = [0x83] ++ c66F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c66F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c66_encode3 : (BLT.bytes c66F3).toBytes = [0x94] ++ c66F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c66F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c66_encode4 : (BLT.bytes c66F4).toBytes = [0x80] ++ c66F4 := by
  unfold c66F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c66_encode5 : (BLT.bytes c66F5).toBytes = [0x80] ++ c66F5 := by
  unfold c66F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c66_encode6 : (BLT.bytes c66F6).toBytes = [] ++ c66F6 := by
  unfold c66F6
  rw [BLT.toBytes]
  decide +kernel

theorem c66_encode7 : (BLT.bytes c66F7).toBytes = [0xa0] ++ c66F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c66F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c66_encode8 : (BLT.bytes c66F8).toBytes = [0xa0] ++ c66F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c66F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c66_canonical : c66Tx.toBLT.toBytes = c66Signed := by
  have encoded : BLTs.toBytesJoin c66Fields = c66Payload := by
    simp only [c66Fields, BLTs.toBytesJoin,
      c66_encode0, c66_encode1, c66_encode2, c66_encode3, c66_encode4, c66_encode5, c66_encode6, c66_encode7, c66_encode8, c66Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c66_blt, BLT.toBytes, BLTs.toBytes, encoded, c66_payload_length]
  norm_num only [c66Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c67F0 : Bytes := [0x08]

def c67F1 : Bytes := [0x77, 0x35, 0x94, 0x00]

def c67F2 : Bytes := [0x01, 0x86, 0xa0]

def c67F3 : Bytes := [0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04]

def c67F4 : Bytes := []

def c67F5 : Bytes := []

def c67F6 : Bytes := [0x1c]

def c67F7 : Bytes := [0x57, 0xdf, 0x86, 0x11, 0xd9, 0x69, 0xde, 0x3e, 0x4d, 0x11, 0x59, 0x49, 0x40, 0xd7, 0xda, 0x4f, 0x6a, 0xcf, 0xae, 0x9a, 0x23, 0x0b, 0xe9, 0xdf, 0xe8, 0xb3, 0x11, 0xe9, 0xf3, 0xfe, 0x76, 0xde]

def c67F8 : Bytes := [0x3c, 0x3d, 0x79, 0xab, 0x4d, 0x39, 0x22, 0x6e, 0x0d, 0x39, 0x31, 0xa5, 0x3a, 0x3b, 0x13, 0x50, 0xad, 0x18, 0x05, 0x00, 0x95, 0xf7, 0xa7, 0x7b, 0x64, 0xde, 0x24, 0x22, 0x8a, 0xd4, 0x16, 0xd8]

def c67Fields : List BLT := [.bytes c67F0, .bytes c67F1, .bytes c67F2, .bytes c67F3, .bytes c67F4, .bytes c67F5, .bytes c67F6, .bytes c67F7, .bytes c67F8]

def c67Payload : Bytes := [] ++ c67F0 ++ [0x84] ++ c67F1 ++ [0x83] ++ c67F2 ++ [0x94] ++ c67F3 ++ [0x80] ++ c67F4 ++ [0x80] ++ c67F5 ++ [] ++ c67F6 ++ [0xa0] ++ c67F7 ++ [0xa0] ++ c67F8

def c67Signed : Bytes := [0xf8, 0x64] ++ c67Payload

def c67Tx : Tx := { nonce := 8, gas := 100000, value := 0, data := c67F5, v := 28, r := c67F7, s := c67F8, type := .zero 2000000000 (some 0x3cd9024168e6240b4f18b466d9bea9f8efc66004) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c67_literal : c67Signed = [0xf8, 0x64, 0x08, 0x84, 0x77, 0x35, 0x94, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04, 0x80, 0x80, 0x1c, 0xa0, 0x57, 0xdf, 0x86, 0x11, 0xd9, 0x69, 0xde, 0x3e, 0x4d, 0x11, 0x59, 0x49, 0x40, 0xd7, 0xda, 0x4f, 0x6a, 0xcf, 0xae, 0x9a, 0x23, 0x0b, 0xe9, 0xdf, 0xe8, 0xb3, 0x11, 0xe9, 0xf3, 0xfe, 0x76, 0xde, 0xa0, 0x3c, 0x3d, 0x79, 0xab, 0x4d, 0x39, 0x22, 0x6e, 0x0d, 0x39, 0x31, 0xa5, 0x3a, 0x3b, 0x13, 0x50, 0xad, 0x18, 0x05, 0x00, 0x95, 0xf7, 0xa7, 0x7b, 0x64, 0xde, 0x24, 0x22, 0x8a, 0xd4, 0x16, 0xd8] := by
  decide +kernel

theorem c67_payload_length : c67Payload.length = 100 := by
  decide +kernel

theorem c67_signed_length : c67Signed.length = 102 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c67_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c67Payload = some c67Fields := by
  unfold c67Payload c67Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c67F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c67F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c67F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c67F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c67F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c67_parse : c67Signed.toBLT? = some (.list c67Fields) := by
  have outer : Bytes.toBLTDiff? 102 c67Signed = some (.list c67Fields, []) := by
    simpa only [c67Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 101 100 c67Payload [] c67Fields
        (by rw [c67_payload_length]; decide +kernel) (c67_payload_parse 92)
  unfold Bytes.toBLT?
  rw [c67_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c67_decode :
    (c67Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c67Tx := by
  rw [c67_parse]
  decide +kernel

theorem c67_blt : c67Tx.toBLT = .list c67Fields := by
  norm_num only [c67Tx, c67Fields, c67F0, c67F1, c67F2, c67F3, c67F4, c67F6, c67F7, c67F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c67_encode0 : (BLT.bytes c67F0).toBytes = [] ++ c67F0 := by
  unfold c67F0
  rw [BLT.toBytes]
  decide +kernel

theorem c67_encode1 : (BLT.bytes c67F1).toBytes = [0x84] ++ c67F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c67F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c67_encode2 : (BLT.bytes c67F2).toBytes = [0x83] ++ c67F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c67F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c67_encode3 : (BLT.bytes c67F3).toBytes = [0x94] ++ c67F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c67F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c67_encode4 : (BLT.bytes c67F4).toBytes = [0x80] ++ c67F4 := by
  unfold c67F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c67_encode5 : (BLT.bytes c67F5).toBytes = [0x80] ++ c67F5 := by
  unfold c67F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c67_encode6 : (BLT.bytes c67F6).toBytes = [] ++ c67F6 := by
  unfold c67F6
  rw [BLT.toBytes]
  decide +kernel

theorem c67_encode7 : (BLT.bytes c67F7).toBytes = [0xa0] ++ c67F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c67F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c67_encode8 : (BLT.bytes c67F8).toBytes = [0xa0] ++ c67F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c67F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c67_canonical : c67Tx.toBLT.toBytes = c67Signed := by
  have encoded : BLTs.toBytesJoin c67Fields = c67Payload := by
    simp only [c67Fields, BLTs.toBytesJoin,
      c67_encode0, c67_encode1, c67_encode2, c67_encode3, c67_encode4, c67_encode5, c67_encode6, c67_encode7, c67_encode8, c67Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c67_blt, BLT.toBytes, BLTs.toBytes, encoded, c67_payload_length]
  norm_num only [c67Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c68F0 : Bytes := [0x07]

def c68F1 : Bytes := [0x77, 0x35, 0x94, 0x00]

def c68F2 : Bytes := [0x01, 0x86, 0xa0]

def c68F3 : Bytes := [0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04]

def c68F4 : Bytes := []

def c68F5 : Bytes := []

def c68F6 : Bytes := [0x1c]

def c68F7 : Bytes := [0x36, 0xf9, 0x85, 0x3e, 0x84, 0x14, 0x5e, 0x79, 0xa9, 0x15, 0x71, 0xa9, 0x8e, 0x18, 0x24, 0xa2, 0x3e, 0xba, 0xf8, 0x82, 0x5e, 0xa1, 0xb7, 0xb5, 0xb9, 0x6c, 0xbe, 0xaa, 0x84, 0x22, 0x8b, 0x8a]

def c68F8 : Bytes := [0x38, 0x54, 0x46, 0x5e, 0xdb, 0x0b, 0xb4, 0x1c, 0x21, 0xa7, 0x76, 0x25, 0xaf, 0x47, 0xc1, 0xd5, 0x77, 0x9a, 0x99, 0x7c, 0xf3, 0x0f, 0x21, 0x00, 0x07, 0x3f, 0x4c, 0xf5, 0x8e, 0x93, 0x23, 0x85]

def c68Fields : List BLT := [.bytes c68F0, .bytes c68F1, .bytes c68F2, .bytes c68F3, .bytes c68F4, .bytes c68F5, .bytes c68F6, .bytes c68F7, .bytes c68F8]

def c68Payload : Bytes := [] ++ c68F0 ++ [0x84] ++ c68F1 ++ [0x83] ++ c68F2 ++ [0x94] ++ c68F3 ++ [0x80] ++ c68F4 ++ [0x80] ++ c68F5 ++ [] ++ c68F6 ++ [0xa0] ++ c68F7 ++ [0xa0] ++ c68F8

def c68Signed : Bytes := [0xf8, 0x64] ++ c68Payload

def c68Tx : Tx := { nonce := 7, gas := 100000, value := 0, data := c68F5, v := 28, r := c68F7, s := c68F8, type := .zero 2000000000 (some 0x3cd9024168e6240b4f18b466d9bea9f8efc66004) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c68_literal : c68Signed = [0xf8, 0x64, 0x07, 0x84, 0x77, 0x35, 0x94, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04, 0x80, 0x80, 0x1c, 0xa0, 0x36, 0xf9, 0x85, 0x3e, 0x84, 0x14, 0x5e, 0x79, 0xa9, 0x15, 0x71, 0xa9, 0x8e, 0x18, 0x24, 0xa2, 0x3e, 0xba, 0xf8, 0x82, 0x5e, 0xa1, 0xb7, 0xb5, 0xb9, 0x6c, 0xbe, 0xaa, 0x84, 0x22, 0x8b, 0x8a, 0xa0, 0x38, 0x54, 0x46, 0x5e, 0xdb, 0x0b, 0xb4, 0x1c, 0x21, 0xa7, 0x76, 0x25, 0xaf, 0x47, 0xc1, 0xd5, 0x77, 0x9a, 0x99, 0x7c, 0xf3, 0x0f, 0x21, 0x00, 0x07, 0x3f, 0x4c, 0xf5, 0x8e, 0x93, 0x23, 0x85] := by
  decide +kernel

theorem c68_payload_length : c68Payload.length = 100 := by
  decide +kernel

theorem c68_signed_length : c68Signed.length = 102 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c68_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c68Payload = some c68Fields := by
  unfold c68Payload c68Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c68F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c68F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c68F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c68F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c68F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c68_parse : c68Signed.toBLT? = some (.list c68Fields) := by
  have outer : Bytes.toBLTDiff? 102 c68Signed = some (.list c68Fields, []) := by
    simpa only [c68Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 101 100 c68Payload [] c68Fields
        (by rw [c68_payload_length]; decide +kernel) (c68_payload_parse 92)
  unfold Bytes.toBLT?
  rw [c68_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c68_decode :
    (c68Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c68Tx := by
  rw [c68_parse]
  decide +kernel

theorem c68_blt : c68Tx.toBLT = .list c68Fields := by
  norm_num only [c68Tx, c68Fields, c68F0, c68F1, c68F2, c68F3, c68F4, c68F6, c68F7, c68F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c68_encode0 : (BLT.bytes c68F0).toBytes = [] ++ c68F0 := by
  unfold c68F0
  rw [BLT.toBytes]
  decide +kernel

theorem c68_encode1 : (BLT.bytes c68F1).toBytes = [0x84] ++ c68F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c68F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c68_encode2 : (BLT.bytes c68F2).toBytes = [0x83] ++ c68F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c68F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c68_encode3 : (BLT.bytes c68F3).toBytes = [0x94] ++ c68F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c68F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c68_encode4 : (BLT.bytes c68F4).toBytes = [0x80] ++ c68F4 := by
  unfold c68F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c68_encode5 : (BLT.bytes c68F5).toBytes = [0x80] ++ c68F5 := by
  unfold c68F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c68_encode6 : (BLT.bytes c68F6).toBytes = [] ++ c68F6 := by
  unfold c68F6
  rw [BLT.toBytes]
  decide +kernel

theorem c68_encode7 : (BLT.bytes c68F7).toBytes = [0xa0] ++ c68F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c68F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c68_encode8 : (BLT.bytes c68F8).toBytes = [0xa0] ++ c68F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c68F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c68_canonical : c68Tx.toBLT.toBytes = c68Signed := by
  have encoded : BLTs.toBytesJoin c68Fields = c68Payload := by
    simp only [c68Fields, BLTs.toBytesJoin,
      c68_encode0, c68_encode1, c68_encode2, c68_encode3, c68_encode4, c68_encode5, c68_encode6, c68_encode7, c68_encode8, c68Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c68_blt, BLT.toBytes, BLTs.toBytes, encoded, c68_payload_length]
  norm_num only [c68Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c69F0 : Bytes := [0x07]

def c69F1 : Bytes := [0x77, 0x35, 0x94, 0x00]

def c69F2 : Bytes := [0x01, 0x86, 0xa0]

def c69F3 : Bytes := [0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04]

def c69F4 : Bytes := []

def c69F5 : Bytes := []

def c69F6 : Bytes := [0x1c]

def c69F7 : Bytes := [0x11, 0xde, 0x38, 0x54, 0xbd, 0x32, 0x60, 0xe6, 0xc6, 0xd1, 0x61, 0x22, 0x67, 0x2e, 0x03, 0xa3, 0x18, 0xd7, 0x9d, 0x0a, 0xeb, 0x4b, 0x8c, 0x94, 0xca, 0x80, 0xb5, 0xab, 0x5f, 0x40, 0xe6, 0x4f]

def c69F8 : Bytes := [0x7d, 0xb5, 0xee, 0xe4, 0xe9, 0xd0, 0xc0, 0x46, 0xce, 0xaa, 0x6a, 0x40, 0xd2, 0x2a, 0x0f, 0xbf, 0x85, 0x46, 0x3a, 0x50, 0xe3, 0xd1, 0x38, 0x0d, 0xc6, 0x55, 0x00, 0xea, 0xb3, 0x4a, 0x00, 0x70]

def c69Fields : List BLT := [.bytes c69F0, .bytes c69F1, .bytes c69F2, .bytes c69F3, .bytes c69F4, .bytes c69F5, .bytes c69F6, .bytes c69F7, .bytes c69F8]

def c69Payload : Bytes := [] ++ c69F0 ++ [0x84] ++ c69F1 ++ [0x83] ++ c69F2 ++ [0x94] ++ c69F3 ++ [0x80] ++ c69F4 ++ [0x80] ++ c69F5 ++ [] ++ c69F6 ++ [0xa0] ++ c69F7 ++ [0xa0] ++ c69F8

def c69Signed : Bytes := [0xf8, 0x64] ++ c69Payload

def c69Tx : Tx := { nonce := 7, gas := 100000, value := 0, data := c69F5, v := 28, r := c69F7, s := c69F8, type := .zero 2000000000 (some 0x3cd9024168e6240b4f18b466d9bea9f8efc66004) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c69_literal : c69Signed = [0xf8, 0x64, 0x07, 0x84, 0x77, 0x35, 0x94, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04, 0x80, 0x80, 0x1c, 0xa0, 0x11, 0xde, 0x38, 0x54, 0xbd, 0x32, 0x60, 0xe6, 0xc6, 0xd1, 0x61, 0x22, 0x67, 0x2e, 0x03, 0xa3, 0x18, 0xd7, 0x9d, 0x0a, 0xeb, 0x4b, 0x8c, 0x94, 0xca, 0x80, 0xb5, 0xab, 0x5f, 0x40, 0xe6, 0x4f, 0xa0, 0x7d, 0xb5, 0xee, 0xe4, 0xe9, 0xd0, 0xc0, 0x46, 0xce, 0xaa, 0x6a, 0x40, 0xd2, 0x2a, 0x0f, 0xbf, 0x85, 0x46, 0x3a, 0x50, 0xe3, 0xd1, 0x38, 0x0d, 0xc6, 0x55, 0x00, 0xea, 0xb3, 0x4a, 0x00, 0x70] := by
  decide +kernel

theorem c69_payload_length : c69Payload.length = 100 := by
  decide +kernel

theorem c69_signed_length : c69Signed.length = 102 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c69_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c69Payload = some c69Fields := by
  unfold c69Payload c69Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c69F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c69F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c69F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c69F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c69F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c69_parse : c69Signed.toBLT? = some (.list c69Fields) := by
  have outer : Bytes.toBLTDiff? 102 c69Signed = some (.list c69Fields, []) := by
    simpa only [c69Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 101 100 c69Payload [] c69Fields
        (by rw [c69_payload_length]; decide +kernel) (c69_payload_parse 92)
  unfold Bytes.toBLT?
  rw [c69_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c69_decode :
    (c69Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c69Tx := by
  rw [c69_parse]
  decide +kernel

theorem c69_blt : c69Tx.toBLT = .list c69Fields := by
  norm_num only [c69Tx, c69Fields, c69F0, c69F1, c69F2, c69F3, c69F4, c69F6, c69F7, c69F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c69_encode0 : (BLT.bytes c69F0).toBytes = [] ++ c69F0 := by
  unfold c69F0
  rw [BLT.toBytes]
  decide +kernel

theorem c69_encode1 : (BLT.bytes c69F1).toBytes = [0x84] ++ c69F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c69F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c69_encode2 : (BLT.bytes c69F2).toBytes = [0x83] ++ c69F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c69F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c69_encode3 : (BLT.bytes c69F3).toBytes = [0x94] ++ c69F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c69F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c69_encode4 : (BLT.bytes c69F4).toBytes = [0x80] ++ c69F4 := by
  unfold c69F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c69_encode5 : (BLT.bytes c69F5).toBytes = [0x80] ++ c69F5 := by
  unfold c69F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c69_encode6 : (BLT.bytes c69F6).toBytes = [] ++ c69F6 := by
  unfold c69F6
  rw [BLT.toBytes]
  decide +kernel

theorem c69_encode7 : (BLT.bytes c69F7).toBytes = [0xa0] ++ c69F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c69F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c69_encode8 : (BLT.bytes c69F8).toBytes = [0xa0] ++ c69F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c69F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c69_canonical : c69Tx.toBLT.toBytes = c69Signed := by
  have encoded : BLTs.toBytesJoin c69Fields = c69Payload := by
    simp only [c69Fields, BLTs.toBytesJoin,
      c69_encode0, c69_encode1, c69_encode2, c69_encode3, c69_encode4, c69_encode5, c69_encode6, c69_encode7, c69_encode8, c69Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c69_blt, BLT.toBytes, BLTs.toBytes, encoded, c69_payload_length]
  norm_num only [c69Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c70F0 : Bytes := [0x07]

def c70F1 : Bytes := [0x77, 0x35, 0x94, 0x00]

def c70F2 : Bytes := [0x01, 0x86, 0xa0]

def c70F3 : Bytes := [0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04]

def c70F4 : Bytes := []

def c70F5 : Bytes := []

def c70F6 : Bytes := [0x1b]

def c70F7 : Bytes := [0x51, 0x2e, 0xf8, 0x85, 0xfe, 0x46, 0x37, 0x76, 0xcd, 0xf8, 0xc5, 0x76, 0x4f, 0x60, 0x07, 0xa8, 0xd3, 0x54, 0x98, 0xff, 0xe5, 0x2a, 0x52, 0x55, 0x2a, 0x5f, 0x1b, 0x07, 0x86, 0x23, 0xc3, 0xce]

def c70F8 : Bytes := [0x0f, 0x19, 0x83, 0x80, 0x4f, 0x37, 0xcf, 0x03, 0x67, 0xd0, 0x53, 0x62, 0x0e, 0x14, 0x7c, 0xa3, 0x15, 0xf0, 0x29, 0x48, 0x24, 0xa5, 0x27, 0x60, 0xa9, 0xc7, 0xf8, 0xf3, 0xb2, 0x3b, 0xdf, 0x9d]

def c70Fields : List BLT := [.bytes c70F0, .bytes c70F1, .bytes c70F2, .bytes c70F3, .bytes c70F4, .bytes c70F5, .bytes c70F6, .bytes c70F7, .bytes c70F8]

def c70Payload : Bytes := [] ++ c70F0 ++ [0x84] ++ c70F1 ++ [0x83] ++ c70F2 ++ [0x94] ++ c70F3 ++ [0x80] ++ c70F4 ++ [0x80] ++ c70F5 ++ [] ++ c70F6 ++ [0xa0] ++ c70F7 ++ [0xa0] ++ c70F8

def c70Signed : Bytes := [0xf8, 0x64] ++ c70Payload

def c70Tx : Tx := { nonce := 7, gas := 100000, value := 0, data := c70F5, v := 27, r := c70F7, s := c70F8, type := .zero 2000000000 (some 0x3cd9024168e6240b4f18b466d9bea9f8efc66004) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c70_literal : c70Signed = [0xf8, 0x64, 0x07, 0x84, 0x77, 0x35, 0x94, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x3c, 0xd9, 0x02, 0x41, 0x68, 0xe6, 0x24, 0x0b, 0x4f, 0x18, 0xb4, 0x66, 0xd9, 0xbe, 0xa9, 0xf8, 0xef, 0xc6, 0x60, 0x04, 0x80, 0x80, 0x1b, 0xa0, 0x51, 0x2e, 0xf8, 0x85, 0xfe, 0x46, 0x37, 0x76, 0xcd, 0xf8, 0xc5, 0x76, 0x4f, 0x60, 0x07, 0xa8, 0xd3, 0x54, 0x98, 0xff, 0xe5, 0x2a, 0x52, 0x55, 0x2a, 0x5f, 0x1b, 0x07, 0x86, 0x23, 0xc3, 0xce, 0xa0, 0x0f, 0x19, 0x83, 0x80, 0x4f, 0x37, 0xcf, 0x03, 0x67, 0xd0, 0x53, 0x62, 0x0e, 0x14, 0x7c, 0xa3, 0x15, 0xf0, 0x29, 0x48, 0x24, 0xa5, 0x27, 0x60, 0xa9, 0xc7, 0xf8, 0xf3, 0xb2, 0x3b, 0xdf, 0x9d] := by
  decide +kernel

theorem c70_payload_length : c70Payload.length = 100 := by
  decide +kernel

theorem c70_signed_length : c70Signed.length = 102 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c70_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c70Payload = some c70Fields := by
  unfold c70Payload c70Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c70F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c70F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c70F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c70F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c70F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c70_parse : c70Signed.toBLT? = some (.list c70Fields) := by
  have outer : Bytes.toBLTDiff? 102 c70Signed = some (.list c70Fields, []) := by
    simpa only [c70Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 101 100 c70Payload [] c70Fields
        (by rw [c70_payload_length]; decide +kernel) (c70_payload_parse 92)
  unfold Bytes.toBLT?
  rw [c70_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c70_decode :
    (c70Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c70Tx := by
  rw [c70_parse]
  decide +kernel

theorem c70_blt : c70Tx.toBLT = .list c70Fields := by
  norm_num only [c70Tx, c70Fields, c70F0, c70F1, c70F2, c70F3, c70F4, c70F6, c70F7, c70F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c70_encode0 : (BLT.bytes c70F0).toBytes = [] ++ c70F0 := by
  unfold c70F0
  rw [BLT.toBytes]
  decide +kernel

theorem c70_encode1 : (BLT.bytes c70F1).toBytes = [0x84] ++ c70F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c70F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c70_encode2 : (BLT.bytes c70F2).toBytes = [0x83] ++ c70F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c70F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c70_encode3 : (BLT.bytes c70F3).toBytes = [0x94] ++ c70F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c70F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c70_encode4 : (BLT.bytes c70F4).toBytes = [0x80] ++ c70F4 := by
  unfold c70F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c70_encode5 : (BLT.bytes c70F5).toBytes = [0x80] ++ c70F5 := by
  unfold c70F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c70_encode6 : (BLT.bytes c70F6).toBytes = [] ++ c70F6 := by
  unfold c70F6
  rw [BLT.toBytes]
  decide +kernel

theorem c70_encode7 : (BLT.bytes c70F7).toBytes = [0xa0] ++ c70F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c70F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c70_encode8 : (BLT.bytes c70F8).toBytes = [0xa0] ++ c70F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c70F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c70_canonical : c70Tx.toBLT.toBytes = c70Signed := by
  have encoded : BLTs.toBytesJoin c70Fields = c70Payload := by
    simp only [c70Fields, BLTs.toBytesJoin,
      c70_encode0, c70_encode1, c70_encode2, c70_encode3, c70_encode4, c70_encode5, c70_encode6, c70_encode7, c70_encode8, c70Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c70_blt, BLT.toBytes, BLTs.toBytes, encoded, c70_payload_length]
  norm_num only [c70Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c71F0 : Bytes := [0x09]

def c71F1 : Bytes := [0x77, 0x35, 0x94, 0x00]

def c71F2 : Bytes := [0x90, 0x73]

def c71F3 : Bytes := [0x27, 0x5b, 0x69, 0xaa, 0x7c, 0x8c, 0x1d, 0x64, 0x8a, 0x05, 0x57, 0x65, 0x6b, 0xce, 0x1c, 0x28, 0x6e, 0x69, 0xa2, 0x9d]

def c71F4 : Bytes := []

def c71F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x76, 0xfc, 0x52, 0xee, 0x7a, 0x08, 0x76, 0x03, 0x9a, 0xe7, 0x77, 0x57, 0xe0, 0x8a, 0xdf, 0x27, 0x9f, 0x1a, 0x1a, 0x1e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3d, 0xc8, 0x84, 0xb9, 0x22]

def c71F6 : Bytes := [0x26]

def c71F7 : Bytes := [0xef, 0x14, 0x7b, 0xfd, 0x6a, 0x7a, 0xcf, 0x13, 0x62, 0x9b, 0x30, 0x7e, 0x64, 0x67, 0xfd, 0x9c, 0x60, 0x40, 0xe4, 0x07, 0x42, 0xb7, 0x4d, 0xe0, 0x2f, 0x5f, 0xa0, 0x5a, 0xba, 0xfe, 0x51, 0x69]

def c71F8 : Bytes := [0x63, 0xa2, 0x18, 0x9b, 0x65, 0x04, 0x6c, 0x34, 0xce, 0x81, 0x85, 0x0c, 0xfd, 0x4b, 0xa7, 0x79, 0x0d, 0xbd, 0x73, 0x20, 0x9b, 0x4e, 0xeb, 0x9c, 0x96, 0xd1, 0xd1, 0xd9, 0x52, 0xf0, 0x8e, 0x43]

def c71Fields : List BLT := [.bytes c71F0, .bytes c71F1, .bytes c71F2, .bytes c71F3, .bytes c71F4, .bytes c71F5, .bytes c71F6, .bytes c71F7, .bytes c71F8]

def c71Payload : Bytes := [] ++ c71F0 ++ [0x84] ++ c71F1 ++ [0x82] ++ c71F2 ++ [0x94] ++ c71F3 ++ [0x80] ++ c71F4 ++ [0xb8, 0x44] ++ c71F5 ++ [] ++ c71F6 ++ [0xa0] ++ c71F7 ++ [0xa0] ++ c71F8

def c71Signed : Bytes := [0xf8, 0xa8] ++ c71Payload

def c71Tx : Tx := { nonce := 9, gas := 36979, value := 0, data := c71F5, v := 38, r := c71F7, s := c71F8, type := .zero 2000000000 (some 0x275b69aa7c8c1d648a0557656bce1c286e69a29d) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c71_literal : c71Signed = [0xf8, 0xa8, 0x09, 0x84, 0x77, 0x35, 0x94, 0x00, 0x82, 0x90, 0x73, 0x94, 0x27, 0x5b, 0x69, 0xaa, 0x7c, 0x8c, 0x1d, 0x64, 0x8a, 0x05, 0x57, 0x65, 0x6b, 0xce, 0x1c, 0x28, 0x6e, 0x69, 0xa2, 0x9d, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x76, 0xfc, 0x52, 0xee, 0x7a, 0x08, 0x76, 0x03, 0x9a, 0xe7, 0x77, 0x57, 0xe0, 0x8a, 0xdf, 0x27, 0x9f, 0x1a, 0x1a, 0x1e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3d, 0xc8, 0x84, 0xb9, 0x22, 0x26, 0xa0, 0xef, 0x14, 0x7b, 0xfd, 0x6a, 0x7a, 0xcf, 0x13, 0x62, 0x9b, 0x30, 0x7e, 0x64, 0x67, 0xfd, 0x9c, 0x60, 0x40, 0xe4, 0x07, 0x42, 0xb7, 0x4d, 0xe0, 0x2f, 0x5f, 0xa0, 0x5a, 0xba, 0xfe, 0x51, 0x69, 0xa0, 0x63, 0xa2, 0x18, 0x9b, 0x65, 0x04, 0x6c, 0x34, 0xce, 0x81, 0x85, 0x0c, 0xfd, 0x4b, 0xa7, 0x79, 0x0d, 0xbd, 0x73, 0x20, 0x9b, 0x4e, 0xeb, 0x9c, 0x96, 0xd1, 0xd1, 0xd9, 0x52, 0xf0, 0x8e, 0x43] := by
  decide +kernel

theorem c71_payload_length : c71Payload.length = 168 := by
  decide +kernel

theorem c71_signed_length : c71Signed.length = 170 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c71_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c71Payload = some c71Fields := by
  unfold c71Payload c71Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c71F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c71F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c71F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c71F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c71F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c71F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c71_parse : c71Signed.toBLT? = some (.list c71Fields) := by
  have outer : Bytes.toBLTDiff? 170 c71Signed = some (.list c71Fields, []) := by
    simpa only [c71Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 169 168 c71Payload [] c71Fields
        (by rw [c71_payload_length]; decide +kernel) (c71_payload_parse 160)
  unfold Bytes.toBLT?
  rw [c71_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c71_decode :
    (c71Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c71Tx := by
  rw [c71_parse]
  decide +kernel

theorem c71_blt : c71Tx.toBLT = .list c71Fields := by
  norm_num only [c71Tx, c71Fields, c71F0, c71F1, c71F2, c71F3, c71F4, c71F6, c71F7, c71F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c71_encode0 : (BLT.bytes c71F0).toBytes = [] ++ c71F0 := by
  unfold c71F0
  rw [BLT.toBytes]
  decide +kernel

theorem c71_encode1 : (BLT.bytes c71F1).toBytes = [0x84] ++ c71F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c71F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c71_encode2 : (BLT.bytes c71F2).toBytes = [0x82] ++ c71F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c71F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c71_encode3 : (BLT.bytes c71F3).toBytes = [0x94] ++ c71F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c71F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c71_encode4 : (BLT.bytes c71F4).toBytes = [0x80] ++ c71F4 := by
  unfold c71F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c71_encode5 : (BLT.bytes c71F5).toBytes = [0xb8, 0x44] ++ c71F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c71F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c71_encode6 : (BLT.bytes c71F6).toBytes = [] ++ c71F6 := by
  unfold c71F6
  rw [BLT.toBytes]
  decide +kernel

theorem c71_encode7 : (BLT.bytes c71F7).toBytes = [0xa0] ++ c71F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c71F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c71_encode8 : (BLT.bytes c71F8).toBytes = [0xa0] ++ c71F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c71F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c71_canonical : c71Tx.toBLT.toBytes = c71Signed := by
  have encoded : BLTs.toBytesJoin c71Fields = c71Payload := by
    simp only [c71Fields, BLTs.toBytesJoin,
      c71_encode0, c71_encode1, c71_encode2, c71_encode3, c71_encode4, c71_encode5, c71_encode6, c71_encode7, c71_encode8, c71Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c71_blt, BLT.toBytes, BLTs.toBytes, encoded, c71_payload_length]
  norm_num only [c71Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
