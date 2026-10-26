import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def c40F0 : Bytes := []

def c40F1 : Bytes := [0xb2, 0xd0, 0x5e, 0x00]

def c40F2 : Bytes := [0x52, 0x08]

def c40F3 : Bytes := [0x54, 0xc8, 0x2c, 0x81, 0xd2, 0xad, 0x7a, 0x2b, 0xec, 0xc4, 0x55, 0x6a, 0xb1, 0x25, 0x1b, 0x88, 0x33, 0x96, 0x7e, 0xe1]

def c40F4 : Bytes := [0x07, 0xc4, 0x35, 0xcb, 0x12, 0x27, 0x90, 0x00]

def c40F5 : Bytes := []

def c40F6 : Bytes := [0x26]

def c40F7 : Bytes := [0xb1, 0x4a, 0xe7, 0xa0, 0x2d, 0xa8, 0xb1, 0xec, 0xb2, 0xc4, 0x23, 0x22, 0x83, 0x48, 0x08, 0xf3, 0x52, 0x48, 0xa8, 0xea, 0x17, 0x3d, 0xc9, 0xd3, 0xf4, 0x28, 0x0c, 0x2b, 0x47, 0x41, 0xcf, 0x94]

def c40F8 : Bytes := [0x17, 0x94, 0xaa, 0x34, 0xd4, 0xa1, 0x79, 0x88, 0x5e, 0xe9, 0x4a, 0x8f, 0x5e, 0x47, 0xd7, 0x5b, 0x95, 0xb0, 0xc4, 0x9f, 0xd2, 0xac, 0xb7, 0x2e, 0x19, 0xee, 0x04, 0x96, 0x81, 0xeb, 0x8a, 0xa7]

def c40Fields : List BLT := [.bytes c40F0, .bytes c40F1, .bytes c40F2, .bytes c40F3, .bytes c40F4, .bytes c40F5, .bytes c40F6, .bytes c40F7, .bytes c40F8]

def c40Payload : Bytes := [0x80] ++ c40F0 ++ [0x84] ++ c40F1 ++ [0x82] ++ c40F2 ++ [0x94] ++ c40F3 ++ [0x88] ++ c40F4 ++ [0x80] ++ c40F5 ++ [] ++ c40F6 ++ [0xa0] ++ c40F7 ++ [0xa0] ++ c40F8

def c40Signed : Bytes := [0xf8, 0x6b] ++ c40Payload

def c40Tx : Tx := { nonce := 0, gas := 21000, value := 559631400000000000, data := c40F5, v := 38, r := c40F7, s := c40F8, type := .zero 3000000000 (some 0x54c82c81d2ad7a2becc4556ab1251b8833967ee1) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c40_literal : c40Signed = [0xf8, 0x6b, 0x80, 0x84, 0xb2, 0xd0, 0x5e, 0x00, 0x82, 0x52, 0x08, 0x94, 0x54, 0xc8, 0x2c, 0x81, 0xd2, 0xad, 0x7a, 0x2b, 0xec, 0xc4, 0x55, 0x6a, 0xb1, 0x25, 0x1b, 0x88, 0x33, 0x96, 0x7e, 0xe1, 0x88, 0x07, 0xc4, 0x35, 0xcb, 0x12, 0x27, 0x90, 0x00, 0x80, 0x26, 0xa0, 0xb1, 0x4a, 0xe7, 0xa0, 0x2d, 0xa8, 0xb1, 0xec, 0xb2, 0xc4, 0x23, 0x22, 0x83, 0x48, 0x08, 0xf3, 0x52, 0x48, 0xa8, 0xea, 0x17, 0x3d, 0xc9, 0xd3, 0xf4, 0x28, 0x0c, 0x2b, 0x47, 0x41, 0xcf, 0x94, 0xa0, 0x17, 0x94, 0xaa, 0x34, 0xd4, 0xa1, 0x79, 0x88, 0x5e, 0xe9, 0x4a, 0x8f, 0x5e, 0x47, 0xd7, 0x5b, 0x95, 0xb0, 0xc4, 0x9f, 0xd2, 0xac, 0xb7, 0x2e, 0x19, 0xee, 0x04, 0x96, 0x81, 0xeb, 0x8a, 0xa7] := by
  decide +kernel

theorem c40_payload_length : c40Payload.length = 107 := by
  decide +kernel

theorem c40_signed_length : c40Signed.length = 109 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c40_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c40Payload = some c40Fields := by
  unfold c40Payload c40Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c40F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c40F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c40F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c40F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c40F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c40F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c40_parse : c40Signed.toBLT? = some (.list c40Fields) := by
  have outer : Bytes.toBLTDiff? 109 c40Signed = some (.list c40Fields, []) := by
    simpa only [c40Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 108 107 c40Payload [] c40Fields
        (by rw [c40_payload_length]; decide +kernel) (c40_payload_parse 99)
  unfold Bytes.toBLT?
  rw [c40_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c40_decode :
    (c40Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c40Tx := by
  rw [c40_parse]
  decide +kernel

theorem c40_blt : c40Tx.toBLT = .list c40Fields := by
  norm_num only [c40Tx, c40Fields, c40F0, c40F1, c40F2, c40F3, c40F4, c40F6, c40F7, c40F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c40_encode0 : (BLT.bytes c40F0).toBytes = [0x80] ++ c40F0 := by
  unfold c40F0
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c40_encode1 : (BLT.bytes c40F1).toBytes = [0x84] ++ c40F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c40F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c40_encode2 : (BLT.bytes c40F2).toBytes = [0x82] ++ c40F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c40F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c40_encode3 : (BLT.bytes c40F3).toBytes = [0x94] ++ c40F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c40F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c40_encode4 : (BLT.bytes c40F4).toBytes = [0x88] ++ c40F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c40F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c40_encode5 : (BLT.bytes c40F5).toBytes = [0x80] ++ c40F5 := by
  unfold c40F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c40_encode6 : (BLT.bytes c40F6).toBytes = [] ++ c40F6 := by
  unfold c40F6
  rw [BLT.toBytes]
  decide +kernel

theorem c40_encode7 : (BLT.bytes c40F7).toBytes = [0xa0] ++ c40F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c40F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c40_encode8 : (BLT.bytes c40F8).toBytes = [0xa0] ++ c40F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c40F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c40_canonical : c40Tx.toBLT.toBytes = c40Signed := by
  have encoded : BLTs.toBytesJoin c40Fields = c40Payload := by
    simp only [c40Fields, BLTs.toBytesJoin,
      c40_encode0, c40_encode1, c40_encode2, c40_encode3, c40_encode4, c40_encode5, c40_encode6, c40_encode7, c40_encode8, c40Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c40_blt, BLT.toBytes, BLTs.toBytes, encoded, c40_payload_length]
  norm_num only [c40Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c41F0 : Bytes := []

def c41F1 : Bytes := [0xb2, 0xd0, 0x5e, 0x00]

def c41F2 : Bytes := [0x52, 0x08]

def c41F3 : Bytes := [0x43, 0x50, 0x8e, 0xeb, 0x8f, 0xca, 0x5b, 0x00, 0xd1, 0x24, 0xca, 0x22, 0xfb, 0xf1, 0x40, 0x05, 0x59, 0x98, 0x0c, 0x59]

def c41F4 : Bytes := [0x04, 0xe4, 0x80, 0xc1, 0xa3, 0x63, 0xa0, 0x00]

def c41F5 : Bytes := []

def c41F6 : Bytes := [0x26]

def c41F7 : Bytes := [0x18, 0x59, 0xb1, 0x73, 0x6b, 0xe1, 0xff, 0xd8, 0xf5, 0xab, 0x7e, 0xa3, 0xa0, 0x58, 0x6e, 0x6e, 0x2e, 0xde, 0xe4, 0x71, 0xd1, 0x33, 0x92, 0x1d, 0x25, 0x56, 0x38, 0x59, 0x41, 0x52, 0x9c, 0xe7]

def c41F8 : Bytes := [0x0c, 0x27, 0xca, 0xf1, 0xcb, 0x97, 0xca, 0x0c, 0xf8, 0x82, 0x90, 0x46, 0x2a, 0x8c, 0x31, 0xa9, 0xb5, 0xbd, 0x11, 0x16, 0xc9, 0x40, 0xe0, 0x42, 0x00, 0x06, 0x3b, 0xe7, 0xdd, 0x37, 0x71, 0xe5]

def c41Fields : List BLT := [.bytes c41F0, .bytes c41F1, .bytes c41F2, .bytes c41F3, .bytes c41F4, .bytes c41F5, .bytes c41F6, .bytes c41F7, .bytes c41F8]

def c41Payload : Bytes := [0x80] ++ c41F0 ++ [0x84] ++ c41F1 ++ [0x82] ++ c41F2 ++ [0x94] ++ c41F3 ++ [0x88] ++ c41F4 ++ [0x80] ++ c41F5 ++ [] ++ c41F6 ++ [0xa0] ++ c41F7 ++ [0xa0] ++ c41F8

def c41Signed : Bytes := [0xf8, 0x6b] ++ c41Payload

def c41Tx : Tx := { nonce := 0, gas := 21000, value := 352548240000000000, data := c41F5, v := 38, r := c41F7, s := c41F8, type := .zero 3000000000 (some 0x43508eeb8fca5b00d124ca22fbf1400559980c59) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c41_literal : c41Signed = [0xf8, 0x6b, 0x80, 0x84, 0xb2, 0xd0, 0x5e, 0x00, 0x82, 0x52, 0x08, 0x94, 0x43, 0x50, 0x8e, 0xeb, 0x8f, 0xca, 0x5b, 0x00, 0xd1, 0x24, 0xca, 0x22, 0xfb, 0xf1, 0x40, 0x05, 0x59, 0x98, 0x0c, 0x59, 0x88, 0x04, 0xe4, 0x80, 0xc1, 0xa3, 0x63, 0xa0, 0x00, 0x80, 0x26, 0xa0, 0x18, 0x59, 0xb1, 0x73, 0x6b, 0xe1, 0xff, 0xd8, 0xf5, 0xab, 0x7e, 0xa3, 0xa0, 0x58, 0x6e, 0x6e, 0x2e, 0xde, 0xe4, 0x71, 0xd1, 0x33, 0x92, 0x1d, 0x25, 0x56, 0x38, 0x59, 0x41, 0x52, 0x9c, 0xe7, 0xa0, 0x0c, 0x27, 0xca, 0xf1, 0xcb, 0x97, 0xca, 0x0c, 0xf8, 0x82, 0x90, 0x46, 0x2a, 0x8c, 0x31, 0xa9, 0xb5, 0xbd, 0x11, 0x16, 0xc9, 0x40, 0xe0, 0x42, 0x00, 0x06, 0x3b, 0xe7, 0xdd, 0x37, 0x71, 0xe5] := by
  decide +kernel

theorem c41_payload_length : c41Payload.length = 107 := by
  decide +kernel

theorem c41_signed_length : c41Signed.length = 109 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c41_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c41Payload = some c41Fields := by
  unfold c41Payload c41Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c41F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c41F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c41F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c41F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c41F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c41F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c41_parse : c41Signed.toBLT? = some (.list c41Fields) := by
  have outer : Bytes.toBLTDiff? 109 c41Signed = some (.list c41Fields, []) := by
    simpa only [c41Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 108 107 c41Payload [] c41Fields
        (by rw [c41_payload_length]; decide +kernel) (c41_payload_parse 99)
  unfold Bytes.toBLT?
  rw [c41_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c41_decode :
    (c41Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c41Tx := by
  rw [c41_parse]
  decide +kernel

theorem c41_blt : c41Tx.toBLT = .list c41Fields := by
  norm_num only [c41Tx, c41Fields, c41F0, c41F1, c41F2, c41F3, c41F4, c41F6, c41F7, c41F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c41_encode0 : (BLT.bytes c41F0).toBytes = [0x80] ++ c41F0 := by
  unfold c41F0
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c41_encode1 : (BLT.bytes c41F1).toBytes = [0x84] ++ c41F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c41F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c41_encode2 : (BLT.bytes c41F2).toBytes = [0x82] ++ c41F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c41F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c41_encode3 : (BLT.bytes c41F3).toBytes = [0x94] ++ c41F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c41F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c41_encode4 : (BLT.bytes c41F4).toBytes = [0x88] ++ c41F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c41F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c41_encode5 : (BLT.bytes c41F5).toBytes = [0x80] ++ c41F5 := by
  unfold c41F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c41_encode6 : (BLT.bytes c41F6).toBytes = [] ++ c41F6 := by
  unfold c41F6
  rw [BLT.toBytes]
  decide +kernel

theorem c41_encode7 : (BLT.bytes c41F7).toBytes = [0xa0] ++ c41F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c41F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c41_encode8 : (BLT.bytes c41F8).toBytes = [0xa0] ++ c41F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c41F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c41_canonical : c41Tx.toBLT.toBytes = c41Signed := by
  have encoded : BLTs.toBytesJoin c41Fields = c41Payload := by
    simp only [c41Fields, BLTs.toBytesJoin,
      c41_encode0, c41_encode1, c41_encode2, c41_encode3, c41_encode4, c41_encode5, c41_encode6, c41_encode7, c41_encode8, c41Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c41_blt, BLT.toBytes, BLTs.toBytes, encoded, c41_payload_length]
  norm_num only [c41Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c42F0 : Bytes := [0x09]

def c42F1 : Bytes := [0xb2, 0xd0, 0x5e, 0x00]

def c42F2 : Bytes := [0x52, 0x08]

def c42F3 : Bytes := [0xbd, 0x3e, 0xe2, 0xa6, 0xbe, 0x60, 0xd3, 0x38, 0xb1, 0xa4, 0xc8, 0x7c, 0x64, 0x0e, 0x73, 0x7b, 0xac, 0x52, 0xf9, 0x25]

def c42F4 : Bytes := [0x02, 0xc6, 0x8a, 0xf0, 0xbb, 0x14, 0x00, 0x00]

def c42F5 : Bytes := []

def c42F6 : Bytes := [0x25]

def c42F7 : Bytes := [0x1b, 0xef, 0xbd, 0x24, 0xd3, 0xb3, 0x25, 0x61, 0x84, 0xaf, 0x9f, 0x27, 0x83, 0x1f, 0x8c, 0xce, 0x57, 0x5d, 0xca, 0xa5, 0x75, 0x86, 0x39, 0xa6, 0x7f, 0xa6, 0xa9, 0xe4, 0x88, 0x2e, 0xa1, 0x74]

def c42F8 : Bytes := [0x0f, 0x95, 0x2d, 0x22, 0x86, 0xcb, 0x01, 0xfe, 0x97, 0x3d, 0xf1, 0x02, 0x18, 0x8c, 0xd2, 0x3b, 0xbb, 0xfa, 0xa7, 0x7e, 0x0b, 0x98, 0x3e, 0x5d, 0xab, 0x49, 0xd7, 0x67, 0xeb, 0xe4, 0x31, 0x3a]

def c42Fields : List BLT := [.bytes c42F0, .bytes c42F1, .bytes c42F2, .bytes c42F3, .bytes c42F4, .bytes c42F5, .bytes c42F6, .bytes c42F7, .bytes c42F8]

def c42Payload : Bytes := [] ++ c42F0 ++ [0x84] ++ c42F1 ++ [0x82] ++ c42F2 ++ [0x94] ++ c42F3 ++ [0x88] ++ c42F4 ++ [0x80] ++ c42F5 ++ [] ++ c42F6 ++ [0xa0] ++ c42F7 ++ [0xa0] ++ c42F8

def c42Signed : Bytes := [0xf8, 0x6b] ++ c42Payload

def c42Tx : Tx := { nonce := 9, gas := 21000, value := 200000000000000000, data := c42F5, v := 37, r := c42F7, s := c42F8, type := .zero 3000000000 (some 0xbd3ee2a6be60d338b1a4c87c640e737bac52f925) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c42_literal : c42Signed = [0xf8, 0x6b, 0x09, 0x84, 0xb2, 0xd0, 0x5e, 0x00, 0x82, 0x52, 0x08, 0x94, 0xbd, 0x3e, 0xe2, 0xa6, 0xbe, 0x60, 0xd3, 0x38, 0xb1, 0xa4, 0xc8, 0x7c, 0x64, 0x0e, 0x73, 0x7b, 0xac, 0x52, 0xf9, 0x25, 0x88, 0x02, 0xc6, 0x8a, 0xf0, 0xbb, 0x14, 0x00, 0x00, 0x80, 0x25, 0xa0, 0x1b, 0xef, 0xbd, 0x24, 0xd3, 0xb3, 0x25, 0x61, 0x84, 0xaf, 0x9f, 0x27, 0x83, 0x1f, 0x8c, 0xce, 0x57, 0x5d, 0xca, 0xa5, 0x75, 0x86, 0x39, 0xa6, 0x7f, 0xa6, 0xa9, 0xe4, 0x88, 0x2e, 0xa1, 0x74, 0xa0, 0x0f, 0x95, 0x2d, 0x22, 0x86, 0xcb, 0x01, 0xfe, 0x97, 0x3d, 0xf1, 0x02, 0x18, 0x8c, 0xd2, 0x3b, 0xbb, 0xfa, 0xa7, 0x7e, 0x0b, 0x98, 0x3e, 0x5d, 0xab, 0x49, 0xd7, 0x67, 0xeb, 0xe4, 0x31, 0x3a] := by
  decide +kernel

theorem c42_payload_length : c42Payload.length = 107 := by
  decide +kernel

theorem c42_signed_length : c42Signed.length = 109 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c42_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c42Payload = some c42Fields := by
  unfold c42Payload c42Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c42F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c42F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c42F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c42F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c42F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c42F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c42_parse : c42Signed.toBLT? = some (.list c42Fields) := by
  have outer : Bytes.toBLTDiff? 109 c42Signed = some (.list c42Fields, []) := by
    simpa only [c42Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 108 107 c42Payload [] c42Fields
        (by rw [c42_payload_length]; decide +kernel) (c42_payload_parse 99)
  unfold Bytes.toBLT?
  rw [c42_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c42_decode :
    (c42Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c42Tx := by
  rw [c42_parse]
  decide +kernel

theorem c42_blt : c42Tx.toBLT = .list c42Fields := by
  norm_num only [c42Tx, c42Fields, c42F0, c42F1, c42F2, c42F3, c42F4, c42F6, c42F7, c42F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c42_encode0 : (BLT.bytes c42F0).toBytes = [] ++ c42F0 := by
  unfold c42F0
  rw [BLT.toBytes]
  decide +kernel

theorem c42_encode1 : (BLT.bytes c42F1).toBytes = [0x84] ++ c42F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c42F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c42_encode2 : (BLT.bytes c42F2).toBytes = [0x82] ++ c42F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c42F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c42_encode3 : (BLT.bytes c42F3).toBytes = [0x94] ++ c42F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c42F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c42_encode4 : (BLT.bytes c42F4).toBytes = [0x88] ++ c42F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c42F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c42_encode5 : (BLT.bytes c42F5).toBytes = [0x80] ++ c42F5 := by
  unfold c42F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c42_encode6 : (BLT.bytes c42F6).toBytes = [] ++ c42F6 := by
  unfold c42F6
  rw [BLT.toBytes]
  decide +kernel

theorem c42_encode7 : (BLT.bytes c42F7).toBytes = [0xa0] ++ c42F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c42F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c42_encode8 : (BLT.bytes c42F8).toBytes = [0xa0] ++ c42F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c42F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c42_canonical : c42Tx.toBLT.toBytes = c42Signed := by
  have encoded : BLTs.toBytesJoin c42Fields = c42Payload := by
    simp only [c42Fields, BLTs.toBytesJoin,
      c42_encode0, c42_encode1, c42_encode2, c42_encode3, c42_encode4, c42_encode5, c42_encode6, c42_encode7, c42_encode8, c42Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c42_blt, BLT.toBytes, BLTs.toBytes, encoded, c42_payload_length]
  norm_num only [c42Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c43F0 : Bytes := [0x02, 0x00]

def c43F1 : Bytes := [0x95, 0x02, 0xf9, 0x00]

def c43F2 : Bytes := [0x02, 0x49, 0xf0]

def c43F3 : Bytes := [0x1d, 0x4c, 0xcc, 0x31, 0xda, 0xb6, 0xea, 0x20, 0xf4, 0x61, 0xd3, 0x29, 0xa0, 0x56, 0x2c, 0x1c, 0x58, 0x41, 0x25, 0x15]

def c43F4 : Bytes := []

def c43F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x62, 0xb0, 0x74, 0x60, 0x98, 0x37, 0x8f, 0x54, 0xb9, 0x40, 0xc5, 0x1d, 0xcf, 0xab, 0x31, 0x93, 0xae, 0xa5, 0x78, 0x59, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x4d, 0x11, 0x20, 0xd7, 0xb1, 0x60, 0x00, 0x00]

def c43F6 : Bytes := [0x26]

def c43F7 : Bytes := [0xf7, 0x98, 0x9f, 0x69, 0x6b, 0xde, 0xf0, 0x2e, 0x58, 0xd4, 0xd0, 0x2d, 0xcd, 0xee, 0x22, 0x43, 0x33, 0x9b, 0x10, 0x16, 0xc6, 0xbe, 0x60, 0x25, 0x50, 0x17, 0xb6, 0x71, 0xa1, 0x90, 0x71, 0xad]

def c43F8 : Bytes := [0x3f, 0x11, 0x9b, 0x95, 0x7a, 0x88, 0xca, 0x00, 0xb6, 0x45, 0xce, 0x3f, 0x84, 0x2c, 0x61, 0x31, 0xd3, 0x9f, 0xf9, 0x72, 0x09, 0x31, 0x46, 0x31, 0xc9, 0x32, 0x46, 0x70, 0xba, 0xf0, 0x84, 0xd6]

def c43Fields : List BLT := [.bytes c43F0, .bytes c43F1, .bytes c43F2, .bytes c43F3, .bytes c43F4, .bytes c43F5, .bytes c43F6, .bytes c43F7, .bytes c43F8]

def c43Payload : Bytes := [0x82] ++ c43F0 ++ [0x84] ++ c43F1 ++ [0x83] ++ c43F2 ++ [0x94] ++ c43F3 ++ [0x80] ++ c43F4 ++ [0xb8, 0x44] ++ c43F5 ++ [] ++ c43F6 ++ [0xa0] ++ c43F7 ++ [0xa0] ++ c43F8

def c43Signed : Bytes := [0xf8, 0xab] ++ c43Payload

def c43Tx : Tx := { nonce := 512, gas := 150000, value := 0, data := c43F5, v := 38, r := c43F7, s := c43F8, type := .zero 2500000000 (some 0x1d4ccc31dab6ea20f461d329a0562c1c58412515) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c43_literal : c43Signed = [0xf8, 0xab, 0x82, 0x02, 0x00, 0x84, 0x95, 0x02, 0xf9, 0x00, 0x83, 0x02, 0x49, 0xf0, 0x94, 0x1d, 0x4c, 0xcc, 0x31, 0xda, 0xb6, 0xea, 0x20, 0xf4, 0x61, 0xd3, 0x29, 0xa0, 0x56, 0x2c, 0x1c, 0x58, 0x41, 0x25, 0x15, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x62, 0xb0, 0x74, 0x60, 0x98, 0x37, 0x8f, 0x54, 0xb9, 0x40, 0xc5, 0x1d, 0xcf, 0xab, 0x31, 0x93, 0xae, 0xa5, 0x78, 0x59, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x4d, 0x11, 0x20, 0xd7, 0xb1, 0x60, 0x00, 0x00, 0x26, 0xa0, 0xf7, 0x98, 0x9f, 0x69, 0x6b, 0xde, 0xf0, 0x2e, 0x58, 0xd4, 0xd0, 0x2d, 0xcd, 0xee, 0x22, 0x43, 0x33, 0x9b, 0x10, 0x16, 0xc6, 0xbe, 0x60, 0x25, 0x50, 0x17, 0xb6, 0x71, 0xa1, 0x90, 0x71, 0xad, 0xa0, 0x3f, 0x11, 0x9b, 0x95, 0x7a, 0x88, 0xca, 0x00, 0xb6, 0x45, 0xce, 0x3f, 0x84, 0x2c, 0x61, 0x31, 0xd3, 0x9f, 0xf9, 0x72, 0x09, 0x31, 0x46, 0x31, 0xc9, 0x32, 0x46, 0x70, 0xba, 0xf0, 0x84, 0xd6] := by
  decide +kernel

theorem c43_payload_length : c43Payload.length = 171 := by
  decide +kernel

theorem c43_signed_length : c43Signed.length = 173 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c43_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c43Payload = some c43Fields := by
  unfold c43Payload c43Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c43F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c43F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c43F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c43F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c43F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c43F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c43F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c43_parse : c43Signed.toBLT? = some (.list c43Fields) := by
  have outer : Bytes.toBLTDiff? 173 c43Signed = some (.list c43Fields, []) := by
    simpa only [c43Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 172 171 c43Payload [] c43Fields
        (by rw [c43_payload_length]; decide +kernel) (c43_payload_parse 163)
  unfold Bytes.toBLT?
  rw [c43_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c43_decode :
    (c43Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c43Tx := by
  rw [c43_parse]
  decide +kernel

theorem c43_blt : c43Tx.toBLT = .list c43Fields := by
  norm_num only [c43Tx, c43Fields, c43F0, c43F1, c43F2, c43F3, c43F4, c43F6, c43F7, c43F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c43_encode0 : (BLT.bytes c43F0).toBytes = [0x82] ++ c43F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c43F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c43_encode1 : (BLT.bytes c43F1).toBytes = [0x84] ++ c43F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c43F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c43_encode2 : (BLT.bytes c43F2).toBytes = [0x83] ++ c43F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c43F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c43_encode3 : (BLT.bytes c43F3).toBytes = [0x94] ++ c43F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c43F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c43_encode4 : (BLT.bytes c43F4).toBytes = [0x80] ++ c43F4 := by
  unfold c43F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c43_encode5 : (BLT.bytes c43F5).toBytes = [0xb8, 0x44] ++ c43F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c43F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c43_encode6 : (BLT.bytes c43F6).toBytes = [] ++ c43F6 := by
  unfold c43F6
  rw [BLT.toBytes]
  decide +kernel

theorem c43_encode7 : (BLT.bytes c43F7).toBytes = [0xa0] ++ c43F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c43F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c43_encode8 : (BLT.bytes c43F8).toBytes = [0xa0] ++ c43F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c43F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c43_canonical : c43Tx.toBLT.toBytes = c43Signed := by
  have encoded : BLTs.toBytesJoin c43Fields = c43Payload := by
    simp only [c43Fields, BLTs.toBytesJoin,
      c43_encode0, c43_encode1, c43_encode2, c43_encode3, c43_encode4, c43_encode5, c43_encode6, c43_encode7, c43_encode8, c43Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c43_blt, BLT.toBytes, BLTs.toBytes, encoded, c43_payload_length]
  norm_num only [c43Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c44F0 : Bytes := [0x7d, 0x52]

def c44F1 : Bytes := [0x95, 0x02, 0xf9, 0x00]

def c44F2 : Bytes := [0x0e, 0x57, 0xe0]

def c44F3 : Bytes := [0x5c, 0xe2, 0xa5, 0x2c, 0x9f, 0x53, 0x5b, 0x5c, 0x84, 0x1b, 0x21, 0x10, 0x91, 0xd8, 0xe1, 0x53, 0x4c, 0x09, 0x01, 0x94]

def c44F4 : Bytes := [0x01, 0x63, 0x95, 0x15, 0xa9, 0x54, 0x2a, 0x00]

def c44F5 : Bytes := []

def c44F6 : Bytes := [0x26]

def c44F7 : Bytes := [0xce, 0xc7, 0xa8, 0x5a, 0x71, 0xec, 0xa5, 0xe9, 0xac, 0x15, 0x9e, 0x0a, 0xfa, 0x5b, 0x29, 0xf0, 0x3b, 0x75, 0x8f, 0x99, 0xb0, 0x40, 0x57, 0x2b, 0x9f, 0x7d, 0xc9, 0x27, 0x1f, 0xcf, 0x61, 0xb5]

def c44F8 : Bytes := [0x4e, 0x25, 0xf5, 0xa0, 0x9e, 0x04, 0x93, 0x10, 0x4d, 0x68, 0xfe, 0xa0, 0x69, 0x79, 0x82, 0xd1, 0x7e, 0x7b, 0xd2, 0x62, 0x92, 0x3d, 0x3b, 0xd7, 0xd6, 0x70, 0xda, 0xb2, 0xfa, 0x90, 0x05, 0x2f]

def c44Fields : List BLT := [.bytes c44F0, .bytes c44F1, .bytes c44F2, .bytes c44F3, .bytes c44F4, .bytes c44F5, .bytes c44F6, .bytes c44F7, .bytes c44F8]

def c44Payload : Bytes := [0x82] ++ c44F0 ++ [0x84] ++ c44F1 ++ [0x83] ++ c44F2 ++ [0x94] ++ c44F3 ++ [0x88] ++ c44F4 ++ [0x80] ++ c44F5 ++ [] ++ c44F6 ++ [0xa0] ++ c44F7 ++ [0xa0] ++ c44F8

def c44Signed : Bytes := [0xf8, 0x6e] ++ c44Payload

def c44Tx : Tx := { nonce := 32082, gas := 940000, value := 100087537000000000, data := c44F5, v := 38, r := c44F7, s := c44F8, type := .zero 2500000000 (some 0x5ce2a52c9f535b5c841b211091d8e1534c090194) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c44_literal : c44Signed = [0xf8, 0x6e, 0x82, 0x7d, 0x52, 0x84, 0x95, 0x02, 0xf9, 0x00, 0x83, 0x0e, 0x57, 0xe0, 0x94, 0x5c, 0xe2, 0xa5, 0x2c, 0x9f, 0x53, 0x5b, 0x5c, 0x84, 0x1b, 0x21, 0x10, 0x91, 0xd8, 0xe1, 0x53, 0x4c, 0x09, 0x01, 0x94, 0x88, 0x01, 0x63, 0x95, 0x15, 0xa9, 0x54, 0x2a, 0x00, 0x80, 0x26, 0xa0, 0xce, 0xc7, 0xa8, 0x5a, 0x71, 0xec, 0xa5, 0xe9, 0xac, 0x15, 0x9e, 0x0a, 0xfa, 0x5b, 0x29, 0xf0, 0x3b, 0x75, 0x8f, 0x99, 0xb0, 0x40, 0x57, 0x2b, 0x9f, 0x7d, 0xc9, 0x27, 0x1f, 0xcf, 0x61, 0xb5, 0xa0, 0x4e, 0x25, 0xf5, 0xa0, 0x9e, 0x04, 0x93, 0x10, 0x4d, 0x68, 0xfe, 0xa0, 0x69, 0x79, 0x82, 0xd1, 0x7e, 0x7b, 0xd2, 0x62, 0x92, 0x3d, 0x3b, 0xd7, 0xd6, 0x70, 0xda, 0xb2, 0xfa, 0x90, 0x05, 0x2f] := by
  decide +kernel

theorem c44_payload_length : c44Payload.length = 110 := by
  decide +kernel

theorem c44_signed_length : c44Signed.length = 112 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c44_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c44Payload = some c44Fields := by
  unfold c44Payload c44Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c44F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c44F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c44F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c44F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c44F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c44F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c44F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c44_parse : c44Signed.toBLT? = some (.list c44Fields) := by
  have outer : Bytes.toBLTDiff? 112 c44Signed = some (.list c44Fields, []) := by
    simpa only [c44Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 111 110 c44Payload [] c44Fields
        (by rw [c44_payload_length]; decide +kernel) (c44_payload_parse 102)
  unfold Bytes.toBLT?
  rw [c44_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c44_decode :
    (c44Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c44Tx := by
  rw [c44_parse]
  decide +kernel

theorem c44_blt : c44Tx.toBLT = .list c44Fields := by
  norm_num only [c44Tx, c44Fields, c44F0, c44F1, c44F2, c44F3, c44F4, c44F6, c44F7, c44F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c44_encode0 : (BLT.bytes c44F0).toBytes = [0x82] ++ c44F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c44F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c44_encode1 : (BLT.bytes c44F1).toBytes = [0x84] ++ c44F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c44F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c44_encode2 : (BLT.bytes c44F2).toBytes = [0x83] ++ c44F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c44F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c44_encode3 : (BLT.bytes c44F3).toBytes = [0x94] ++ c44F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c44F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c44_encode4 : (BLT.bytes c44F4).toBytes = [0x88] ++ c44F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c44F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c44_encode5 : (BLT.bytes c44F5).toBytes = [0x80] ++ c44F5 := by
  unfold c44F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c44_encode6 : (BLT.bytes c44F6).toBytes = [] ++ c44F6 := by
  unfold c44F6
  rw [BLT.toBytes]
  decide +kernel

theorem c44_encode7 : (BLT.bytes c44F7).toBytes = [0xa0] ++ c44F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c44F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c44_encode8 : (BLT.bytes c44F8).toBytes = [0xa0] ++ c44F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c44F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c44_canonical : c44Tx.toBLT.toBytes = c44Signed := by
  have encoded : BLTs.toBytesJoin c44Fields = c44Payload := by
    simp only [c44Fields, BLTs.toBytesJoin,
      c44_encode0, c44_encode1, c44_encode2, c44_encode3, c44_encode4, c44_encode5, c44_encode6, c44_encode7, c44_encode8, c44Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c44_blt, BLT.toBytes, BLTs.toBytes, encoded, c44_payload_length]
  norm_num only [c44Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c45F0 : Bytes := []

def c45F1 : Bytes := [0x95, 0x02, 0xf9, 0x00]

def c45F2 : Bytes := [0xb2, 0xbf]

def c45F3 : Bytes := [0xf9, 0x70, 0xb8, 0xe3, 0x6e, 0x23, 0xf7, 0xfc, 0x3f, 0xd7, 0x52, 0xee, 0xa8, 0x6f, 0x8b, 0xe8, 0xd8, 0x33, 0x75, 0xa6]

def c45F4 : Bytes := []

def c45F5 : Bytes := [0x09, 0x5e, 0xa7, 0xb3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xbb, 0xd6, 0x7a, 0x17, 0x2e, 0x17, 0xb9, 0xef, 0xf7, 0x16, 0xbf, 0x34, 0xf3, 0x05, 0x32, 0xdf, 0x26, 0xb5, 0xa9, 0xd7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x4f, 0xce, 0x5e, 0x3e, 0x25, 0x02, 0x61, 0x10, 0x00, 0x00, 0x00]

def c45F6 : Bytes := [0x26]

def c45F7 : Bytes := [0x2c, 0xa8, 0x3a, 0xf6, 0x4e, 0xdd, 0x2f, 0x27, 0xf9, 0x4b, 0x32, 0xb7, 0x7e, 0xe9, 0x6c, 0xe8, 0xb6, 0xbe, 0x38, 0x35, 0xba, 0x5e, 0x70, 0x35, 0x02, 0xe0, 0x91, 0x82, 0xaf, 0x3a, 0x94, 0xe6]

def c45F8 : Bytes := [0x07, 0xc8, 0xeb, 0xce, 0x5a, 0xf9, 0xf8, 0x71, 0xcc, 0xc8, 0x48, 0x07, 0x2d, 0xe2, 0x21, 0x59, 0x56, 0xa7, 0x0d, 0x00, 0x3f, 0x25, 0x38, 0x83, 0x1b, 0x4f, 0xb9, 0x60, 0xa5, 0x5c, 0x58, 0xba]

def c45Fields : List BLT := [.bytes c45F0, .bytes c45F1, .bytes c45F2, .bytes c45F3, .bytes c45F4, .bytes c45F5, .bytes c45F6, .bytes c45F7, .bytes c45F8]

def c45Payload : Bytes := [0x80] ++ c45F0 ++ [0x84] ++ c45F1 ++ [0x82] ++ c45F2 ++ [0x94] ++ c45F3 ++ [0x80] ++ c45F4 ++ [0xb8, 0x44] ++ c45F5 ++ [] ++ c45F6 ++ [0xa0] ++ c45F7 ++ [0xa0] ++ c45F8

def c45Signed : Bytes := [0xf8, 0xa8] ++ c45Payload

def c45Tx : Tx := { nonce := 0, gas := 45759, value := 0, data := c45F5, v := 38, r := c45F7, s := c45F8, type := .zero 2500000000 (some 0xf970b8e36e23f7fc3fd752eea86f8be8d83375a6) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c45_literal : c45Signed = [0xf8, 0xa8, 0x80, 0x84, 0x95, 0x02, 0xf9, 0x00, 0x82, 0xb2, 0xbf, 0x94, 0xf9, 0x70, 0xb8, 0xe3, 0x6e, 0x23, 0xf7, 0xfc, 0x3f, 0xd7, 0x52, 0xee, 0xa8, 0x6f, 0x8b, 0xe8, 0xd8, 0x33, 0x75, 0xa6, 0x80, 0xb8, 0x44, 0x09, 0x5e, 0xa7, 0xb3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xbb, 0xd6, 0x7a, 0x17, 0x2e, 0x17, 0xb9, 0xef, 0xf7, 0x16, 0xbf, 0x34, 0xf3, 0x05, 0x32, 0xdf, 0x26, 0xb5, 0xa9, 0xd7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x4f, 0xce, 0x5e, 0x3e, 0x25, 0x02, 0x61, 0x10, 0x00, 0x00, 0x00, 0x26, 0xa0, 0x2c, 0xa8, 0x3a, 0xf6, 0x4e, 0xdd, 0x2f, 0x27, 0xf9, 0x4b, 0x32, 0xb7, 0x7e, 0xe9, 0x6c, 0xe8, 0xb6, 0xbe, 0x38, 0x35, 0xba, 0x5e, 0x70, 0x35, 0x02, 0xe0, 0x91, 0x82, 0xaf, 0x3a, 0x94, 0xe6, 0xa0, 0x07, 0xc8, 0xeb, 0xce, 0x5a, 0xf9, 0xf8, 0x71, 0xcc, 0xc8, 0x48, 0x07, 0x2d, 0xe2, 0x21, 0x59, 0x56, 0xa7, 0x0d, 0x00, 0x3f, 0x25, 0x38, 0x83, 0x1b, 0x4f, 0xb9, 0x60, 0xa5, 0x5c, 0x58, 0xba] := by
  decide +kernel

theorem c45_payload_length : c45Payload.length = 168 := by
  decide +kernel

theorem c45_signed_length : c45Signed.length = 170 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c45_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c45Payload = some c45Fields := by
  unfold c45Payload c45Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c45F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c45F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c45F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c45F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c45F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c45F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c45_parse : c45Signed.toBLT? = some (.list c45Fields) := by
  have outer : Bytes.toBLTDiff? 170 c45Signed = some (.list c45Fields, []) := by
    simpa only [c45Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 169 168 c45Payload [] c45Fields
        (by rw [c45_payload_length]; decide +kernel) (c45_payload_parse 160)
  unfold Bytes.toBLT?
  rw [c45_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c45_decode :
    (c45Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c45Tx := by
  rw [c45_parse]
  decide +kernel

theorem c45_blt : c45Tx.toBLT = .list c45Fields := by
  norm_num only [c45Tx, c45Fields, c45F0, c45F1, c45F2, c45F3, c45F4, c45F6, c45F7, c45F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c45_encode0 : (BLT.bytes c45F0).toBytes = [0x80] ++ c45F0 := by
  unfold c45F0
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c45_encode1 : (BLT.bytes c45F1).toBytes = [0x84] ++ c45F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c45F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c45_encode2 : (BLT.bytes c45F2).toBytes = [0x82] ++ c45F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c45F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c45_encode3 : (BLT.bytes c45F3).toBytes = [0x94] ++ c45F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c45F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c45_encode4 : (BLT.bytes c45F4).toBytes = [0x80] ++ c45F4 := by
  unfold c45F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c45_encode5 : (BLT.bytes c45F5).toBytes = [0xb8, 0x44] ++ c45F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c45F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c45_encode6 : (BLT.bytes c45F6).toBytes = [] ++ c45F6 := by
  unfold c45F6
  rw [BLT.toBytes]
  decide +kernel

theorem c45_encode7 : (BLT.bytes c45F7).toBytes = [0xa0] ++ c45F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c45F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c45_encode8 : (BLT.bytes c45F8).toBytes = [0xa0] ++ c45F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c45F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c45_canonical : c45Tx.toBLT.toBytes = c45Signed := by
  have encoded : BLTs.toBytesJoin c45Fields = c45Payload := by
    simp only [c45Fields, BLTs.toBytesJoin,
      c45_encode0, c45_encode1, c45_encode2, c45_encode3, c45_encode4, c45_encode5, c45_encode6, c45_encode7, c45_encode8, c45Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c45_blt, BLT.toBytes, BLTs.toBytes, encoded, c45_payload_length]
  norm_num only [c45Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c46F0 : Bytes := [0x01, 0x07, 0x45]

def c46F1 : Bytes := [0x95, 0x02, 0xf9, 0x00]

def c46F2 : Bytes := [0x52, 0x08]

def c46F3 : Bytes := [0x7a, 0x44, 0x3b, 0x66, 0x7e, 0x7c, 0x4f, 0x76, 0x15, 0xd7, 0x4f, 0xb7, 0x96, 0xc0, 0x4b, 0x90, 0xa6, 0x36, 0x05, 0xec]

def c46F4 : Bytes := [0x67, 0x86, 0xac, 0xf4, 0xc1, 0x40, 0x00]

def c46F5 : Bytes := []

def c46F6 : Bytes := [0x25]

def c46F7 : Bytes := [0x8a, 0x41, 0x7e, 0x45, 0x24, 0xa7, 0x09, 0xef, 0x2c, 0x1e, 0x39, 0x5b, 0x96, 0xab, 0xb2, 0x20, 0xcc, 0xd9, 0x2a, 0xfd, 0xa1, 0xc6, 0xd0, 0xa3, 0x47, 0x02, 0x3d, 0x52, 0x86, 0x8c, 0x36, 0x70]

def c46F8 : Bytes := [0x4c, 0xf4, 0xa8, 0x39, 0x68, 0xc5, 0xff, 0xef, 0x1a, 0x28, 0x8a, 0x7d, 0x8c, 0x3e, 0x9d, 0x42, 0x69, 0x66, 0x94, 0x67, 0xfa, 0x91, 0xb7, 0x93, 0x10, 0x60, 0xb7, 0xed, 0x0a, 0x1f, 0x2c, 0xdc]

def c46Fields : List BLT := [.bytes c46F0, .bytes c46F1, .bytes c46F2, .bytes c46F3, .bytes c46F4, .bytes c46F5, .bytes c46F6, .bytes c46F7, .bytes c46F8]

def c46Payload : Bytes := [0x83] ++ c46F0 ++ [0x84] ++ c46F1 ++ [0x82] ++ c46F2 ++ [0x94] ++ c46F3 ++ [0x87] ++ c46F4 ++ [0x80] ++ c46F5 ++ [] ++ c46F6 ++ [0xa0] ++ c46F7 ++ [0xa0] ++ c46F8

def c46Signed : Bytes := [0xf8, 0x6d] ++ c46Payload

def c46Tx : Tx := { nonce := 67397, gas := 21000, value := 29140000000000000, data := c46F5, v := 37, r := c46F7, s := c46F8, type := .zero 2500000000 (some 0x7a443b667e7c4f7615d74fb796c04b90a63605ec) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c46_literal : c46Signed = [0xf8, 0x6d, 0x83, 0x01, 0x07, 0x45, 0x84, 0x95, 0x02, 0xf9, 0x00, 0x82, 0x52, 0x08, 0x94, 0x7a, 0x44, 0x3b, 0x66, 0x7e, 0x7c, 0x4f, 0x76, 0x15, 0xd7, 0x4f, 0xb7, 0x96, 0xc0, 0x4b, 0x90, 0xa6, 0x36, 0x05, 0xec, 0x87, 0x67, 0x86, 0xac, 0xf4, 0xc1, 0x40, 0x00, 0x80, 0x25, 0xa0, 0x8a, 0x41, 0x7e, 0x45, 0x24, 0xa7, 0x09, 0xef, 0x2c, 0x1e, 0x39, 0x5b, 0x96, 0xab, 0xb2, 0x20, 0xcc, 0xd9, 0x2a, 0xfd, 0xa1, 0xc6, 0xd0, 0xa3, 0x47, 0x02, 0x3d, 0x52, 0x86, 0x8c, 0x36, 0x70, 0xa0, 0x4c, 0xf4, 0xa8, 0x39, 0x68, 0xc5, 0xff, 0xef, 0x1a, 0x28, 0x8a, 0x7d, 0x8c, 0x3e, 0x9d, 0x42, 0x69, 0x66, 0x94, 0x67, 0xfa, 0x91, 0xb7, 0x93, 0x10, 0x60, 0xb7, 0xed, 0x0a, 0x1f, 0x2c, 0xdc] := by
  decide +kernel

theorem c46_payload_length : c46Payload.length = 109 := by
  decide +kernel

theorem c46_signed_length : c46Signed.length = 111 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c46_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c46Payload = some c46Fields := by
  unfold c46Payload c46Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c46F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c46F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c46F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c46F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 7 c46F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c46F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c46F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c46_parse : c46Signed.toBLT? = some (.list c46Fields) := by
  have outer : Bytes.toBLTDiff? 111 c46Signed = some (.list c46Fields, []) := by
    simpa only [c46Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 110 109 c46Payload [] c46Fields
        (by rw [c46_payload_length]; decide +kernel) (c46_payload_parse 101)
  unfold Bytes.toBLT?
  rw [c46_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c46_decode :
    (c46Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c46Tx := by
  rw [c46_parse]
  decide +kernel

theorem c46_blt : c46Tx.toBLT = .list c46Fields := by
  norm_num only [c46Tx, c46Fields, c46F0, c46F1, c46F2, c46F3, c46F4, c46F6, c46F7, c46F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c46_encode0 : (BLT.bytes c46F0).toBytes = [0x83] ++ c46F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c46F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c46_encode1 : (BLT.bytes c46F1).toBytes = [0x84] ++ c46F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c46F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c46_encode2 : (BLT.bytes c46F2).toBytes = [0x82] ++ c46F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c46F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c46_encode3 : (BLT.bytes c46F3).toBytes = [0x94] ++ c46F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c46F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c46_encode4 : (BLT.bytes c46F4).toBytes = [0x87] ++ c46F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c46F4.length = 7 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c46_encode5 : (BLT.bytes c46F5).toBytes = [0x80] ++ c46F5 := by
  unfold c46F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c46_encode6 : (BLT.bytes c46F6).toBytes = [] ++ c46F6 := by
  unfold c46F6
  rw [BLT.toBytes]
  decide +kernel

theorem c46_encode7 : (BLT.bytes c46F7).toBytes = [0xa0] ++ c46F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c46F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c46_encode8 : (BLT.bytes c46F8).toBytes = [0xa0] ++ c46F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c46F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c46_canonical : c46Tx.toBLT.toBytes = c46Signed := by
  have encoded : BLTs.toBytesJoin c46Fields = c46Payload := by
    simp only [c46Fields, BLTs.toBytesJoin,
      c46_encode0, c46_encode1, c46_encode2, c46_encode3, c46_encode4, c46_encode5, c46_encode6, c46_encode7, c46_encode8, c46Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c46_blt, BLT.toBytes, BLTs.toBytes, encoded, c46_payload_length]
  norm_num only [c46Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c47F0 : Bytes := [0x01, 0x21]

def c47F1 : Bytes := [0x89, 0x17, 0x37, 0x00]

def c47F2 : Bytes := [0x52, 0x08]

def c47F3 : Bytes := [0x30, 0x1d, 0x18, 0xac, 0x55, 0x5d, 0xd9, 0x89, 0x74, 0xd9, 0xde, 0x74, 0x2d, 0x06, 0xe1, 0x42, 0xb3, 0x30, 0x63, 0x4a]

def c47F4 : Bytes := [0x02, 0xd7, 0x98, 0x83, 0xd2, 0x00, 0x00]

def c47F5 : Bytes := []

def c47F6 : Bytes := [0x26]

def c47F7 : Bytes := [0xe6, 0xde, 0x2f, 0x1f, 0x24, 0x42, 0x11, 0x00, 0xdc, 0x97, 0xc3, 0x87, 0x5d, 0xb1, 0xbc, 0x76, 0x6f, 0xed, 0x5a, 0xed, 0xf3, 0x29, 0x78, 0xfd, 0x6b, 0x8c, 0xdb, 0x9e, 0xd6, 0x46, 0xa5, 0x55]

def c47F8 : Bytes := [0x75, 0xe3, 0x54, 0x55, 0x08, 0xab, 0x92, 0xd0, 0x7f, 0x95, 0x61, 0x72, 0xab, 0xa6, 0xd1, 0xfc, 0x8b, 0x98, 0x97, 0x6b, 0x03, 0x93, 0x90, 0x24, 0x3a, 0x92, 0x04, 0x55, 0x6e, 0xcf, 0x42, 0x72]

def c47Fields : List BLT := [.bytes c47F0, .bytes c47F1, .bytes c47F2, .bytes c47F3, .bytes c47F4, .bytes c47F5, .bytes c47F6, .bytes c47F7, .bytes c47F8]

def c47Payload : Bytes := [0x82] ++ c47F0 ++ [0x84] ++ c47F1 ++ [0x82] ++ c47F2 ++ [0x94] ++ c47F3 ++ [0x87] ++ c47F4 ++ [0x80] ++ c47F5 ++ [] ++ c47F6 ++ [0xa0] ++ c47F7 ++ [0xa0] ++ c47F8

def c47Signed : Bytes := [0xf8, 0x6c] ++ c47Payload

def c47Tx : Tx := { nonce := 289, gas := 21000, value := 800000000000000, data := c47F5, v := 38, r := c47F7, s := c47F8, type := .zero 2300000000 (some 0x301d18ac555dd98974d9de742d06e142b330634a) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c47_literal : c47Signed = [0xf8, 0x6c, 0x82, 0x01, 0x21, 0x84, 0x89, 0x17, 0x37, 0x00, 0x82, 0x52, 0x08, 0x94, 0x30, 0x1d, 0x18, 0xac, 0x55, 0x5d, 0xd9, 0x89, 0x74, 0xd9, 0xde, 0x74, 0x2d, 0x06, 0xe1, 0x42, 0xb3, 0x30, 0x63, 0x4a, 0x87, 0x02, 0xd7, 0x98, 0x83, 0xd2, 0x00, 0x00, 0x80, 0x26, 0xa0, 0xe6, 0xde, 0x2f, 0x1f, 0x24, 0x42, 0x11, 0x00, 0xdc, 0x97, 0xc3, 0x87, 0x5d, 0xb1, 0xbc, 0x76, 0x6f, 0xed, 0x5a, 0xed, 0xf3, 0x29, 0x78, 0xfd, 0x6b, 0x8c, 0xdb, 0x9e, 0xd6, 0x46, 0xa5, 0x55, 0xa0, 0x75, 0xe3, 0x54, 0x55, 0x08, 0xab, 0x92, 0xd0, 0x7f, 0x95, 0x61, 0x72, 0xab, 0xa6, 0xd1, 0xfc, 0x8b, 0x98, 0x97, 0x6b, 0x03, 0x93, 0x90, 0x24, 0x3a, 0x92, 0x04, 0x55, 0x6e, 0xcf, 0x42, 0x72] := by
  decide +kernel

theorem c47_payload_length : c47Payload.length = 108 := by
  decide +kernel

theorem c47_signed_length : c47Signed.length = 110 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c47_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c47Payload = some c47Fields := by
  unfold c47Payload c47Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c47F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 c47F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c47F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c47F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 7 c47F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c47F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c47F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c47_parse : c47Signed.toBLT? = some (.list c47Fields) := by
  have outer : Bytes.toBLTDiff? 110 c47Signed = some (.list c47Fields, []) := by
    simpa only [c47Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 109 108 c47Payload [] c47Fields
        (by rw [c47_payload_length]; decide +kernel) (c47_payload_parse 100)
  unfold Bytes.toBLT?
  rw [c47_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c47_decode :
    (c47Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c47Tx := by
  rw [c47_parse]
  decide +kernel

theorem c47_blt : c47Tx.toBLT = .list c47Fields := by
  norm_num only [c47Tx, c47Fields, c47F0, c47F1, c47F2, c47F3, c47F4, c47F6, c47F7, c47F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c47_encode0 : (BLT.bytes c47F0).toBytes = [0x82] ++ c47F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c47F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c47_encode1 : (BLT.bytes c47F1).toBytes = [0x84] ++ c47F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c47F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c47_encode2 : (BLT.bytes c47F2).toBytes = [0x82] ++ c47F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c47F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c47_encode3 : (BLT.bytes c47F3).toBytes = [0x94] ++ c47F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c47F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c47_encode4 : (BLT.bytes c47F4).toBytes = [0x87] ++ c47F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c47F4.length = 7 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c47_encode5 : (BLT.bytes c47F5).toBytes = [0x80] ++ c47F5 := by
  unfold c47F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c47_encode6 : (BLT.bytes c47F6).toBytes = [] ++ c47F6 := by
  unfold c47F6
  rw [BLT.toBytes]
  decide +kernel

theorem c47_encode7 : (BLT.bytes c47F7).toBytes = [0xa0] ++ c47F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c47F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c47_encode8 : (BLT.bytes c47F8).toBytes = [0xa0] ++ c47F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c47F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c47_canonical : c47Tx.toBLT.toBytes = c47Signed := by
  have encoded : BLTs.toBytesJoin c47Fields = c47Payload := by
    simp only [c47Fields, BLTs.toBytesJoin,
      c47_encode0, c47_encode1, c47_encode2, c47_encode3, c47_encode4, c47_encode5, c47_encode6, c47_encode7, c47_encode8, c47Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c47_blt, BLT.toBytes, BLTs.toBytes, encoded, c47_payload_length]
  norm_num only [c47Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
