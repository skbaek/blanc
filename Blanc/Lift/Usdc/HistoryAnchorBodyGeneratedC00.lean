import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def c00F0 : Bytes := [0x01, 0xaa]

def c00F1 : Bytes := [0x17, 0x48, 0x76, 0xe8, 0x00]

def c00F2 : Bytes := [0x01, 0x11, 0x70]

def c00F3 : Bytes := [0xff, 0xe0, 0x2e, 0xe4, 0xc6, 0x9e, 0xdf, 0x1b, 0x34, 0x0f, 0xca, 0xd6, 0x4f, 0xbd, 0x6b, 0x37, 0xa7, 0xb9, 0xe2, 0x65]

def c00F4 : Bytes := []

def c00F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8c, 0x51, 0x42, 0x51, 0x45, 0x31, 0x43, 0x2d, 0x17, 0x91, 0x69, 0xcd, 0xa9, 0x24, 0x16, 0x45, 0xf6, 0x75, 0x27, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2e, 0x90, 0xed, 0xd0, 0x00]

def c00F6 : Bytes := [0x1b]

def c00F7 : Bytes := [0x0e, 0xab, 0x28, 0x31, 0x59, 0x6e, 0x62, 0xa6, 0x66, 0xc8, 0x7c, 0xd7, 0xb4, 0xab, 0x25, 0x25, 0x5d, 0x59, 0xee, 0x93, 0x12, 0x53, 0x76, 0x98, 0x9c, 0x81, 0x38, 0x3e, 0xe1, 0xaf, 0x43, 0xc7]

def c00F8 : Bytes := [0x78, 0xd8, 0x8c, 0xc9, 0xcd, 0x1c, 0x9f, 0xdf, 0xa1, 0xa9, 0xcc, 0x0c, 0x03, 0x6d, 0x61, 0x04, 0xbf, 0xcc, 0xa0, 0xa0, 0x00, 0x0d, 0x44, 0x73, 0x45, 0x87, 0xb6, 0x1a, 0xc5, 0xe4, 0x7a, 0xfa]

def c00Fields : List BLT := [.bytes c00F0, .bytes c00F1, .bytes c00F2, .bytes c00F3, .bytes c00F4, .bytes c00F5, .bytes c00F6, .bytes c00F7, .bytes c00F8]

def c00Payload : Bytes := [0x82] ++ c00F0 ++ [0x85] ++ c00F1 ++ [0x83] ++ c00F2 ++ [0x94] ++ c00F3 ++ [0x80] ++ c00F4 ++ [0xb8, 0x44] ++ c00F5 ++ [] ++ c00F6 ++ [0xa0] ++ c00F7 ++ [0xa0] ++ c00F8

def c00Signed : Bytes := [0xf8, 0xac] ++ c00Payload

def c00Tx : Tx := { nonce := 426, gas := 70000, value := 0, data := c00F5, v := 27, r := c00F7, s := c00F8, type := .zero 100000000000 (some 0xffe02ee4c69edf1b340fcad64fbd6b37a7b9e265) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c00_literal : c00Signed = [0xf8, 0xac, 0x82, 0x01, 0xaa, 0x85, 0x17, 0x48, 0x76, 0xe8, 0x00, 0x83, 0x01, 0x11, 0x70, 0x94, 0xff, 0xe0, 0x2e, 0xe4, 0xc6, 0x9e, 0xdf, 0x1b, 0x34, 0x0f, 0xca, 0xd6, 0x4f, 0xbd, 0x6b, 0x37, 0xa7, 0xb9, 0xe2, 0x65, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8c, 0x51, 0x42, 0x51, 0x45, 0x31, 0x43, 0x2d, 0x17, 0x91, 0x69, 0xcd, 0xa9, 0x24, 0x16, 0x45, 0xf6, 0x75, 0x27, 0x82, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2e, 0x90, 0xed, 0xd0, 0x00, 0x1b, 0xa0, 0x0e, 0xab, 0x28, 0x31, 0x59, 0x6e, 0x62, 0xa6, 0x66, 0xc8, 0x7c, 0xd7, 0xb4, 0xab, 0x25, 0x25, 0x5d, 0x59, 0xee, 0x93, 0x12, 0x53, 0x76, 0x98, 0x9c, 0x81, 0x38, 0x3e, 0xe1, 0xaf, 0x43, 0xc7, 0xa0, 0x78, 0xd8, 0x8c, 0xc9, 0xcd, 0x1c, 0x9f, 0xdf, 0xa1, 0xa9, 0xcc, 0x0c, 0x03, 0x6d, 0x61, 0x04, 0xbf, 0xcc, 0xa0, 0xa0, 0x00, 0x0d, 0x44, 0x73, 0x45, 0x87, 0xb6, 0x1a, 0xc5, 0xe4, 0x7a, 0xfa] := by
  decide +kernel

theorem c00_payload_length : c00Payload.length = 172 := by
  decide +kernel

theorem c00_signed_length : c00Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c00_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c00Payload = some c00Fields := by
  unfold c00Payload c00Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c00F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c00F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c00F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c00F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c00F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c00F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c00F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c00_parse : c00Signed.toBLT? = some (.list c00Fields) := by
  have outer : Bytes.toBLTDiff? 174 c00Signed = some (.list c00Fields, []) := by
    simpa only [c00Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 c00Payload [] c00Fields
        (by rw [c00_payload_length]; decide +kernel) (c00_payload_parse 164)
  unfold Bytes.toBLT?
  rw [c00_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c00_decode :
    (c00Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c00Tx := by
  rw [c00_parse]
  decide +kernel

theorem c00_blt : c00Tx.toBLT = .list c00Fields := by
  norm_num only [c00Tx, c00Fields, c00F0, c00F1, c00F2, c00F3, c00F4, c00F6, c00F7, c00F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c00_encode0 : (BLT.bytes c00F0).toBytes = [0x82] ++ c00F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c00F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c00_encode1 : (BLT.bytes c00F1).toBytes = [0x85] ++ c00F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c00F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c00_encode2 : (BLT.bytes c00F2).toBytes = [0x83] ++ c00F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c00F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c00_encode3 : (BLT.bytes c00F3).toBytes = [0x94] ++ c00F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c00F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c00_encode4 : (BLT.bytes c00F4).toBytes = [0x80] ++ c00F4 := by
  unfold c00F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c00_encode5 : (BLT.bytes c00F5).toBytes = [0xb8, 0x44] ++ c00F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c00F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c00_encode6 : (BLT.bytes c00F6).toBytes = [] ++ c00F6 := by
  unfold c00F6
  rw [BLT.toBytes]
  decide +kernel

theorem c00_encode7 : (BLT.bytes c00F7).toBytes = [0xa0] ++ c00F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c00F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c00_encode8 : (BLT.bytes c00F8).toBytes = [0xa0] ++ c00F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c00F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c00_canonical : c00Tx.toBLT.toBytes = c00Signed := by
  have encoded : BLTs.toBytesJoin c00Fields = c00Payload := by
    simp only [c00Fields, BLTs.toBytesJoin,
      c00_encode0, c00_encode1, c00_encode2, c00_encode3, c00_encode4, c00_encode5, c00_encode6, c00_encode7, c00_encode8, c00Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c00_blt, BLT.toBytes, BLTs.toBytes, encoded, c00_payload_length]
  norm_num only [c00Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c01F0 : Bytes := [0x51, 0xe7]

def c01F1 : Bytes := [0x15, 0x30, 0x05, 0xce, 0x00]

def c01F2 : Bytes := [0x52, 0x08]

def c01F3 : Bytes := [0xbc, 0xcd, 0x28, 0x89, 0xd1, 0x56, 0x91, 0x1d, 0x87, 0x05, 0x73, 0x66, 0xf3, 0xc3, 0xb4, 0xcd, 0x7b, 0x8a, 0x95, 0x61]

def c01F4 : Bytes := [0x5b, 0x30, 0x18, 0xc9, 0x7d, 0x1b, 0x7c, 0x00]

def c01F5 : Bytes := []

def c01F6 : Bytes := [0x1b]

def c01F7 : Bytes := [0x17, 0xb5, 0x54, 0x32, 0x25, 0x39, 0x86, 0x77, 0xe6, 0x7d, 0x66, 0xf9, 0x45, 0x80, 0xd6, 0x15, 0x7d, 0xa8, 0xaa, 0x2c, 0x83, 0x89, 0x48, 0xb6, 0x99, 0x49, 0xdd, 0x65, 0x3f, 0x8b, 0x7b, 0x23]

def c01F8 : Bytes := [0x37, 0x5e, 0xef, 0xb2, 0x32, 0x57, 0x87, 0x13, 0xe2, 0x91, 0x07, 0xfd, 0x9c, 0x84, 0x17, 0xf1, 0x54, 0x3b, 0x43, 0xfe, 0x27, 0xe8, 0x84, 0x66, 0xb2, 0x17, 0x18, 0x5c, 0xb7, 0x69, 0x2f, 0x61]

def c01Fields : List BLT := [.bytes c01F0, .bytes c01F1, .bytes c01F2, .bytes c01F3, .bytes c01F4, .bytes c01F5, .bytes c01F6, .bytes c01F7, .bytes c01F8]

def c01Payload : Bytes := [0x82] ++ c01F0 ++ [0x85] ++ c01F1 ++ [0x82] ++ c01F2 ++ [0x94] ++ c01F3 ++ [0x88] ++ c01F4 ++ [0x80] ++ c01F5 ++ [] ++ c01F6 ++ [0xa0] ++ c01F7 ++ [0xa0] ++ c01F8

def c01Signed : Bytes := [0xf8, 0x6e] ++ c01Payload

def c01Tx : Tx := { nonce := 20967, gas := 21000, value := 6570779110000000000, data := c01F5, v := 27, r := c01F7, s := c01F8, type := .zero 91000000000 (some 0xbccd2889d156911d87057366f3c3b4cd7b8a9561) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c01_literal : c01Signed = [0xf8, 0x6e, 0x82, 0x51, 0xe7, 0x85, 0x15, 0x30, 0x05, 0xce, 0x00, 0x82, 0x52, 0x08, 0x94, 0xbc, 0xcd, 0x28, 0x89, 0xd1, 0x56, 0x91, 0x1d, 0x87, 0x05, 0x73, 0x66, 0xf3, 0xc3, 0xb4, 0xcd, 0x7b, 0x8a, 0x95, 0x61, 0x88, 0x5b, 0x30, 0x18, 0xc9, 0x7d, 0x1b, 0x7c, 0x00, 0x80, 0x1b, 0xa0, 0x17, 0xb5, 0x54, 0x32, 0x25, 0x39, 0x86, 0x77, 0xe6, 0x7d, 0x66, 0xf9, 0x45, 0x80, 0xd6, 0x15, 0x7d, 0xa8, 0xaa, 0x2c, 0x83, 0x89, 0x48, 0xb6, 0x99, 0x49, 0xdd, 0x65, 0x3f, 0x8b, 0x7b, 0x23, 0xa0, 0x37, 0x5e, 0xef, 0xb2, 0x32, 0x57, 0x87, 0x13, 0xe2, 0x91, 0x07, 0xfd, 0x9c, 0x84, 0x17, 0xf1, 0x54, 0x3b, 0x43, 0xfe, 0x27, 0xe8, 0x84, 0x66, 0xb2, 0x17, 0x18, 0x5c, 0xb7, 0x69, 0x2f, 0x61] := by
  decide +kernel

theorem c01_payload_length : c01Payload.length = 110 := by
  decide +kernel

theorem c01_signed_length : c01Signed.length = 112 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c01_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c01Payload = some c01Fields := by
  unfold c01Payload c01Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c01F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c01F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c01F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c01F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c01F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c01F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c01F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c01_parse : c01Signed.toBLT? = some (.list c01Fields) := by
  have outer : Bytes.toBLTDiff? 112 c01Signed = some (.list c01Fields, []) := by
    simpa only [c01Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 111 110 c01Payload [] c01Fields
        (by rw [c01_payload_length]; decide +kernel) (c01_payload_parse 102)
  unfold Bytes.toBLT?
  rw [c01_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c01_decode :
    (c01Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c01Tx := by
  rw [c01_parse]
  decide +kernel

theorem c01_blt : c01Tx.toBLT = .list c01Fields := by
  norm_num only [c01Tx, c01Fields, c01F0, c01F1, c01F2, c01F3, c01F4, c01F6, c01F7, c01F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c01_encode0 : (BLT.bytes c01F0).toBytes = [0x82] ++ c01F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c01F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c01_encode1 : (BLT.bytes c01F1).toBytes = [0x85] ++ c01F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c01F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c01_encode2 : (BLT.bytes c01F2).toBytes = [0x82] ++ c01F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c01F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c01_encode3 : (BLT.bytes c01F3).toBytes = [0x94] ++ c01F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c01F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c01_encode4 : (BLT.bytes c01F4).toBytes = [0x88] ++ c01F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c01F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c01_encode5 : (BLT.bytes c01F5).toBytes = [0x80] ++ c01F5 := by
  unfold c01F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c01_encode6 : (BLT.bytes c01F6).toBytes = [] ++ c01F6 := by
  unfold c01F6
  rw [BLT.toBytes]
  decide +kernel

theorem c01_encode7 : (BLT.bytes c01F7).toBytes = [0xa0] ++ c01F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c01F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c01_encode8 : (BLT.bytes c01F8).toBytes = [0xa0] ++ c01F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c01F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c01_canonical : c01Tx.toBLT.toBytes = c01Signed := by
  have encoded : BLTs.toBytesJoin c01Fields = c01Payload := by
    simp only [c01Fields, BLTs.toBytesJoin,
      c01_encode0, c01_encode1, c01_encode2, c01_encode3, c01_encode4, c01_encode5, c01_encode6, c01_encode7, c01_encode8, c01Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c01_blt, BLT.toBytes, BLTs.toBytes, encoded, c01_payload_length]
  norm_num only [c01Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c02F0 : Bytes := []

def c02F1 : Bytes := [0x12, 0xa0, 0x5f, 0x20, 0x00]

def c02F2 : Bytes := [0x01, 0x9a, 0x28]

def c02F3 : Bytes := [0x2d, 0x0e, 0x95, 0xbd, 0x47, 0x95, 0xd7, 0xac, 0xe0, 0xda, 0x3c, 0x0f, 0xf7, 0xb7, 0x06, 0xa5, 0x97, 0x0e, 0xb9, 0xd3]

def c02F4 : Bytes := []

def c02F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x6c, 0xc5, 0xf6, 0x88, 0xa3, 0x15, 0xf3, 0xdc, 0x28, 0xa7, 0x78, 0x17, 0x17, 0xa9, 0xa7, 0x98, 0xa5, 0x9f, 0xda, 0x7b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x06, 0x0b, 0x5f, 0x93, 0x3f, 0x68, 0x0d, 0xff, 0xff]

def c02F6 : Bytes := [0x1b]

def c02F7 : Bytes := [0xcf, 0xab, 0x8e, 0x92, 0xdf, 0x7b, 0x40, 0x00, 0x26, 0x76, 0xc7, 0xf2, 0x51, 0xaa, 0x66, 0xbd, 0x12, 0x32, 0x10, 0xdf, 0xe8, 0xca, 0x0c, 0xd3, 0x46, 0xf9, 0x35, 0x65, 0xcf, 0xac, 0x48, 0x9e]

def c02F8 : Bytes := [0x63, 0xc7, 0xaa, 0xcb, 0x37, 0x8b, 0xc8, 0xa0, 0xb3, 0x54, 0x34, 0x9a, 0x5f, 0x4d, 0xc4, 0xf8, 0xc7, 0xc8, 0x39, 0xe1, 0x52, 0x2c, 0x02, 0xe2, 0xc7, 0x4e, 0xff, 0xb3, 0x8f, 0x98, 0x82, 0xc6]

def c02Fields : List BLT := [.bytes c02F0, .bytes c02F1, .bytes c02F2, .bytes c02F3, .bytes c02F4, .bytes c02F5, .bytes c02F6, .bytes c02F7, .bytes c02F8]

def c02Payload : Bytes := [0x80] ++ c02F0 ++ [0x85] ++ c02F1 ++ [0x83] ++ c02F2 ++ [0x94] ++ c02F3 ++ [0x80] ++ c02F4 ++ [0xb8, 0x44] ++ c02F5 ++ [] ++ c02F6 ++ [0xa0] ++ c02F7 ++ [0xa0] ++ c02F8

def c02Signed : Bytes := [0xf8, 0xaa] ++ c02Payload

def c02Tx : Tx := { nonce := 0, gas := 105000, value := 0, data := c02F5, v := 27, r := c02F7, s := c02F8, type := .zero 80000000000 (some 0x2d0e95bd4795d7ace0da3c0ff7b706a5970eb9d3) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c02_literal : c02Signed = [0xf8, 0xaa, 0x80, 0x85, 0x12, 0xa0, 0x5f, 0x20, 0x00, 0x83, 0x01, 0x9a, 0x28, 0x94, 0x2d, 0x0e, 0x95, 0xbd, 0x47, 0x95, 0xd7, 0xac, 0xe0, 0xda, 0x3c, 0x0f, 0xf7, 0xb7, 0x06, 0xa5, 0x97, 0x0e, 0xb9, 0xd3, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x6c, 0xc5, 0xf6, 0x88, 0xa3, 0x15, 0xf3, 0xdc, 0x28, 0xa7, 0x78, 0x17, 0x17, 0xa9, 0xa7, 0x98, 0xa5, 0x9f, 0xda, 0x7b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x06, 0x0b, 0x5f, 0x93, 0x3f, 0x68, 0x0d, 0xff, 0xff, 0x1b, 0xa0, 0xcf, 0xab, 0x8e, 0x92, 0xdf, 0x7b, 0x40, 0x00, 0x26, 0x76, 0xc7, 0xf2, 0x51, 0xaa, 0x66, 0xbd, 0x12, 0x32, 0x10, 0xdf, 0xe8, 0xca, 0x0c, 0xd3, 0x46, 0xf9, 0x35, 0x65, 0xcf, 0xac, 0x48, 0x9e, 0xa0, 0x63, 0xc7, 0xaa, 0xcb, 0x37, 0x8b, 0xc8, 0xa0, 0xb3, 0x54, 0x34, 0x9a, 0x5f, 0x4d, 0xc4, 0xf8, 0xc7, 0xc8, 0x39, 0xe1, 0x52, 0x2c, 0x02, 0xe2, 0xc7, 0x4e, 0xff, 0xb3, 0x8f, 0x98, 0x82, 0xc6] := by
  decide +kernel

theorem c02_payload_length : c02Payload.length = 170 := by
  decide +kernel

theorem c02_signed_length : c02Signed.length = 172 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c02_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c02Payload = some c02Fields := by
  unfold c02Payload c02Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c02F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c02F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c02F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c02F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c02F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c02F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c02_parse : c02Signed.toBLT? = some (.list c02Fields) := by
  have outer : Bytes.toBLTDiff? 172 c02Signed = some (.list c02Fields, []) := by
    simpa only [c02Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 171 170 c02Payload [] c02Fields
        (by rw [c02_payload_length]; decide +kernel) (c02_payload_parse 162)
  unfold Bytes.toBLT?
  rw [c02_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c02_decode :
    (c02Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c02Tx := by
  rw [c02_parse]
  decide +kernel

theorem c02_blt : c02Tx.toBLT = .list c02Fields := by
  norm_num only [c02Tx, c02Fields, c02F0, c02F1, c02F2, c02F3, c02F4, c02F6, c02F7, c02F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c02_encode0 : (BLT.bytes c02F0).toBytes = [0x80] ++ c02F0 := by
  unfold c02F0
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c02_encode1 : (BLT.bytes c02F1).toBytes = [0x85] ++ c02F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c02F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c02_encode2 : (BLT.bytes c02F2).toBytes = [0x83] ++ c02F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c02F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c02_encode3 : (BLT.bytes c02F3).toBytes = [0x94] ++ c02F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c02F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c02_encode4 : (BLT.bytes c02F4).toBytes = [0x80] ++ c02F4 := by
  unfold c02F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c02_encode5 : (BLT.bytes c02F5).toBytes = [0xb8, 0x44] ++ c02F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c02F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c02_encode6 : (BLT.bytes c02F6).toBytes = [] ++ c02F6 := by
  unfold c02F6
  rw [BLT.toBytes]
  decide +kernel

theorem c02_encode7 : (BLT.bytes c02F7).toBytes = [0xa0] ++ c02F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c02F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c02_encode8 : (BLT.bytes c02F8).toBytes = [0xa0] ++ c02F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c02F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c02_canonical : c02Tx.toBLT.toBytes = c02Signed := by
  have encoded : BLTs.toBytesJoin c02Fields = c02Payload := by
    simp only [c02Fields, BLTs.toBytesJoin,
      c02_encode0, c02_encode1, c02_encode2, c02_encode3, c02_encode4, c02_encode5, c02_encode6, c02_encode7, c02_encode8, c02Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c02_blt, BLT.toBytes, BLTs.toBytes, encoded, c02_payload_length]
  norm_num only [c02Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c03F0 : Bytes := [0x11, 0x5c]

def c03F1 : Bytes := [0x0e, 0x33, 0xe2, 0x22, 0x00]

def c03F2 : Bytes := [0xc7, 0x38]

def c03F3 : Bytes := [0xd5, 0x10, 0x59, 0x08, 0x2b, 0x30, 0x30, 0x14, 0xe1, 0xf9, 0xc3, 0xce, 0xc4, 0x5e, 0x70, 0x21, 0x49, 0x9a, 0x63, 0x9a]

def c03F4 : Bytes := [0x23, 0x88, 0x68, 0xd4, 0x05, 0xd0, 0x00]

def c03F5 : Bytes := []

def c03F6 : Bytes := [0x26]

def c03F7 : Bytes := [0x8c, 0x0c, 0x1f, 0x7a, 0xb1, 0xe9, 0xd6, 0xf8, 0x9b, 0x6f, 0xcb, 0x71, 0x8d, 0x1f, 0x66, 0x6a, 0xe9, 0xea, 0x0a, 0x56, 0x94, 0x53, 0x28, 0xc9, 0x3a, 0x12, 0x11, 0x2c, 0xae, 0xb9, 0xcb, 0x6e]

def c03F8 : Bytes := [0x24, 0xa2, 0xe9, 0x48, 0x15, 0x31, 0x91, 0xeb, 0x23, 0x00, 0x33, 0x28, 0xbc, 0x79, 0xec, 0x20, 0xc0, 0xfc, 0x4e, 0xa8, 0x38, 0x6a, 0x8e, 0x49, 0xa2, 0xf5, 0xa6, 0xf6, 0xb6, 0x85, 0x0f, 0x51]

def c03Fields : List BLT := [.bytes c03F0, .bytes c03F1, .bytes c03F2, .bytes c03F3, .bytes c03F4, .bytes c03F5, .bytes c03F6, .bytes c03F7, .bytes c03F8]

def c03Payload : Bytes := [0x82] ++ c03F0 ++ [0x85] ++ c03F1 ++ [0x82] ++ c03F2 ++ [0x94] ++ c03F3 ++ [0x87] ++ c03F4 ++ [0x80] ++ c03F5 ++ [] ++ c03F6 ++ [0xa0] ++ c03F7 ++ [0xa0] ++ c03F8

def c03Signed : Bytes := [0xf8, 0x6d] ++ c03Payload

def c03Tx : Tx := { nonce := 4444, gas := 51000, value := 10001608000000000, data := c03F5, v := 38, r := c03F7, s := c03F8, type := .zero 61000000000 (some 0xd51059082b303014e1f9c3cec45e7021499a639a) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c03_literal : c03Signed = [0xf8, 0x6d, 0x82, 0x11, 0x5c, 0x85, 0x0e, 0x33, 0xe2, 0x22, 0x00, 0x82, 0xc7, 0x38, 0x94, 0xd5, 0x10, 0x59, 0x08, 0x2b, 0x30, 0x30, 0x14, 0xe1, 0xf9, 0xc3, 0xce, 0xc4, 0x5e, 0x70, 0x21, 0x49, 0x9a, 0x63, 0x9a, 0x87, 0x23, 0x88, 0x68, 0xd4, 0x05, 0xd0, 0x00, 0x80, 0x26, 0xa0, 0x8c, 0x0c, 0x1f, 0x7a, 0xb1, 0xe9, 0xd6, 0xf8, 0x9b, 0x6f, 0xcb, 0x71, 0x8d, 0x1f, 0x66, 0x6a, 0xe9, 0xea, 0x0a, 0x56, 0x94, 0x53, 0x28, 0xc9, 0x3a, 0x12, 0x11, 0x2c, 0xae, 0xb9, 0xcb, 0x6e, 0xa0, 0x24, 0xa2, 0xe9, 0x48, 0x15, 0x31, 0x91, 0xeb, 0x23, 0x00, 0x33, 0x28, 0xbc, 0x79, 0xec, 0x20, 0xc0, 0xfc, 0x4e, 0xa8, 0x38, 0x6a, 0x8e, 0x49, 0xa2, 0xf5, 0xa6, 0xf6, 0xb6, 0x85, 0x0f, 0x51] := by
  decide +kernel

theorem c03_payload_length : c03Payload.length = 109 := by
  decide +kernel

theorem c03_signed_length : c03Signed.length = 111 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c03_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c03Payload = some c03Fields := by
  unfold c03Payload c03Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c03F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c03F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c03F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c03F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 7 c03F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c03F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c03F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c03_parse : c03Signed.toBLT? = some (.list c03Fields) := by
  have outer : Bytes.toBLTDiff? 111 c03Signed = some (.list c03Fields, []) := by
    simpa only [c03Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 110 109 c03Payload [] c03Fields
        (by rw [c03_payload_length]; decide +kernel) (c03_payload_parse 101)
  unfold Bytes.toBLT?
  rw [c03_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c03_decode :
    (c03Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c03Tx := by
  rw [c03_parse]
  decide +kernel

theorem c03_blt : c03Tx.toBLT = .list c03Fields := by
  norm_num only [c03Tx, c03Fields, c03F0, c03F1, c03F2, c03F3, c03F4, c03F6, c03F7, c03F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c03_encode0 : (BLT.bytes c03F0).toBytes = [0x82] ++ c03F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c03F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c03_encode1 : (BLT.bytes c03F1).toBytes = [0x85] ++ c03F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c03F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c03_encode2 : (BLT.bytes c03F2).toBytes = [0x82] ++ c03F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c03F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c03_encode3 : (BLT.bytes c03F3).toBytes = [0x94] ++ c03F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c03F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c03_encode4 : (BLT.bytes c03F4).toBytes = [0x87] ++ c03F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c03F4.length = 7 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c03_encode5 : (BLT.bytes c03F5).toBytes = [0x80] ++ c03F5 := by
  unfold c03F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c03_encode6 : (BLT.bytes c03F6).toBytes = [] ++ c03F6 := by
  unfold c03F6
  rw [BLT.toBytes]
  decide +kernel

theorem c03_encode7 : (BLT.bytes c03F7).toBytes = [0xa0] ++ c03F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c03F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c03_encode8 : (BLT.bytes c03F8).toBytes = [0xa0] ++ c03F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c03F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c03_canonical : c03Tx.toBLT.toBytes = c03Signed := by
  have encoded : BLTs.toBytesJoin c03Fields = c03Payload := by
    simp only [c03Fields, BLTs.toBytesJoin,
      c03_encode0, c03_encode1, c03_encode2, c03_encode3, c03_encode4, c03_encode5, c03_encode6, c03_encode7, c03_encode8, c03Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c03_blt, BLT.toBytes, BLTs.toBytes, encoded, c03_payload_length]
  norm_num only [c03Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c04F0 : Bytes := []

def c04F1 : Bytes := [0x0c, 0x39, 0x3e, 0x6d, 0x00]

def c04F2 : Bytes := [0x52, 0x08]

def c04F3 : Bytes := [0x70, 0xfa, 0xa2, 0x8a, 0x6b, 0x8d, 0x68, 0x29, 0xa4, 0xb1, 0xe6, 0x49, 0xd2, 0x6e, 0xc9, 0xa2, 0xa3, 0x9b, 0xa4, 0x13]

def c04F4 : Bytes := [0x02, 0x70, 0xe9, 0x30, 0x81, 0x08, 0xf8, 0x00]

def c04F5 : Bytes := []

def c04F6 : Bytes := [0x1c]

def c04F7 : Bytes := [0xb5, 0x2d, 0xac, 0x52, 0x74, 0x47, 0x06, 0x97, 0xe7, 0x32, 0x3d, 0xb0, 0xcc, 0xd1, 0xd5, 0x82, 0x6c, 0xd8, 0xa8, 0x19, 0x83, 0xd3, 0x6a, 0xf7, 0x1d, 0x89, 0xd3, 0xcb, 0xb9, 0xcc, 0xcd, 0xb1]

def c04F8 : Bytes := [0x76, 0x57, 0xc3, 0x88, 0x68, 0x04, 0x8b, 0x83, 0xd4, 0xa3, 0xf1, 0xc6, 0x9c, 0xaa, 0x61, 0xe7, 0xc4, 0x97, 0x6c, 0xa8, 0xac, 0x94, 0xdf, 0xf7, 0xc2, 0x18, 0x8e, 0xa5, 0x40, 0x3b, 0xb0, 0xbf]

def c04Fields : List BLT := [.bytes c04F0, .bytes c04F1, .bytes c04F2, .bytes c04F3, .bytes c04F4, .bytes c04F5, .bytes c04F6, .bytes c04F7, .bytes c04F8]

def c04Payload : Bytes := [0x80] ++ c04F0 ++ [0x85] ++ c04F1 ++ [0x82] ++ c04F2 ++ [0x94] ++ c04F3 ++ [0x88] ++ c04F4 ++ [0x80] ++ c04F5 ++ [] ++ c04F6 ++ [0xa0] ++ c04F7 ++ [0xa0] ++ c04F8

def c04Signed : Bytes := [0xf8, 0x6c] ++ c04Payload

def c04Tx : Tx := { nonce := 0, gas := 21000, value := 175896780000000000, data := c04F5, v := 28, r := c04F7, s := c04F8, type := .zero 52500000000 (some 0x70faa28a6b8d6829a4b1e649d26ec9a2a39ba413) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c04_literal : c04Signed = [0xf8, 0x6c, 0x80, 0x85, 0x0c, 0x39, 0x3e, 0x6d, 0x00, 0x82, 0x52, 0x08, 0x94, 0x70, 0xfa, 0xa2, 0x8a, 0x6b, 0x8d, 0x68, 0x29, 0xa4, 0xb1, 0xe6, 0x49, 0xd2, 0x6e, 0xc9, 0xa2, 0xa3, 0x9b, 0xa4, 0x13, 0x88, 0x02, 0x70, 0xe9, 0x30, 0x81, 0x08, 0xf8, 0x00, 0x80, 0x1c, 0xa0, 0xb5, 0x2d, 0xac, 0x52, 0x74, 0x47, 0x06, 0x97, 0xe7, 0x32, 0x3d, 0xb0, 0xcc, 0xd1, 0xd5, 0x82, 0x6c, 0xd8, 0xa8, 0x19, 0x83, 0xd3, 0x6a, 0xf7, 0x1d, 0x89, 0xd3, 0xcb, 0xb9, 0xcc, 0xcd, 0xb1, 0xa0, 0x76, 0x57, 0xc3, 0x88, 0x68, 0x04, 0x8b, 0x83, 0xd4, 0xa3, 0xf1, 0xc6, 0x9c, 0xaa, 0x61, 0xe7, 0xc4, 0x97, 0x6c, 0xa8, 0xac, 0x94, 0xdf, 0xf7, 0xc2, 0x18, 0x8e, 0xa5, 0x40, 0x3b, 0xb0, 0xbf] := by
  decide +kernel

theorem c04_payload_length : c04Payload.length = 108 := by
  decide +kernel

theorem c04_signed_length : c04Signed.length = 110 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c04_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c04Payload = some c04Fields := by
  unfold c04Payload c04Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c04F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c04F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c04F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c04F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c04F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c04F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c04_parse : c04Signed.toBLT? = some (.list c04Fields) := by
  have outer : Bytes.toBLTDiff? 110 c04Signed = some (.list c04Fields, []) := by
    simpa only [c04Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 109 108 c04Payload [] c04Fields
        (by rw [c04_payload_length]; decide +kernel) (c04_payload_parse 100)
  unfold Bytes.toBLT?
  rw [c04_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c04_decode :
    (c04Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c04Tx := by
  rw [c04_parse]
  decide +kernel

theorem c04_blt : c04Tx.toBLT = .list c04Fields := by
  norm_num only [c04Tx, c04Fields, c04F0, c04F1, c04F2, c04F3, c04F4, c04F6, c04F7, c04F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c04_encode0 : (BLT.bytes c04F0).toBytes = [0x80] ++ c04F0 := by
  unfold c04F0
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c04_encode1 : (BLT.bytes c04F1).toBytes = [0x85] ++ c04F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c04F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c04_encode2 : (BLT.bytes c04F2).toBytes = [0x82] ++ c04F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c04F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c04_encode3 : (BLT.bytes c04F3).toBytes = [0x94] ++ c04F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c04F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c04_encode4 : (BLT.bytes c04F4).toBytes = [0x88] ++ c04F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c04F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c04_encode5 : (BLT.bytes c04F5).toBytes = [0x80] ++ c04F5 := by
  unfold c04F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c04_encode6 : (BLT.bytes c04F6).toBytes = [] ++ c04F6 := by
  unfold c04F6
  rw [BLT.toBytes]
  decide +kernel

theorem c04_encode7 : (BLT.bytes c04F7).toBytes = [0xa0] ++ c04F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c04F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c04_encode8 : (BLT.bytes c04F8).toBytes = [0xa0] ++ c04F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c04F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c04_canonical : c04Tx.toBLT.toBytes = c04Signed := by
  have encoded : BLTs.toBytesJoin c04Fields = c04Payload := by
    simp only [c04Fields, BLTs.toBytesJoin,
      c04_encode0, c04_encode1, c04_encode2, c04_encode3, c04_encode4, c04_encode5, c04_encode6, c04_encode7, c04_encode8, c04Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c04_blt, BLT.toBytes, BLTs.toBytes, encoded, c04_payload_length]
  norm_num only [c04Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c05F0 : Bytes := [0x57]

def c05F1 : Bytes := [0x09, 0x8b, 0xca, 0x5a, 0x00]

def c05F2 : Bytes := [0x90, 0x77]

def c05F3 : Bytes := [0x69, 0xc4, 0xbb, 0x24, 0x0c, 0xf0, 0x5d, 0x51, 0xee, 0xab, 0x69, 0x85, 0xba, 0xb3, 0x55, 0x27, 0xd0, 0x4a, 0x8c, 0x64]

def c05F4 : Bytes := []

def c05F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x32, 0x99, 0x88, 0x6b, 0xc8, 0x5c, 0x0d, 0x1c, 0x21, 0xcf, 0x7d, 0xd7, 0x2e, 0x86, 0xad, 0xc4, 0x56, 0x17, 0xd4, 0xed, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x89, 0xf3, 0xf8, 0x9e]

def c05F6 : Bytes := [0x25]

def c05F7 : Bytes := [0x22, 0xaf, 0xa9, 0x50, 0xb4, 0x24, 0x6d, 0x69, 0x40, 0xd3, 0x1d, 0xe0, 0x75, 0x90, 0xc0, 0x08, 0xd7, 0x35, 0x20, 0xba, 0x4f, 0x86, 0x29, 0xd6, 0x7e, 0x7e, 0x61, 0xa7, 0xab, 0x2d, 0xf6, 0x87]

def c05F8 : Bytes := [0x79, 0x60, 0x28, 0x11, 0xcc, 0xa9, 0x42, 0x7e, 0x68, 0x2c, 0xd4, 0xc9, 0x79, 0x30, 0xbf, 0xfe, 0xec, 0x7e, 0xf5, 0xb4, 0x08, 0xba, 0xad, 0x7b, 0x93, 0x7f, 0xa3, 0xb3, 0x9f, 0xe6, 0xe1, 0x71]

def c05Fields : List BLT := [.bytes c05F0, .bytes c05F1, .bytes c05F2, .bytes c05F3, .bytes c05F4, .bytes c05F5, .bytes c05F6, .bytes c05F7, .bytes c05F8]

def c05Payload : Bytes := [] ++ c05F0 ++ [0x85] ++ c05F1 ++ [0x82] ++ c05F2 ++ [0x94] ++ c05F3 ++ [0x80] ++ c05F4 ++ [0xb8, 0x44] ++ c05F5 ++ [] ++ c05F6 ++ [0xa0] ++ c05F7 ++ [0xa0] ++ c05F8

def c05Signed : Bytes := [0xf8, 0xa9] ++ c05Payload

def c05Tx : Tx := { nonce := 87, gas := 36983, value := 0, data := c05F5, v := 37, r := c05F7, s := c05F8, type := .zero 41000000000 (some 0x69c4bb240cf05d51eeab6985bab35527d04a8c64) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c05_literal : c05Signed = [0xf8, 0xa9, 0x57, 0x85, 0x09, 0x8b, 0xca, 0x5a, 0x00, 0x82, 0x90, 0x77, 0x94, 0x69, 0xc4, 0xbb, 0x24, 0x0c, 0xf0, 0x5d, 0x51, 0xee, 0xab, 0x69, 0x85, 0xba, 0xb3, 0x55, 0x27, 0xd0, 0x4a, 0x8c, 0x64, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x32, 0x99, 0x88, 0x6b, 0xc8, 0x5c, 0x0d, 0x1c, 0x21, 0xcf, 0x7d, 0xd7, 0x2e, 0x86, 0xad, 0xc4, 0x56, 0x17, 0xd4, 0xed, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x89, 0xf3, 0xf8, 0x9e, 0x25, 0xa0, 0x22, 0xaf, 0xa9, 0x50, 0xb4, 0x24, 0x6d, 0x69, 0x40, 0xd3, 0x1d, 0xe0, 0x75, 0x90, 0xc0, 0x08, 0xd7, 0x35, 0x20, 0xba, 0x4f, 0x86, 0x29, 0xd6, 0x7e, 0x7e, 0x61, 0xa7, 0xab, 0x2d, 0xf6, 0x87, 0xa0, 0x79, 0x60, 0x28, 0x11, 0xcc, 0xa9, 0x42, 0x7e, 0x68, 0x2c, 0xd4, 0xc9, 0x79, 0x30, 0xbf, 0xfe, 0xec, 0x7e, 0xf5, 0xb4, 0x08, 0xba, 0xad, 0x7b, 0x93, 0x7f, 0xa3, 0xb3, 0x9f, 0xe6, 0xe1, 0x71] := by
  decide +kernel

theorem c05_payload_length : c05Payload.length = 169 := by
  decide +kernel

theorem c05_signed_length : c05Signed.length = 171 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c05_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c05Payload = some c05Fields := by
  unfold c05Payload c05Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c05F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c05F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c05F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c05F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c05F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c05F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c05_parse : c05Signed.toBLT? = some (.list c05Fields) := by
  have outer : Bytes.toBLTDiff? 171 c05Signed = some (.list c05Fields, []) := by
    simpa only [c05Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 170 169 c05Payload [] c05Fields
        (by rw [c05_payload_length]; decide +kernel) (c05_payload_parse 161)
  unfold Bytes.toBLT?
  rw [c05_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c05_decode :
    (c05Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c05Tx := by
  rw [c05_parse]
  decide +kernel

theorem c05_blt : c05Tx.toBLT = .list c05Fields := by
  norm_num only [c05Tx, c05Fields, c05F0, c05F1, c05F2, c05F3, c05F4, c05F6, c05F7, c05F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c05_encode0 : (BLT.bytes c05F0).toBytes = [] ++ c05F0 := by
  unfold c05F0
  rw [BLT.toBytes]
  decide +kernel

theorem c05_encode1 : (BLT.bytes c05F1).toBytes = [0x85] ++ c05F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c05F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c05_encode2 : (BLT.bytes c05F2).toBytes = [0x82] ++ c05F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c05F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c05_encode3 : (BLT.bytes c05F3).toBytes = [0x94] ++ c05F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c05F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c05_encode4 : (BLT.bytes c05F4).toBytes = [0x80] ++ c05F4 := by
  unfold c05F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c05_encode5 : (BLT.bytes c05F5).toBytes = [0xb8, 0x44] ++ c05F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c05F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c05_encode6 : (BLT.bytes c05F6).toBytes = [] ++ c05F6 := by
  unfold c05F6
  rw [BLT.toBytes]
  decide +kernel

theorem c05_encode7 : (BLT.bytes c05F7).toBytes = [0xa0] ++ c05F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c05F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c05_encode8 : (BLT.bytes c05F8).toBytes = [0xa0] ++ c05F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c05F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c05_canonical : c05Tx.toBLT.toBytes = c05Signed := by
  have encoded : BLTs.toBytesJoin c05Fields = c05Payload := by
    simp only [c05Fields, BLTs.toBytesJoin,
      c05_encode0, c05_encode1, c05_encode2, c05_encode3, c05_encode4, c05_encode5, c05_encode6, c05_encode7, c05_encode8, c05Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c05_blt, BLT.toBytes, BLTs.toBytes, encoded, c05_payload_length]
  norm_num only [c05Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c06F0 : Bytes := [0x86]

def c06F1 : Bytes := [0x07, 0xc0, 0x9f, 0x7e, 0xc4]

def c06F2 : Bytes := [0x05, 0x57, 0x30]

def c06F3 : Bytes := [0x4e, 0x8e, 0xcf, 0x79, 0xad, 0xe5, 0xe2, 0xc4, 0x9b, 0x9e, 0x30, 0xd7, 0x95, 0x51, 0x7a, 0x81, 0xe0, 0xbf, 0x00, 0xb8]

def c06F4 : Bytes := [0x8f, 0x04, 0x62, 0x5e, 0x8c, 0xa1, 0x98]

def c06F5 : Bytes := [0xa6, 0x5b, 0x37, 0xa1, 0x63, 0x72, 0x65, 0x61, 0x74, 0x65, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]

def c06F6 : Bytes := [0x25]

def c06F7 : Bytes := [0xec, 0x72, 0x2d, 0x8f, 0x1e, 0x74, 0xe5, 0x54, 0x18, 0x00, 0xe0, 0x0c, 0xa5, 0x66, 0x66, 0xd1, 0xd9, 0x5c, 0x39, 0xd3, 0x64, 0xae, 0x85, 0x3e, 0x5c, 0x1a, 0xa6, 0x02, 0xf6, 0x18, 0x0b, 0x78]

def c06F8 : Bytes := [0x66, 0x44, 0x08, 0xc8, 0xcf, 0x95, 0x1b, 0x67, 0x4c, 0xe0, 0x92, 0x7c, 0xf7, 0xa6, 0xf2, 0x3a, 0xb7, 0x8f, 0xc4, 0x1a, 0x9a, 0xa0, 0x2d, 0x2a, 0xab, 0x04, 0x46, 0x8e, 0xc6, 0x9b, 0xc3, 0x3c]

def c06Fields : List BLT := [.bytes c06F0, .bytes c06F1, .bytes c06F2, .bytes c06F3, .bytes c06F4, .bytes c06F5, .bytes c06F6, .bytes c06F7, .bytes c06F8]

def c06Payload : Bytes := [0x81] ++ c06F0 ++ [0x85] ++ c06F1 ++ [0x83] ++ c06F2 ++ [0x94] ++ c06F3 ++ [0x87] ++ c06F4 ++ [0xb8, 0x44] ++ c06F5 ++ [] ++ c06F6 ++ [0xa0] ++ c06F7 ++ [0xa0] ++ c06F8

def c06Signed : Bytes := [0xf8, 0xb2] ++ c06Payload

def c06Tx : Tx := { nonce := 134, gas := 350000, value := 40255742209204632, data := c06F5, v := 37, r := c06F7, s := c06F8, type := .zero 33296449220 (some 0x4e8ecf79ade5e2c49b9e30d795517a81e0bf00b8) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c06_literal : c06Signed = [0xf8, 0xb2, 0x81, 0x86, 0x85, 0x07, 0xc0, 0x9f, 0x7e, 0xc4, 0x83, 0x05, 0x57, 0x30, 0x94, 0x4e, 0x8e, 0xcf, 0x79, 0xad, 0xe5, 0xe2, 0xc4, 0x9b, 0x9e, 0x30, 0xd7, 0x95, 0x51, 0x7a, 0x81, 0xe0, 0xbf, 0x00, 0xb8, 0x87, 0x8f, 0x04, 0x62, 0x5e, 0x8c, 0xa1, 0x98, 0xb8, 0x44, 0xa6, 0x5b, 0x37, 0xa1, 0x63, 0x72, 0x65, 0x61, 0x74, 0x65, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x25, 0xa0, 0xec, 0x72, 0x2d, 0x8f, 0x1e, 0x74, 0xe5, 0x54, 0x18, 0x00, 0xe0, 0x0c, 0xa5, 0x66, 0x66, 0xd1, 0xd9, 0x5c, 0x39, 0xd3, 0x64, 0xae, 0x85, 0x3e, 0x5c, 0x1a, 0xa6, 0x02, 0xf6, 0x18, 0x0b, 0x78, 0xa0, 0x66, 0x44, 0x08, 0xc8, 0xcf, 0x95, 0x1b, 0x67, 0x4c, 0xe0, 0x92, 0x7c, 0xf7, 0xa6, 0xf2, 0x3a, 0xb7, 0x8f, 0xc4, 0x1a, 0x9a, 0xa0, 0x2d, 0x2a, 0xab, 0x04, 0x46, 0x8e, 0xc6, 0x9b, 0xc3, 0x3c] := by
  decide +kernel

theorem c06_payload_length : c06Payload.length = 178 := by
  decide +kernel

theorem c06_signed_length : c06Signed.length = 180 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c06_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c06Payload = some c06Fields := by
  unfold c06Payload c06Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 1 c06F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c06F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c06F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c06F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 7 c06F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 c06F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c06F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c06F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c06_parse : c06Signed.toBLT? = some (.list c06Fields) := by
  have outer : Bytes.toBLTDiff? 180 c06Signed = some (.list c06Fields, []) := by
    simpa only [c06Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 179 178 c06Payload [] c06Fields
        (by rw [c06_payload_length]; decide +kernel) (c06_payload_parse 170)
  unfold Bytes.toBLT?
  rw [c06_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c06_decode :
    (c06Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c06Tx := by
  rw [c06_parse]
  decide +kernel

theorem c06_blt : c06Tx.toBLT = .list c06Fields := by
  norm_num only [c06Tx, c06Fields, c06F0, c06F1, c06F2, c06F3, c06F4, c06F6, c06F7, c06F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c06_encode0 : (BLT.bytes c06F0).toBytes = [0x81] ++ c06F0 := by
  unfold c06F0
  rw [BLT.toBytes]
  decide +kernel

theorem c06_encode1 : (BLT.bytes c06F1).toBytes = [0x85] ++ c06F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c06F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c06_encode2 : (BLT.bytes c06F2).toBytes = [0x83] ++ c06F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c06F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c06_encode3 : (BLT.bytes c06F3).toBytes = [0x94] ++ c06F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c06F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c06_encode4 : (BLT.bytes c06F4).toBytes = [0x87] ++ c06F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c06F4.length = 7 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c06_encode5 : (BLT.bytes c06F5).toBytes = [0xb8, 0x44] ++ c06F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c06F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c06_encode6 : (BLT.bytes c06F6).toBytes = [] ++ c06F6 := by
  unfold c06F6
  rw [BLT.toBytes]
  decide +kernel

theorem c06_encode7 : (BLT.bytes c06F7).toBytes = [0xa0] ++ c06F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c06F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c06_encode8 : (BLT.bytes c06F8).toBytes = [0xa0] ++ c06F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c06F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c06_canonical : c06Tx.toBLT.toBytes = c06Signed := by
  have encoded : BLTs.toBytesJoin c06Fields = c06Payload := by
    simp only [c06Fields, BLTs.toBytesJoin,
      c06_encode0, c06_encode1, c06_encode2, c06_encode3, c06_encode4, c06_encode5, c06_encode6, c06_encode7, c06_encode8, c06Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c06_blt, BLT.toBytes, BLTs.toBytes, encoded, c06_payload_length]
  norm_num only [c06Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def c07F0 : Bytes := [0x02, 0xf7, 0xeb]

def c07F1 : Bytes := [0x07, 0xae, 0xf4, 0x0a, 0x00]

def c07F2 : Bytes := [0xa4, 0x10]

def c07F3 : Bytes := [0x4b, 0x81, 0x14, 0x1c, 0x31, 0x98, 0xa6, 0xf9, 0x90, 0xf5, 0x52, 0x1d, 0xfa, 0xb2, 0x0c, 0x39, 0x3f, 0x34, 0x28, 0x67]

def c07F4 : Bytes := [0x24, 0xb5, 0x1b, 0x8d, 0x56, 0x2a, 0x84, 0x00]

def c07F5 : Bytes := []

def c07F6 : Bytes := [0x26]

def c07F7 : Bytes := [0x58, 0x68, 0x34, 0xab, 0x1d, 0x82, 0x03, 0x2e, 0xaa, 0x4c, 0xeb, 0x74, 0x40, 0x01, 0x72, 0xab, 0x5a, 0xd8, 0xf1, 0x5e, 0x44, 0xb1, 0x2e, 0x9e, 0xbb, 0x84, 0xa7, 0x91, 0xec, 0xb8, 0x18, 0x1f]

def c07F8 : Bytes := [0x3b, 0x08, 0x54, 0x32, 0x18, 0x03, 0x24, 0xa8, 0x4b, 0xb3, 0x79, 0x8d, 0x19, 0xbe, 0x43, 0x72, 0x29, 0x77, 0x77, 0x66, 0x40, 0x6d, 0x80, 0x23, 0x72, 0x94, 0xe0, 0xc0, 0x12, 0xb6, 0x7a, 0x38]

def c07Fields : List BLT := [.bytes c07F0, .bytes c07F1, .bytes c07F2, .bytes c07F3, .bytes c07F4, .bytes c07F5, .bytes c07F6, .bytes c07F7, .bytes c07F8]

def c07Payload : Bytes := [0x83] ++ c07F0 ++ [0x85] ++ c07F1 ++ [0x82] ++ c07F2 ++ [0x94] ++ c07F3 ++ [0x88] ++ c07F4 ++ [0x80] ++ c07F5 ++ [] ++ c07F6 ++ [0xa0] ++ c07F7 ++ [0xa0] ++ c07F8

def c07Signed : Bytes := [0xf8, 0x6f] ++ c07Payload

def c07Tx : Tx := { nonce := 194539, gas := 42000, value := 2645050650000000000, data := c07F5, v := 38, r := c07F7, s := c07F8, type := .zero 33000000000 (some 0x4b81141c3198a6f990f5521dfab20c393f342867) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem c07_literal : c07Signed = [0xf8, 0x6f, 0x83, 0x02, 0xf7, 0xeb, 0x85, 0x07, 0xae, 0xf4, 0x0a, 0x00, 0x82, 0xa4, 0x10, 0x94, 0x4b, 0x81, 0x14, 0x1c, 0x31, 0x98, 0xa6, 0xf9, 0x90, 0xf5, 0x52, 0x1d, 0xfa, 0xb2, 0x0c, 0x39, 0x3f, 0x34, 0x28, 0x67, 0x88, 0x24, 0xb5, 0x1b, 0x8d, 0x56, 0x2a, 0x84, 0x00, 0x80, 0x26, 0xa0, 0x58, 0x68, 0x34, 0xab, 0x1d, 0x82, 0x03, 0x2e, 0xaa, 0x4c, 0xeb, 0x74, 0x40, 0x01, 0x72, 0xab, 0x5a, 0xd8, 0xf1, 0x5e, 0x44, 0xb1, 0x2e, 0x9e, 0xbb, 0x84, 0xa7, 0x91, 0xec, 0xb8, 0x18, 0x1f, 0xa0, 0x3b, 0x08, 0x54, 0x32, 0x18, 0x03, 0x24, 0xa8, 0x4b, 0xb3, 0x79, 0x8d, 0x19, 0xbe, 0x43, 0x72, 0x29, 0x77, 0x77, 0x66, 0x40, 0x6d, 0x80, 0x23, 0x72, 0x94, 0xe0, 0xc0, 0x12, 0xb6, 0x7a, 0x38] := by
  decide +kernel

theorem c07_payload_length : c07Payload.length = 111 := by
  decide +kernel

theorem c07_signed_length : c07Signed.length = 113 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem c07_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) c07Payload = some c07Fields := by
  unfold c07Payload c07Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 c07F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 c07F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 c07F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 c07F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 c07F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 c07F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 c07F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem c07_parse : c07Signed.toBLT? = some (.list c07Fields) := by
  have outer : Bytes.toBLTDiff? 113 c07Signed = some (.list c07Fields, []) := by
    simpa only [c07Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 112 111 c07Payload [] c07Fields
        (by rw [c07_payload_length]; decide +kernel) (c07_payload_parse 103)
  unfold Bytes.toBLT?
  rw [c07_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem c07_decode :
    (c07Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some c07Tx := by
  rw [c07_parse]
  decide +kernel

theorem c07_blt : c07Tx.toBLT = .list c07Fields := by
  norm_num only [c07Tx, c07Fields, c07F0, c07F1, c07F2, c07F3, c07F4, c07F6, c07F7, c07F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem c07_encode0 : (BLT.bytes c07F0).toBytes = [0x83] ++ c07F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c07F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c07_encode1 : (BLT.bytes c07F1).toBytes = [0x85] ++ c07F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c07F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c07_encode2 : (BLT.bytes c07F2).toBytes = [0x82] ++ c07F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c07F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c07_encode3 : (BLT.bytes c07F3).toBytes = [0x94] ++ c07F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c07F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c07_encode4 : (BLT.bytes c07F4).toBytes = [0x88] ++ c07F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c07F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c07_encode5 : (BLT.bytes c07F5).toBytes = [0x80] ++ c07F5 := by
  unfold c07F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem c07_encode6 : (BLT.bytes c07F6).toBytes = [] ++ c07F6 := by
  unfold c07F6
  rw [BLT.toBytes]
  decide +kernel

theorem c07_encode7 : (BLT.bytes c07F7).toBytes = [0xa0] ++ c07F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c07F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem c07_encode8 : (BLT.bytes c07F8).toBytes = [0xa0] ++ c07F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show c07F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem c07_canonical : c07Tx.toBLT.toBytes = c07Signed := by
  have encoded : BLTs.toBytesJoin c07Fields = c07Payload := by
    simp only [c07Fields, BLTs.toBytesJoin,
      c07_encode0, c07_encode1, c07_encode2, c07_encode3, c07_encode4, c07_encode5, c07_encode6, c07_encode7, c07_encode8, c07Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [c07_blt, BLT.toBytes, BLTs.toBytes, encoded, c07_payload_length]
  norm_num only [c07Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
