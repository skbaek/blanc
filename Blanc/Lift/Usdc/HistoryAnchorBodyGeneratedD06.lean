import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def d48F0 : Bytes := [0x05]

def d48F1 : Bytes := [0xe8, 0x75, 0x47, 0x00]

def d48F2 : Bytes := [0x14, 0x17, 0x06]

def d48F3 : Bytes := [0xb4, 0x40, 0xdd, 0x67, 0x4e, 0x12, 0x43, 0x64, 0x47, 0x91, 0xa4, 0xad, 0xfe, 0x3a, 0x2a, 0xbb, 0x0a, 0x92, 0xd3, 0x09]

def d48F4 : Bytes := []

def d48F5 : Bytes := [0xd2, 0x94, 0xf0, 0x93]

def d48F6 : Bytes := [0x26]

def d48F7 : Bytes := [0xee, 0x95, 0xcb, 0xbb, 0xe3, 0xb3, 0x4b, 0xda, 0xf5, 0x32, 0x5e, 0x91, 0x31, 0xd3, 0x18, 0x27, 0xb6, 0xf5, 0x0b, 0x9e, 0x4b, 0x53, 0x9e, 0xbb, 0x66, 0x40, 0x44, 0x7b, 0x85, 0x7a, 0xd4, 0x04]

def d48F8 : Bytes := [0x2e, 0x9f, 0xcb, 0xfb, 0xb5, 0x1b, 0x61, 0x19, 0xfb, 0xc8, 0x45, 0x9e, 0x82, 0x0f, 0xc9, 0xae, 0x5e, 0xa9, 0xde, 0xa6, 0xaf, 0x92, 0x85, 0x59, 0xb5, 0x89, 0x58, 0x68, 0x10, 0xe8, 0x3a, 0x15]

def d48Fields : List BLT := [.bytes d48F0, .bytes d48F1, .bytes d48F2, .bytes d48F3, .bytes d48F4, .bytes d48F5, .bytes d48F6, .bytes d48F7, .bytes d48F8]

def d48Payload : Bytes := [] ++ d48F0 ++ [0x84] ++ d48F1 ++ [0x83] ++ d48F2 ++ [0x94] ++ d48F3 ++ [0x80] ++ d48F4 ++ [0x84] ++ d48F5 ++ [] ++ d48F6 ++ [0xa0] ++ d48F7 ++ [0xa0] ++ d48F8

def d48Signed : Bytes := [0xf8, 0x68] ++ d48Payload

def d48Tx : Tx := { nonce := 5, gas := 1316614, value := 0, data := d48F5, v := 38, r := d48F7, s := d48F8, type := .zero 3900000000 (some 0xb440dd674e1243644791a4adfe3a2abb0a92d309) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d48_literal : d48Signed = [0xf8, 0x68, 0x05, 0x84, 0xe8, 0x75, 0x47, 0x00, 0x83, 0x14, 0x17, 0x06, 0x94, 0xb4, 0x40, 0xdd, 0x67, 0x4e, 0x12, 0x43, 0x64, 0x47, 0x91, 0xa4, 0xad, 0xfe, 0x3a, 0x2a, 0xbb, 0x0a, 0x92, 0xd3, 0x09, 0x80, 0x84, 0xd2, 0x94, 0xf0, 0x93, 0x26, 0xa0, 0xee, 0x95, 0xcb, 0xbb, 0xe3, 0xb3, 0x4b, 0xda, 0xf5, 0x32, 0x5e, 0x91, 0x31, 0xd3, 0x18, 0x27, 0xb6, 0xf5, 0x0b, 0x9e, 0x4b, 0x53, 0x9e, 0xbb, 0x66, 0x40, 0x44, 0x7b, 0x85, 0x7a, 0xd4, 0x04, 0xa0, 0x2e, 0x9f, 0xcb, 0xfb, 0xb5, 0x1b, 0x61, 0x19, 0xfb, 0xc8, 0x45, 0x9e, 0x82, 0x0f, 0xc9, 0xae, 0x5e, 0xa9, 0xde, 0xa6, 0xaf, 0x92, 0x85, 0x59, 0xb5, 0x89, 0x58, 0x68, 0x10, 0xe8, 0x3a, 0x15] := by
  decide +kernel

theorem d48_payload_length : d48Payload.length = 104 := by
  decide +kernel

theorem d48_signed_length : d48Signed.length = 106 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d48_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d48Payload = some d48Fields := by
  unfold d48Payload d48Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d48F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d48F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d48F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d48F5 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d48F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d48F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d48_parse : d48Signed.toBLT? = some (.list d48Fields) := by
  have outer : Bytes.toBLTDiff? 106 d48Signed = some (.list d48Fields, []) := by
    simpa only [d48Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 105 104 d48Payload [] d48Fields
        (by rw [d48_payload_length]; decide +kernel) (d48_payload_parse 96)
  unfold Bytes.toBLT?
  rw [d48_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d48_decode :
    (d48Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d48Tx := by
  rw [d48_parse]
  decide +kernel

theorem d48_blt : d48Tx.toBLT = .list d48Fields := by
  norm_num only [d48Tx, d48Fields, d48F0, d48F1, d48F2, d48F3, d48F4, d48F6, d48F7, d48F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d48_encode0 : (BLT.bytes d48F0).toBytes = [] ++ d48F0 := by
  unfold d48F0
  rw [BLT.toBytes]
  decide +kernel

theorem d48_encode1 : (BLT.bytes d48F1).toBytes = [0x84] ++ d48F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d48F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d48_encode2 : (BLT.bytes d48F2).toBytes = [0x83] ++ d48F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d48F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d48_encode3 : (BLT.bytes d48F3).toBytes = [0x94] ++ d48F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d48F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d48_encode4 : (BLT.bytes d48F4).toBytes = [0x80] ++ d48F4 := by
  unfold d48F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d48_encode5 : (BLT.bytes d48F5).toBytes = [0x84] ++ d48F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d48F5.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d48_encode6 : (BLT.bytes d48F6).toBytes = [] ++ d48F6 := by
  unfold d48F6
  rw [BLT.toBytes]
  decide +kernel

theorem d48_encode7 : (BLT.bytes d48F7).toBytes = [0xa0] ++ d48F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d48F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d48_encode8 : (BLT.bytes d48F8).toBytes = [0xa0] ++ d48F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d48F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d48_canonical : d48Tx.toBLT.toBytes = d48Signed := by
  have encoded : BLTs.toBytesJoin d48Fields = d48Payload := by
    simp only [d48Fields, BLTs.toBytesJoin,
      d48_encode0, d48_encode1, d48_encode2, d48_encode3, d48_encode4, d48_encode5, d48_encode6, d48_encode7, d48_encode8, d48Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d48_blt, BLT.toBytes, BLTs.toBytes, encoded, d48_payload_length]
  norm_num only [d48Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d49F0 : Bytes := [0x02, 0xd3, 0x8d]

def d49F1 : Bytes := [0xe8, 0x4b, 0x34, 0xd3]

def d49F2 : Bytes := [0x02, 0xab, 0x98]

def d49F3 : Bytes := []

def d49F4 : Bytes := []

def d49F5 : Bytes := [0x60, 0x60, 0x60, 0x40, 0x52, 0x34, 0x15, 0x61, 0x00, 0x0f, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0xb9, 0x69, 0x1e, 0xb0, 0xe3, 0xc0, 0xb2, 0x37, 0xfc, 0x7e, 0x92, 0x07, 0x72, 0xda, 0x27, 0x3e, 0xb1, 0x61, 0xe5, 0x95, 0x59, 0xcd, 0xa2, 0x5b, 0x73, 0xf8, 0x02, 0x8c, 0x10, 0x84, 0xcb, 0xf2, 0x30, 0x60, 0x40, 0x51, 0x80, 0x82, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x01, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x61, 0x01, 0x6d, 0x80, 0x61, 0x00, 0x98, 0x60, 0x00, 0x39, 0x60, 0x00, 0xf3, 0x00, 0x60, 0x60, 0x60, 0x40, 0x52, 0x60, 0x00, 0x80, 0x30, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x31, 0x91, 0x50, 0x60, 0x00, 0x82, 0x11, 0x15, 0x15, 0x61, 0x00, 0x30, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x73, 0xaf, 0x19, 0x31, 0xc2, 0x0e, 0xe0, 0xc1, 0x1b, 0xea, 0x17, 0xa4, 0x1b, 0xfb, 0xba, 0xd2, 0x99, 0xb2, 0x76, 0x3b, 0xc0, 0x90, 0x50, 0x80, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x08, 0xfc, 0x83, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x40, 0x51, 0x60, 0x00, 0x60, 0x40, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x00, 0x87, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x80, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0xe6, 0x59, 0xbb, 0x22, 0x72, 0x6a, 0xfd, 0x60, 0x09, 0xb1, 0x7c, 0x3a, 0xe2, 0x36, 0x79, 0xed, 0x41, 0x78, 0x4f, 0x38, 0x21, 0x29, 0xf7, 0xfb, 0x0b, 0x2e, 0xf6, 0x77, 0x6e, 0x04, 0x13, 0xd9, 0x30, 0x33, 0x85, 0x60, 0x40, 0x51, 0x80, 0x84, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x01, 0x83, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x01, 0x82, 0x81, 0x52, 0x60, 0x20, 0x01, 0x93, 0x50, 0x50, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x50, 0x50, 0x00, 0x00, 0xa1, 0x65, 0x62, 0x7a, 0x7a, 0x72, 0x30, 0x58, 0x20, 0xd2, 0xaa, 0xc5, 0xa9, 0x15, 0xbf, 0x75, 0xf1, 0x0f, 0x6a, 0x15, 0xe2, 0x59, 0x46, 0x52, 0x32, 0x00, 0x95, 0x28, 0xad, 0x32, 0xea, 0x57, 0x43, 0xce, 0x15, 0x23, 0x09, 0xfc, 0xde, 0x2d, 0xd1, 0x00, 0x29]

def d49F6 : Bytes := [0x26]

def d49F7 : Bytes := [0x54, 0x50, 0x24, 0x8c, 0x8a, 0x5a, 0x99, 0x94, 0x1b, 0x5d, 0x5b, 0x9c, 0x66, 0x3f, 0xac, 0x28, 0x79, 0x02, 0xa8, 0xd5, 0x3e, 0x3b, 0x71, 0x66, 0x57, 0x91, 0xcc, 0x11, 0x59, 0xab, 0xc7, 0xe6]

def d49F8 : Bytes := [0x39, 0x80, 0xcc, 0x06, 0xb9, 0xb9, 0x56, 0xcb, 0xdf, 0x0d, 0x52, 0x2d, 0x29, 0x88, 0x0b, 0x28, 0x77, 0xd5, 0x57, 0x7b, 0x6a, 0x72, 0x54, 0x45, 0x1f, 0x02, 0xe4, 0xd7, 0xe1, 0x4b, 0xa7, 0x4d]

def d49Fields : List BLT := [.bytes d49F0, .bytes d49F1, .bytes d49F2, .bytes d49F3, .bytes d49F4, .bytes d49F5, .bytes d49F6, .bytes d49F7, .bytes d49F8]

def d49Payload : Bytes := [0x83] ++ d49F0 ++ [0x84] ++ d49F1 ++ [0x83] ++ d49F2 ++ [0x80] ++ d49F3 ++ [0x80] ++ d49F4 ++ [0xb9, 0x02, 0x05] ++ d49F5 ++ [] ++ d49F6 ++ [0xa0] ++ d49F7 ++ [0xa0] ++ d49F8

def d49Signed : Bytes := [0xf9, 0x02, 0x5a] ++ d49Payload

def d49Tx : Tx := { nonce := 185229, gas := 175000, value := 0, data := d49F5, v := 38, r := d49F7, s := d49F8, type := .zero 3897242835 none }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d49_literal : d49Signed = [0xf9, 0x02, 0x5a, 0x83, 0x02, 0xd3, 0x8d, 0x84, 0xe8, 0x4b, 0x34, 0xd3, 0x83, 0x02, 0xab, 0x98, 0x80, 0x80, 0xb9, 0x02, 0x05, 0x60, 0x60, 0x60, 0x40, 0x52, 0x34, 0x15, 0x61, 0x00, 0x0f, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x33, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0xb9, 0x69, 0x1e, 0xb0, 0xe3, 0xc0, 0xb2, 0x37, 0xfc, 0x7e, 0x92, 0x07, 0x72, 0xda, 0x27, 0x3e, 0xb1, 0x61, 0xe5, 0x95, 0x59, 0xcd, 0xa2, 0x5b, 0x73, 0xf8, 0x02, 0x8c, 0x10, 0x84, 0xcb, 0xf2, 0x30, 0x60, 0x40, 0x51, 0x80, 0x82, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x01, 0x91, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x61, 0x01, 0x6d, 0x80, 0x61, 0x00, 0x98, 0x60, 0x00, 0x39, 0x60, 0x00, 0xf3, 0x00, 0x60, 0x60, 0x60, 0x40, 0x52, 0x60, 0x00, 0x80, 0x30, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x31, 0x91, 0x50, 0x60, 0x00, 0x82, 0x11, 0x15, 0x15, 0x61, 0x00, 0x30, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x73, 0xaf, 0x19, 0x31, 0xc2, 0x0e, 0xe0, 0xc1, 0x1b, 0xea, 0x17, 0xa4, 0x1b, 0xfb, 0xba, 0xd2, 0x99, 0xb2, 0x76, 0x3b, 0xc0, 0x90, 0x50, 0x80, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x61, 0x08, 0xfc, 0x83, 0x90, 0x81, 0x15, 0x02, 0x90, 0x60, 0x40, 0x51, 0x60, 0x00, 0x60, 0x40, 0x51, 0x80, 0x83, 0x03, 0x81, 0x85, 0x88, 0x88, 0xf1, 0x93, 0x50, 0x50, 0x50, 0x50, 0x15, 0x15, 0x61, 0x00, 0x87, 0x57, 0x60, 0x00, 0x80, 0xfd, 0x5b, 0x80, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x7f, 0xe6, 0x59, 0xbb, 0x22, 0x72, 0x6a, 0xfd, 0x60, 0x09, 0xb1, 0x7c, 0x3a, 0xe2, 0x36, 0x79, 0xed, 0x41, 0x78, 0x4f, 0x38, 0x21, 0x29, 0xf7, 0xfb, 0x0b, 0x2e, 0xf6, 0x77, 0x6e, 0x04, 0x13, 0xd9, 0x30, 0x33, 0x85, 0x60, 0x40, 0x51, 0x80, 0x84, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x01, 0x83, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x73, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x81, 0x52, 0x60, 0x20, 0x01, 0x82, 0x81, 0x52, 0x60, 0x20, 0x01, 0x93, 0x50, 0x50, 0x50, 0x50, 0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xa2, 0x50, 0x50, 0x00, 0x00, 0xa1, 0x65, 0x62, 0x7a, 0x7a, 0x72, 0x30, 0x58, 0x20, 0xd2, 0xaa, 0xc5, 0xa9, 0x15, 0xbf, 0x75, 0xf1, 0x0f, 0x6a, 0x15, 0xe2, 0x59, 0x46, 0x52, 0x32, 0x00, 0x95, 0x28, 0xad, 0x32, 0xea, 0x57, 0x43, 0xce, 0x15, 0x23, 0x09, 0xfc, 0xde, 0x2d, 0xd1, 0x00, 0x29, 0x26, 0xa0, 0x54, 0x50, 0x24, 0x8c, 0x8a, 0x5a, 0x99, 0x94, 0x1b, 0x5d, 0x5b, 0x9c, 0x66, 0x3f, 0xac, 0x28, 0x79, 0x02, 0xa8, 0xd5, 0x3e, 0x3b, 0x71, 0x66, 0x57, 0x91, 0xcc, 0x11, 0x59, 0xab, 0xc7, 0xe6, 0xa0, 0x39, 0x80, 0xcc, 0x06, 0xb9, 0xb9, 0x56, 0xcb, 0xdf, 0x0d, 0x52, 0x2d, 0x29, 0x88, 0x0b, 0x28, 0x77, 0xd5, 0x57, 0x7b, 0x6a, 0x72, 0x54, 0x45, 0x1f, 0x02, 0xe4, 0xd7, 0xe1, 0x4b, 0xa7, 0x4d] := by
  decide +kernel

theorem d49_payload_length : d49Payload.length = 602 := by
  decide +kernel

theorem d49_signed_length : d49Signed.length = 605 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d49_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d49Payload = some d49Fields := by
  unfold d49Payload d49Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d49F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d49F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d49F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_two _ 2 5 d49F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d49F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d49F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d49_parse : d49Signed.toBLT? = some (.list d49Fields) := by
  have outer : Bytes.toBLTDiff? 605 d49Signed = some (.list d49Fields, []) := by
    simpa only [d49Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_two 604 2 90 d49Payload [] d49Fields
        (by rw [d49_payload_length]; decide +kernel) (d49_payload_parse 595)
  unfold Bytes.toBLT?
  rw [d49_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d49_decode :
    (d49Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d49Tx := by
  rw [d49_parse]
  decide +kernel

theorem d49_blt : d49Tx.toBLT = .list d49Fields := by
  norm_num only [d49Tx, d49Fields, d49F0, d49F1, d49F2, d49F3, d49F4, d49F6, d49F7, d49F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d49_encode0 : (BLT.bytes d49F0).toBytes = [0x83] ++ d49F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d49F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d49_encode1 : (BLT.bytes d49F1).toBytes = [0x84] ++ d49F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d49F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d49_encode2 : (BLT.bytes d49F2).toBytes = [0x83] ++ d49F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d49F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d49_encode3 : (BLT.bytes d49F3).toBytes = [0x80] ++ d49F3 := by
  unfold d49F3
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d49_encode4 : (BLT.bytes d49F4).toBytes = [0x80] ++ d49F4 := by
  unfold d49F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d49_encode5 : (BLT.bytes d49F5).toBytes = [0xb9, 0x02, 0x05] ++ d49F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d49F5.length = 517 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d49_encode6 : (BLT.bytes d49F6).toBytes = [] ++ d49F6 := by
  unfold d49F6
  rw [BLT.toBytes]
  decide +kernel

theorem d49_encode7 : (BLT.bytes d49F7).toBytes = [0xa0] ++ d49F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d49F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d49_encode8 : (BLT.bytes d49F8).toBytes = [0xa0] ++ d49F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d49F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d49_canonical : d49Tx.toBLT.toBytes = d49Signed := by
  have encoded : BLTs.toBytesJoin d49Fields = d49Payload := by
    simp only [d49Fields, BLTs.toBytesJoin,
      d49_encode0, d49_encode1, d49_encode2, d49_encode3, d49_encode4, d49_encode5, d49_encode6, d49_encode7, d49_encode8, d49Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d49_blt, BLT.toBytes, BLTs.toBytes, encoded, d49_payload_length]
  norm_num only [d49Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d50F0 : Bytes := [0x3a]

def d50F1 : Bytes := [0xe3, 0x3e, 0x22, 0x20]

def d50F2 : Bytes := [0x01, 0x77, 0x00]

def d50F3 : Bytes := [0xe6, 0x2e, 0x6e, 0x6c, 0x3b, 0x80, 0x8f, 0xaa, 0xd3, 0xa5, 0x4b, 0x22, 0x63, 0x79, 0x46, 0x65, 0x44, 0xd7, 0x6e, 0xa4]

def d50F4 : Bytes := []

def d50F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x26, 0x99, 0xe1, 0x5b, 0x0a, 0x22, 0x82, 0xb8, 0xfb, 0x75, 0xb4, 0x0b, 0x48, 0x56, 0x3f, 0xbd, 0x81, 0x17, 0xa1, 0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1c, 0x03, 0xa1, 0x80]

def d50F6 : Bytes := [0x26]

def d50F7 : Bytes := [0xf1, 0x1f, 0x56, 0x51, 0xc6, 0xbb, 0xa9, 0x76, 0x6d, 0xc1, 0xe4, 0x76, 0x25, 0xa3, 0x9a, 0x83, 0xb2, 0x6b, 0xc3, 0xc3, 0xa4, 0xff, 0x7d, 0xdb, 0xb4, 0x14, 0xc0, 0x4f, 0x32, 0x50, 0xdb, 0x6e]

def d50F8 : Bytes := [0x58, 0x88, 0xa5, 0x60, 0x1b, 0xf9, 0x2a, 0x9a, 0x31, 0xa8, 0x8a, 0x19, 0xf8, 0xe9, 0x4a, 0xae, 0x81, 0x51, 0x99, 0x99, 0xdd, 0x41, 0xe4, 0xb6, 0xf0, 0xab, 0xda, 0x7d, 0xc7, 0xf3, 0x55, 0x58]

def d50Fields : List BLT := [.bytes d50F0, .bytes d50F1, .bytes d50F2, .bytes d50F3, .bytes d50F4, .bytes d50F5, .bytes d50F6, .bytes d50F7, .bytes d50F8]

def d50Payload : Bytes := [] ++ d50F0 ++ [0x84] ++ d50F1 ++ [0x83] ++ d50F2 ++ [0x94] ++ d50F3 ++ [0x80] ++ d50F4 ++ [0xb8, 0x44] ++ d50F5 ++ [] ++ d50F6 ++ [0xa0] ++ d50F7 ++ [0xa0] ++ d50F8

def d50Signed : Bytes := [0xf8, 0xa9] ++ d50Payload

def d50Tx : Tx := { nonce := 58, gas := 96000, value := 0, data := d50F5, v := 38, r := d50F7, s := d50F8, type := .zero 3812500000 (some 0xe62e6e6c3b808faad3a54b226379466544d76ea4) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d50_literal : d50Signed = [0xf8, 0xa9, 0x3a, 0x84, 0xe3, 0x3e, 0x22, 0x20, 0x83, 0x01, 0x77, 0x00, 0x94, 0xe6, 0x2e, 0x6e, 0x6c, 0x3b, 0x80, 0x8f, 0xaa, 0xd3, 0xa5, 0x4b, 0x22, 0x63, 0x79, 0x46, 0x65, 0x44, 0xd7, 0x6e, 0xa4, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x26, 0x99, 0xe1, 0x5b, 0x0a, 0x22, 0x82, 0xb8, 0xfb, 0x75, 0xb4, 0x0b, 0x48, 0x56, 0x3f, 0xbd, 0x81, 0x17, 0xa1, 0x56, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1c, 0x03, 0xa1, 0x80, 0x26, 0xa0, 0xf1, 0x1f, 0x56, 0x51, 0xc6, 0xbb, 0xa9, 0x76, 0x6d, 0xc1, 0xe4, 0x76, 0x25, 0xa3, 0x9a, 0x83, 0xb2, 0x6b, 0xc3, 0xc3, 0xa4, 0xff, 0x7d, 0xdb, 0xb4, 0x14, 0xc0, 0x4f, 0x32, 0x50, 0xdb, 0x6e, 0xa0, 0x58, 0x88, 0xa5, 0x60, 0x1b, 0xf9, 0x2a, 0x9a, 0x31, 0xa8, 0x8a, 0x19, 0xf8, 0xe9, 0x4a, 0xae, 0x81, 0x51, 0x99, 0x99, 0xdd, 0x41, 0xe4, 0xb6, 0xf0, 0xab, 0xda, 0x7d, 0xc7, 0xf3, 0x55, 0x58] := by
  decide +kernel

theorem d50_payload_length : d50Payload.length = 169 := by
  decide +kernel

theorem d50_signed_length : d50Signed.length = 171 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d50_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d50Payload = some d50Fields := by
  unfold d50Payload d50Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d50F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d50F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d50F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d50F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d50F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d50F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d50_parse : d50Signed.toBLT? = some (.list d50Fields) := by
  have outer : Bytes.toBLTDiff? 171 d50Signed = some (.list d50Fields, []) := by
    simpa only [d50Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 170 169 d50Payload [] d50Fields
        (by rw [d50_payload_length]; decide +kernel) (d50_payload_parse 161)
  unfold Bytes.toBLT?
  rw [d50_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d50_decode :
    (d50Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d50Tx := by
  rw [d50_parse]
  decide +kernel

theorem d50_blt : d50Tx.toBLT = .list d50Fields := by
  norm_num only [d50Tx, d50Fields, d50F0, d50F1, d50F2, d50F3, d50F4, d50F6, d50F7, d50F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d50_encode0 : (BLT.bytes d50F0).toBytes = [] ++ d50F0 := by
  unfold d50F0
  rw [BLT.toBytes]
  decide +kernel

theorem d50_encode1 : (BLT.bytes d50F1).toBytes = [0x84] ++ d50F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d50F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d50_encode2 : (BLT.bytes d50F2).toBytes = [0x83] ++ d50F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d50F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d50_encode3 : (BLT.bytes d50F3).toBytes = [0x94] ++ d50F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d50F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d50_encode4 : (BLT.bytes d50F4).toBytes = [0x80] ++ d50F4 := by
  unfold d50F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d50_encode5 : (BLT.bytes d50F5).toBytes = [0xb8, 0x44] ++ d50F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d50F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d50_encode6 : (BLT.bytes d50F6).toBytes = [] ++ d50F6 := by
  unfold d50F6
  rw [BLT.toBytes]
  decide +kernel

theorem d50_encode7 : (BLT.bytes d50F7).toBytes = [0xa0] ++ d50F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d50F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d50_encode8 : (BLT.bytes d50F8).toBytes = [0xa0] ++ d50F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d50F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d50_canonical : d50Tx.toBLT.toBytes = d50Signed := by
  have encoded : BLTs.toBytesJoin d50Fields = d50Payload := by
    simp only [d50Fields, BLTs.toBytesJoin,
      d50_encode0, d50_encode1, d50_encode2, d50_encode3, d50_encode4, d50_encode5, d50_encode6, d50_encode7, d50_encode8, d50Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d50_blt, BLT.toBytes, BLTs.toBytes, encoded, d50_payload_length]
  norm_num only [d50Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d51F0 : Bytes := [0x04]

def d51F1 : Bytes := [0xe3, 0x3e, 0x22, 0x20]

def d51F2 : Bytes := [0xea, 0x60]

def d51F3 : Bytes := [0x45, 0x01, 0xb1, 0x84, 0x69, 0x4b, 0x40, 0x1b, 0x53, 0xb3, 0xa4, 0xf2, 0x66, 0xf8, 0xef, 0x24, 0xfe, 0xc0, 0x9d, 0xf8]

def d51F4 : Bytes := []

def d51F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd6, 0x97, 0x00, 0x8d, 0x1b, 0xf5, 0x36, 0xfc, 0x65, 0x4a, 0x06, 0x7a, 0x3e, 0x2f, 0x91, 0xd6, 0xc0, 0x39, 0x66, 0xda, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05, 0x87, 0x88, 0xcb, 0x94, 0xb1, 0xd8, 0x00, 0x00]

def d51F6 : Bytes := [0x26]

def d51F7 : Bytes := [0xe8, 0x6b, 0x43, 0x87, 0x33, 0x87, 0xde, 0xcb, 0x57, 0xe7, 0x0a, 0xd1, 0x68, 0x10, 0x91, 0x85, 0xf5, 0x77, 0x5d, 0xe7, 0xad, 0x4b, 0x8e, 0xbe, 0x34, 0x29, 0x18, 0xeb, 0x4d, 0x89, 0x34, 0x69]

def d51F8 : Bytes := [0x24, 0x7f, 0x1d, 0xfc, 0x6c, 0x2f, 0xa6, 0x4c, 0x8e, 0x30, 0x55, 0xce, 0x9b, 0xc8, 0x17, 0x03, 0x78, 0x9c, 0xcb, 0x77, 0x6b, 0x2d, 0xa9, 0x7c, 0x15, 0x35, 0xfb, 0xde, 0x81, 0xe2, 0x57, 0xd6]

def d51Fields : List BLT := [.bytes d51F0, .bytes d51F1, .bytes d51F2, .bytes d51F3, .bytes d51F4, .bytes d51F5, .bytes d51F6, .bytes d51F7, .bytes d51F8]

def d51Payload : Bytes := [] ++ d51F0 ++ [0x84] ++ d51F1 ++ [0x82] ++ d51F2 ++ [0x94] ++ d51F3 ++ [0x80] ++ d51F4 ++ [0xb8, 0x44] ++ d51F5 ++ [] ++ d51F6 ++ [0xa0] ++ d51F7 ++ [0xa0] ++ d51F8

def d51Signed : Bytes := [0xf8, 0xa8] ++ d51Payload

def d51Tx : Tx := { nonce := 4, gas := 60000, value := 0, data := d51F5, v := 38, r := d51F7, s := d51F8, type := .zero 3812500000 (some 0x4501b184694b401b53b3a4f266f8ef24fec09df8) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d51_literal : d51Signed = [0xf8, 0xa8, 0x04, 0x84, 0xe3, 0x3e, 0x22, 0x20, 0x82, 0xea, 0x60, 0x94, 0x45, 0x01, 0xb1, 0x84, 0x69, 0x4b, 0x40, 0x1b, 0x53, 0xb3, 0xa4, 0xf2, 0x66, 0xf8, 0xef, 0x24, 0xfe, 0xc0, 0x9d, 0xf8, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd6, 0x97, 0x00, 0x8d, 0x1b, 0xf5, 0x36, 0xfc, 0x65, 0x4a, 0x06, 0x7a, 0x3e, 0x2f, 0x91, 0xd6, 0xc0, 0x39, 0x66, 0xda, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x05, 0x87, 0x88, 0xcb, 0x94, 0xb1, 0xd8, 0x00, 0x00, 0x26, 0xa0, 0xe8, 0x6b, 0x43, 0x87, 0x33, 0x87, 0xde, 0xcb, 0x57, 0xe7, 0x0a, 0xd1, 0x68, 0x10, 0x91, 0x85, 0xf5, 0x77, 0x5d, 0xe7, 0xad, 0x4b, 0x8e, 0xbe, 0x34, 0x29, 0x18, 0xeb, 0x4d, 0x89, 0x34, 0x69, 0xa0, 0x24, 0x7f, 0x1d, 0xfc, 0x6c, 0x2f, 0xa6, 0x4c, 0x8e, 0x30, 0x55, 0xce, 0x9b, 0xc8, 0x17, 0x03, 0x78, 0x9c, 0xcb, 0x77, 0x6b, 0x2d, 0xa9, 0x7c, 0x15, 0x35, 0xfb, 0xde, 0x81, 0xe2, 0x57, 0xd6] := by
  decide +kernel

theorem d51_payload_length : d51Payload.length = 168 := by
  decide +kernel

theorem d51_signed_length : d51Signed.length = 170 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d51_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d51Payload = some d51Fields := by
  unfold d51Payload d51Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d51F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d51F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d51F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d51F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d51F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d51F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d51_parse : d51Signed.toBLT? = some (.list d51Fields) := by
  have outer : Bytes.toBLTDiff? 170 d51Signed = some (.list d51Fields, []) := by
    simpa only [d51Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 169 168 d51Payload [] d51Fields
        (by rw [d51_payload_length]; decide +kernel) (d51_payload_parse 160)
  unfold Bytes.toBLT?
  rw [d51_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d51_decode :
    (d51Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d51Tx := by
  rw [d51_parse]
  decide +kernel

theorem d51_blt : d51Tx.toBLT = .list d51Fields := by
  norm_num only [d51Tx, d51Fields, d51F0, d51F1, d51F2, d51F3, d51F4, d51F6, d51F7, d51F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d51_encode0 : (BLT.bytes d51F0).toBytes = [] ++ d51F0 := by
  unfold d51F0
  rw [BLT.toBytes]
  decide +kernel

theorem d51_encode1 : (BLT.bytes d51F1).toBytes = [0x84] ++ d51F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d51F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d51_encode2 : (BLT.bytes d51F2).toBytes = [0x82] ++ d51F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d51F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d51_encode3 : (BLT.bytes d51F3).toBytes = [0x94] ++ d51F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d51F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d51_encode4 : (BLT.bytes d51F4).toBytes = [0x80] ++ d51F4 := by
  unfold d51F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d51_encode5 : (BLT.bytes d51F5).toBytes = [0xb8, 0x44] ++ d51F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d51F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d51_encode6 : (BLT.bytes d51F6).toBytes = [] ++ d51F6 := by
  unfold d51F6
  rw [BLT.toBytes]
  decide +kernel

theorem d51_encode7 : (BLT.bytes d51F7).toBytes = [0xa0] ++ d51F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d51F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d51_encode8 : (BLT.bytes d51F8).toBytes = [0xa0] ++ d51F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d51F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d51_canonical : d51Tx.toBLT.toBytes = d51Signed := by
  have encoded : BLTs.toBytesJoin d51Fields = d51Payload := by
    simp only [d51Fields, BLTs.toBytesJoin,
      d51_encode0, d51_encode1, d51_encode2, d51_encode3, d51_encode4, d51_encode5, d51_encode6, d51_encode7, d51_encode8, d51Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d51_blt, BLT.toBytes, BLTs.toBytes, encoded, d51_payload_length]
  norm_num only [d51Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d52F0 : Bytes := []

def d52F1 : Bytes := [0xd6, 0x93, 0xa4, 0x00]

def d52F2 : Bytes := [0x52, 0x08]

def d52F3 : Bytes := [0x54, 0x5d, 0xd7, 0xa2, 0x85, 0xa8, 0x9b, 0xa5, 0x15, 0xb8, 0x5a, 0x39, 0xa5, 0xab, 0x46, 0x49, 0xc9, 0x05, 0xc8, 0x83]

def d52F4 : Bytes := [0x03, 0x82, 0x4d, 0x30, 0x8c, 0xab, 0xb0, 0x00]

def d52F5 : Bytes := []

def d52F6 : Bytes := [0x26]

def d52F7 : Bytes := [0xf0, 0x66, 0xbf, 0x0b, 0x12, 0x80, 0x98, 0x8f, 0x16, 0x33, 0x2f, 0x5f, 0xfa, 0x54, 0x8d, 0x6f, 0x04, 0x83, 0x47, 0xc6, 0x5b, 0x26, 0x53, 0xe8, 0xf8, 0x55, 0x50, 0xa7, 0x84, 0xd9, 0xad, 0x4c]

def d52F8 : Bytes := [0x30, 0x07, 0x10, 0x6b, 0x67, 0x15, 0x07, 0x69, 0xa6, 0x7e, 0xf8, 0x5e, 0xd7, 0x04, 0x5b, 0x04, 0xb2, 0x10, 0x1a, 0x6e, 0xf5, 0x7e, 0x85, 0x39, 0xa7, 0x0b, 0x9c, 0x16, 0x97, 0x6c, 0x8e, 0x90]

def d52Fields : List BLT := [.bytes d52F0, .bytes d52F1, .bytes d52F2, .bytes d52F3, .bytes d52F4, .bytes d52F5, .bytes d52F6, .bytes d52F7, .bytes d52F8]

def d52Payload : Bytes := [0x80] ++ d52F0 ++ [0x84] ++ d52F1 ++ [0x82] ++ d52F2 ++ [0x94] ++ d52F3 ++ [0x88] ++ d52F4 ++ [0x80] ++ d52F5 ++ [] ++ d52F6 ++ [0xa0] ++ d52F7 ++ [0xa0] ++ d52F8

def d52Signed : Bytes := [0xf8, 0x6b] ++ d52Payload

def d52Tx : Tx := { nonce := 0, gas := 21000, value := 252849400000000000, data := d52F5, v := 38, r := d52F7, s := d52F8, type := .zero 3600000000 (some 0x545dd7a285a89ba515b85a39a5ab4649c905c883) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d52_literal : d52Signed = [0xf8, 0x6b, 0x80, 0x84, 0xd6, 0x93, 0xa4, 0x00, 0x82, 0x52, 0x08, 0x94, 0x54, 0x5d, 0xd7, 0xa2, 0x85, 0xa8, 0x9b, 0xa5, 0x15, 0xb8, 0x5a, 0x39, 0xa5, 0xab, 0x46, 0x49, 0xc9, 0x05, 0xc8, 0x83, 0x88, 0x03, 0x82, 0x4d, 0x30, 0x8c, 0xab, 0xb0, 0x00, 0x80, 0x26, 0xa0, 0xf0, 0x66, 0xbf, 0x0b, 0x12, 0x80, 0x98, 0x8f, 0x16, 0x33, 0x2f, 0x5f, 0xfa, 0x54, 0x8d, 0x6f, 0x04, 0x83, 0x47, 0xc6, 0x5b, 0x26, 0x53, 0xe8, 0xf8, 0x55, 0x50, 0xa7, 0x84, 0xd9, 0xad, 0x4c, 0xa0, 0x30, 0x07, 0x10, 0x6b, 0x67, 0x15, 0x07, 0x69, 0xa6, 0x7e, 0xf8, 0x5e, 0xd7, 0x04, 0x5b, 0x04, 0xb2, 0x10, 0x1a, 0x6e, 0xf5, 0x7e, 0x85, 0x39, 0xa7, 0x0b, 0x9c, 0x16, 0x97, 0x6c, 0x8e, 0x90] := by
  decide +kernel

theorem d52_payload_length : d52Payload.length = 107 := by
  decide +kernel

theorem d52_signed_length : d52Signed.length = 109 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d52_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d52Payload = some d52Fields := by
  unfold d52Payload d52Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 4 d52F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d52F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d52F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 d52F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d52F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d52F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d52_parse : d52Signed.toBLT? = some (.list d52Fields) := by
  have outer : Bytes.toBLTDiff? 109 d52Signed = some (.list d52Fields, []) := by
    simpa only [d52Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 108 107 d52Payload [] d52Fields
        (by rw [d52_payload_length]; decide +kernel) (d52_payload_parse 99)
  unfold Bytes.toBLT?
  rw [d52_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d52_decode :
    (d52Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d52Tx := by
  rw [d52_parse]
  decide +kernel

theorem d52_blt : d52Tx.toBLT = .list d52Fields := by
  norm_num only [d52Tx, d52Fields, d52F0, d52F1, d52F2, d52F3, d52F4, d52F6, d52F7, d52F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d52_encode0 : (BLT.bytes d52F0).toBytes = [0x80] ++ d52F0 := by
  unfold d52F0
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d52_encode1 : (BLT.bytes d52F1).toBytes = [0x84] ++ d52F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d52F1.length = 4 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d52_encode2 : (BLT.bytes d52F2).toBytes = [0x82] ++ d52F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d52F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d52_encode3 : (BLT.bytes d52F3).toBytes = [0x94] ++ d52F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d52F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d52_encode4 : (BLT.bytes d52F4).toBytes = [0x88] ++ d52F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d52F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d52_encode5 : (BLT.bytes d52F5).toBytes = [0x80] ++ d52F5 := by
  unfold d52F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d52_encode6 : (BLT.bytes d52F6).toBytes = [] ++ d52F6 := by
  unfold d52F6
  rw [BLT.toBytes]
  decide +kernel

theorem d52_encode7 : (BLT.bytes d52F7).toBytes = [0xa0] ++ d52F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d52F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d52_encode8 : (BLT.bytes d52F8).toBytes = [0xa0] ++ d52F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d52F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d52_canonical : d52Tx.toBLT.toBytes = d52Signed := by
  have encoded : BLTs.toBytesJoin d52Fields = d52Payload := by
    simp only [d52Fields, BLTs.toBytesJoin,
      d52_encode0, d52_encode1, d52_encode2, d52_encode3, d52_encode4, d52_encode5, d52_encode6, d52_encode7, d52_encode8, d52Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d52_blt, BLT.toBytes, BLTs.toBytes, encoded, d52_payload_length]
  norm_num only [d52Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
