import Blanc.ExecutionBodyTransactionCut

/-! Generated only by scripts/history-anchor-body-generate.py.
Exact frozen packet bytes; historical observation adoption remains unresolved. -/

namespace Blanc.Lift.Usdc.HistoryAnchorBody

open Jaune

def d00F0 : Bytes := [0xe5, 0xa7, 0xf6]

def d00F1 : Bytes := [0x02, 0x54, 0x0b, 0xe4, 0x00]

def d00F2 : Bytes := [0xc3, 0x50]

def d00F3 : Bytes := [0xd0, 0x8e, 0xa6, 0x8a, 0xfd, 0x98, 0xa2, 0x8b, 0xb4, 0x98, 0x25, 0x16, 0x35, 0x59, 0xa3, 0x8f, 0xcb, 0xfa, 0xc8, 0x95]

def d00F4 : Bytes := [0x0d, 0xe2, 0x64, 0xcc, 0x7b, 0x04, 0xa8, 0x00]

def d00F5 : Bytes := []

def d00F6 : Bytes := [0x26]

def d00F7 : Bytes := [0xe7, 0x6c, 0xc7, 0x37, 0xc1, 0xb4, 0x4c, 0x84, 0x87, 0x1a, 0x28, 0x7c, 0xe9, 0xdc, 0xec, 0x88, 0x2a, 0x43, 0x7e, 0x7b, 0x07, 0x0b, 0xd7, 0x6a, 0xc2, 0x62, 0xaf, 0xf1, 0x9a, 0xcc, 0x6b, 0xfc]

def d00F8 : Bytes := [0x18, 0xf2, 0x7a, 0x80, 0xc4, 0xf3, 0xc2, 0xf7, 0xe8, 0xf9, 0x51, 0x30, 0xc9, 0x39, 0x5f, 0xea, 0xa5, 0x90, 0x74, 0xfb, 0xbf, 0x56, 0x6a, 0xc3, 0xe5, 0x6d, 0xf4, 0x7a, 0x74, 0xc9, 0xb7, 0x66]

def d00Fields : List BLT := [.bytes d00F0, .bytes d00F1, .bytes d00F2, .bytes d00F3, .bytes d00F4, .bytes d00F5, .bytes d00F6, .bytes d00F7, .bytes d00F8]

def d00Payload : Bytes := [0x83] ++ d00F0 ++ [0x85] ++ d00F1 ++ [0x82] ++ d00F2 ++ [0x94] ++ d00F3 ++ [0x88] ++ d00F4 ++ [0x80] ++ d00F5 ++ [] ++ d00F6 ++ [0xa0] ++ d00F7 ++ [0xa0] ++ d00F8

def d00Signed : Bytes := [0xf8, 0x6f] ++ d00Payload

def d00Tx : Tx := { nonce := 15050742, gas := 50000, value := 1000472896629680128, data := d00F5, v := 38, r := d00F7, s := d00F8, type := .zero 10000000000 (some 0xd08ea68afd98a28bb49825163559a38fcbfac895) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d00_literal : d00Signed = [0xf8, 0x6f, 0x83, 0xe5, 0xa7, 0xf6, 0x85, 0x02, 0x54, 0x0b, 0xe4, 0x00, 0x82, 0xc3, 0x50, 0x94, 0xd0, 0x8e, 0xa6, 0x8a, 0xfd, 0x98, 0xa2, 0x8b, 0xb4, 0x98, 0x25, 0x16, 0x35, 0x59, 0xa3, 0x8f, 0xcb, 0xfa, 0xc8, 0x95, 0x88, 0x0d, 0xe2, 0x64, 0xcc, 0x7b, 0x04, 0xa8, 0x00, 0x80, 0x26, 0xa0, 0xe7, 0x6c, 0xc7, 0x37, 0xc1, 0xb4, 0x4c, 0x84, 0x87, 0x1a, 0x28, 0x7c, 0xe9, 0xdc, 0xec, 0x88, 0x2a, 0x43, 0x7e, 0x7b, 0x07, 0x0b, 0xd7, 0x6a, 0xc2, 0x62, 0xaf, 0xf1, 0x9a, 0xcc, 0x6b, 0xfc, 0xa0, 0x18, 0xf2, 0x7a, 0x80, 0xc4, 0xf3, 0xc2, 0xf7, 0xe8, 0xf9, 0x51, 0x30, 0xc9, 0x39, 0x5f, 0xea, 0xa5, 0x90, 0x74, 0xfb, 0xbf, 0x56, 0x6a, 0xc3, 0xe5, 0x6d, 0xf4, 0x7a, 0x74, 0xc9, 0xb7, 0x66] := by
  decide +kernel

theorem d00_payload_length : d00Payload.length = 111 := by
  decide +kernel

theorem d00_signed_length : d00Signed.length = 113 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d00_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d00Payload = some d00Fields := by
  unfold d00Payload d00Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d00F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d00F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d00F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d00F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 d00F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d00F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d00F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d00_parse : d00Signed.toBLT? = some (.list d00Fields) := by
  have outer : Bytes.toBLTDiff? 113 d00Signed = some (.list d00Fields, []) := by
    simpa only [d00Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 112 111 d00Payload [] d00Fields
        (by rw [d00_payload_length]; decide +kernel) (d00_payload_parse 103)
  unfold Bytes.toBLT?
  rw [d00_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d00_decode :
    (d00Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d00Tx := by
  rw [d00_parse]
  decide +kernel

theorem d00_blt : d00Tx.toBLT = .list d00Fields := by
  norm_num only [d00Tx, d00Fields, d00F0, d00F1, d00F2, d00F3, d00F4, d00F6, d00F7, d00F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d00_encode0 : (BLT.bytes d00F0).toBytes = [0x83] ++ d00F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d00F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d00_encode1 : (BLT.bytes d00F1).toBytes = [0x85] ++ d00F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d00F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d00_encode2 : (BLT.bytes d00F2).toBytes = [0x82] ++ d00F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d00F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d00_encode3 : (BLT.bytes d00F3).toBytes = [0x94] ++ d00F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d00F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d00_encode4 : (BLT.bytes d00F4).toBytes = [0x88] ++ d00F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d00F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d00_encode5 : (BLT.bytes d00F5).toBytes = [0x80] ++ d00F5 := by
  unfold d00F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d00_encode6 : (BLT.bytes d00F6).toBytes = [] ++ d00F6 := by
  unfold d00F6
  rw [BLT.toBytes]
  decide +kernel

theorem d00_encode7 : (BLT.bytes d00F7).toBytes = [0xa0] ++ d00F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d00F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d00_encode8 : (BLT.bytes d00F8).toBytes = [0xa0] ++ d00F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d00F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d00_canonical : d00Tx.toBLT.toBytes = d00Signed := by
  have encoded : BLTs.toBytesJoin d00Fields = d00Payload := by
    simp only [d00Fields, BLTs.toBytesJoin,
      d00_encode0, d00_encode1, d00_encode2, d00_encode3, d00_encode4, d00_encode5, d00_encode6, d00_encode7, d00_encode8, d00Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d00_blt, BLT.toBytes, BLTs.toBytes, encoded, d00_payload_length]
  norm_num only [d00Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d01F0 : Bytes := [0x01, 0x3f, 0xac]

def d01F1 : Bytes := [0x01, 0x65, 0xa0, 0xbc, 0x00]

def d01F2 : Bytes := [0x02, 0xb6, 0x54]

def d01F3 : Bytes := [0x80, 0xd2, 0x21, 0xb8, 0x9a, 0x11, 0xf6, 0xaf, 0x47, 0xd6, 0xe4, 0x87, 0xfe, 0xb5, 0xfc, 0x22, 0xb1, 0x9a, 0x1f, 0xf8]

def d01F4 : Bytes := []

def d01F5 : Bytes := [0x39, 0x12, 0x52, 0x15, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x65, 0xb0, 0xbf, 0x8e, 0xe4, 0x94, 0x7e, 0xdd, 0x2a, 0x50, 0x0d, 0x74, 0xe5, 0x0a, 0x3d, 0x75, 0x7d, 0xc7, 0x9d, 0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x98, 0x09, 0xdf, 0x7c, 0x15, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0xbb, 0x05, 0x7e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x41, 0xa3, 0x0f, 0x09, 0xda, 0x8a, 0xdb, 0xdc, 0x61, 0x8c, 0xd6, 0xe0, 0xc4, 0xd2, 0xad, 0xc5, 0xb1, 0x58, 0xbf, 0x6f, 0xd5, 0xbc, 0xf4, 0x61, 0x2e, 0xe6, 0xc8, 0xf2, 0xd5, 0x39, 0x2d, 0xe6, 0xbc, 0x56, 0xe8, 0x8d, 0x81, 0x59, 0xfd, 0x0f, 0x78, 0x7d, 0x69, 0xf4, 0x96, 0x8d, 0x98, 0x28, 0xcb, 0x1d, 0x0b, 0xb7, 0xd4, 0xee, 0x93, 0x70, 0xb8, 0x50, 0x10, 0x53, 0x2a, 0x59, 0x0b, 0xb4, 0x4a, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

def d01F6 : Bytes := [0x1b]

def d01F7 : Bytes := [0x36, 0x87, 0x53, 0xa8, 0xe6, 0x0a, 0xa3, 0x7f, 0xae, 0x43, 0xf7, 0x3b, 0xc0, 0xd9, 0x79, 0x3c, 0x24, 0xf9, 0x3a, 0x32, 0x12, 0xbc, 0xc2, 0x1b, 0xb3, 0x92, 0x0d, 0x20, 0x68, 0x87, 0xba, 0x16]

def d01F8 : Bytes := [0x1a, 0xe1, 0xb4, 0x5f, 0xea, 0x7c, 0x0a, 0xbe, 0xa0, 0xcb, 0x38, 0x85, 0x42, 0x65, 0x28, 0xe3, 0xd5, 0xea, 0xaa, 0x83, 0xa3, 0xe5, 0x8e, 0x34, 0xe0, 0xea, 0x80, 0x0f, 0x4e, 0xfc, 0x02, 0xf4]

def d01Fields : List BLT := [.bytes d01F0, .bytes d01F1, .bytes d01F2, .bytes d01F3, .bytes d01F4, .bytes d01F5, .bytes d01F6, .bytes d01F7, .bytes d01F8]

def d01Payload : Bytes := [0x83] ++ d01F0 ++ [0x85] ++ d01F1 ++ [0x83] ++ d01F2 ++ [0x94] ++ d01F3 ++ [0x80] ++ d01F4 ++ [0xb9, 0x01, 0x84] ++ d01F5 ++ [] ++ d01F6 ++ [0xa0] ++ d01F7 ++ [0xa0] ++ d01F8

def d01Signed : Bytes := [0xf9, 0x01, 0xee] ++ d01Payload

def d01Tx : Tx := { nonce := 81836, gas := 177748, value := 0, data := d01F5, v := 27, r := d01F7, s := d01F8, type := .zero 6000000000 (some 0x80d221b89a11f6af47d6e487feb5fc22b19a1ff8) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d01_literal : d01Signed = [0xf9, 0x01, 0xee, 0x83, 0x01, 0x3f, 0xac, 0x85, 0x01, 0x65, 0xa0, 0xbc, 0x00, 0x83, 0x02, 0xb6, 0x54, 0x94, 0x80, 0xd2, 0x21, 0xb8, 0x9a, 0x11, 0xf6, 0xaf, 0x47, 0xd6, 0xe4, 0x87, 0xfe, 0xb5, 0xfc, 0x22, 0xb1, 0x9a, 0x1f, 0xf8, 0x80, 0xb9, 0x01, 0x84, 0x39, 0x12, 0x52, 0x15, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x65, 0xb0, 0xbf, 0x8e, 0xe4, 0x94, 0x7e, 0xdd, 0x2a, 0x50, 0x0d, 0x74, 0xe5, 0x0a, 0x3d, 0x75, 0x7d, 0xc7, 0x9d, 0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x98, 0x09, 0xdf, 0x7c, 0x15, 0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5e, 0xbb, 0x05, 0x7e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x41, 0xa3, 0x0f, 0x09, 0xda, 0x8a, 0xdb, 0xdc, 0x61, 0x8c, 0xd6, 0xe0, 0xc4, 0xd2, 0xad, 0xc5, 0xb1, 0x58, 0xbf, 0x6f, 0xd5, 0xbc, 0xf4, 0x61, 0x2e, 0xe6, 0xc8, 0xf2, 0xd5, 0x39, 0x2d, 0xe6, 0xbc, 0x56, 0xe8, 0x8d, 0x81, 0x59, 0xfd, 0x0f, 0x78, 0x7d, 0x69, 0xf4, 0x96, 0x8d, 0x98, 0x28, 0xcb, 0x1d, 0x0b, 0xb7, 0xd4, 0xee, 0x93, 0x70, 0xb8, 0x50, 0x10, 0x53, 0x2a, 0x59, 0x0b, 0xb4, 0x4a, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1b, 0xa0, 0x36, 0x87, 0x53, 0xa8, 0xe6, 0x0a, 0xa3, 0x7f, 0xae, 0x43, 0xf7, 0x3b, 0xc0, 0xd9, 0x79, 0x3c, 0x24, 0xf9, 0x3a, 0x32, 0x12, 0xbc, 0xc2, 0x1b, 0xb3, 0x92, 0x0d, 0x20, 0x68, 0x87, 0xba, 0x16, 0xa0, 0x1a, 0xe1, 0xb4, 0x5f, 0xea, 0x7c, 0x0a, 0xbe, 0xa0, 0xcb, 0x38, 0x85, 0x42, 0x65, 0x28, 0xe3, 0xd5, 0xea, 0xaa, 0x83, 0xa3, 0xe5, 0x8e, 0x34, 0xe0, 0xea, 0x80, 0x0f, 0x4e, 0xfc, 0x02, 0xf4] := by
  decide +kernel

theorem d01_payload_length : d01Payload.length = 494 := by
  decide +kernel

theorem d01_signed_length : d01Signed.length = 497 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d01_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d01Payload = some d01Fields := by
  unfold d01Payload d01Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d01F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d01F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d01F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d01F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_two _ 1 132 d01F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d01F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d01F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d01_parse : d01Signed.toBLT? = some (.list d01Fields) := by
  have outer : Bytes.toBLTDiff? 497 d01Signed = some (.list d01Fields, []) := by
    simpa only [d01Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_two 496 1 238 d01Payload [] d01Fields
        (by rw [d01_payload_length]; decide +kernel) (d01_payload_parse 487)
  unfold Bytes.toBLT?
  rw [d01_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d01_decode :
    (d01Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d01Tx := by
  rw [d01_parse]
  decide +kernel

theorem d01_blt : d01Tx.toBLT = .list d01Fields := by
  norm_num only [d01Tx, d01Fields, d01F0, d01F1, d01F2, d01F3, d01F4, d01F6, d01F7, d01F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d01_encode0 : (BLT.bytes d01F0).toBytes = [0x83] ++ d01F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d01F0.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d01_encode1 : (BLT.bytes d01F1).toBytes = [0x85] ++ d01F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d01F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d01_encode2 : (BLT.bytes d01F2).toBytes = [0x83] ++ d01F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d01F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d01_encode3 : (BLT.bytes d01F3).toBytes = [0x94] ++ d01F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d01F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d01_encode4 : (BLT.bytes d01F4).toBytes = [0x80] ++ d01F4 := by
  unfold d01F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d01_encode5 : (BLT.bytes d01F5).toBytes = [0xb9, 0x01, 0x84] ++ d01F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d01F5.length = 388 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d01_encode6 : (BLT.bytes d01F6).toBytes = [] ++ d01F6 := by
  unfold d01F6
  rw [BLT.toBytes]
  decide +kernel

theorem d01_encode7 : (BLT.bytes d01F7).toBytes = [0xa0] ++ d01F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d01F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d01_encode8 : (BLT.bytes d01F8).toBytes = [0xa0] ++ d01F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d01F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d01_canonical : d01Tx.toBLT.toBytes = d01Signed := by
  have encoded : BLTs.toBytesJoin d01Fields = d01Payload := by
    simp only [d01Fields, BLTs.toBytesJoin,
      d01_encode0, d01_encode1, d01_encode2, d01_encode3, d01_encode4, d01_encode5, d01_encode6, d01_encode7, d01_encode8, d01Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d01_blt, BLT.toBytes, BLTs.toBytes, encoded, d01_payload_length]
  norm_num only [d01Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d02F0 : Bytes := [0x01]

def d02F1 : Bytes := [0x01, 0x40, 0x89, 0x2e, 0xb9]

def d02F2 : Bytes := [0x52, 0x08]

def d02F3 : Bytes := [0x74, 0x38, 0x1d, 0x45, 0x33, 0xcc, 0x43, 0x12, 0x1a, 0xbf, 0xef, 0x75, 0x66, 0x01, 0x0d, 0xd9, 0xfb, 0x7c, 0x9f, 0x7a]

def d02F4 : Bytes := [0x05, 0x73, 0x91, 0x42, 0x19, 0x05, 0x32, 0x68]

def d02F5 : Bytes := []

def d02F6 : Bytes := [0x1b]

def d02F7 : Bytes := [0x86, 0x19, 0xd6, 0xd1, 0xd6, 0xc8, 0x9f, 0xdb, 0x38, 0x3b, 0xb8, 0xac, 0x56, 0x37, 0x7e, 0x59, 0xb6, 0xcd, 0x4a, 0xd1, 0xb2, 0x94, 0xf9, 0xe9, 0xdf, 0x8c, 0x23, 0xe3, 0x42, 0x9b, 0x7a, 0x42]

def d02F8 : Bytes := [0x64, 0x86, 0xb2, 0x49, 0xa6, 0x14, 0x6c, 0xbf, 0x22, 0x69, 0x41, 0xee, 0x28, 0xa0, 0x33, 0x20, 0x51, 0x13, 0xf7, 0xfc, 0xca, 0x2e, 0xa8, 0x60, 0x7b, 0x01, 0x43, 0x80, 0xd6, 0x02, 0xdf, 0x86]

def d02Fields : List BLT := [.bytes d02F0, .bytes d02F1, .bytes d02F2, .bytes d02F3, .bytes d02F4, .bytes d02F5, .bytes d02F6, .bytes d02F7, .bytes d02F8]

def d02Payload : Bytes := [] ++ d02F0 ++ [0x85] ++ d02F1 ++ [0x82] ++ d02F2 ++ [0x94] ++ d02F3 ++ [0x88] ++ d02F4 ++ [0x80] ++ d02F5 ++ [] ++ d02F6 ++ [0xa0] ++ d02F7 ++ [0xa0] ++ d02F8

def d02Signed : Bytes := [0xf8, 0x6c] ++ d02Payload

def d02Tx : Tx := { nonce := 1, gas := 21000, value := 392817305585005160, data := d02F5, v := 27, r := d02F7, s := d02F8, type := .zero 5377699513 (some 0x74381d4533cc43121abfef7566010dd9fb7c9f7a) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d02_literal : d02Signed = [0xf8, 0x6c, 0x01, 0x85, 0x01, 0x40, 0x89, 0x2e, 0xb9, 0x82, 0x52, 0x08, 0x94, 0x74, 0x38, 0x1d, 0x45, 0x33, 0xcc, 0x43, 0x12, 0x1a, 0xbf, 0xef, 0x75, 0x66, 0x01, 0x0d, 0xd9, 0xfb, 0x7c, 0x9f, 0x7a, 0x88, 0x05, 0x73, 0x91, 0x42, 0x19, 0x05, 0x32, 0x68, 0x80, 0x1b, 0xa0, 0x86, 0x19, 0xd6, 0xd1, 0xd6, 0xc8, 0x9f, 0xdb, 0x38, 0x3b, 0xb8, 0xac, 0x56, 0x37, 0x7e, 0x59, 0xb6, 0xcd, 0x4a, 0xd1, 0xb2, 0x94, 0xf9, 0xe9, 0xdf, 0x8c, 0x23, 0xe3, 0x42, 0x9b, 0x7a, 0x42, 0xa0, 0x64, 0x86, 0xb2, 0x49, 0xa6, 0x14, 0x6c, 0xbf, 0x22, 0x69, 0x41, 0xee, 0x28, 0xa0, 0x33, 0x20, 0x51, 0x13, 0xf7, 0xfc, 0xca, 0x2e, 0xa8, 0x60, 0x7b, 0x01, 0x43, 0x80, 0xd6, 0x02, 0xdf, 0x86] := by
  decide +kernel

theorem d02_payload_length : d02Payload.length = 108 := by
  decide +kernel

theorem d02_signed_length : d02Signed.length = 110 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d02_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d02Payload = some d02Fields := by
  unfold d02Payload d02Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d02F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d02F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d02F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 8 d02F4 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d02F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d02F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d02_parse : d02Signed.toBLT? = some (.list d02Fields) := by
  have outer : Bytes.toBLTDiff? 110 d02Signed = some (.list d02Fields, []) := by
    simpa only [d02Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 109 108 d02Payload [] d02Fields
        (by rw [d02_payload_length]; decide +kernel) (d02_payload_parse 100)
  unfold Bytes.toBLT?
  rw [d02_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d02_decode :
    (d02Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d02Tx := by
  rw [d02_parse]
  decide +kernel

theorem d02_blt : d02Tx.toBLT = .list d02Fields := by
  norm_num only [d02Tx, d02Fields, d02F0, d02F1, d02F2, d02F3, d02F4, d02F6, d02F7, d02F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d02_encode0 : (BLT.bytes d02F0).toBytes = [] ++ d02F0 := by
  unfold d02F0
  rw [BLT.toBytes]
  decide +kernel

theorem d02_encode1 : (BLT.bytes d02F1).toBytes = [0x85] ++ d02F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d02F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d02_encode2 : (BLT.bytes d02F2).toBytes = [0x82] ++ d02F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d02F2.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d02_encode3 : (BLT.bytes d02F3).toBytes = [0x94] ++ d02F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d02F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d02_encode4 : (BLT.bytes d02F4).toBytes = [0x88] ++ d02F4 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d02F4.length = 8 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d02_encode5 : (BLT.bytes d02F5).toBytes = [0x80] ++ d02F5 := by
  unfold d02F5
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d02_encode6 : (BLT.bytes d02F6).toBytes = [] ++ d02F6 := by
  unfold d02F6
  rw [BLT.toBytes]
  decide +kernel

theorem d02_encode7 : (BLT.bytes d02F7).toBytes = [0xa0] ++ d02F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d02F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d02_encode8 : (BLT.bytes d02F8).toBytes = [0xa0] ++ d02F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d02F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d02_canonical : d02Tx.toBLT.toBytes = d02Signed := by
  have encoded : BLTs.toBytesJoin d02Fields = d02Payload := by
    simp only [d02Fields, BLTs.toBytesJoin,
      d02_encode0, d02_encode1, d02_encode2, d02_encode3, d02_encode4, d02_encode5, d02_encode6, d02_encode7, d02_encode8, d02Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d02_blt, BLT.toBytes, BLTs.toBytes, encoded, d02_payload_length]
  norm_num only [d02Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d03F0 : Bytes := [0x4e, 0x35]

def d03F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d03F2 : Bytes := [0x01, 0x86, 0xa0]

def d03F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d03F4 : Bytes := []

def d03F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xca, 0x3c, 0x2f, 0x48, 0x75, 0xec, 0x28, 0x04, 0x81, 0x96, 0x46, 0xf1, 0x6e, 0x40, 0xd6, 0xf2, 0xc0, 0x49, 0x4e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11, 0x6c, 0x8c]

def d03F6 : Bytes := [0x1c]

def d03F7 : Bytes := [0x83, 0xf8, 0x68, 0xfa, 0x87, 0xa2, 0xde, 0x39, 0x7a, 0x5f, 0x9d, 0xf6, 0xc2, 0x25, 0xab, 0xc8, 0x2e, 0xee, 0x01, 0x2b, 0x07, 0xd5, 0x49, 0x5f, 0x71, 0xab, 0x0e, 0x34, 0x06, 0xaa, 0x34, 0x2a]

def d03F8 : Bytes := [0x0a, 0x71, 0xe3, 0xc0, 0xf9, 0x08, 0x15, 0xee, 0xc2, 0x31, 0xf7, 0xe7, 0xbd, 0xe8, 0x12, 0xdc, 0x38, 0x68, 0xdc, 0x4e, 0xae, 0x8e, 0xd5, 0x02, 0x0e, 0x44, 0xef, 0xaa, 0x5c, 0xaf, 0x3c, 0xc0]

def d03Fields : List BLT := [.bytes d03F0, .bytes d03F1, .bytes d03F2, .bytes d03F3, .bytes d03F4, .bytes d03F5, .bytes d03F6, .bytes d03F7, .bytes d03F8]

def d03Payload : Bytes := [0x82] ++ d03F0 ++ [0x85] ++ d03F1 ++ [0x83] ++ d03F2 ++ [0x94] ++ d03F3 ++ [0x80] ++ d03F4 ++ [0xb8, 0x44] ++ d03F5 ++ [] ++ d03F6 ++ [0xa0] ++ d03F7 ++ [0xa0] ++ d03F8

def d03Signed : Bytes := [0xf8, 0xac] ++ d03Payload

def d03Tx : Tx := { nonce := 20021, gas := 100000, value := 0, data := d03F5, v := 28, r := d03F7, s := d03F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d03_literal : d03Signed = [0xf8, 0xac, 0x82, 0x4e, 0x35, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xca, 0x3c, 0x2f, 0x48, 0x75, 0xec, 0x28, 0x04, 0x81, 0x96, 0x46, 0xf1, 0x6e, 0x40, 0xd6, 0xf2, 0xc0, 0x49, 0x4e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11, 0x6c, 0x8c, 0x1c, 0xa0, 0x83, 0xf8, 0x68, 0xfa, 0x87, 0xa2, 0xde, 0x39, 0x7a, 0x5f, 0x9d, 0xf6, 0xc2, 0x25, 0xab, 0xc8, 0x2e, 0xee, 0x01, 0x2b, 0x07, 0xd5, 0x49, 0x5f, 0x71, 0xab, 0x0e, 0x34, 0x06, 0xaa, 0x34, 0x2a, 0xa0, 0x0a, 0x71, 0xe3, 0xc0, 0xf9, 0x08, 0x15, 0xee, 0xc2, 0x31, 0xf7, 0xe7, 0xbd, 0xe8, 0x12, 0xdc, 0x38, 0x68, 0xdc, 0x4e, 0xae, 0x8e, 0xd5, 0x02, 0x0e, 0x44, 0xef, 0xaa, 0x5c, 0xaf, 0x3c, 0xc0] := by
  decide +kernel

theorem d03_payload_length : d03Payload.length = 172 := by
  decide +kernel

theorem d03_signed_length : d03Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d03_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d03Payload = some d03Fields := by
  unfold d03Payload d03Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d03F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d03F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d03F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d03F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d03F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d03F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d03F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d03_parse : d03Signed.toBLT? = some (.list d03Fields) := by
  have outer : Bytes.toBLTDiff? 174 d03Signed = some (.list d03Fields, []) := by
    simpa only [d03Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d03Payload [] d03Fields
        (by rw [d03_payload_length]; decide +kernel) (d03_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d03_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d03_decode :
    (d03Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d03Tx := by
  rw [d03_parse]
  decide +kernel

theorem d03_blt : d03Tx.toBLT = .list d03Fields := by
  norm_num only [d03Tx, d03Fields, d03F0, d03F1, d03F2, d03F3, d03F4, d03F6, d03F7, d03F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d03_encode0 : (BLT.bytes d03F0).toBytes = [0x82] ++ d03F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d03F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d03_encode1 : (BLT.bytes d03F1).toBytes = [0x85] ++ d03F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d03F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d03_encode2 : (BLT.bytes d03F2).toBytes = [0x83] ++ d03F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d03F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d03_encode3 : (BLT.bytes d03F3).toBytes = [0x94] ++ d03F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d03F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d03_encode4 : (BLT.bytes d03F4).toBytes = [0x80] ++ d03F4 := by
  unfold d03F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d03_encode5 : (BLT.bytes d03F5).toBytes = [0xb8, 0x44] ++ d03F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d03F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d03_encode6 : (BLT.bytes d03F6).toBytes = [] ++ d03F6 := by
  unfold d03F6
  rw [BLT.toBytes]
  decide +kernel

theorem d03_encode7 : (BLT.bytes d03F7).toBytes = [0xa0] ++ d03F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d03F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d03_encode8 : (BLT.bytes d03F8).toBytes = [0xa0] ++ d03F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d03F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d03_canonical : d03Tx.toBLT.toBytes = d03Signed := by
  have encoded : BLTs.toBytesJoin d03Fields = d03Payload := by
    simp only [d03Fields, BLTs.toBytesJoin,
      d03_encode0, d03_encode1, d03_encode2, d03_encode3, d03_encode4, d03_encode5, d03_encode6, d03_encode7, d03_encode8, d03Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d03_blt, BLT.toBytes, BLTs.toBytes, encoded, d03_payload_length]
  norm_num only [d03Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d04F0 : Bytes := [0x4e, 0x36]

def d04F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d04F2 : Bytes := [0x01, 0x86, 0xa0]

def d04F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d04F4 : Bytes := []

def d04F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xcc, 0xe2, 0xff, 0x6f, 0xa2, 0xd7, 0xbe, 0x74, 0xae, 0x1e, 0x6c, 0xb9, 0x7b, 0x5f, 0x57, 0x9f, 0x59, 0x0f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x05, 0xad, 0x44]

def d04F6 : Bytes := [0x1b]

def d04F7 : Bytes := [0x8e, 0xa5, 0xb7, 0xc2, 0x63, 0x1e, 0xdf, 0x51, 0x65, 0xb2, 0x8d, 0x7b, 0x00, 0x77, 0x04, 0x38, 0x31, 0x1c, 0x09, 0xcb, 0x38, 0x9f, 0x44, 0x9f, 0x0e, 0xb8, 0xd4, 0x62, 0x33, 0xb7, 0x61, 0xd5]

def d04F8 : Bytes := [0x1a, 0xaf, 0x9e, 0x3e, 0x73, 0xa9, 0x25, 0xf8, 0xc3, 0xb4, 0x10, 0xd7, 0x49, 0xd0, 0x7c, 0xc4, 0x20, 0x59, 0xec, 0x02, 0x6b, 0x40, 0x8b, 0x26, 0x77, 0x88, 0x1d, 0x72, 0xa8, 0xbf, 0x28, 0xbd]

def d04Fields : List BLT := [.bytes d04F0, .bytes d04F1, .bytes d04F2, .bytes d04F3, .bytes d04F4, .bytes d04F5, .bytes d04F6, .bytes d04F7, .bytes d04F8]

def d04Payload : Bytes := [0x82] ++ d04F0 ++ [0x85] ++ d04F1 ++ [0x83] ++ d04F2 ++ [0x94] ++ d04F3 ++ [0x80] ++ d04F4 ++ [0xb8, 0x44] ++ d04F5 ++ [] ++ d04F6 ++ [0xa0] ++ d04F7 ++ [0xa0] ++ d04F8

def d04Signed : Bytes := [0xf8, 0xac] ++ d04Payload

def d04Tx : Tx := { nonce := 20022, gas := 100000, value := 0, data := d04F5, v := 27, r := d04F7, s := d04F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d04_literal : d04Signed = [0xf8, 0xac, 0x82, 0x4e, 0x36, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xcc, 0xe2, 0xff, 0x6f, 0xa2, 0xd7, 0xbe, 0x74, 0xae, 0x1e, 0x6c, 0xb9, 0x7b, 0x5f, 0x57, 0x9f, 0x59, 0x0f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x05, 0xad, 0x44, 0x1b, 0xa0, 0x8e, 0xa5, 0xb7, 0xc2, 0x63, 0x1e, 0xdf, 0x51, 0x65, 0xb2, 0x8d, 0x7b, 0x00, 0x77, 0x04, 0x38, 0x31, 0x1c, 0x09, 0xcb, 0x38, 0x9f, 0x44, 0x9f, 0x0e, 0xb8, 0xd4, 0x62, 0x33, 0xb7, 0x61, 0xd5, 0xa0, 0x1a, 0xaf, 0x9e, 0x3e, 0x73, 0xa9, 0x25, 0xf8, 0xc3, 0xb4, 0x10, 0xd7, 0x49, 0xd0, 0x7c, 0xc4, 0x20, 0x59, 0xec, 0x02, 0x6b, 0x40, 0x8b, 0x26, 0x77, 0x88, 0x1d, 0x72, 0xa8, 0xbf, 0x28, 0xbd] := by
  decide +kernel

theorem d04_payload_length : d04Payload.length = 172 := by
  decide +kernel

theorem d04_signed_length : d04Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d04_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d04Payload = some d04Fields := by
  unfold d04Payload d04Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d04F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d04F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d04F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d04F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d04F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d04F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d04F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d04_parse : d04Signed.toBLT? = some (.list d04Fields) := by
  have outer : Bytes.toBLTDiff? 174 d04Signed = some (.list d04Fields, []) := by
    simpa only [d04Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d04Payload [] d04Fields
        (by rw [d04_payload_length]; decide +kernel) (d04_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d04_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d04_decode :
    (d04Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d04Tx := by
  rw [d04_parse]
  decide +kernel

theorem d04_blt : d04Tx.toBLT = .list d04Fields := by
  norm_num only [d04Tx, d04Fields, d04F0, d04F1, d04F2, d04F3, d04F4, d04F6, d04F7, d04F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d04_encode0 : (BLT.bytes d04F0).toBytes = [0x82] ++ d04F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d04F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d04_encode1 : (BLT.bytes d04F1).toBytes = [0x85] ++ d04F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d04F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d04_encode2 : (BLT.bytes d04F2).toBytes = [0x83] ++ d04F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d04F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d04_encode3 : (BLT.bytes d04F3).toBytes = [0x94] ++ d04F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d04F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d04_encode4 : (BLT.bytes d04F4).toBytes = [0x80] ++ d04F4 := by
  unfold d04F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d04_encode5 : (BLT.bytes d04F5).toBytes = [0xb8, 0x44] ++ d04F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d04F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d04_encode6 : (BLT.bytes d04F6).toBytes = [] ++ d04F6 := by
  unfold d04F6
  rw [BLT.toBytes]
  decide +kernel

theorem d04_encode7 : (BLT.bytes d04F7).toBytes = [0xa0] ++ d04F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d04F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d04_encode8 : (BLT.bytes d04F8).toBytes = [0xa0] ++ d04F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d04F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d04_canonical : d04Tx.toBLT.toBytes = d04Signed := by
  have encoded : BLTs.toBytesJoin d04Fields = d04Payload := by
    simp only [d04Fields, BLTs.toBytesJoin,
      d04_encode0, d04_encode1, d04_encode2, d04_encode3, d04_encode4, d04_encode5, d04_encode6, d04_encode7, d04_encode8, d04Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d04_blt, BLT.toBytes, BLTs.toBytes, encoded, d04_payload_length]
  norm_num only [d04Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d05F0 : Bytes := [0x4e, 0x37]

def d05F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d05F2 : Bytes := [0x01, 0x86, 0xa0]

def d05F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d05F4 : Bytes := []

def d05F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xe2, 0x28, 0xaf, 0xa8, 0xc8, 0x8f, 0x9d, 0x22, 0x63, 0xb3, 0xcd, 0x98, 0xf6, 0x5b, 0xe4, 0xfc, 0x9f, 0x68, 0x1c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x9d, 0x4f, 0xe0]

def d05F6 : Bytes := [0x1c]

def d05F7 : Bytes := [0x5a, 0x38, 0x4d, 0x29, 0x4c, 0x85, 0xdd, 0xf8, 0x01, 0xde, 0x44, 0x86, 0xf5, 0xce, 0xf2, 0xb8, 0xd5, 0xd9, 0xa7, 0xab, 0x42, 0x07, 0xde, 0x5f, 0x5c, 0xc3, 0x7f, 0xca, 0xa6, 0xaf, 0xc0, 0x24]

def d05F8 : Bytes := [0x05, 0x7c, 0xcc, 0xe8, 0x77, 0x5a, 0x99, 0x70, 0x2d, 0x3a, 0x2f, 0xb2, 0x45, 0x4a, 0x16, 0xc7, 0xab, 0x5b, 0x69, 0x8c, 0x12, 0xb6, 0x44, 0xb0, 0x68, 0x07, 0xb7, 0x78, 0x1a, 0x2c, 0xe7, 0x20]

def d05Fields : List BLT := [.bytes d05F0, .bytes d05F1, .bytes d05F2, .bytes d05F3, .bytes d05F4, .bytes d05F5, .bytes d05F6, .bytes d05F7, .bytes d05F8]

def d05Payload : Bytes := [0x82] ++ d05F0 ++ [0x85] ++ d05F1 ++ [0x83] ++ d05F2 ++ [0x94] ++ d05F3 ++ [0x80] ++ d05F4 ++ [0xb8, 0x44] ++ d05F5 ++ [] ++ d05F6 ++ [0xa0] ++ d05F7 ++ [0xa0] ++ d05F8

def d05Signed : Bytes := [0xf8, 0xac] ++ d05Payload

def d05Tx : Tx := { nonce := 20023, gas := 100000, value := 0, data := d05F5, v := 28, r := d05F7, s := d05F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d05_literal : d05Signed = [0xf8, 0xac, 0x82, 0x4e, 0x37, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xe2, 0x28, 0xaf, 0xa8, 0xc8, 0x8f, 0x9d, 0x22, 0x63, 0xb3, 0xcd, 0x98, 0xf6, 0x5b, 0xe4, 0xfc, 0x9f, 0x68, 0x1c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x9d, 0x4f, 0xe0, 0x1c, 0xa0, 0x5a, 0x38, 0x4d, 0x29, 0x4c, 0x85, 0xdd, 0xf8, 0x01, 0xde, 0x44, 0x86, 0xf5, 0xce, 0xf2, 0xb8, 0xd5, 0xd9, 0xa7, 0xab, 0x42, 0x07, 0xde, 0x5f, 0x5c, 0xc3, 0x7f, 0xca, 0xa6, 0xaf, 0xc0, 0x24, 0xa0, 0x05, 0x7c, 0xcc, 0xe8, 0x77, 0x5a, 0x99, 0x70, 0x2d, 0x3a, 0x2f, 0xb2, 0x45, 0x4a, 0x16, 0xc7, 0xab, 0x5b, 0x69, 0x8c, 0x12, 0xb6, 0x44, 0xb0, 0x68, 0x07, 0xb7, 0x78, 0x1a, 0x2c, 0xe7, 0x20] := by
  decide +kernel

theorem d05_payload_length : d05Payload.length = 172 := by
  decide +kernel

theorem d05_signed_length : d05Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d05_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d05Payload = some d05Fields := by
  unfold d05Payload d05Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d05F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d05F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d05F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d05F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d05F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d05F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d05F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d05_parse : d05Signed.toBLT? = some (.list d05Fields) := by
  have outer : Bytes.toBLTDiff? 174 d05Signed = some (.list d05Fields, []) := by
    simpa only [d05Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d05Payload [] d05Fields
        (by rw [d05_payload_length]; decide +kernel) (d05_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d05_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d05_decode :
    (d05Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d05Tx := by
  rw [d05_parse]
  decide +kernel

theorem d05_blt : d05Tx.toBLT = .list d05Fields := by
  norm_num only [d05Tx, d05Fields, d05F0, d05F1, d05F2, d05F3, d05F4, d05F6, d05F7, d05F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d05_encode0 : (BLT.bytes d05F0).toBytes = [0x82] ++ d05F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d05F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d05_encode1 : (BLT.bytes d05F1).toBytes = [0x85] ++ d05F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d05F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d05_encode2 : (BLT.bytes d05F2).toBytes = [0x83] ++ d05F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d05F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d05_encode3 : (BLT.bytes d05F3).toBytes = [0x94] ++ d05F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d05F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d05_encode4 : (BLT.bytes d05F4).toBytes = [0x80] ++ d05F4 := by
  unfold d05F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d05_encode5 : (BLT.bytes d05F5).toBytes = [0xb8, 0x44] ++ d05F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d05F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d05_encode6 : (BLT.bytes d05F6).toBytes = [] ++ d05F6 := by
  unfold d05F6
  rw [BLT.toBytes]
  decide +kernel

theorem d05_encode7 : (BLT.bytes d05F7).toBytes = [0xa0] ++ d05F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d05F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d05_encode8 : (BLT.bytes d05F8).toBytes = [0xa0] ++ d05F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d05F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d05_canonical : d05Tx.toBLT.toBytes = d05Signed := by
  have encoded : BLTs.toBytesJoin d05Fields = d05Payload := by
    simp only [d05Fields, BLTs.toBytesJoin,
      d05_encode0, d05_encode1, d05_encode2, d05_encode3, d05_encode4, d05_encode5, d05_encode6, d05_encode7, d05_encode8, d05Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d05_blt, BLT.toBytes, BLTs.toBytes, encoded, d05_payload_length]
  norm_num only [d05Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d06F0 : Bytes := [0x4e, 0x38]

def d06F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d06F2 : Bytes := [0x01, 0x86, 0xa0]

def d06F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d06F4 : Bytes := []

def d06F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xe3, 0x46, 0x57, 0xb5, 0xf3, 0x9f, 0x17, 0xc2, 0x46, 0x40, 0x3b, 0x18, 0xf4, 0xbe, 0x1b, 0xb5, 0x5d, 0xe5, 0x34, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd5, 0x88, 0x74]

def d06F6 : Bytes := [0x1b]

def d06F7 : Bytes := [0x4b, 0x81, 0xaf, 0xff, 0xa6, 0xac, 0x08, 0x73, 0x78, 0x40, 0x79, 0x1e, 0xea, 0x05, 0x51, 0x41, 0xbc, 0xff, 0x23, 0x4b, 0x0a, 0xcc, 0xe1, 0x04, 0x71, 0xde, 0xef, 0xb9, 0x7d, 0x12, 0xa4, 0x8e]

def d06F8 : Bytes := [0x6e, 0xe5, 0x4d, 0xa6, 0xd9, 0x26, 0xd0, 0xd8, 0x78, 0xcd, 0xbf, 0xd8, 0x33, 0x28, 0x99, 0xb6, 0xdd, 0xdf, 0x68, 0xaf, 0x9e, 0xa7, 0x0c, 0x88, 0xe1, 0x58, 0x39, 0xa3, 0xfe, 0x6c, 0x54, 0xd6]

def d06Fields : List BLT := [.bytes d06F0, .bytes d06F1, .bytes d06F2, .bytes d06F3, .bytes d06F4, .bytes d06F5, .bytes d06F6, .bytes d06F7, .bytes d06F8]

def d06Payload : Bytes := [0x82] ++ d06F0 ++ [0x85] ++ d06F1 ++ [0x83] ++ d06F2 ++ [0x94] ++ d06F3 ++ [0x80] ++ d06F4 ++ [0xb8, 0x44] ++ d06F5 ++ [] ++ d06F6 ++ [0xa0] ++ d06F7 ++ [0xa0] ++ d06F8

def d06Signed : Bytes := [0xf8, 0xac] ++ d06Payload

def d06Tx : Tx := { nonce := 20024, gas := 100000, value := 0, data := d06F5, v := 27, r := d06F7, s := d06F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d06_literal : d06Signed = [0xf8, 0xac, 0x82, 0x4e, 0x38, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xe3, 0x46, 0x57, 0xb5, 0xf3, 0x9f, 0x17, 0xc2, 0x46, 0x40, 0x3b, 0x18, 0xf4, 0xbe, 0x1b, 0xb5, 0x5d, 0xe5, 0x34, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd5, 0x88, 0x74, 0x1b, 0xa0, 0x4b, 0x81, 0xaf, 0xff, 0xa6, 0xac, 0x08, 0x73, 0x78, 0x40, 0x79, 0x1e, 0xea, 0x05, 0x51, 0x41, 0xbc, 0xff, 0x23, 0x4b, 0x0a, 0xcc, 0xe1, 0x04, 0x71, 0xde, 0xef, 0xb9, 0x7d, 0x12, 0xa4, 0x8e, 0xa0, 0x6e, 0xe5, 0x4d, 0xa6, 0xd9, 0x26, 0xd0, 0xd8, 0x78, 0xcd, 0xbf, 0xd8, 0x33, 0x28, 0x99, 0xb6, 0xdd, 0xdf, 0x68, 0xaf, 0x9e, 0xa7, 0x0c, 0x88, 0xe1, 0x58, 0x39, 0xa3, 0xfe, 0x6c, 0x54, 0xd6] := by
  decide +kernel

theorem d06_payload_length : d06Payload.length = 172 := by
  decide +kernel

theorem d06_signed_length : d06Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d06_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d06Payload = some d06Fields := by
  unfold d06Payload d06Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d06F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d06F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d06F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d06F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d06F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d06F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d06F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d06_parse : d06Signed.toBLT? = some (.list d06Fields) := by
  have outer : Bytes.toBLTDiff? 174 d06Signed = some (.list d06Fields, []) := by
    simpa only [d06Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d06Payload [] d06Fields
        (by rw [d06_payload_length]; decide +kernel) (d06_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d06_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d06_decode :
    (d06Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d06Tx := by
  rw [d06_parse]
  decide +kernel

theorem d06_blt : d06Tx.toBLT = .list d06Fields := by
  norm_num only [d06Tx, d06Fields, d06F0, d06F1, d06F2, d06F3, d06F4, d06F6, d06F7, d06F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d06_encode0 : (BLT.bytes d06F0).toBytes = [0x82] ++ d06F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d06F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d06_encode1 : (BLT.bytes d06F1).toBytes = [0x85] ++ d06F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d06F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d06_encode2 : (BLT.bytes d06F2).toBytes = [0x83] ++ d06F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d06F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d06_encode3 : (BLT.bytes d06F3).toBytes = [0x94] ++ d06F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d06F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d06_encode4 : (BLT.bytes d06F4).toBytes = [0x80] ++ d06F4 := by
  unfold d06F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d06_encode5 : (BLT.bytes d06F5).toBytes = [0xb8, 0x44] ++ d06F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d06F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d06_encode6 : (BLT.bytes d06F6).toBytes = [] ++ d06F6 := by
  unfold d06F6
  rw [BLT.toBytes]
  decide +kernel

theorem d06_encode7 : (BLT.bytes d06F7).toBytes = [0xa0] ++ d06F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d06F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d06_encode8 : (BLT.bytes d06F8).toBytes = [0xa0] ++ d06F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d06F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d06_canonical : d06Tx.toBLT.toBytes = d06Signed := by
  have encoded : BLTs.toBytesJoin d06Fields = d06Payload := by
    simp only [d06Fields, BLTs.toBytesJoin,
      d06_encode0, d06_encode1, d06_encode2, d06_encode3, d06_encode4, d06_encode5, d06_encode6, d06_encode7, d06_encode8, d06Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d06_blt, BLT.toBytes, BLTs.toBytes, encoded, d06_payload_length]
  norm_num only [d06Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

def d07F0 : Bytes := [0x4e, 0x39]

def d07F1 : Bytes := [0x01, 0x2a, 0x05, 0xf2, 0x00]

def d07F2 : Bytes := [0x01, 0x86, 0xa0]

def d07F3 : Bytes := [0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5]

def d07F4 : Bytes := []

def d07F5 : Bytes := [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xe8, 0x0f, 0xc0, 0x93, 0x5f, 0xa7, 0x8a, 0xdf, 0xcd, 0x3b, 0xd8, 0x48, 0xb3, 0xed, 0x32, 0x71, 0x02, 0x71, 0xb2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x74, 0x0f, 0xb8]

def d07F6 : Bytes := [0x1b]

def d07F7 : Bytes := [0x79, 0x82, 0xde, 0xb6, 0x77, 0xfe, 0xf9, 0x7b, 0xe5, 0xf3, 0x8a, 0x09, 0x3b, 0x6d, 0xff, 0xec, 0x98, 0x4a, 0x76, 0xad, 0xdc, 0x62, 0x4d, 0x5a, 0x39, 0xc3, 0x7e, 0x3b, 0x86, 0xee, 0x69, 0x6e]

def d07F8 : Bytes := [0x03, 0xf6, 0x1f, 0x72, 0xa1, 0x74, 0x2f, 0x08, 0x17, 0x97, 0xdf, 0xf4, 0x76, 0x17, 0x96, 0x97, 0x18, 0x92, 0xeb, 0x10, 0x9d, 0xbf, 0xb0, 0xa9, 0x1b, 0xc5, 0x10, 0xb2, 0x42, 0xbf, 0x85, 0x8f]

def d07Fields : List BLT := [.bytes d07F0, .bytes d07F1, .bytes d07F2, .bytes d07F3, .bytes d07F4, .bytes d07F5, .bytes d07F6, .bytes d07F7, .bytes d07F8]

def d07Payload : Bytes := [0x82] ++ d07F0 ++ [0x85] ++ d07F1 ++ [0x83] ++ d07F2 ++ [0x94] ++ d07F3 ++ [0x80] ++ d07F4 ++ [0xb8, 0x44] ++ d07F5 ++ [] ++ d07F6 ++ [0xa0] ++ d07F7 ++ [0xa0] ++ d07F8

def d07Signed : Bytes := [0xf8, 0xac] ++ d07Payload

def d07Tx : Tx := { nonce := 20025, gas := 100000, value := 0, data := d07F5, v := 27, r := d07F7, s := d07F8, type := .zero 5000000000 (some 0x1f0f468ee03a6d99cd8a09dd071494a83dc1c0e5) }

/-- Equality to the entire original frozen signed literal, including its first byte. -/
theorem d07_literal : d07Signed = [0xf8, 0xac, 0x82, 0x4e, 0x39, 0x85, 0x01, 0x2a, 0x05, 0xf2, 0x00, 0x83, 0x01, 0x86, 0xa0, 0x94, 0x1f, 0x0f, 0x46, 0x8e, 0xe0, 0x3a, 0x6d, 0x99, 0xcd, 0x8a, 0x09, 0xdd, 0x07, 0x14, 0x94, 0xa8, 0x3d, 0xc1, 0xc0, 0xe5, 0x80, 0xb8, 0x44, 0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5d, 0xe8, 0x0f, 0xc0, 0x93, 0x5f, 0xa7, 0x8a, 0xdf, 0xcd, 0x3b, 0xd8, 0x48, 0xb3, 0xed, 0x32, 0x71, 0x02, 0x71, 0xb2, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x74, 0x0f, 0xb8, 0x1b, 0xa0, 0x79, 0x82, 0xde, 0xb6, 0x77, 0xfe, 0xf9, 0x7b, 0xe5, 0xf3, 0x8a, 0x09, 0x3b, 0x6d, 0xff, 0xec, 0x98, 0x4a, 0x76, 0xad, 0xdc, 0x62, 0x4d, 0x5a, 0x39, 0xc3, 0x7e, 0x3b, 0x86, 0xee, 0x69, 0x6e, 0xa0, 0x03, 0xf6, 0x1f, 0x72, 0xa1, 0x74, 0x2f, 0x08, 0x17, 0x97, 0xdf, 0xf4, 0x76, 0x17, 0x96, 0x97, 0x18, 0x92, 0xeb, 0x10, 0x9d, 0xbf, 0xb0, 0xa9, 0x1b, 0xc5, 0x10, 0xb2, 0x42, 0xbf, 0x85, 0x8f] := by
  decide +kernel

theorem d07_payload_length : d07Payload.length = 172 := by
  decide +kernel

theorem d07_signed_length : d07Signed.length = 174 := by
  decide +kernel

/-- Nine actual Jaune field-parser steps, with full ordered consumption. -/
theorem d07_payload_parse (k : Nat) :
    Bytes.toBLTs? (k + 9) d07Payload = some d07Fields := by
  unfold d07Payload d07Fields
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 2 d07F0 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 5 d07F1 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 3 d07F2 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 20 d07F3 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_empty_bytes _ _
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_long_one _ 68 d07F5 _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_byte _ _ _ (by decide +kernel)
  apply RlpConcrete.parse_cons
  · exact RlpConcrete.decode_bytes_short _ 32 d07F7 _ (by decide +kernel) rfl
  apply RlpConcrete.parse_cons
  · simpa only [List.append_nil, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd] using RlpConcrete.decode_bytes_short _ 32 d07F8 [] (by decide +kernel) rfl
  rw [Bytes.toBLTs?]

theorem d07_parse : d07Signed.toBLT? = some (.list d07Fields) := by
  have outer : Bytes.toBLTDiff? 174 d07Signed = some (.list d07Fields, []) := by
    simpa only [d07Signed, List.cons_append, List.nil_append, List.append_nil] using
      RlpConcrete.decode_list_long_one 173 172 d07Payload [] d07Fields
        (by rw [d07_payload_length]; decide +kernel) (d07_payload_parse 164)
  unfold Bytes.toBLT?
  rw [d07_signed_length, outer]

/-- Strict Jaune legacy fields, rather than trusted normalized RPC fields. -/
theorem d07_decode :
    (d07Signed.toBLT?.bind (fun blt => blt.toExTx.toOption)) = some d07Tx := by
  rw [d07_parse]
  decide +kernel

theorem d07_blt : d07Tx.toBLT = .list d07Fields := by
  norm_num only [d07Tx, d07Fields, d07F0, d07F1, d07F2, d07F3, d07F4, d07F6, d07F7, d07F8, Tx.toBLT, Nat.toBytes, Nat.toBytes.aux, trimZero, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.toUInt8_eq, UInt8.reduceOfNat, List.dropWhile_cons, Bool.false_eq_true, ↓reduceIte, BLT.list.injEq, BLT.bytes.injEq, List.cons.injEq, true_and, and_true]
  decide +kernel

theorem d07_encode0 : (BLT.bytes d07F0).toBytes = [0x82] ++ d07F0 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d07F0.length = 2 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d07_encode1 : (BLT.bytes d07F1).toBytes = [0x85] ++ d07F1 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d07F1.length = 5 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d07_encode2 : (BLT.bytes d07F2).toBytes = [0x83] ++ d07F2 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d07F2.length = 3 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d07_encode3 : (BLT.bytes d07F3).toBytes = [0x94] ++ d07F3 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d07F3.length = 20 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d07_encode4 : (BLT.bytes d07F4).toBytes = [0x80] ++ d07F4 := by
  unfold d07F4
  rw [BLT.toBytes]
  · decide +kernel
  · intro b impossible
    cases impossible

theorem d07_encode5 : (BLT.bytes d07F5).toBytes = [0xb8, 0x44] ++ d07F5 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d07F5.length = 68 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d07_encode6 : (BLT.bytes d07F6).toBytes = [] ++ d07F6 := by
  unfold d07F6
  rw [BLT.toBytes]
  decide +kernel

theorem d07_encode7 : (BLT.bytes d07F7).toBytes = [0xa0] ++ d07F7 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d07F7.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

theorem d07_encode8 : (BLT.bytes d07F8).toBytes = [0xa0] ++ d07F8 := by
  rw [RlpConcrete.encode_bytes_many _ (by decide +kernel),
    show d07F8.length = 32 from by decide +kernel]
  norm_num only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

/-- Canonical re-encoding excludes alternate RLP representations. -/
theorem d07_canonical : d07Tx.toBLT.toBytes = d07Signed := by
  have encoded : BLTs.toBytesJoin d07Fields = d07Payload := by
    simp only [d07Fields, BLTs.toBytesJoin,
      d07_encode0, d07_encode1, d07_encode2, d07_encode3, d07_encode4, d07_encode5, d07_encode6, d07_encode7, d07_encode8, d07Payload, List.append_nil, List.append_assoc, List.nil_append]
  rw [d07_blt, BLT.toBytes, BLTs.toBytes, encoded, d07_payload_length]
  norm_num only [d07Signed, Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLT, Nat.toUInt8_eq, UInt8.reduceOfNat, UInt8.reduceAdd, List.length_cons, List.length_nil, ↓reduceIte, List.cons_append, List.nil_append]

end Blanc.Lift.Usdc.HistoryAnchorBody
