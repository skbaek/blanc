import Blanc.RlpConcrete
import Blanc.Lift.BeaconDeposit.Creation.Deploy

/-!
Unadopted candidate for the historical signed creation transaction. The creation
payload remains owned by `Creation.code`; this module proves codec facts only.
The frozen external raw-byte binding is recorded in the goal's Plans evidence.
-/

namespace Blanc.Lift.BeaconDeposit.Creation.HistoricalTx

open Jaune Blanc.RlpConcrete

/-- The signature's minimally encoded first scalar. -/
def rBytes : Bytes :=
  [0x6d, 0xb8, 0x68, 0x5e, 0x44, 0x61, 0x6a, 0xce,
   0x6f, 0x28, 0x10, 0x46, 0x92, 0x10, 0x0d, 0x6d,
   0xfb, 0x26, 0xf7, 0x7b, 0x53, 0x68, 0x8e, 0x1e,
   0xca, 0x1d, 0x97, 0x2e, 0x8d, 0xa9, 0x8c, 0xfa]

/-- The signature's minimally encoded second scalar. -/
def sBytes : Bytes :=
  [0x0f, 0x2a, 0x4c, 0x64, 0xc3, 0xe1, 0x6a, 0x47,
   0xc0, 0x3d, 0x99, 0x8b, 0xc0, 0x91, 0xc3, 0xec,
   0x99, 0x4f, 0xff, 0x4f, 0xf3, 0x07, 0x4b, 0x27,
   0x21, 0xb4, 0x81, 0x27, 0x58, 0x7f, 0x1a, 0xae]

/-- Exact signed prefix before the existing creation-code owner. -/
def rawPrefix : Bytes :=
  [0xf9, 0x1a, 0x3c, 0x80, 0x85, 0x22, 0x39, 0xe1, 0xfe, 0x00,
   0x83, 0x2f, 0xef, 0xd8, 0x80, 0x80, 0xb9, 0x19, 0xe9]

/-- Exact signed suffix following the existing creation-code owner. -/
def rawSuffix : Bytes := [0x26, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

/-- Unadopted signed raw candidate; no new creation-code copy. -/
def raw : Bytes := rawPrefix ++ code.toList ++ rawSuffix

/-- Exact nine legacy byte-string fields. -/
def fields : List BLT :=
  [.bytes [], .bytes [0x22, 0x39, 0xe1, 0xfe, 0x00],
   .bytes [0x2f, 0xef, 0xd8], .bytes [], .bytes [], .bytes code.toList,
   .bytes [0x26], .bytes rBytes, .bytes sBytes]

/-- The actual candidate legacy record; chain one is encoded by v = 38. -/
def tx : Tx :=
  { nonce := 0, gas := 3141592, value := 0, data := code.toList,
    v := 38, r := rBytes, s := sBytes, type := .zero 147000000000 none }

/-- The shared creation-code owner has the frozen payload length. -/
theorem data_length : code.toList.length = 6633 := by
  rw [ByteArray.toList_eq_toList_data]
  simp only [code, List.toList_toArray, List.length_append]
  have h0 : codeChunk0.length = 4096 := by decide +kernel
  have h1 : codeChunk1.length = 2537 := by decide +kernel
  rw [h0, h1]

theorem tx_data : tx.data = code.toList := rfl

/-- The strict decoder constructs the candidate from exactly the nine fields. -/
theorem legacy_decode : BLT.toExLegacyTx fields = .ok tx := by
  rfl

theorem wireWellFormed : Tx.WireWellFormed tx :=
  (BLT.toExLegacyTx_wireWellFormed legacy_decode).1

theorem isLegacy : tx.type.isLegacy = true :=
  (BLT.toExLegacyTx_wireWellFormed legacy_decode).2

theorem tx_toBLT : tx.toBLT = .list fields := by
  simp only [tx, Tx.toBLT, fields]
  simp only [BLT.list.injEq, List.cons.injEq, BLT.bytes.injEq, and_true, true_and]
  decide +kernel

theorem raw_length : raw.length = 6719 := by
  simp only [raw, List.length_append, data_length]
  decide +kernel

/-- The creation data uses its exact two-byte long-string header. -/
theorem data_encoded :
    (BLT.bytes code.toList).toBytes = [0xb9, 0x19, 0xe9] ++ code.toList := by
  rw [encode_bytes_many _ (by rw [data_length]; decide)]
  simp only [data_length, Nat.reduceLT, ↓reduceIte, Nat.toBytesPack,
    Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
    Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv,
    List.length_cons, List.length_nil, UInt8.reduceAdd, List.cons_append,
    List.nil_append]

/-- The list body retains the shared data payload. -/
def rawBody : Bytes :=
  [0x80, 0x85, 0x22, 0x39, 0xe1, 0xfe, 0x00, 0x83, 0x2f, 0xef, 0xd8,
   0x80, 0x80, 0xb9, 0x19, 0xe9] ++ code.toList ++ rawSuffix

theorem body_length : rawBody.length = 6716 := by
  simp only [rawBody, List.length_append, data_length]
  decide +kernel

/-- Each field parser retains the remaining payload without reducing its data. -/
theorem body_parse (k : Nat) : Bytes.toBLTs? (k + 9) rawBody = some fields := by
  have hs := decode_bytes_32 k sBytes [] (by decide +kernel)
  have ps := parse_cons k 0xa0 (sBytes ++ []) [] (.bytes sBytes) [] hs (by rw [Bytes.toBLTs?])
  have hr := decode_bytes_32 (k + 1) rBytes (0xa0 :: (sBytes ++ [])) (by decide +kernel)
  have pr := parse_cons (k + 1) 0xa0 (rBytes ++ (0xa0 :: (sBytes ++ [])))
    (0xa0 :: (sBytes ++ [])) (.bytes rBytes) [.bytes sBytes] hr ps
  have hv := decode_byte (k + 2) 0x26
    (0xa0 :: (rBytes ++ (0xa0 :: (sBytes ++ [])))) (by rfl)
  have pv := parse_cons (k + 2) 0x26 _ _ (.bytes [0x26]) _ hv pr
  have hd := decode_bytes_long_two (k + 3) 0x19 0xe9 code.toList
    (0x26 :: (0xa0 :: (rBytes ++ (0xa0 :: (sBytes ++ [])))))
    (by rw [data_length]; rfl)
  have pd := parse_cons (k + 3) 0xb9 _ _ (.bytes code.toList) _ hd pv
  have he0 := decode_empty_bytes (k + 4)
    (0xb9 :: 0x19 :: 0xe9 :: (code.toList ++
      (0x26 :: 0xa0 :: (rBytes ++ (0xa0 :: (sBytes ++ []))))))
  have pe0 := parse_cons (k + 4) 0x80 _ _ (.bytes []) _ he0 pd
  have he1 := decode_empty_bytes (k + 5)
    (0x80 :: 0xb9 :: 0x19 :: 0xe9 :: (code.toList ++
      (0x26 :: 0xa0 :: (rBytes ++ (0xa0 :: (sBytes ++ []))))))
  have pe1 := parse_cons (k + 5) 0x80 _ _ (.bytes []) _ he1 pe0
  have pg := parse_cons (k + 6) 0x83 _ _ (.bytes [0x2f, 0xef, 0xd8]) _
    (decode_bytes_three (k + 6) [0x2f, 0xef, 0xd8] _ rfl) pe1
  have pp := parse_cons (k + 7) 0x85 _ _ (.bytes [0x22, 0x39, 0xe1, 0xfe, 0x00]) _
    (decode_bytes_short (k + 7) 5 [0x22, 0x39, 0xe1, 0xfe, 0x00] _ (by decide) rfl) pg
  have pn := parse_cons (k + 8) 0x80 _ _ (.bytes []) _
    (decode_empty_bytes (k + 8) _) pp
  simpa only [rawBody, rawSuffix, fields, List.cons_append, List.nil_append,
    List.append_nil, List.append_assoc] using pn

/-- The exact raw candidate passes Jaune's full-consumption RLP parser. -/
theorem raw_decode : Bytes.toBLT? raw = some (.list fields) := by
  have hp := decode_list_long_two 6718 0x1a 0x3c rawBody [] fields
    (by rw [body_length]; rfl) (body_parse 6709)
  have he : raw = 0xf9 :: 0x1a :: 0x3c :: (rawBody ++ []) := by
    simp only [raw, rawPrefix, rawBody, List.cons_append, List.nil_append,
      List.append_nil]
  unfold Bytes.toBLT?
  rw [raw_length, he, hp]

theorem fields_encoded_body : BLTs.toBytesJoin fields = rawBody := by
  have hr : (BLT.bytes rBytes).toBytes = 0xa0 :: rBytes := by
    rw [encode_bytes_many _ (by decide +kernel)]
    decide +kernel
  have hs : (BLT.bytes sBytes).toBytes = 0xa0 :: sBytes := by
    rw [encode_bytes_many _ (by decide +kernel)]
    decide +kernel
  simp only [fields, BLTs.toBytesJoin, data_encoded, hr, hs]
  simp only [BLT.toBytes, UInt8.reduceLT, ↓reduceIte, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.toUInt8_eq,
    UInt8.reduceOfNat, UInt8.reduceAdd, rawBody, rawSuffix,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc]

/-- Canonical signed re-encoding returns precisely the raw candidate. -/
theorem tx_encoded : tx.toBLT.toBytes = raw := by
  rw [tx_toBLT]
  rw [BLT.toBytes, BLTs.toBytes]
  rw [fields_encoded_body, body_length]
  simp only [Nat.reduceLT, ↓reduceIte, Nat.toBytesPack, Nat.toBytes,
    Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMod,
    Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv, List.length_cons,
    List.length_nil, UInt8.reduceAdd, raw, rawPrefix, rawBody,
    List.cons_append, List.nil_append]

/-- Fixed EIP-155 payload, again retaining the existing creation-code owner. -/
def signingPayload : Bytes :=
  [0xf9, 0x19, 0xfc, 0x80, 0x85, 0x22, 0x39, 0xe1, 0xfe, 0x00,
   0x83, 0x2f, 0xef, 0xd8, 0x80, 0x80, 0xb9, 0x19, 0xe9] ++
  code.toList ++ [0x01, 0x80, 0x80]

/-- EIP-155 encoding is factored from the subsequent cryptographic reduction. -/
theorem signingEncoded : tx.signingHash = some signingPayload.keccak := by
  have hn : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have hp : Nat.toBytes 147000000000 = [0x22, 0x39, 0xe1, 0xfe, 0x00] := by decide +kernel
  have hg : Nat.toBytes 3141592 = [0x2f, 0xef, 0xd8] := by decide +kernel
  have h0 : Nat.toBytes 0 = [] := by decide +kernel
  have h1 : Nat.toBytes 1 = [1] := by decide +kernel
  simp only [Tx.signingHash, tx,
    Nat.reduceSub, Nat.reduceDiv, hn, hp, hg, h0, h1]
  change some ((BLT.list
    [.bytes [], .bytes [0x22, 0x39, 0xe1, 0xfe, 0x00],
     .bytes [0x2f, 0xef, 0xd8], .bytes [], .bytes [], .bytes code.toList,
     .bytes [1], .bytes [], .bytes []]).toBytes.keccak) = _
  apply congrArg some
  apply congrArg Bytes.keccak
  rw [BLT.toBytes, BLTs.toBytes]
  have hj : BLTs.toBytesJoin
      [.bytes [], .bytes [0x22, 0x39, 0xe1, 0xfe, 0x00],
       .bytes [0x2f, 0xef, 0xd8], .bytes [], .bytes [], .bytes code.toList,
       .bytes [1], .bytes [], .bytes []] =
      [0x80, 0x85, 0x22, 0x39, 0xe1, 0xfe, 0x00, 0x83, 0x2f, 0xef, 0xd8,
       0x80, 0x80, 0xb9, 0x19, 0xe9] ++ code.toList ++ [1, 0x80, 0x80] := by
    simp only [BLTs.toBytesJoin, data_encoded]
    simp only [BLT.toBytes, UInt8.reduceLT, ↓reduceIte, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.toUInt8_eq,
      UInt8.reduceOfNat, UInt8.reduceAdd, List.cons_append,
      List.nil_append, List.append_nil]
  rw [hj]
  simp only [List.length_append, List.length_cons, List.length_nil,
    data_length, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toBytesPack,
    Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceMod,
    Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv, UInt8.reduceAdd,
    signingPayload, List.cons_append, List.nil_append]

end Blanc.Lift.BeaconDeposit.Creation.HistoricalTx
