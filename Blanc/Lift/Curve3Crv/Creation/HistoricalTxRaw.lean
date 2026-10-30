import Blanc.RlpListEncode
import Blanc.Lift.LegacyRecover
import Blanc.Lift.Curve3Crv.Creation.HistoricalTx

/-!
# The 3Crv creation transaction's signed bytes and strict decoding

Codec facts for the recorded signed creation transaction `HistoricalTx.tx` (hash
`0xa7d90e46…053694f8`, block 10,809,467, index 76): the nine legacy fields with `v = 28` and an
empty receiver, the strict decoder's result (`legacy_decode`, from the shared pre-EIP-155
decoder `LegacyRecover.legacy_decode_pre155`), wire well-formedness, the exact signed bytes
`raw = rawPrefix ++ code.toList ++ rawSuffix` (3,237 bytes) with their full-consumption RLP
parse and canonical re-encoding, and the six-field pre-EIP-155 signing payload. The creation
input stays owned by `Creation.code`; no byte of it is copied here.
-/

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx

open Jaune Blanc.RlpConcrete

/-- Exact signed prefix before the creation input: the list header `f9 0ca2`, nonce `0x2a`,
gas price `85 1c0a0408ee`, gas `83 0a59c7`, empty receiver and value, and the data header
`b9 0c4f`. -/
def rawPrefix : Bytes :=
  [0xf9, 0x0c, 0xa2, 0x2a, 0x85, 0x1c, 0x0a, 0x04, 0x08, 0xee,
   0x83, 0x0a, 0x59, 0xc7, 0x80, 0x80, 0xb9, 0x0c, 0x4f]

/-- Exact signed suffix after the creation input: `v = 0x1c` and the two 32-byte scalars. -/
def rawSuffix : Bytes := [0x1c, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

/-- The recorded signed transaction bytes. -/
def raw : Bytes := rawPrefix ++ code.toList ++ rawSuffix

/-- The nine legacy byte-string fields. -/
def fields : List BLT :=
  [.bytes [0x2a], .bytes [0x1c, 0x0a, 0x04, 0x08, 0xee],
   .bytes [0x0a, 0x59, 0xc7], .bytes [], .bytes [], .bytes code.toList,
   .bytes [0x1c], .bytes rBytes, .bytes sBytes]

/-- The creation input is 3,151 bytes. -/
theorem data_length : code.toList.length = 3151 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

/-- The strict legacy decoder constructs exactly `tx` from the nine fields, and `tx` is wire
well-formed (shared pre-EIP-155 decoder; the data field is never reduced). -/
theorem legacy_decode_wf : BLT.toExLegacyTx fields = .ok tx ∧ Tx.WireWellFormed tx :=
  LegacyRecover.legacy_decode_pre155 (nonce := 42) (gp := 120427120878) (gas := 678343)
    (rcv := none) (value := 0) (v := 28) (data := code.toList) rfl rfl rfl rfl rfl
    (Or.inr rfl) rfl rfl

theorem legacy_decode : BLT.toExLegacyTx fields = .ok tx := legacy_decode_wf.1

theorem wireWellFormed : Tx.WireWellFormed tx := legacy_decode_wf.2

theorem tx_toBLT : tx.toBLT = .list fields := by
  simp only [tx, Tx.toBLT, fields]
  simp only [BLT.list.injEq, List.cons.injEq, BLT.bytes.injEq, and_true, true_and]
  decide +kernel

theorem raw_length : raw.length = 3237 := by
  simp only [raw, List.length_append, data_length]
  decide +kernel

/-- The creation data uses its exact two-byte long-string header. -/
theorem data_encoded :
    (BLT.bytes code.toList).toBytes = [0xb9, 0x0c, 0x4f] ++ code.toList := by
  rw [encode_bytes_many _ (by rw [data_length]; decide)]
  simp only [data_length, Nat.reduceLT, ↓reduceIte, Nat.toBytesPack,
    Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
    Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv,
    List.length_cons, List.length_nil, UInt8.reduceAdd, List.cons_append,
    List.nil_append]

/-- The list body, retaining the shared data payload. -/
def rawBody : Bytes :=
  [0x2a, 0x85, 0x1c, 0x0a, 0x04, 0x08, 0xee, 0x83, 0x0a, 0x59, 0xc7,
   0x80, 0x80, 0xb9, 0x0c, 0x4f] ++ code.toList ++ rawSuffix

theorem body_length : rawBody.length = 3234 := by
  simp only [rawBody, List.length_append, data_length]
  decide +kernel

/-- Each field parser retains the remaining payload without reducing its data. -/
theorem body_parse (k : Nat) : Bytes.toBLTs? (k + 9) rawBody = some fields := by
  have hs := decode_bytes_32 k sBytes [] (by decide +kernel)
  have ps := parse_cons k 0xa0 (sBytes ++ []) [] (.bytes sBytes) [] hs (by rw [Bytes.toBLTs?])
  have hr := decode_bytes_32 (k + 1) rBytes (0xa0 :: (sBytes ++ [])) (by decide +kernel)
  have pr := parse_cons (k + 1) 0xa0 (rBytes ++ (0xa0 :: (sBytes ++ [])))
    (0xa0 :: (sBytes ++ [])) (.bytes rBytes) [.bytes sBytes] hr ps
  have hv := decode_byte (k + 2) 0x1c
    (0xa0 :: (rBytes ++ (0xa0 :: (sBytes ++ [])))) (by rfl)
  have pv := parse_cons (k + 2) 0x1c _ _ (.bytes [0x1c]) _ hv pr
  have hd := decode_bytes_long_two (k + 3) 0x0c 0x4f code.toList
    (0x1c :: (0xa0 :: (rBytes ++ (0xa0 :: (sBytes ++ [])))))
    (by rw [data_length]; rfl)
  have pd := parse_cons (k + 3) 0xb9 _ _ (.bytes code.toList) _ hd pv
  have he0 := decode_empty_bytes (k + 4)
    (0xb9 :: 0x0c :: 0x4f :: (code.toList ++
      (0x1c :: 0xa0 :: (rBytes ++ (0xa0 :: (sBytes ++ []))))))
  have pe0 := parse_cons (k + 4) 0x80 _ _ (.bytes []) _ he0 pd
  have he1 := decode_empty_bytes (k + 5)
    (0x80 :: 0xb9 :: 0x0c :: 0x4f :: (code.toList ++
      (0x1c :: 0xa0 :: (rBytes ++ (0xa0 :: (sBytes ++ []))))))
  have pe1 := parse_cons (k + 5) 0x80 _ _ (.bytes []) _ he1 pe0
  have pg := parse_cons (k + 6) 0x83 _ _ (.bytes [0x0a, 0x59, 0xc7]) _
    (decode_bytes_three (k + 6) [0x0a, 0x59, 0xc7] _ rfl) pe1
  have pp := parse_cons (k + 7) 0x85 _ _ (.bytes [0x1c, 0x0a, 0x04, 0x08, 0xee]) _
    (decode_bytes_short (k + 7) 5 [0x1c, 0x0a, 0x04, 0x08, 0xee] _ (by decide) rfl) pg
  have pn := parse_cons (k + 8) 0x2a _ _ (.bytes [0x2a]) _
    (decode_byte (k + 8) 0x2a _ (by rfl)) pp
  simpa only [rawBody, rawSuffix, fields, List.cons_append, List.nil_append,
    List.append_nil, List.append_assoc] using pn

/-- The signed bytes pass Jaune's full-consumption RLP parser. -/
theorem raw_decode : Bytes.toBLT? raw = some (.list fields) := by
  have hp := decode_list_long_two 3236 0x0c 0xa2 rawBody [] fields
    (by rw [body_length]; rfl) (body_parse 3227)
  have he : raw = 0xf9 :: 0x0c :: 0xa2 :: (rawBody ++ []) := by
    simp only [raw, rawPrefix, rawBody, List.cons_append, List.nil_append,
      List.append_nil]
  unfold Bytes.toBLT?
  rw [raw_length, he, hp]

/-- The five leading scalar fields, shared by the signed list and the signing payload. -/
def headFields : List BLT :=
  [.bytes [0x2a], .bytes [0x1c, 0x0a, 0x04, 0x08, 0xee], .bytes [0x0a, 0x59, 0xc7],
   .bytes [], .bytes []]

theorem headFields_encoded :
    BLTs.toBytesJoin headFields =
      [0x2a, 0x85, 0x1c, 0x0a, 0x04, 0x08, 0xee, 0x83, 0x0a, 0x59, 0xc7, 0x80, 0x80] := by
  simp only [headFields, BLTs.toBytesJoin, BLT.toBytes, UInt8.reduceLT, ↓reduceIte,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.toUInt8_eq,
    UInt8.reduceOfNat, UInt8.reduceAdd, List.cons_append, List.nil_append, List.append_nil]

/-- The three signature fields encode to the raw suffix. -/
theorem sigFields_encoded :
    BLTs.toBytesJoin [.bytes [0x1c], .bytes rBytes, .bytes sBytes] = rawSuffix := by
  have hr : (BLT.bytes rBytes).toBytes = 0xa0 :: rBytes := by
    rw [encode_bytes_many _ (by decide +kernel)]
    decide +kernel
  have hs : (BLT.bytes sBytes).toBytes = 0xa0 :: sBytes := by
    rw [encode_bytes_many _ (by decide +kernel)]
    decide +kernel
  have hv : (BLT.bytes [0x1c]).toBytes = [0x1c] := by
    simp only [BLT.toBytes, UInt8.reduceLT, ↓reduceIte]
  simp only [BLTs.toBytesJoin, hv, hr, hs, rawSuffix, List.append_nil, List.cons_append,
    List.nil_append, List.append_assoc]

theorem fields_split :
    fields = headFields ++ [.bytes code.toList] ++ [.bytes [0x1c], .bytes rBytes, .bytes sBytes] :=
  rfl

theorem fields_encoded_body : BLTs.toBytesJoin fields = rawBody := by
  rw [fields_split, toBytesJoin_append, toBytesJoin_append, headFields_encoded,
    sigFields_encoded]
  simp only [BLTs.toBytesJoin, data_encoded, rawBody, List.append_nil, List.cons_append,
    List.nil_append]

/-- Canonical signed re-encoding returns precisely the recorded bytes. -/
theorem tx_encoded : tx.toBLT.toBytes = raw := by
  rw [tx_toBLT, encode_list_long fields_encoded_body (by rw [body_length]; decide),
    body_length]
  simp only [Nat.toBytesPack, Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
    Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv, List.length_cons,
    List.length_nil, UInt8.reduceAdd, raw, rawPrefix, rawBody, List.cons_append, List.nil_append]

/-- The six-field pre-EIP-155 signing payload (no chain-id trailer), retaining the creation
input. -/
def signingPayload : Bytes :=
  [0xf9, 0x0c, 0x5f, 0x2a, 0x85, 0x1c, 0x0a, 0x04, 0x08, 0xee,
   0x83, 0x0a, 0x59, 0xc7, 0x80, 0x80, 0xb9, 0x0c, 0x4f] ++ code.toList

/-- Pre-EIP-155 encoding, factored from the cryptographic reduction (shared
`signingHash_pre155` and `signingPayload_pre155`). -/
theorem signingEncoded : tx.signingHash = some signingPayload.keccak := by
  rw [LegacyRecover.signingHash_pre155 (p := 120427120878) (rcv := none) rfl (Or.inr rfl)]
  have hn : (UInt64.toBytes 42).sig = [0x2a] := by decide +kernel
  have hp : Nat.toBytes 120427120878 = [0x1c, 0x0a, 0x04, 0x08, 0xee] := by decide +kernel
  have hg : Nat.toBytes 678343 = [0x0a, 0x59, 0xc7] := by decide +kernel
  have h0 : Nat.toBytes 0 = [] := by decide +kernel
  have hfields : [BLT.bytes tx.nonce.toBytes.sig, .bytes (120427120878 : Nat).toBytes,
      .bytes tx.gas.toBytes, .bytes (((none : Option Adr) <&> Adr.toBytes).getD []),
      .bytes tx.value.toBytes, .bytes tx.data] =
      headFields ++ [.bytes code.toList] := by
    change [BLT.bytes (UInt64.toBytes 42).sig, .bytes (120427120878 : Nat).toBytes,
      .bytes (678343 : Nat).toBytes, .bytes [], .bytes (0 : Nat).toBytes, .bytes code.toList] = _
    rw [hn, hp, hg, h0]
    rfl
  rw [hfields, LegacyRecover.signingPayload_pre155 headFields_encoded
    (by rw [data_length]; decide)]
  simp only [data_length, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.toBytesPack,
    Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceMod, Nat.toUInt8_eq,
    UInt8.reduceOfNat, Nat.reduceDiv, UInt8.reduceAdd, signingPayload, List.cons_append,
    List.nil_append]

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx
