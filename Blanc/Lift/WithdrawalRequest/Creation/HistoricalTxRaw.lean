import Blanc.RlpConcrete
import Blanc.Lift.LegacyRecover
import Blanc.Lift.WithdrawalRequest.Creation.Deploy

/-!
# The EIP-7002 deployment transaction's signed bytes and strict decoding

Codec facts for the candidate signed keyless creation transaction `HistoricalTx.tx` (hash
`0x8ded54be…2572`, mainnet block 21,881,389, index 0): nonce 0, gas price 10^12, gas 250,000,
no receiver, zero value, the 549-byte creation input `creationCode` as data, and the
pre-EIP-155 signature `v = 27`, `r = 0x0539`. The strict decoder's result comes from the shared
`LegacyRecover.legacy_decode_pre155`; `raw = rawPrefix ++ creationCode.toList ++ rawSuffix`
(592 bytes) parses with full consumption and is the canonical re-encoding; the six-field
pre-EIP-155 signing payload is factored by `LegacyRecover.signingPayload_pre155`. The creation
input stays owned by `Creation.creationCode`; no byte of it is copied here. The values are
unadopted candidate observations.
-/

namespace Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx

open Jaune Blanc.RlpConcrete

/-- The signature's first scalar, minimally encoded. -/
def rBytes : Bytes := [0x05, 0x39]

/-- The signature's second scalar, minimally encoded (nineteen bytes). -/
def sBytes : Bytes :=
  [0x5f, 0xee, 0xb0, 0x84, 0x55, 0x1e, 0x4e, 0x03, 0xa3, 0x58,
   0x1e, 0x26, 0x9b, 0xc2, 0xea, 0x2f, 0x8d, 0x00, 0x08]

/-- The candidate creation transaction (pre-EIP-155: `v = 27`, no chain id). -/
def tx : Tx :=
  { nonce := 0, gas := 250000, value := 0, data := creationCode.toList,
    v := 27, r := rBytes, s := sBytes, type := .zero 1000000000000 none }

theorem tx_data : tx.data = creationCode.toList := rfl

/-- Exact signed prefix before the creation input: list header `f9 024d`, empty nonce,
gas price `85 e8d4a51000`, gas `83 03d090`, empty receiver and value, data header `b9 0225`. -/
def rawPrefix : Bytes :=
  [0xf9, 0x02, 0x4d, 0x80, 0x85, 0xe8, 0xd4, 0xa5, 0x10, 0x00,
   0x83, 0x03, 0xd0, 0x90, 0x80, 0x80, 0xb9, 0x02, 0x25]

/-- Exact signed suffix after the creation input: `v = 0x1b` and the two short scalars. -/
def rawSuffix : Bytes := [0x1b, 0x82] ++ rBytes ++ [0x93] ++ sBytes

/-- The candidate signed transaction bytes. -/
def raw : Bytes := rawPrefix ++ creationCode.toList ++ rawSuffix

/-- The nine legacy byte-string fields. -/
def fields : List BLT :=
  [.bytes [], .bytes [0xe8, 0xd4, 0xa5, 0x10, 0x00], .bytes [0x03, 0xd0, 0x90],
   .bytes [], .bytes [], .bytes creationCode.toList,
   .bytes [0x1b], .bytes rBytes, .bytes sBytes]

/-- The creation input is 549 bytes: the 45-byte constructor and the 504-byte runtime. -/
theorem data_length : creationCode.toList.length = 549 := by
  rw [creationCode, ByteArray.toList_eq_toList_data, List.toList_toArray,
    List.length_append, runtime_length]
  rfl

/-- The strict legacy decoder constructs exactly `tx` from the nine fields, and `tx` is wire
well-formed (shared pre-EIP-155 decoder; the data field is never reduced). -/
theorem legacy_decode_wf : BLT.toExLegacyTx fields = .ok tx ∧ Tx.WireWellFormed tx :=
  LegacyRecover.legacy_decode_pre155 (nonce := 0) (gp := 1000000000000) (gas := 250000)
    (rcv := none) (value := 0) (v := 27) (data := creationCode.toList) rfl rfl rfl rfl rfl
    (Or.inl rfl) rfl rfl

theorem tx_toBLT : tx.toBLT = .list fields := by
  simp only [tx, Tx.toBLT, fields]
  simp only [BLT.list.injEq, List.cons.injEq, BLT.bytes.injEq, and_true, true_and]
  decide +kernel

theorem raw_length : raw.length = 592 := by
  simp only [raw, List.length_append, data_length]
  decide +kernel

/-- The creation data uses its exact two-byte long-string header. -/
theorem data_encoded :
    (BLT.bytes creationCode.toList).toBytes = [0xb9, 0x02, 0x25] ++ creationCode.toList := by
  rw [encode_bytes_many _ (by rw [data_length]; decide)]
  simp only [data_length, Nat.reduceLT, ↓reduceIte, Nat.toBytesPack,
    Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceAdd,
    Nat.reduceMod, Nat.toUInt8_eq, UInt8.reduceOfNat, Nat.reduceDiv,
    List.length_cons, List.length_nil, UInt8.reduceAdd, List.cons_append,
    List.nil_append]

/-- The list body, retaining the shared data payload. -/
def rawBody : Bytes :=
  [0x80, 0x85, 0xe8, 0xd4, 0xa5, 0x10, 0x00, 0x83, 0x03, 0xd0, 0x90,
   0x80, 0x80, 0xb9, 0x02, 0x25] ++ creationCode.toList ++ rawSuffix

theorem body_length : rawBody.length = 589 := by
  simp only [rawBody, List.length_append, data_length]
  decide +kernel

/-- Each field parser retains the remaining payload without reducing its data. -/
theorem body_parse (k : Nat) : Bytes.toBLTs? (k + 9) rawBody = some fields := by
  have hs := decode_bytes_short k 19 sBytes [] (by decide) rfl
  have ps := parse_cons k 0x93 (sBytes ++ []) [] (.bytes sBytes) [] hs (by rw [Bytes.toBLTs?])
  have hr := decode_bytes_short (k + 1) 2 rBytes (0x93 :: (sBytes ++ [])) (by decide) rfl
  have pr := parse_cons (k + 1) 0x82 (rBytes ++ (0x93 :: (sBytes ++ [])))
    (0x93 :: (sBytes ++ [])) (.bytes rBytes) [.bytes sBytes] hr ps
  have hv := decode_byte (k + 2) 0x1b
    (0x82 :: (rBytes ++ (0x93 :: (sBytes ++ [])))) (by rfl)
  have pv := parse_cons (k + 2) 0x1b _ _ (.bytes [0x1b]) _ hv pr
  have hd := decode_bytes_long_two (k + 3) 0x02 0x25 creationCode.toList
    (0x1b :: (0x82 :: (rBytes ++ (0x93 :: (sBytes ++ [])))))
    (by rw [data_length]; rfl)
  have pd := parse_cons (k + 3) 0xb9 _ _ (.bytes creationCode.toList) _ hd pv
  have he0 := decode_empty_bytes (k + 4)
    (0xb9 :: 0x02 :: 0x25 :: (creationCode.toList ++
      (0x1b :: 0x82 :: (rBytes ++ (0x93 :: (sBytes ++ []))))))
  have pe0 := parse_cons (k + 4) 0x80 _ _ (.bytes []) _ he0 pd
  have he1 := decode_empty_bytes (k + 5)
    (0x80 :: 0xb9 :: 0x02 :: 0x25 :: (creationCode.toList ++
      (0x1b :: 0x82 :: (rBytes ++ (0x93 :: (sBytes ++ []))))))
  have pe1 := parse_cons (k + 5) 0x80 _ _ (.bytes []) _ he1 pe0
  have pg := parse_cons (k + 6) 0x83 _ _ (.bytes [0x03, 0xd0, 0x90]) _
    (decode_bytes_three (k + 6) [0x03, 0xd0, 0x90] _ rfl) pe1
  have pp := parse_cons (k + 7) 0x85 _ _ (.bytes [0xe8, 0xd4, 0xa5, 0x10, 0x00]) _
    (decode_bytes_short (k + 7) 5 [0xe8, 0xd4, 0xa5, 0x10, 0x00] _ (by decide) rfl) pg
  have pn := parse_cons (k + 8) 0x80 _ _ (.bytes []) _
    (decode_empty_bytes (k + 8) _) pp
  simpa only [rawBody, rawSuffix, fields, List.cons_append, List.nil_append,
    List.append_nil, List.append_assoc] using pn

/-- The signed bytes pass Jaune's full-consumption RLP parser. -/
theorem raw_decode : Bytes.toBLT? raw = some (.list fields) := by
  have hp := decode_list_long_two 591 0x02 0x4d rawBody [] fields
    (by rw [body_length]; rfl) (body_parse 582)
  have he : raw = 0xf9 :: 0x02 :: 0x4d :: (rawBody ++ []) := by
    simp only [raw, rawPrefix, rawBody, List.cons_append, List.nil_append,
      List.append_nil]
  unfold Bytes.toBLT?
  rw [raw_length, he, hp]

theorem fields_encoded_body : BLTs.toBytesJoin fields = rawBody := by
  have hr : (BLT.bytes rBytes).toBytes = 0x82 :: rBytes := by
    rw [encode_bytes_many _ (by decide)]
    decide +kernel
  have hs : (BLT.bytes sBytes).toBytes = 0x93 :: sBytes := by
    rw [encode_bytes_many _ (by decide)]
    decide +kernel
  simp only [fields, BLTs.toBytesJoin, data_encoded, hr, hs]
  simp only [BLT.toBytes, UInt8.reduceLT, ↓reduceIte, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.toUInt8_eq,
    UInt8.reduceOfNat, UInt8.reduceAdd, rawBody, rawSuffix,
    List.cons_append, List.nil_append, List.append_nil, List.append_assoc]

/-- Canonical signed re-encoding returns precisely the candidate bytes. -/
theorem tx_encoded : tx.toBLT.toBytes = raw := by
  have header : (589 : Nat).toBytesPack = [0x02, 0x4d] := by decide +kernel
  rw [tx_toBLT, BLT.toBytes, BLTs.toBytes, fields_encoded_body, body_length,
    ite_eq_right (by decide), header]
  rfl

/-- The five leading scalar fields, shared by the signed list and the signing payload. -/
def headFields : List BLT :=
  [.bytes [], .bytes [0xe8, 0xd4, 0xa5, 0x10, 0x00], .bytes [0x03, 0xd0, 0x90],
   .bytes [], .bytes []]

theorem headFields_encoded :
    BLTs.toBytesJoin headFields =
      [0x80, 0x85, 0xe8, 0xd4, 0xa5, 0x10, 0x00, 0x83, 0x03, 0xd0, 0x90, 0x80, 0x80] := by
  simp only [headFields, BLTs.toBytesJoin, BLT.toBytes, ↓reduceIte,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.toUInt8_eq,
    UInt8.reduceOfNat, UInt8.reduceAdd, List.cons_append, List.nil_append, List.append_nil]

/-- The six-field pre-EIP-155 signing payload (no chain-id trailer), retaining the creation
input. -/
def signingPayload : Bytes :=
  [0xf9, 0x02, 0x35, 0x80, 0x85, 0xe8, 0xd4, 0xa5, 0x10, 0x00,
   0x83, 0x03, 0xd0, 0x90, 0x80, 0x80, 0xb9, 0x02, 0x25] ++ creationCode.toList

/-- Pre-EIP-155 encoding, factored from the cryptographic reduction (shared
`signingHash_pre155` and `signingPayload_pre155`). -/
theorem signingEncoded : tx.signingHash = some signingPayload.keccak := by
  rw [LegacyRecover.signingHash_pre155 (p := 1000000000000) (rcv := none) rfl (Or.inl rfl)]
  have hn : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have hp : Nat.toBytes 1000000000000 = [0xe8, 0xd4, 0xa5, 0x10, 0x00] := by decide +kernel
  have hg : Nat.toBytes 250000 = [0x03, 0xd0, 0x90] := by decide +kernel
  have h0 : Nat.toBytes 0 = [] := by decide +kernel
  have hfields : [BLT.bytes tx.nonce.toBytes.sig, .bytes (1000000000000 : Nat).toBytes,
      .bytes tx.gas.toBytes, .bytes (((none : Option Adr) <&> Adr.toBytes).getD []),
      .bytes tx.value.toBytes, .bytes tx.data] =
      headFields ++ [.bytes creationCode.toList] := by
    change [BLT.bytes (UInt64.toBytes 0).sig, .bytes (1000000000000 : Nat).toBytes,
      .bytes (250000 : Nat).toBytes, .bytes [], .bytes (0 : Nat).toBytes,
      .bytes creationCode.toList] = _
    rw [hn, hp, hg, h0]
    rfl
  rw [hfields, LegacyRecover.signingPayload_pre155 headFields_encoded
    (by rw [data_length]; decide)]
  simp only [data_length, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.toBytesPack,
    Nat.toBytes, Nat.toBytes.aux, Nat.succ_eq_add_one, Nat.reduceMod, Nat.toUInt8_eq,
    UInt8.reduceOfNat, Nat.reduceDiv, UInt8.reduceAdd, signingPayload, List.cons_append,
    List.nil_append]

end Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx
