import Blanc.RlpListEncode
import Blanc.RlpRoundTrip
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
pre-EIP-155 signing payload is encoded by `RlpConcrete.encode_list_at_last`. The creation
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

/-- Canonical signed re-encoding returns precisely the candidate bytes. -/
theorem tx_encoded : tx.toBLT.toBytes = raw := by
  rw [tx_toBLT]
  exact encode_list_at 5 rfl data_length (by decide) (by decide +kernel) (by decide +kernel)

/-- The signed bytes pass Jaune's full-consumption RLP parser. -/
theorem raw_decode : Bytes.toBLT? raw = some (.list fields) :=
  toBLT?_of_encoded (tx_toBLT ▸ tx_encoded) (by rw [raw_length]; decide)

/-- The six-field pre-EIP-155 signing payload (no chain-id trailer), retaining the creation
input. -/
def signingPayload : Bytes :=
  [0xf9, 0x02, 0x35, 0x80, 0x85, 0xe8, 0xd4, 0xa5, 0x10, 0x00,
   0x83, 0x03, 0xd0, 0x90, 0x80, 0x80, 0xb9, 0x02, 0x25] ++ creationCode.toList

/-- Pre-EIP-155 encoding, factored from the cryptographic reduction (shared
`signingHash_pre155` and `RlpConcrete.encode_list_at_last`). -/
theorem signingEncoded : tx.signingHash = some signingPayload.keccak := by
  rw [LegacyRecover.signingHash_pre155 (p := 1000000000000) (rcv := none) rfl (Or.inl rfl)]
  exact congrArg (fun b => some (Bytes.keccak b))
    (encode_list_at_last 5 rfl rfl data_length (by decide) (by decide +kernel))

end Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx
