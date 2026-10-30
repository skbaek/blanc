import Blanc.RlpConcrete
import Blanc.Lift.LegacyRecover
import Blanc.Lift.WithdrawalRequest.Creation.Deploy

/-!
# The EIP-7002 deployment transaction and its signing payload

The candidate signed keyless creation transaction `HistoricalTx.tx` (hash `0x8ded54be…2572`,
mainnet block 21,881,389, index 0): nonce 0, gas price 10^12, gas 250,000, no receiver, zero
value, the 549-byte creation input `creationCode` as data, and the pre-EIP-155 signature
`v = 27`, `r = 0x0539`. The six-field pre-EIP-155 signing payload is factored by
`LegacyRecover.signingPayload_pre155` (`signingEncoded`). The creation input stays owned by
`Creation.creationCode`; no byte of it is copied here. The values are unadopted candidate
observations.
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

/-- The creation input is 549 bytes: the 45-byte constructor and the 504-byte runtime. -/
theorem data_length : creationCode.toList.length = 549 := by
  rw [creationCode, ByteArray.toList_eq_toList_data, List.toList_toArray,
    List.length_append, runtime_length]
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
