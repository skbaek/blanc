import Blanc.RlpListEncode
import Blanc.Lift.LegacyRecover
import Blanc.Lift.Curve3Crv.Creation.HistoricalTx

/-!
# The 3Crv creation transaction's signing payload

For the recorded signed creation transaction `HistoricalTx.tx` (hash `0xa7d90e46…053694f8`,
block 10,809,467, index 76; nine legacy fields with `v = 28` and an empty receiver): the length
of its creation input and the six-field pre-EIP-155 signing payload (`signingEncoded`, through
the shared `LegacyRecover.signingPayload_pre155`). The creation input stays owned by
`Creation.code`; no byte of it is copied here.
-/

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx

open Jaune Blanc.RlpConcrete

/-- The creation input is 3,151 bytes. -/
theorem data_length : code.toList.length = 3151 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

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
