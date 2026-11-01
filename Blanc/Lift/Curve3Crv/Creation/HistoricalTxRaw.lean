import Blanc.RlpListEncode
import Blanc.RlpRoundTrip
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

/-- Canonical signed re-encoding returns precisely the recorded bytes. -/
theorem tx_encoded : tx.toBLT.toBytes = raw := by
  rw [tx_toBLT]
  exact encode_list_at 5 rfl data_length (by decide) (by decide +kernel) (by decide +kernel)

/-- The signed bytes pass Jaune's full-consumption RLP parser. -/
theorem raw_decode : Bytes.toBLT? raw = some (.list fields) :=
  toBLT?_of_encoded (tx_toBLT ▸ tx_encoded) (by rw [raw_length]; decide)

/-- The six-field pre-EIP-155 signing payload (no chain-id trailer), retaining the creation
input. -/
def signingPayload : Bytes :=
  [0xf9, 0x0c, 0x5f, 0x2a, 0x85, 0x1c, 0x0a, 0x04, 0x08, 0xee,
   0x83, 0x0a, 0x59, 0xc7, 0x80, 0x80, 0xb9, 0x0c, 0x4f] ++ code.toList

/-- Pre-EIP-155 encoding, factored from the cryptographic reduction (shared
`signingHash_pre155` and `RlpConcrete.encode_list_at_last`). -/
theorem signingEncoded : tx.signingHash = some signingPayload.keccak := by
  rw [LegacyRecover.signingHash_pre155 (p := 120427120878) (rcv := none) rfl (Or.inr rfl)]
  exact congrArg (fun b => some (Bytes.keccak b))
    (encode_list_at_last 5 rfl rfl data_length (by decide) (by decide +kernel))

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx
