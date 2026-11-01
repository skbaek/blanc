import Blanc.RlpListEncode
import Blanc.RlpRoundTrip
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

/-- Canonical signed re-encoding returns precisely the raw candidate. -/
theorem tx_encoded : tx.toBLT.toBytes = raw := by
  rw [tx_toBLT]
  exact encode_list_at 5 rfl data_length (by decide) (by decide +kernel) (by decide +kernel)

/-- The exact raw candidate passes Jaune's full-consumption RLP parser. -/
theorem raw_decode : Bytes.toBLT? raw = some (.list fields) :=
  toBLT?_of_encoded (tx_toBLT ▸ tx_encoded) (by rw [raw_length]; decide)

/-- Fixed EIP-155 payload, again retaining the existing creation-code owner. -/
def signingPayload : Bytes :=
  [0xf9, 0x19, 0xfc, 0x80, 0x85, 0x22, 0x39, 0xe1, 0xfe, 0x00,
   0x83, 0x2f, 0xef, 0xd8, 0x80, 0x80, 0xb9, 0x19, 0xe9] ++
  code.toList ++ [0x01, 0x80, 0x80]

/-- EIP-155 encoding is factored from the subsequent cryptographic reduction. -/
theorem signingEncoded : tx.signingHash = some signingPayload.keccak := by
  simp only [Tx.signingHash, tx, Nat.reduceSub, Nat.reduceDiv]
  exact congrArg (fun b => some (Bytes.keccak b))
    (encode_list_at 5 rfl data_length (by decide) (by decide +kernel) (by decide +kernel))

end Blanc.Lift.BeaconDeposit.Creation.HistoricalTx
