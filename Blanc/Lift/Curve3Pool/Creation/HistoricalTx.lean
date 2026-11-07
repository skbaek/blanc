import Blanc.Lift.Curve3Pool.Creation.HistoricalWalk
import Blanc.TransactionForward
import Blanc.RlpListEncode
import Blanc.RlpRoundTrip
import Blanc.Lift.LegacyRecover

/-!
# The 3pool creation transaction's record, signed bytes and sender

The signed legacy creation transaction of the Curve 3pool (hash `0x20793bbf…7f22f3ac6`, block
10,809,473, index 53): sender nonce 43, gas 4,812,312, gas price 120,202,843,721 wei, no receiver,
zero value, the 21,967-byte creation input `Creation.code` as data, and the pre-EIP-155 signature
`v = 28`.

* `muir_intrinsic`: under Muir Glacier the intrinsic gas is exactly 385,884
  (`53000 + 16 · 20418 + 4 · 1549`), so the CREATE message carries `4812312 - 385884 = 4426428`,
  exactly what the constructor and the code deposit consume (`pool_create_muir_meta`).
* `raw_binding`: the signed bytes have the recorded transaction hash and strictly decode to `tx`.
* `recoveredSender`: at every chain id, sender recovery returns the recorded deployer.
-/

namespace Blanc.Lift.Curve3Pool.Creation.HistoricalTx

open Jaune Blanc.RlpConcrete

/-- The signature's first scalar. -/
def rBytes : Bytes :=
  [0x28, 0xbd, 0x99, 0x3b, 0x83, 0xab, 0x47, 0x15,
   0x03, 0xa0, 0x6d, 0x0c, 0x12, 0x91, 0xb7, 0x2f,
   0x3c, 0xd2, 0x05, 0xe0, 0xa9, 0x40, 0x91, 0x99,
   0xdd, 0x73, 0x51, 0x3b, 0xa7, 0x66, 0x8d, 0x3b]

/-- The signature's second scalar. -/
def sBytes : Bytes :=
  [0x38, 0x7e, 0x85, 0xb0, 0xeb, 0xf5, 0xd6, 0x82,
   0xf7, 0x37, 0x90, 0x41, 0x02, 0x4d, 0x44, 0xe4,
   0x71, 0xe6, 0xe6, 0xfd, 0x20, 0x8d, 0xd4, 0xda,
   0x4a, 0xa2, 0xa1, 0x03, 0x02, 0x57, 0x81, 0x9e]

/-- The recorded creation transaction (pre-EIP-155: `v = 28`, no chain id). -/
def tx : Tx :=
  { nonce := 43, gas := 4812312, value := 0, data := code.toList,
    v := 28, r := rBytes, s := sBytes, type := .zero 120202843721 none }

theorem tx_data : tx.data = code.toList := rfl

/-- The creation input's Istanbul data charge: 20,418 nonzero bytes at 16, 1,549 zero bytes at 4. -/
theorem dataCost :
    code.toList.foldl (fun acc x => acc + (if x = 0 then standardCallDataTokenCost else 16)) 0 =
      332884 := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- **The exact Muir Glacier intrinsic gas** of the 3pool creation transaction, for any sender. -/
theorem muir_intrinsic (sender : Adr) :
    calculateIntrinsicCost muirGlacierRules tx sender = (385884, 0) := by
  rw [calculateIntrinsicCost_legacy_create (price := 120202843721) rfl rfl rfl rfl rfl rfl rfl,
    tx_data, dataCost]

/-! ## The signed bytes -/

/-- The signed prefix before the creation input: the list header, nonce `0x2b`, gas price, gas,
empty receiver and value, and the data header. -/
def rawPrefix : Bytes :=
  [0xf9, 0x56, 0x22, 0x2b, 0x85, 0x1b, 0xfc, 0xa5, 0xd6, 0x49,
   0x83, 0x49, 0x6e, 0x18, 0x80, 0x80, 0xb9, 0x55, 0xcf]

/-- The signed suffix after the creation input: `v = 0x1c` and the two 32-byte scalars. -/
def rawSuffix : Bytes := [0x1c, 0xa0] ++ rBytes ++ [0xa0] ++ sBytes

/-- The recorded signed transaction bytes. -/
def raw : Bytes := rawPrefix ++ code.toList ++ rawSuffix

/-- The nine legacy byte-string fields. -/
def fields : List BLT :=
  [.bytes [0x2b], .bytes [0x1b, 0xfc, 0xa5, 0xd6, 0x49],
   .bytes [0x49, 0x6e, 0x18], .bytes [], .bytes [], .bytes code.toList,
   .bytes [0x1c], .bytes rBytes, .bytes sBytes]

theorem data_length : code.toList.length = 21967 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

theorem legacy_decode_wf : BLT.toExLegacyTx fields = .ok tx ∧ Tx.WireWellFormed tx :=
  LegacyRecover.legacy_decode_pre155 (nonce := 43) (gp := 120202843721) (gas := 4812312)
    (rcv := none) (value := 0) (v := 28) (data := code.toList) rfl rfl rfl rfl rfl
    (Or.inr rfl) rfl rfl

theorem tx_toBLT : tx.toBLT = .list fields := by
  simp only [tx, Tx.toBLT, fields]
  simp only [BLT.list.injEq, List.cons.injEq, BLT.bytes.injEq, and_true, true_and]
  decide +kernel

theorem raw_length : raw.length = 22053 := by
  simp only [raw, List.length_append, data_length]
  decide +kernel

/-- Canonical signed re-encoding returns precisely the recorded bytes. -/
theorem tx_encoded : tx.toBLT.toBytes = raw := by
  rw [tx_toBLT]
  exact encode_list_at 5 rfl data_length (by decide) (by decide +kernel) (by decide +kernel)

theorem raw_decode : Bytes.toBLT? raw = some (.list fields) :=
  toBLT?_of_encoded (tx_toBLT ▸ tx_encoded) (by rw [raw_length]; decide)

/-- The signed bytes have the recorded creation transaction hash. -/
theorem rawHash :
    raw.keccak =
      (0x20793bbf260912aae189d5d261ff003c9b9166da8191d8f9d63ff1c7722f3ac6 : B256) := by
  unfold raw
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- **The recorded bytes are the transaction.** -/
theorem raw_binding :
    raw.keccak =
        (0x20793bbf260912aae189d5d261ff003c9b9166da8191d8f9d63ff1c7722f3ac6 : B256) ∧
      Bytes.toBLT? raw = some (.list fields) ∧ BLT.toExLegacyTx fields = .ok tx ∧
      Tx.WireWellFormed tx ∧ tx.toBLT.toBytes = raw :=
  ⟨rawHash, raw_decode, legacy_decode_wf.1, legacy_decode_wf.2, tx_encoded⟩

/-! ## The sender -/

/-- The six-field pre-EIP-155 signing payload. -/
def signingPayload : Bytes :=
  [0xf9, 0x55, 0xdf, 0x2b, 0x85, 0x1b, 0xfc, 0xa5, 0xd6, 0x49,
   0x83, 0x49, 0x6e, 0x18, 0x80, 0x80, 0xb9, 0x55, 0xcf] ++ code.toList

theorem signingEncoded : tx.signingHash = some signingPayload.keccak := by
  rw [LegacyRecover.signingHash_pre155 (p := 120202843721) (rcv := none) rfl (Or.inr rfl)]
  exact congrArg (fun b => some (Bytes.keccak b))
    (encode_list_at_last 5 rfl rfl data_length (by decide) (by decide +kernel))

/-- The pre-EIP-155 signing hash, computed by the kernel from the exact payload. -/
theorem signingHash :
    tx.signingHash =
      some (0xc83be4c07ca17d51b5a84209bed499e6fa992372cac970bcc914ef9bac936fc0 : B256) := by
  rw [signingEncoded]
  unfold signingPayload
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- **Actual sender recovery** of the recorded creation transaction, at every chain id. -/
theorem recoveredSender (cid : UInt64) : recoverSender cid tx = .ok deployer :=
  LegacyRecover.recoverSender_pre155 (p := 120202843721) (rcv := none) rfl (Or.inr rfl)
    signingHash (by decide +kernel) (by decide +kernel) (by decide +kernel) cid

end Blanc.Lift.Curve3Pool.Creation.HistoricalTx
