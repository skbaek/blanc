import Blanc.Lift.Curve3Crv.Creation.HistoricalTxRaw
import Blanc.Lift.Curve3Crv.Creation.Deploy

/-!
# Kernel cryptographic checks of the 3Crv creation transaction

`rawHash`: the signed bytes hash to the recorded transaction hash `0xa7d90e46…053694f8`.
`signingHash`: the pre-EIP-155 signing hash, computed by the kernel from the exact payload.
`raw_binding`: those bytes parse and strictly decode to `tx`, which re-encodes to them.
`recoveredSender`: at every chain id, sender recovery returns the recorded deployer
`0xbabe…9f67` (shared `LegacyRecover.recoverSender_pre155`; scalar guards and the secp256k1
recovery are closed kernel checks).
-/

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx

open Jaune

/-- The signed bytes have the recorded creation transaction hash. -/
theorem rawHash :
    raw.keccak =
      (0xa7d90e460bed56181e41b74d143ec98fe097c8391700e4e0788f5282053694f8 : B256) := by
  unfold raw
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The pre-EIP-155 signing hash, computed by the kernel from the exact payload. -/
theorem signingHash :
    tx.signingHash =
      some (0xfd9885944403245fc8279a6439ded3784a08172cacb328ef54766ad416dac7c6 : B256) := by
  rw [signingEncoded]
  unfold signingPayload
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- **Actual sender recovery** of the recorded creation transaction, at every chain id. -/
theorem recoveredSender (cid : UInt64) : recoverSender cid tx = .ok deployer :=
  LegacyRecover.recoverSender_pre155 (p := 120427120878) (rcv := none) rfl (Or.inr rfl)
    signingHash (by decide +kernel) (by decide +kernel) (by decide +kernel) cid

/-- **The recorded bytes are the transaction.** The signed bytes have the recorded transaction
hash, parse (full consumption) to the nine legacy fields, which the strict decoder turns into
exactly `tx`, a wire well-formed transaction whose canonical encoding is the same bytes. -/
theorem raw_binding :
    raw.keccak =
        (0xa7d90e460bed56181e41b74d143ec98fe097c8391700e4e0788f5282053694f8 : B256) ∧
      Bytes.toBLT? raw = some (.list fields) ∧ BLT.toExLegacyTx fields = .ok tx ∧
      Tx.WireWellFormed tx ∧ tx.toBLT.toBytes = raw :=
  ⟨rawHash, raw_decode, legacy_decode, wireWellFormed, tx_encoded⟩

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx
