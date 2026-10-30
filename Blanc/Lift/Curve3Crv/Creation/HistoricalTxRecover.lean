import Blanc.Lift.Curve3Crv.Creation.HistoricalTxRaw
import Blanc.Lift.Curve3Crv.Creation.Deploy

/-!
# Kernel cryptographic checks of the 3Crv creation transaction

`signingHash`: the pre-EIP-155 signing hash, computed by the kernel from the exact payload.
`recoveredSender`: at every chain id, sender recovery returns the recorded deployer
`0xbabe…9f67` (shared `LegacyRecover.recoverSender_pre155`; scalar guards and the secp256k1
recovery are closed kernel checks).
-/

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx

open Jaune

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

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx
