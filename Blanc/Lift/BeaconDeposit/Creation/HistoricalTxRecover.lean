import Blanc.Lift.BeaconDeposit.Creation.HistoricalTxRaw

/-! Kernel cryptographic checks of the unadopted historical transaction candidate. -/

namespace Blanc.Lift.BeaconDeposit.Creation.HistoricalTx

open Jaune

/-- The signed raw candidate has the frozen creation transaction hash. -/
theorem rawHash :
    raw.keccak =
      (0xe75fb554e433e03763a1560646ee22dcb74e5274b34c5ad644e7c0f619a7e1d0 : B256) := by
  unfold raw
  rw [ByteArray.toList_eq_toList_data]
  simp only [code, List.toList_toArray]
  decide +kernel

/-- The EIP-155 signing hash is computed by the kernel from the exact payload. -/
theorem signingHash :
    tx.signingHash =
      some (0x19c7a59a5a2b4c4c527621c9b80841a21e8eed32c4f6cbb56f98ec555d092b68 : B256) := by
  rw [signingEncoded]
  unfold signingPayload
  rw [ByteArray.toList_eq_toList_data]
  simp only [code, List.toList_toArray]
  decide +kernel

/-- Actual EIP-155 sender recovery, including the scalar and chain-id guards. -/
theorem recoveredSender : recoverSender 1 tx = .ok deployer := by
  rw [recoverSender, signingHash]
  decide +kernel

end Blanc.Lift.BeaconDeposit.Creation.HistoricalTx
