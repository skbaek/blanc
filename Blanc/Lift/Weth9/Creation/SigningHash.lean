import Blanc.Lift.Weth9.Creation.SigningEncoding

/-!
# WETH creation signing hash

`signingPayload_hash`: the kernel hashes the exact EIP-155 envelope over the registered creation
code (3,528 bytes) in one `decide +kernel`, as the 3Crv and Beacon creation checks do.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune

/-- Kernel hash of the exact EIP-155 envelope over the registered creation code. -/
theorem signingPayload_hash : signingPayload.keccak =
    (0x1e62afdbf54076edd8083f93eab1bf693f2a5a3675886b669d13d9b3e6221235 : B256) := by
  unfold signingPayload
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem signingHash {tx : Tx}
    (htype : tx.type = .zero 21000000000 none)
    (hnonce : tx.nonce = 446) (hgas : tx.gas = 1500000)
    (hvalue : tx.value = 0) (hdata : tx.data = code.toList) (hv : tx.v = 37) :
    tx.signingHash =
      some (0x1e62afdbf54076edd8083f93eab1bf693f2a5a3675886b669d13d9b3e6221235 : B256) := by
  rw [signingEncoded htype hnonce hgas hvalue hdata hv, signingPayload_hash]

end Blanc.Lift.Weth9.Creation
