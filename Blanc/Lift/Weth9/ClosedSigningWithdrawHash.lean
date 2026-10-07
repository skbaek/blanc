import Blanc.Lift.Weth9.ClosedSigningWithdrawEncoding

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc.Lift

/-- Kernel-checked Keccak of the concrete type-2 signing payload. -/
theorem withdrawTx_signingHash :
    withdrawTx.signingHash = some (0x32a8a3a03c8c8cd4919cd06c4a856d3e2cf0773c428790adc3d3569bea8d1c76 : B256) := by
  rw [withdrawTx_signingEncoded]
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
