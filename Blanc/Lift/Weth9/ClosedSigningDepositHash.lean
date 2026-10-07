import Blanc.Lift.Weth9.ClosedSigningDepositEncoding

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc.Lift

/-- Kernel-checked Keccak of the concrete type-2 signing payload. -/
theorem depositTx_signingHash :
    depositTx.signingHash = some (0x4902244575f23ced222c8f33d8530db1c33e5b84b8b61618e90e6f120fb560a2 : B256) := by
  rw [depositTx_signingEncoded]
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
