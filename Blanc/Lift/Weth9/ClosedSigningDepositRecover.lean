import Blanc.Lift.Weth9.ClosedSigningDepositHash

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc.Lift

/-- Kernel-checked sender recovery for this signed synthetic transaction. -/
theorem depositTx_recoveredSender : recoverSender 1 depositTx = .ok senderE := by
  rw [recoverSender, depositTx_signingHash]
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
