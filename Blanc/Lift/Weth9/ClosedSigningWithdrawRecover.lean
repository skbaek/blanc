import Blanc.Lift.Weth9.ClosedSigningWithdrawHash

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc.Lift

/-- Kernel-checked sender recovery for this signed synthetic transaction. -/
theorem withdrawTx_recoveredSender : recoverSender 1 withdrawTx = .ok senderE := by
  rw [recoverSender, withdrawTx_signingHash]
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
