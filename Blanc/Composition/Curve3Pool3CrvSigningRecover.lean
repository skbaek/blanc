import Blanc.Composition.Curve3Pool3CrvSigningHash

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift

/-- **Kernel-checked sender recovery of the signed exchange**: the published test key `1` signed
it. -/
theorem exchange_recoveredSender : recoverSender 1 signedExchangeTx = .ok trader := by
  rw [recoverSender, exchange_signingHash]
  decide +kernel

end Blanc.Composition.Curve3Pool3CrvInstance
