import Blanc.Composition.Curve3Pool3CrvSigningEncoding

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift

/-- Kernel-checked Keccak of the exchange transaction's type-2 signing payload. -/
theorem exchange_signingHash :
    signedExchangeTx.signingHash =
      some (0x9a6033e7ed4798f0280fe7e60a9ec9b79276367e064c06e601b3d49079f9c67f : B256) := by
  rw [exchange_signingEncoded]
  decide +kernel

end Blanc.Composition.Curve3Pool3CrvInstance
