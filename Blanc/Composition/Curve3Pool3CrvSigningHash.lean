import Blanc.Composition.Curve3Pool3CrvSigningEncoding

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift

/-- Kernel-checked Keccak of the exchange transaction's type-2 signing payload. -/
theorem exchange_signingHash :
    signedExchangeTx.signingHash =
      some (0x8a52b43f4e4884aa8b0c4c9c2fe73478b4fd95f71182e40be2c16ae0056176b3 : B256) := by
  rw [exchange_signingEncoded]
  decide +kernel

end Blanc.Composition.Curve3Pool3CrvInstance
