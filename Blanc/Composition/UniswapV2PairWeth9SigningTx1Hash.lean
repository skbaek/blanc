import Blanc.Composition.UniswapV2PairWeth9SigningTx1Encoding

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift

/-- Kernel-checked Keccak of `tx1`'s type-2 signing payload. -/
theorem tx1_signingHash :
    signedTx1.signingHash = some (0xafad70331f65a93d4a6d8e203050fa9ab868b5e848963b2b0a717c3e5f5a2e97 : B256) := by
  rw [tx1_signingEncoded]
  decide +kernel

end Blanc.Composition.UniswapV2PairWeth9Instance
