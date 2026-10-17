import Blanc.Composition.UniswapV2PairWeth9SigningTx2Encoding

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift

/-- Kernel-checked Keccak of `tx2`'s type-2 signing payload. -/
theorem tx2_signingHash :
    signedTx2.signingHash = some (0x9f13d0b7b3bd5d04a35efef6c6e53d618b5101e0ac3058b7a7913fb846c4a589 : B256) := by
  rw [tx2_signingEncoded]
  decide +kernel

end Blanc.Composition.UniswapV2PairWeth9Instance
