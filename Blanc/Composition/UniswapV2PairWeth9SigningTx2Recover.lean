import Blanc.Composition.UniswapV2PairWeth9SigningTx2Hash

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift

/-- **Kernel-checked sender recovery of the signed `tx2`**: the published test key `1` signed it. -/
theorem tx2_recoveredSender : recoverSender 1 signedTx2 = .ok trader := by
  rw [recoverSender, tx2_signingHash]
  decide +kernel

end Blanc.Composition.UniswapV2PairWeth9Instance
