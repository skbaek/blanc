import Blanc.Composition.UniswapV2PairWeth9SigningTx1Hash

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift

/-- **Kernel-checked sender recovery of the signed `tx1`**: the published test key `1` signed it. -/
theorem tx1_recoveredSender : recoverSender 1 signedTx1 = .ok trader := by
  rw [recoverSender, tx1_signingHash]
  decide +kernel

end Blanc.Composition.UniswapV2PairWeth9Instance
