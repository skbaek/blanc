import Blanc.Lift.Usdc.Footprint

/-!
USDC history allowance quietness at an arbitrary holder address. The existing
pinned declaration namespace is retained for this physical ownership split;
no Pair code, WETH runtime or joint-checkpoint assumption is used.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift

/-- **The Pair's touched USDC allowance rows read zero at the checkpoint.** -/
def PairUsdcAllowQuiet (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ g, (.allow pair g) ∈ Usdc.historyTouchedKeys usdc trace →
    (checkpoint.state.getStor usdc).get (Usdc.allowSlot pair g) = 0

end Blanc.Composition.UniswapV2PairUsdcWeth9
