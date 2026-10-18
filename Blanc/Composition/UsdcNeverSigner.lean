import Blanc.Lift.Usdc.NeverSigner
import Blanc.Lift.UniswapV2Pair.PairHistory

/-!
# The Pair never signs a USDC entry (unit N, amendment A10)

`usdc_neverSigner_pair` at the Pair's code semantics `pairSem`.  The proof is
`Blanc.Lift.Usdc.usdc_neverSigner_pairCode`; this module only names `pairSem`, which lives in the
Pair's contract stratum, so the statement sits in composition.
-/

namespace Blanc.Composition.UsdcToken

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.Usdc
  Blanc.Lift.UniswapV2Pair

/-- **`NeverSigner` for the Pair** (amendment A10: `pairNotPrecompile`, discharged at the
composition checkpoint). -/
theorem usdc_neverSigner_pair {P pair : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (apart : pair ≠ P)
    (pairNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp pair) :
    NeverSigner P (usdcBookS P) tr pair :=
  usdc_neverSigner_pairCode tr hist.toUsdcHistF rfl installed pairNotPrecompile

end Blanc.Composition.UsdcToken
