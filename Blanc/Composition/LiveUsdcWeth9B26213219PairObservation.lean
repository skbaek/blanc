import Blanc.Composition.LiveUsdcWeth9B26213219CDObservation
import Blanc.Composition.LiveUsdcWeth9FactoryAnchor

/-! The original Pair deployment from its observed block and parent state.
The original body constructs the transaction cut; the parent observation and
checked factory preservation supply code at that cut. Original correspondence,
the continuation and HASH-T remain explicit. No observation is adopted. -/
namespace Blanc.Composition.LiveUsdcWeth9B26213219.CDObservation

open Jaune Blanc.ExecutionTrace Blanc.Lift
  Blanc.Composition.LiveUsdcWeth9FactoryAnchor

/-- The observed full body contains the frozen factory request at position 38. -/
theorem OriginalD.pairSlot {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : OriginalD block) :
    block.block.txs[38]? = some (.inr Usdc.HistoryAnchorBody.d38Tx) := by
  rw [observed.body]
  rfl

/-- Obtain the cut from the original accepted body, including its actual
transaction execution and suffix; no separate cut witness is assumed. -/
noncomputable def OriginalD.pairCut {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : OriginalD block) : block.bodyTrace.transactions.TxSplit 38 :=
  block.bodyTrace.txSplitOfSlot observed.pairSlot rfl

/-- The constructed cut is the frozen request at the original index. -/
theorem OriginalD.pairCut_fields {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : OriginalD block) :
    observed.pairCut.index = 38 ∧ observed.pairCut.tx = Usdc.HistoryAnchorBody.d38Tx :=
  Usdc.HistoryAnchorBody.d_original_cut block observed.pairCut observed.body

/-- Original receipt success and the earlier factory anchor produce all
deployment preconditions. Factory code at the transaction is a conclusion,
not an extra observation or a caller-supplied premise. -/
noncomputable def OriginalD.pairDeploymentFromParent {checkpoint pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post} {parent : Block}
    (observed : OriginalD block) (factory : OriginalDParent block parent)
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post checkpoint)
    (fresh : UniswapV2Pair.WriterFreshKeys (fun _ => False)
      (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
        ((MidHistoryTraceIn.tail block observed.pairCut).append history))) :
    PairDeploymentTo checkpoint :=
  observed.pairDeployment observed.pairCut (factory.factory_at_pair_cut observed.pairCut)
    history fresh

/-- Assembly retains the original same-block suffix and later history exactly. -/
theorem OriginalD.pairDeploymentFromParent_trace {checkpoint pre post : BlockChain}
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post} {parent : Block}
    (observed : OriginalD block) (factory : OriginalDParent block parent)
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post checkpoint)
    (fresh : UniswapV2Pair.WriterFreshKeys (fun _ => False)
      (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
        ((MidHistoryTraceIn.tail block observed.pairCut).append history))) :
    (observed.pairDeploymentFromParent factory history fresh).trace =
      (MidHistoryTraceIn.tail block observed.pairCut).append history := rfl

end Blanc.Composition.LiveUsdcWeth9B26213219.CDObservation
