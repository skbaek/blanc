import Blanc.Composition.LiveUsdcWeth9B26213219WethObservation
import Blanc.Composition.LiveUsdcWeth9B26213219PairObservation
import Blanc.Composition.LiveUsdcWeth9B26213219Anchor

/-! A single original history supplies both deployment inputs and the live
checkpoint. The deployment records and their consistency link are derived.
Fetched correspondence, receipt absence and cryptographic conditions remain
explicit premises; none is authenticated against a block hash here (the WETH
observation alone can be derived from its block hash, `WethHashAnchor.observation`).
This interface does not establish USDC P1. -/
namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift
  Blanc.Composition.UniswapV2PairUsdcWeth9
  Blanc.Composition.LiveUsdcWeth9FactoryAnchor

/-- Original observed deployment blocks joined by actual configured histories.
No final footprint, Pair representation, deployment record or link is an input;
the finite signing hash is the kernel-checked theorem, not a field. -/
structure ObservedDeploymentHistory (checkpoint : BlockChain) where
  wethPre : BlockChain
  wethPost : BlockChain
  pairPre : BlockChain
  pairPost : BlockChain
  wethBlock : ConfiguredBlockTraceIn HistFork mainnetChainConfig wethPre wethPost
  pairBlock : ConfiguredBlockTraceIn HistFork mainnetChainConfig pairPre pairPost
  wethObserved : WethOriginalObservation wethBlock
  pairObserved : CDObservation.OriginalD pairBlock
  parent : Block
  factory : OriginalDParent pairBlock parent
  between : ConfiguredHistoryTraceIn HistFork mainnetChainConfig wethPost pairPre
  later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig pairPost checkpoint
  wethFresh : Weth9.KeysFresh (fun _ => False)
    (Weth9.midTouchedKeysIn Weth9.Creation.weth9Address
      ((MidHistoryTraceIn.tail wethBlock wethObserved.cut).append
        ((between.step pairBlock).append later)))
  pairFresh : UniswapV2Pair.WriterFreshKeys (fun _ => False)
    (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
      ((MidHistoryTraceIn.tail pairBlock pairObserved.pairCut).append later))

/-- The WETH-only observed history: WETH's continuation contains the original
Pair block and its continuation. -/
def ObservedDeploymentHistory.toWeth {checkpoint : BlockChain}
    (h : ObservedDeploymentHistory checkpoint) : WethObservedHistory checkpoint :=
  ⟨h.wethPre, h.wethPost, h.wethBlock, h.wethObserved,
    (h.between.step h.pairBlock).append h.later, h.wethFresh⟩

/-- WETH's deployment input, from its observed history. -/
noncomputable def ObservedDeploymentHistory.wethDeployment {checkpoint : BlockChain}
    (h : ObservedDeploymentHistory checkpoint) : WethDeploymentTo checkpoint :=
  h.toWeth.deployment

/-- The same Pair block and continuation produce its deployment input. -/
noncomputable def ObservedDeploymentHistory.pairDeployment {checkpoint : BlockChain}
    (h : ObservedDeploymentHistory checkpoint) : PairDeploymentTo checkpoint :=
  h.pairObserved.pairDeploymentFromParent h.factory h.later h.pairFresh

/-- The history-consistency premise follows from the shared construction. -/
noncomputable def ObservedDeploymentHistory.link {checkpoint : BlockChain}
    (h : ObservedDeploymentHistory checkpoint) :
    DeploymentHistoryLink h.wethDeployment h.pairDeployment :=
  ⟨h.between, rfl⟩

/-- The finite reads at B and the original observed deployment history produce
the hybrid checkpoint. Sender exclusion keeps all original recovery queries;
receipt absence concerns the same pre-Pair history used by allowance replay. -/
theorem ObservedDeploymentHistory.checkpoint {checkpoint : BlockChain}
    (h : ObservedDeploymentHistory checkpoint) (anchor : ObservedCheckpoint checkpoint)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots
      h.wethDeployment.keys (.bal pair))
    (excluded : ∀ query ∈ h.wethDeployment.trace.senderQueries, query.recover ≠ .ok pair)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        h.link.beforePairReceiptLogs) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows)
      h.wethDeployment.keys h.pairDeployment.keys h.pairDeployment.model checkpoint.state := by
  exact checkpoint_at_bound_deployment_model_of_receipts anchor h.wethDeployment
    h.pairDeployment h.link holderFresh excluded logs

end Blanc.Composition.LiveUsdcWeth9B26213219
