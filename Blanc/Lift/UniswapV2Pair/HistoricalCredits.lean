import Blanc.ExecutionRewardCredits
import Blanc.ExecutionStagedBodyTrace
import Blanc.Lift.UniswapV2Pair.WriterStorage

/-!
# Pair historical fork selection and proof-of-work reward credits

The represented model and tracked keys are unchanged by the actual reward
fold. Installed code supplies protection; token-answer assumptions play no
part in this frame-free storage transition.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The mainnet schedule selects Muir Glacier at the Pair's approved deployment
coordinates: block 10008355, timestamp 1588710145. Plans
`evidence/mac-l4-anchor-reads-20261022/anchor-adoption-proposal.json` binds these
coordinates to block
`0x359d1dc4f14f9a07cba3ae8416958978ce98f78ad7b8d505925dad9722081f04`
and transaction
`0xd07cbde817318492092cc7a27b3064a69bd893c01cb593d6029683ffd290ab3a`.
This theorem selects rules; it does not prove historical configured creation,
receipt inclusion or consensus authentication. -/
theorem pair_deployment_fork :
    mainnetChainConfig.forkAt 10008355 1588710145 = .ok .muirGlacier := by
  decide +kernel

/-- Real miner and ommer rewards leave the represented storage/model exactly
unchanged. This storage fact needs no token answers or nonwrap premise. -/
theorem WriterRep.payRewards {K : WriterKey → Prop} {world : Jaune.State}
    {pair : Adr} {model : State}
    (initial : WriterRep K (world.getStor pair) model)
    (protection : Blanc.State.Protected world pair)
    (pow : PowRules) (number : Nat) (coinbase : Adr) (ommers : List Header) :
    WriterRep K ((payRewards pow number coinbase ommers world).getStor pair) model := by
  rw [payRewards_getStor_of_protected pow number coinbase ommers protection]
  exact initial

/-- The Pair's represented model survives the actual retained final reward
stage, with skipped and PoW branches both following the carrier's endpoint. -/
theorem writerRep_after_rewardStage {K : WriterKey → Prop} {pair : Adr} {model : State}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {world : Jaune.State} {bout : BlockOutput}
    (trace : ExecutionTrace.StagedBodyTrace benv txs ommers wds world bout)
    (initial : WriterRep K (trace.requestState.getStor pair) model)
    (protection : Blanc.State.Protected trace.requestState pair) :
    WriterRep K (world.getStor pair) model := by
  rw [trace.reward_getStor_of_protected protection]
  exact initial

end Blanc.Lift.UniswapV2Pair
