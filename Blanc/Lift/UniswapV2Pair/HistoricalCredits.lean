import Blanc.ExecutionRewardCredits
import Blanc.ExecutionStagedBodyTrace
import Blanc.Lift.UniswapV2Pair.WriterStorage

/-!
# Pair representation across historical proof-of-work reward credits

The represented model and tracked keys are unchanged by the actual reward
fold. Installed code supplies protection; token-answer assumptions play no
part in this frame-free storage transition.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

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
