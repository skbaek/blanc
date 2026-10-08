import Blanc.Lift.UniswapV2Pair.BurnPositionalFeeFacts
import Blanc.Lift.UniswapV2Pair.BurnPricingTurns

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnThreeCalls.sourceObserved {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (current : Checkpoint) : BurnObserved :=
  { locals := ⟨(Sevm.dataWord sevm 4).toAdr, current.state.cachedReserves,
      current.state.token0, current.state.token1⟩,
    balance0 := Bytes.toB256 (r.initial.out0.take 32),
    balance1 := Bytes.toB256 (r.initial.out1.take 32),
    liquidity := current.state.balanceOf sevm.currentTarget }

/-- The same actual fee/pricing/LP result selects the first transfer suspension
and represents its physical input. No independently selected payout is used. -/
theorem BurnFourCalls.payoutSource {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {resumed : Frame}
    (r : BurnFourCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : r.three.feeFresh K current) (tracked : K (.balance sevm.currentTarget))
    (pair : resumed.context.pair = sevm.currentTarget)
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork) :
    let observed := r.three.sourceObserved current
    let fee := r.three.sourceFee current
    let amount0 := r.three.amount0 r.pricing
    let amount1 := r.three.amount1 r.pricing
    resumed.burnAfterFee observed fee =
      .suspended (burnPricedFrame resumed observed fee)
        (requestFor .burnTransfer0 current.state.token0
          (.transfer (Sevm.dataWord sevm 4).toAdr amount0))
        (.burnTransfer0 (burnPricedSource observed fee amount0 amount1)) ∧
    WriterRep (WriterExtend (r.three.sourceFeeKeys K current) (lpMintTouched sevm.currentTarget))
      (r.transfer.occurrence.node.devm.getStor sevm.currentTarget)
      (burnPricedFrame resumed observed fee).current.state := by
  have env : r.three.fee.occurrence.call.returned.sevm = sevm :=
    ((Cursor.parentStep_sevm r.three.fee.occurrence.call.edge).trans
      r.three.fee.occurrence.sevm_eq).trans
        ((Cursor.parentStep_sevm r.three.initial.second.edge).trans r.three.initial.second_sevm)
  have startEnv : r.three.initial.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.three.initial.second.edge).trans r.three.initial.second_sevm
  have sample : feeBurnLiquidity r.three.initial.second.returned.sevm
      r.three.initial.second.returned.devm = current.state.balanceOf sevm.currentTarget := by
    rw [startEnv]
    exact r.three.initial.sampled_liquidity rep tracked
  have represented := r.pricingRep rep fresh
  have lpFresh := r.pricingFresh rep fresh tracked
  obtain ⟨_, _, _, supplyEq, amounts, positive0, positive1, _, lp⟩ :=
    r.lp_source_result represented lpFresh success fork
  have sourceAmounts : burnAmounts (r.three.sourceObserved current).liquidity
      (r.three.sourceObserved current).balance0 (r.three.sourceObserved current).balance1
      (r.three.sourceFee current).state.totalSupply =
        .ok ((r.three.amount0 r.pricing).toNat, (r.three.amount1 r.pricing).toNat) := by
    rw [← supplyEq]
    simpa only [BurnThreeCalls.sourceObserved, sample] using amounts
  have burned : (r.three.sourceFee current).state.burnLP resumed.context.pair
      (r.three.sourceObserved current).liquidity =
      .ok (lpBurnSourceState (r.three.sourceFee current).state resumed.context.pair
        (r.three.sourceObserved current).liquidity,
        [.transfer resumed.context.pair 0 (r.three.sourceObserved current).liquidity]) := by
    simpa only [pair, env, toAdr_toB256, sample, BurnThreeCalls.sourceObserved] using lp.1
  refine ⟨burnAfterFee_source_accept sourceAmounts positive0 positive1 burned, ?_⟩
  rw [r.transfer_input]
  simpa only [St_getStor, BurnThreeCalls.transferWorld, env, sample, burnPricedFrame,
    Frame.withEvents, pair, BurnThreeCalls.sourceObserved, toAdr_toB256] using lp.2.1

end Blanc.Lift.UniswapV2Pair
