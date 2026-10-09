import Blanc.Lift.UniswapV2Pair.PairFeeSourceKeys
import Blanc.Lift.UniswapV2Pair.BurnFrameWalk

/-! Actual fee and LP-burn observations produce Burn's first transfer frame. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Pricing retains pre-fee liquidity and uses the actual post-fee supply. -/
def burnPricedSource (observed : BurnObserved) (fee : FeeResult)
    (amount0 amount1 : B256) : BurnPriced :=
  { observed := observed, feeOn := fee.feeOn, feeMinted := fee.minted,
    supply := fee.state.totalSupply, amount0 := amount0, amount1 := amount1 }

/-- Fee events precede the LP debit at the same resumed source origin. -/
def burnPricedFrame (frame : Frame) (observed : BurnObserved) (fee : FeeResult) : Frame :=
  (frame.withEvents fee.state fee.events).withEvents
    (lpBurnSourceState fee.state frame.context.pair observed.liquidity)
    [.transfer frame.context.pair 0 observed.liquidity]

/-- Source acceptance derived from the checked bytecode floors and LP debit. -/
theorem burnAfterFee_source_accept {frame : Frame} {observed : BurnObserved} {fee : FeeResult}
    {amount0 amount1 : B256}
    (amounts : burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply = .ok (amount0.toNat, amount1.toNat))
    (positive0 : 0 < amount0.toNat) (positive1 : 0 < amount1.toNat)
    (burned : fee.state.burnLP frame.context.pair observed.liquidity =
      .ok (lpBurnSourceState fee.state frame.context.pair observed.liquidity,
        [.transfer frame.context.pair 0 observed.liquidity])) :
    frame.burnAfterFee observed fee =
      .suspended (burnPricedFrame frame observed fee)
        (requestFor .burnTransfer0 observed.locals.token0
          (.transfer observed.locals.recipient amount0))
        (.burnTransfer0 (burnPricedSource observed fee amount0 amount1)) := by
  simp only [Frame.burnAfterFee, amounts, ite_eq_left (show amount0.toNat > 0 ∧ amount1.toNat > 0 from ⟨positive0, positive1⟩), burned,
    toB256_toNat]
  rfl

/-- The actual fee branch's Boolean matches its retained bytecode word. -/
theorem feeBranchSourceFee_flag (st : State) (sevm : Sevm) (b : Devm) (w r0 r1 : B256) :
    (feeBranchSourceFee st sevm b w r0 r1).feeOn = decide (feeOnWord w ≠ 0) := by
  by_cases zero : w.toAdr = 0
  · have word : w.toAdr.toB256 = 0 := congrArg Adr.toB256 zero
    have flag : feeOnWord w = 0 := by
      simp only [feeOnWord, B256.eqCheck, ite_eq_left word,
        ite_eq_right (by decide : (1 : B256) ≠ 0)]
    rw [feeBranchSourceFee, ite_eq_left zero, flag]
    rfl
  · have word : w.toAdr.toB256 ≠ 0 := fun h => zero (Adr.toB256_inj h)
    have flag : feeOnWord w = 1 := by
      simp only [feeOnWord, B256.eqCheck, ite_eq_right word, ite_true]
    have on : (feeBranchSourceFee st sevm b w r0 r1).feeOn = true := by
      unfold feeBranchSourceFee
      rw [ite_eq_right zero]
      split
      · rfl
      · split
        · unfold feeGrowthSourceFee
          split <;> rfl
        · rfl
    rw [on, flag]
    rfl

end Blanc.Lift.UniswapV2Pair
