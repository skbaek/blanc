import Blanc.Lift.UniswapV2Pair.BurnSource
import Blanc.Lift.UniswapV2Pair.StaticViewTurns

/-! Typed consumption of Burn's two actual post-transfer balance calls. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Raw locals retained at the literal post-transfer Burn cut. -/
structure BurnFinalWords where
  supply : B256
  fee : B256
  liquidity : B256
  balance1 : B256
  balance0 : B256
  token1 : B256
  token0 : B256
  reserve1 : B256
  reserve0 : B256
  amount1 : B256
  amount0 : B256
  recipient : B256

/-- Internal cut correspondence; the full Burn entry proof must produce this
from its fee, pricing, LP-burn and settled transfer observations. -/
structure BurnFinalCut (K : WriterKey → Prop) (frame : Frame) (priced : BurnPriced)
    (sevm : Sevm) (b : Devm) (w : BurnFinalWords) (p : B256) (n : Nat) (M : Mem) : Prop where
  rep : WriterRep K (b.getStor sevm.currentTarget) frame.current.state
  time : frame.context.timestamp = sevm.benvStat.time
  pair : frame.context.pair = sevm.currentTarget
  sender : frame.context.sender = sevm.caller
  token0 : (w.token0 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr =
    priced.observed.locals.token0
  token1 : (w.token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr =
    priced.observed.locals.token1
  recipient : w.recipient.toAdr = priced.observed.locals.recipient
  reserve0 : w.reserve0.toNat = priced.observed.locals.reserves.reserve0.val
  reserve1 : w.reserve1.toNat = priced.observed.locals.reserves.reserve1.val
  fee : priced.feeOn = decide (w.fee ≠ 0)
  amount0 : w.amount0 = priced.amount0
  amount1 : w.amount1 = priced.amount1
  mem : PtrMem p n M
  lower : 96 ≤ p.toNat
  width : p.toNat + 1024 < 2 ^ 256

/-- The actual source request for the first post-transfer balance. -/
def burnFinalRequest0 (frame : Frame) (priced : BurnPriced) : Request :=
  requestFor .burnFinalBalance0 priced.observed.locals.token0 (.balanceOf frame.context.pair)

/-- The actual source request for the second post-transfer balance. -/
def burnFinalRequest1 (frame : Frame) (priced : BurnPriced) : Request :=
  requestFor .burnFinalBalance1 priced.observed.locals.token1 (.balanceOf frame.context.pair)

/-- A complete first reply advances only the segment and cached balance. -/
theorem burn_resumeFinalBalance0 {frame : Frame} {priced : BurnPriced} {out : Bytes}
    (long : 32 ≤ out.length) :
    resumeSegment frame (burnFinalRequest0 frame priced) (.burnFinalBalance0 priced)
        (feeObservedResult out) =
      .suspended (frame.beginResume (burnFinalRequest0 frame priced))
        (burnFinalRequest1 (frame.beginResume (burnFinalRequest0 frame priced)) priced)
        (.burnFinalBalance1 priced (Bytes.toB256 (out.take 32))) := by
  simp only [resumeSegment, decodeExternal, burnFinalRequest0, burnFinalRequest1, requestFor,
    feeObservedResult, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
    long]
  rfl

/-- The complete second reply reaches the accepted actual source finisher. -/
theorem burn_resumeFinalBalance1 {frame : Frame} {priced : BurnPriced} {out : Bytes}
    {balance0 f toWord : B256} {post : State} {event : Event} {oracle : OracleUpdate}
    (long : 32 ≤ out.length) (fee : priced.feeOn = decide (f ≠ 0))
    (recipient : toWord.toAdr = priced.observed.locals.recipient)
    (updated : frame.current.state.update frame.context balance0 (Bytes.toB256 (out.take 32))
      priced.observed.locals.reserves.reserve0.val priced.observed.locals.reserves.reserve1.val =
        .ok (post, event, oracle)) :
    resumeSegment frame (burnFinalRequest1 frame priced) (.burnFinalBalance1 priced balance0)
        (feeObservedResult out) =
      .finished (burnFinishedFrame (frame.beginResume (burnFinalRequest1 frame priced))
        post event oracle f toWord priced.amount0 priced.amount1)
        (encodeWords [priced.amount0, priced.amount1]) := by
  simp only [resumeSegment, decodeExternal, burnFinalRequest1, requestFor,
    feeObservedResult, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
    long]
  rw [fee, ← recipient]
  exact burnFinish_frame_accept updated

end Blanc.Lift.UniswapV2Pair
