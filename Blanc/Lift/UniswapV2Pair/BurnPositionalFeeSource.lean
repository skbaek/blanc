import Blanc.Lift.UniswapV2Pair.BurnPositionalInitialSource
import Blanc.Lift.UniswapV2Pair.BurnPositionalUniverse

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnPositionalFeeFrame (current : Checkpoint) (invocation : List Nat) (sevm : Sevm) : Frame :=
  ((burnSourceLockedFrame current (writerContext sevm invocation) (Sevm.dataWord sevm 4).toAdr).beginResume
    (requestFor .burnInitialBalance0 current.state.token0 (.balanceOf sevm.currentTarget))).beginResume
      (requestFor .burnInitialBalance1 current.state.token1 (.balanceOf sevm.currentTarget))

def burnPositionalAfterFeeFrame (current : Checkpoint) (invocation : List Nat) (sevm : Sevm) : Frame :=
  (burnPositionalFeeFrame current invocation sevm).beginResume
    (requestFor .burnFeeTo current.state.factory .feeTo)

def BurnFourCalls.sourcePriced {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) (current : Checkpoint) : BurnPriced :=
  burnPricedSource (r.three.sourceObserved current) (r.three.sourceFee current)
    (r.three.amount0 r.pricing) (r.three.amount1 r.pricing)

def BurnFourCalls.sourceTransferFrame {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFourCalls root sevm b) (current : Checkpoint) (invocation : List Nat) : Frame :=
  burnPricedFrame (burnPositionalAfterFeeFrame current invocation sevm)
    (r.three.sourceObserved current) (r.three.sourceFee current)

/-- The same physical fee reply and retained LP result select the exact typed
first-transfer suspension. -/
theorem BurnFourCalls.feeResume {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : r.three.feeFresh K current) (tracked : K (.balance sevm.currentTarget))
    (invocation : List Nat) (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork) :
    resumeSegment (burnPositionalFeeFrame current invocation sevm)
      (requestFor .burnFeeTo current.state.factory .feeTo) (.burnFee (r.three.sourceObserved current))
      (feeObservedResult r.three.fee.out) =
      .suspended (r.sourceTransferFrame current invocation)
        (requestFor .burnTransfer0 current.state.token0
          (.transfer (Sevm.dataWord sevm 4).toAdr (r.three.amount0 r.pricing)))
        (.burnTransfer0 (r.sourcePriced current)) := by
  obtain ⟨cache0, cache1, _, _, _⟩ := r.three.initial.cache_targets rep
  have nat0 : (burnInitialReserve0 sevm b).toNat = current.state.reserve0.val := by
    rw [cache0, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have nat1 : (burnInitialReserve1 sevm b).toNat = current.state.reserve1.val := by
    rw [cache1, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  obtain ⟨_, _, result⟩ := r.fee_source_result rep fresh
  have accepted := result.1
  simp only [nat0, nat1] at accepted
  have resumed : resumeSegment (burnPositionalFeeFrame current invocation sevm)
      (requestFor .burnFeeTo current.state.factory .feeTo) (.burnFee (r.three.sourceObserved current))
      (feeObservedResult r.three.fee.out) =
      (burnPositionalAfterFeeFrame current invocation sevm).burnAfterFee
        (r.three.sourceObserved current) (r.three.sourceFee current) := by
    rw [resumeSegment, feeObservedResult_decode _ _ r.three.fee.width]
    simp only [burnPositionalFeeFrame, Frame.beginResume, burnSourceLockedFrame,
      BurnThreeCalls.sourceObserved, State.cachedReserves, accepted]
    rfl
  rw [resumed]
  exact (r.payoutSource rep fresh tracked (resumed := burnPositionalAfterFeeFrame current invocation sevm)
    rfl success fork).1

end Blanc.Lift.UniswapV2Pair
