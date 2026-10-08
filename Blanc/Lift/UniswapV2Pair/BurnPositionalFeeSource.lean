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

/-- The actual third slot's complete static-view queue resumes into the same
retained payout suspension and same admitted transfer continuation. -/
theorem BurnFourCalls.feeSource
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : r.three.feeFresh K current) (tracked : K (.balance sevm.currentTarget))
    (invocation : List Nat) (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork)
    (staticFresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys K (staticViewDecodedKeys F.sevm))
    {tail : Transcript} {out : RunResult}
    (rest : AdmittedSourceConsumes Auth root r.three.fee.occurrence.call.returned 3
      (.suspended (r.sourceTransferFrame current invocation)
        (requestFor .burnTransfer0 current.state.token0
          (.transfer (Sevm.dataWord sevm 4).toAdr (r.three.amount0 r.pricing)))
        (.burnTransfer0 (r.sourcePriced current))) tail out) :
    ∃ views : List StaticViewTurn,
      AdmittedSourceConsumes Auth root r.three.initial.second.returned 2
        (.suspended (burnPositionalFeeFrame current invocation sevm)
          (requestFor .burnFeeTo current.state.factory .feeTo) (.burnFee (r.three.sourceObserved current)))
        (.next (feeObservedResult r.three.fee.out) (staticViewTranscript views .done) tail)
        {out with childReturns :=
          (staticViewChildReturns (burnPositionalFeeFrame current invocation sevm)
            (requestFor .burnFeeTo current.state.factory .feeTo) 0 views ++ out.childReturns)} := by
  obtain ⟨observed, views, same, during⟩ :=
    r.three.feeViews rep invocation sem image installed fork staticFresh
  rw [← r.feeResume rep fresh tracked invocation success fork] at rest
  have result := AdmittedSourceConsumes.nextCall (start := r.three.initial.second.returned)
    (continuation := .burnFee (r.three.sourceObserved current)) observed
    (by rw [same]; exact r.three.fee.occurrence.free)
    (by simp only [externalStatic, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro absent; cases absent) during
    (by simpa only [same, feeObservedResult, ite_true, burnPositionalFeeFrame] using rest)
  exact ⟨views, result⟩

end Blanc.Lift.UniswapV2Pair
