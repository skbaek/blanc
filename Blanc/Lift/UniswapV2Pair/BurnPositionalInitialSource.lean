import Blanc.Lift.UniswapV2Pair.BurnPositionalInitialQueues
import Blanc.Lift.UniswapV2Pair.BurnPositionalPayoutSource
import Blanc.Lift.UniswapV2Pair.SourceAdmission

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Both initial balance suspensions consume their own original slots and full
static-view queues before the same supplied fee continuation. -/
theorem BurnThreeCalls.initialSource
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnThreeCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (invocation : List Nat) (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (fresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys K (staticViewDecodedKeys F.sevm))
    {tail : Transcript} {out : RunResult} :
    let frame0 := burnSourceLockedFrame current (writerContext sevm invocation)
      (Sevm.dataWord sevm 4).toAdr
    let request0 := requestFor .burnInitialBalance0 current.state.token0 (.balanceOf sevm.currentTarget)
    let frame1 := frame0.beginResume request0
    let request1 := requestFor .burnInitialBalance1 current.state.token1 (.balanceOf sevm.currentTarget)
    let frameF := frame1.beginResume request1
    AdmittedSourceConsumes Auth root r.initial.second.returned 2
      (.suspended frameF (requestFor .burnFeeTo current.state.factory .feeTo)
        (.burnFee (r.sourceObserved current))) tail out →
    ∃ views0 views1 : List StaticViewTurn,
      AdmittedSourceConsumes Auth root root 0
        (.suspended frame0 request0 (.burnInitialBalance0 (r.sourceObserved current).locals))
        (.next (feeObservedResult r.initial.out0) (staticViewTranscript views0 .done)
          (.next (feeObservedResult r.initial.out1) (staticViewTranscript views1 .done) tail))
        {out with childReturns := staticViewChildReturns frame0 request0 0 views0 ++
          (staticViewChildReturns frame1 request1 0 views1 ++ out.childReturns)} := by
  dsimp only
  intro rest
  let frame0 := burnSourceLockedFrame current (writerContext sevm invocation)
    (Sevm.dataWord sevm 4).toAdr
  let request0 := requestFor .burnInitialBalance0 current.state.token0 (.balanceOf sevm.currentTarget)
  let frame1 := frame0.beginResume request0
  let request1 := requestFor .burnInitialBalance1 current.state.token1 (.balanceOf sevm.currentTarget)
  obtain ⟨observed0, views0, same0, during0⟩ :=
    r.initial.firstViews rep invocation sem image installed fork fresh
  obtain ⟨observed1, views1, same1, during1⟩ :=
    r.initial.secondViews rep invocation sem image installed fork fresh
  have resume1 : resumeSegment frame1 request1
      (.burnInitialBalance1 (r.sourceObserved current).locals
        (Bytes.toB256 (r.initial.out0.take 32))) (feeObservedResult r.initial.out1) =
      .suspended (frame1.beginResume request1)
        (requestFor .burnFeeTo current.state.factory .feeTo) (.burnFee (r.sourceObserved current)) :=
    burn_resumeInitialBalance1 r.initial.second_width
  rw [← resume1] at rest
  have second := AdmittedSourceConsumes.nextCall (start := r.initial.first.returned)
    (continuation := .burnInitialBalance1 (r.sourceObserved current).locals
      (Bytes.toB256 (r.initial.out0.take 32))) observed1
    (by rw [same1]; exact r.initial.second_gap)
    (by simp only [externalStatic, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro absent; cases absent) during1
    (by simpa only [same1, feeObservedResult, ite_true] using rest)
  have resume0 : resumeSegment frame0 request0
      (.burnInitialBalance0 (r.sourceObserved current).locals) (feeObservedResult r.initial.out0) =
      .suspended frame1 request1
        (.burnInitialBalance1 (r.sourceObserved current).locals
          (Bytes.toB256 (r.initial.out0.take 32))) :=
    burn_resumeInitialBalance0 r.initial.first_width
  rw [← resume0] at second
  have first := AdmittedSourceConsumes.nextCall (start := root)
    (continuation := .burnInitialBalance0 (r.sourceObserved current).locals) observed0
    (by rw [same0]; exact r.initial.first_gap)
    (by simp only [externalStatic, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro absent; cases absent) during0
    (by simpa only [same0, feeObservedResult, ite_true] using second)
  exact ⟨views0, views1, first⟩

end Blanc.Lift.UniswapV2Pair
