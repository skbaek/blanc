import Blanc.Lift.UniswapV2Pair.SourceAdmission
import Blanc.Lift.UniswapV2Pair.MintPositionalQueues
import Blanc.Lift.UniswapV2Pair.MintPositionalFresh

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The typed fee handler consumes this certificate's physical factory reply. -/
theorem MintRootCallPositions.feeResume {root : Exec.Deriv} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} {G : Nat}
    (r : MintRootCallPositions root b)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state)
    (invocation : List Nat)
    (sourceFee : FeeMintSourceResult K {current.state with unlocked := 0} root.sevm
      (mintPositionalFeeBase r) (mintPositionalLocals r) (mintPositionalFeeMemory r)
      (mintPositionalFeeWord r) (mintRootReserve0 root b) (mintRootReserve1 root b) G) :
    let ctx := writerContext root.sevm invocation
    let recipient := (Sevm.dataWord root.sevm 4).toAdr
    let observed := mintBalanceObserved current.state recipient
      (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32))
    resumeSegment (mintSourceFeeFrame current ctx recipient)
      (requestFor .mintFeeTo current.state.factory .feeTo) (.mintFee observed)
      (feeObservedResult r.fee.out) =
      (mintSourceAfterFeeFrame current ctx recipient).mintAfterFee observed
        (mintPositionalFeeResult current r) := by
  dsimp only
  obtain ⟨cache0, cache1, _, _, _⟩ := r.cache_targets rep
  have nat0 : (mintRootReserve0 root b).toNat = current.state.reserve0.val := by
    rw [cache0, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have nat1 : (mintRootReserve1 root b).toNat = current.state.reserve1.val := by
    rw [cache1, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have accept := sourceFee.1
  simp only [nat0, nat1, mintPositionalFeeWord] at accept
  have state : (mintSourceFeeFrame current (writerContext root.sevm invocation)
      (Sevm.dataWord root.sevm 4).toAdr).current.state = {current.state with unlocked := 0} := rfl
  have reserve0 : (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
      (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32))).reserves.reserve0.val =
      current.state.reserve0.val := rfl
  have reserve1 : (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
      (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32))).reserves.reserve1.val =
      current.state.reserve1.val := rfl
  rw [resumeSegment, feeObservedResult_decode _ _ r.fee.width]
  simp only [Frame.beginResume, state, reserve0, reserve1, accept]
  rfl

/-- Exact source consumption follows all three actual calls in order, carries
those full queues, and stops only after this certificate's final call-free suffix. -/
theorem MintPositionalQueues.admittedConsumes {Auth : Exec.Deriv → Entry → Transcript → Prop} {root : Exec.Deriv} {b : Devm}
    {current : Checkpoint} {invocation : List Nat} {r : MintRootCallPositions root b}
    (q : MintPositionalQueues current invocation r) {finished : Frame} {bytes : Bytes}
    (fork : CoveredFork root.sevm.benvStat.fork)
    (handlers : MintBalanceHandlerResult current (writerContext root.sevm invocation)
      (Sevm.dataWord root.sevm 4).toAdr r.out0 r.out1)
    (fee : resumeSegment
      (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
      (requestFor .mintFeeTo current.state.factory .feeTo)
      (.mintFee (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
        (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32))))
      (feeObservedResult r.fee.out) = .finished finished bytes) :
    AdmittedSourceConsumes Auth root root 0
      (startTyped current (writerContext root.sevm invocation) (.mint (Sevm.dataWord root.sevm 4).toAdr))
      (.next (feeObservedResult r.out0) (staticViewTranscript q.views0 .done)
        (.next (feeObservedResult r.out1) (staticViewTranscript q.views1 .done)
          (.next (feeObservedResult r.fee.out) (staticViewTranscript q.viewsF .done) .done)))
      {status := .success bytes, frame := finished, remaining := .done,
        childReturns :=
          staticViewChildReturns
            (mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
            (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)) 0 q.views0 ++
          (staticViewChildReturns
            ((mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr).beginResume
              (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)))
            (requestFor .mintBalance1 current.state.token1 (.balanceOf root.sevm.currentTarget)) 0 q.views1 ++
          (staticViewChildReturns
            (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
            (requestFor .mintFeeTo current.state.factory .feeTo) 0 q.viewsF ++ []))} := by
  obtain ⟨start, resume0, resume1⟩ := handlers
  have pair : (writerContext root.sevm invocation).pair = root.sevm.currentTarget := rfl
  simp only [pair] at start resume0 resume1
  have terminal : AdmittedSourceConsumes Auth root r.fee.occurrence.call.returned 3
      (.finished finished bytes) .done
      {status := .success bytes, frame := finished, remaining := .done, childReturns := []} :=
    .finished finished bytes (r.final_no_exec fork)
  rw [← fee] at terminal
  have last := AdmittedSourceConsumes.nextCall (start := r.second.call.returned)
    (continuation := .mintFee (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
      (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32)))) q.callF
    (by rw [q.sameF]; exact r.fee.occurrence.free) rfl
    (by intro absent; cases absent) q.duringF
    (by simpa only [q.sameF, feeObservedResult, ite_true] using terminal)
  simp only [mintBalanceObserved] at last
  rw [← resume1] at last
  have middle := AdmittedSourceConsumes.nextCall (start := r.first.call.returned)
    (continuation := .mintBalance1 (Sevm.dataWord root.sevm 4).toAdr current.state.cachedReserves
      (Bytes.toB256 (r.out0.take 32))) q.call1
    (by rw [q.same1]; exact r.second.free) rfl
    (by intro absent; cases absent) q.during1
    (by simpa only [q.same1, feeObservedResult, ite_true] using last)
  rw [← resume0] at middle
  have first := AdmittedSourceConsumes.nextCall (start := root)
    (continuation := .mintBalance0 (Sevm.dataWord root.sevm 4).toAdr current.state.cachedReserves) q.call0
    (by rw [q.same0]; exact r.first.free) rfl
    (by intro absent; cases absent) q.during0
    (by simpa only [q.same0, feeObservedResult, ite_true] using middle)
  rw [start]
  exact first


/-- Compatibility projects the same admitted source composition. -/
theorem MintPositionalQueues.positionalConsumes {root : Exec.Deriv} {b : Devm}
    {current : Checkpoint} {invocation : List Nat} {r : MintRootCallPositions root b}
    (q : MintPositionalQueues current invocation r) {finished : Frame} {bytes : Bytes}
    (fork : CoveredFork root.sevm.benvStat.fork)
    (handlers : MintBalanceHandlerResult current (writerContext root.sevm invocation)
      (Sevm.dataWord root.sevm 4).toAdr r.out0 r.out1)
    (fee : resumeSegment
      (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
      (requestFor .mintFeeTo current.state.factory .feeTo)
      (.mintFee (mintBalanceObserved current.state (Sevm.dataWord root.sevm 4).toAdr
        (Bytes.toB256 (r.out0.take 32)) (Bytes.toB256 (r.out1.take 32))))
      (feeObservedResult r.fee.out) = .finished finished bytes) :
    PositionalConsumes root root 0
      (startTyped current (writerContext root.sevm invocation) (.mint (Sevm.dataWord root.sevm 4).toAdr))
      (.next (feeObservedResult r.out0) (staticViewTranscript q.views0 .done)
        (.next (feeObservedResult r.out1) (staticViewTranscript q.views1 .done)
          (.next (feeObservedResult r.fee.out) (staticViewTranscript q.viewsF .done) .done)))
      {status := .success bytes, frame := finished, remaining := .done,
        childReturns :=
          staticViewChildReturns
            (mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
            (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)) 0 q.views0 ++
          (staticViewChildReturns
            ((mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr).beginResume
              (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)))
            (requestFor .mintBalance1 current.state.token1 (.balanceOf root.sevm.currentTarget)) 0 q.views1 ++
          (staticViewChildReturns
            (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
            (requestFor .mintFeeTo current.state.factory .feeTo) 0 q.viewsF ++ []))} := by
  exact (q.admittedConsumes (Auth := fun _ _ _ => True) fork handlers fee).positional

end Blanc.Lift.UniswapV2Pair
