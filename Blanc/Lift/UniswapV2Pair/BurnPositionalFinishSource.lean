import Blanc.Lift.UniswapV2Pair.BurnPositionalFinish
import Blanc.Lift.UniswapV2Pair.BurnSource

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The same actual final answers produce the finite update, unlock and Burn
event, and that exact source finisher represents the actual successful post. -/
theorem BurnSevenCalls.finishSource {root : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {K J : WriterKey → Prop} {current : Checkpoint} {frame : Frame}
    (r : BurnSevenCalls root sevm b)
    (incoming : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (rep : WriterRep J (r.final1.call.returned.devm.getStor sevm.currentTarget) frame.current.state)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (success : root.exn = .ok post) (fork : CoveredFork sevm.benvStat.fork) :
    let balance0 := Bytes.toB256 (r.final0.out.take 32)
    let balance1 := Bytes.toB256 (r.final1.out.take 32)
    let flag := feeOnWord (Bytes.toB256 (r.five.four.three.fee.out.take 32))
    let recipient := (Sevm.dataWord sevm 4).toAdr.toB256
    let amount0 := r.five.four.three.amount0 r.five.four.pricing
    let amount1 := r.five.four.three.amount1 r.five.four.pricing
    ∃ (updated : State) (event : Event) (oracle : OracleUpdate),
      frame.current.state.update frame.context balance0 balance1
        current.state.cachedReserves.reserve0.val current.state.cachedReserves.reserve1.val =
          .ok (updated, event, oracle) ∧
      frame.finishUpdated balance0 balance1 current.state.cachedReserves (decide (flag ≠ 0))
        (some (.burn frame.context.sender amount0 amount1 recipient.toAdr))
        (encodeWords [amount0, amount1]) =
          .finished (burnFinishedFrame frame updated event oracle flag recipient amount0 amount1)
            (encodeWords [amount0, amount1]) ∧
      WriterRep J (post.getStor sevm.currentTarget)
        (burnFinishedFrame frame updated event oracle flag recipient amount0 amount1).current.state ∧
      post.output = encodeWords [amount0, amount1] ∧
      post.logs = r.final1.call.returned.devm.logs ++
        [⟨frame.context.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩,
         ⟨frame.context.pair, [burnEventTopic, frame.context.sender.toB256, recipient.toAdr.toB256],
          encodeWords [amount0, amount1]⟩] := by
  obtain ⟨bound0, bound1, _, N, next, gas, span, env, outcome, placed, tree, conts, full, output, stor, logs⟩ :=
    r.finishRaw success fork
  obtain ⟨reserve0, reserve1, _, _, _⟩ := r.five.four.three.initial.cache_targets incoming
  have cache0 : (burnInitialReserve0 sevm b).toNat = current.state.cachedReserves.reserve0.val := by
    rw [reserve0, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
    rfl
  have cache1 : (burnInitialReserve1 sevm b).toNat = current.state.cachedReserves.reserve1.val := by
    rw [reserve1, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
    rfl
  obtain ⟨updated, event, oracle, accepted, finished, represented, rawLogs, _⟩ :=
    burnSuffix_source_result (frame := frame) (sevm := sevm)
      (b := r.final1.call.returned.devm) (reserves := current.state.cachedReserves)
      (old0 := burnInitialReserve0 sevm b) (old1 := burnInitialReserve1 sevm b)
      (balance0 := Bytes.toB256 (r.final0.out.take 32))
      (balance1 := Bytes.toB256 (r.final1.out.take 32))
      (f := feeOnWord (Bytes.toB256 (r.five.four.three.fee.out.take 32)))
      (toWord := (Sevm.dataWord sevm 4).toAdr.toB256)
      (amount0 := r.five.four.three.amount0 r.five.four.pricing)
      (amount1 := r.five.four.three.amount1 r.five.four.pricing)
      rep time pair sender cache0 cache1 bound0 bound1
  exact ⟨updated, event, oracle, accepted, finished,
    (stor sevm.currentTarget).symm ▸ represented, output, logs.trans rawLogs⟩

end Blanc.Lift.UniswapV2Pair
