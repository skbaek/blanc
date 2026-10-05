import Blanc.Lift.UniswapV2Pair.BurnSuffixWalk
import Blanc.Lift.UniswapV2Pair.MintSource
import Blanc.AddressSlotProofs

/-! Actual Burn reserve/oracle, fee-cache, event and unlock source correspondence. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The source frame after the actual Sync, optional kLast store, Burn and unlock. -/
def burnFinishedFrame (frame : Frame) (post : State) (event : Event) (oracle : OracleUpdate)
    (f toWord amount0 amount1 : B256) : Frame :=
  let last := if f = 0 then post else mintLastSourceState post
  let updated := frame.withUpdate last event oracle
  let logged := updated.withEvents last
    [.burn frame.context.sender amount0 amount1 toWord.toAdr]
  logged.withEvents (mintFinishedSourceState post f) []

/-- Actual update acceptance gives the source finisher, with the same fee branch. -/
theorem burnFinish_frame_accept {frame : Frame} {post : State} {event : Event}
    {oracle : OracleUpdate} {reserves : CachedReserves}
    {balance0 balance1 f toWord amount0 amount1 : B256}
    (updated : frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val = .ok (post, event, oracle)) :
    frame.finishUpdated balance0 balance1 reserves (decide (f ≠ 0))
      (some (.burn frame.context.sender amount0 amount1 toWord.toAdr))
      (encodeWords [amount0, amount1]) =
      .finished (burnFinishedFrame frame post event oracle f toWord amount0 amount1)
        (encodeWords [amount0, amount1]) := by
  unfold Frame.finishUpdated
  rw [updated]
  dsimp only
  by_cases zero : f = 0
  · simp only [zero, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      ite_false, burnFinishedFrame, mintFinishedSourceState, ite_true]
    rfl
  · simp only [zero, ne_eq, not_false_eq_true, decide_true, ite_true,
      burnFinishedFrame, mintFinishedSourceState, ite_false]
    rfl

/-- Incoming represented storage and the literal uint112 guards derive the complete
source finisher and physical storage/log images; no post-state witness is assumed. -/
theorem burnSuffix_source_result {K : WriterKey → Prop} {frame : Frame}
    {sevm : Sevm} {b : Devm} {reserves : CachedReserves}
    {old0 old1 balance0 balance1 f toWord amount0 amount1 : B256}
    (rep : WriterRep K (b.getStor sevm.currentTarget) frame.current.state)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (pair : frame.context.pair = sevm.currentTarget)
    (sender : frame.context.sender = sevm.caller)
    (cached0 : old0.toNat = reserves.reserve0.val)
    (cached1 : old1.toNat = reserves.reserve1.val)
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112) :
    ∃ (post : State) (event : Event) (oracle : OracleUpdate),
      frame.current.state.update frame.context balance0 balance1
        reserves.reserve0.val reserves.reserve1.val = .ok (post, event, oracle) ∧
      frame.finishUpdated balance0 balance1 reserves (decide (f ≠ 0))
        (some (.burn frame.context.sender amount0 amount1 toWord.toAdr))
        (encodeWords [amount0, amount1]) =
        .finished (burnFinishedFrame frame post event oracle f toWord amount0 amount1)
          (encodeWords [amount0, amount1]) ∧
      WriterRep K ((burnSuffixPost sevm b old0 old1 balance0 balance1 f
        toWord amount0 amount1).getStor sevm.currentTarget)
        (burnFinishedFrame frame post event oracle f toWord amount0 amount1).current.state ∧
      (burnSuffixPost sevm b old0 old1 balance0 balance1 f toWord amount0 amount1).logs =
        b.logs ++
          [⟨frame.context.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩,
           ⟨frame.context.pair,
             [burnEventTopic, frame.context.sender.toB256, toWord.toAdr.toB256],
             encodeWords [amount0, amount1]⟩] ∧
      (burnSuffixPost sevm b old0 old1 balance0 balance1 f toWord amount0 amount1).output =
        b.output := by
  have oldBound0 : old0.toNat < 2 ^ 112 := cached0.symm ▸ reserves.reserve0.isLt
  have oldBound1 : old1.toNat < 2 ^ 112 := cached1.symm ▸ reserves.reserve1.isLt
  have slots : ReserveSlotMatches frame.current.state sevm b :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  obtain ⟨post, event, oracle, updated, _, _, _, eventEq, updateLogs⟩ :=
    update_source_result slots rep.fixed.2.2.2.2.2.2.2.2.1
      rep.fixed.2.2.2.2.2.2.2.2.2.1 time pair oldBound0 oldBound1 bound0 bound1
  have updateRep := rep.mint_update time pair oldBound0 oldBound1 updated
  have lastRep := updateRep.mint_conditional_last (f := f)
  change WriterRep K ((burnKLastPost sevm
    (updateWorld sevm b old0 old1 balance0 balance1) f).getStor sevm.currentTarget)
      (if f = 0 then post else mintLastSourceState post) at lastRep
  rw [cached0, cached1] at updated
  refine ⟨post, event, oracle, updated, burnFinish_frame_accept updated, ?_, ?_, ?_⟩
  · unfold burnSuffixPost burnUnlockPost burnEventPost
    rw [afterSstore_getStor_self, Devm.addLog_getStor]
    exact lastRep.mint_unlock_store
  · unfold burnSuffixPost burnUnlockPost burnEventPost
    rw [afterSstore_logs]
    change (burnKLastPost sevm (updateWorld sevm b old0 old1 balance0 balance1) f).logs ++ _ = _
    unfold burnKLastPost
    split
    · rw [updateLogs, List.append_assoc, pair, sender]
      rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
        Blanc.and_mask_word]
      rfl
    · rw [burnKLastStorePost, afterSstore_logs, afterSload_logs,
        updateLogs, List.append_assoc, pair, sender]
      rw [show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
        Blanc.and_mask_word]
      rfl
  · unfold burnSuffixPost burnUnlockPost burnEventPost
    rw [afterSstore_output]
    change (burnKLastPost sevm (updateWorld sevm b old0 old1 balance0 balance1) f).output = _
    unfold burnKLastPost
    split
    · exact updateWorld_output _ _ _ _ _ _
    · rw [burnKLastStorePost, afterSstore_output, afterSload_output]
      exact updateWorld_output _ _ _ _ _ _

end Blanc.Lift.UniswapV2Pair
