import Blanc.Composition.UniswapV2PairWeth9Tx2Back

/-!
# The swap frame of `tx2`: `_update`, the `Swap` log and the unlock, viewed

After both queries the Pair runs `_update` (the oracle accumulators, since one second elapsed since
`W0`'s timestamp `0`, and the packed reserves), logs `Sync` and `Swap`, and unlocks.  This file gives
the frame's final world `tx2PostState` (the WETH9 balance writes, the two accumulators, the reserves
`1001000`/`999004` with timestamp `1`, the lock restored), its refund `2800` and its three logs, and
evaluates the back half's post-query charge `swapBackPostGas`.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint

/-- `W0`'s packed reserve slot: both reserves `10^6`, timestamp `0`. -/
def tx2Packed0 : B256 := Nat.toB256 (1000000 + 1000000 * 2 ^ 112)

/-- The elapsed time `_update` sees. -/
def tx2Elapsed : B256 := updateElapsedWord tx2Packed0 1

/-- The first accumulator after `_update`. -/
def tx2Acc0 : B256 :=
  updateAccumulatorWord 0 (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000)) tx2Elapsed

/-- The packed reserves after `_update`: `1001000`, `999004`, timestamp `1`. -/
def tx2Packed1 : B256 := updatePackedWord tx2Packed0 1001000 999004 (updateTimestampWord 1)

theorem tx2Packed1_eq : tx2Packed1 = Nat.toB256 (1001000 + 999004 * 2 ^ 112 + 1 * 2 ^ 224) := by
  decide +kernel

/-- The frame's final world. -/
def tx2PostState (b : Devm) : Jaune.State :=
  ((((tx2SD b).setStorVal pair 9 tx2Acc0).setStorVal pair 10 tx2Acc0).setStorVal pair 8
    tx2Packed1).setStorVal pair 12 1

/-- The `Sync` log. -/
def tx2SyncLog : Log :=
  ⟨pair, [updateSyncTopic], (reserve0Read tx2Packed1).toBytes ++ (reserve1Read tx2Packed1).toBytes⟩

/-- The `Swap` log. -/
def tx2SwapLog : Log :=
  ⟨pair, [swapEventTopic, trader.toB256, swapTokenWord trader.toB256],
    (1000 : B256).toBytes ++ (0 : B256).toBytes ++ (0 : B256).toBytes ++ swapOut.toBytes⟩

theorem tx2SD_pair (b : Devm) (h : b.state.getStor pair = w0PairStor) :
    (tx2SD b).getStor pair = w0PairStor.set 12 0 := by
  unfold tx2SD wethTransferWrites tx2PrefixState
  rw [State.setStorVal_getStor_ne _ pair_ne_weth.symm, State.setStorVal_getStor_ne _ pair_ne_weth.symm,
    State.setStorVal_getStor_self, h]

theorem refund_fresh {g : GasSchedule} {v : B256} {rc : Int} (hv : v ≠ 0) :
    sstoreNewRefundCounter g v 0 0 rc = rc := by
  unfold sstoreNewRefundCounter
  simp only [Ne.symm hv, ne_eq, not_false_eq_true, ↓reduceIte, not_true_eq_false, false_and, and_false]

theorem tx2Acc0_ne :
    updateAccumulatorWord 0 (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000)) tx2Elapsed ≠ 0 := by
  decide +kernel

theorem refund_unlock {g : GasSchedule} (hg : g = Fork.bpo2.ruleSet.gas) :
    sstoreNewRefundCounter g 1 1 0 4800 = 2800 := by
  subst hg
  decide +kernel

section Post

variable {sevm : Sevm} {b d1 : Devm} (h : Tx2Frame sevm b)
  (v1 : DView b d1 tx2K1 tx2A1 (tx2SD b) (4800 + 0 + 0) (([wethTransferLog] ++ []) ++ []))
include h v1

theorem tx2_d1_slot8 : d1.getStorVal sevm.currentTarget 8 = tx2Packed0 := by
  rw [v1.getStorVal, h.target, tx2SD_pair b h.pairStor, Stor.get_set_ne _ (by decide), w0PairStor_8]
  rfl

theorem tx2_oracleActive :
    updateOracleActive sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000) := by
  unfold updateOracleActive
  rw [tx2_d1_slot8 h v1, h.time]
  decide +kernel

theorem tx2_oracleWorld_eq :
    updateOracleWorld sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000) =
      updateAccumulatorPost sevm (updateAccumulatorPost sevm (Blanc.afterSload sevm d1 8) 9
        (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000)) tx2Elapsed) 10
        (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000)) tx2Elapsed := by
  unfold updateOracleWorld
  dsimp only
  rw [ite_eq_left (tx2_oracleActive h v1), tx2_d1_slot8 h v1, h.time]
  rfl

/-- The world after `_update`'s oracle stage. -/
theorem tx2_oracle_view : DView b
    (updateOracleWorld sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000))
    ((pair, 10) :: (pair, 10) :: (pair, 9) :: (pair, 9) :: (pair, 8) :: tx2K1) tx2A1
    (((tx2SD b).setStorVal pair 9 tx2Acc0).setStorVal pair 10 tx2Acc0) 4800
    [wethTransferLog] := by
  rw [tx2_oracleWorld_eq h v1]
  have hp := tx2SD_pair b h.pairStor
  have e0 := v1.afterSload h.target 8
  have hv9 : (Blanc.afterSload sevm d1 8).getStorVal sevm.currentTarget 9 = 0 := by
    rw [e0.getStorVal, h.target, hp, Stor.get_set_ne _ (by decide), w0PairStor_9]
  unfold updateAccumulatorPost
  rw [hv9]
  have e1 := (e0.afterSload h.target 9).afterSstore h.target h.createdPair 9
    (updateAccumulatorWord 0 (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000)) tx2Elapsed)
  have hv10 : (Blanc.afterSstore sevm (Blanc.afterSload sevm (Blanc.afterSload sevm d1 8) 9) 9
      (updateAccumulatorWord 0 (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000))
        tx2Elapsed)).getStorVal sevm.currentTarget 10 = 0 := by
    rw [e1.getStorVal, h.target, State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide), hp,
      Stor.get_set_ne _ (by decide), w0PairStor_10]
  rw [hv10]
  have e2 := (e1.afterSload h.target 10).afterSstore h.target h.createdPair 10
    (updateAccumulatorWord 0 (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000)) tx2Elapsed)
  rw [h.origPair, w0PairStor_9, w0PairStor_10, State.setStorVal_getStor_self,
    Stor.get_set_ne _ (by decide), hp, Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide),
    w0PairStor_9, w0PairStor_10, refund_fresh tx2Acc0_ne, refund_fresh tx2Acc0_ne, Int.add_zero,
    Int.add_zero, List.append_nil, List.append_nil] at e2
  exact e2

theorem tx2_oracle_slot8 :
    (updateOracleWorld sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000)).getStorVal
      sevm.currentTarget 8 = tx2Packed0 := by
  have o := tx2_oracle_view h v1
  rw [o.getStorVal, h.target, State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide),
    State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide), tx2SD_pair b h.pairStor,
    Stor.get_set_ne _ (by decide), w0PairStor_8]
  rfl

theorem tx2_finalPacked :
    updateFinalPackedWord sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000) 1001000 999004 =
      tx2Packed1 := by
  unfold updateFinalPackedWord
  rw [tx2_oracle_slot8 h v1, h.time]
  rfl

/-- **The frame's final machine, viewed.** -/
theorem tx2_post_view : ∃ K, DView b
    (Blanc.afterSstore sevm (swapLoggedWorld sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000)
      1001000 999004 1000 0 0 swapOut trader.toB256) 12 1) K tx2A1 (tx2PostState b) 2800
    [wethTransferLog, tx2SyncLog, tx2SwapLog] := by
  have o := tx2_oracle_view h v1
  unfold swapLoggedWorld updateWorld updatePackedPost updateSyncPost
  rw [tx2_finalPacked h v1, tx2_oracle_slot8 h v1, h.time]
  have e3 := (o.afterSload h.target 8).afterSstore h.target h.createdPair 8
    (updatePackedWord tx2Packed0 1001000 999004 (updateTimestampWord 1))
  have e5 := ((e3.addLog ⟨sevm.currentTarget, [updateSyncTopic], (reserve0Read tx2Packed1).toBytes ++
    (reserve1Read tx2Packed1).toBytes⟩).addLog (swapEventLog sevm 1000 0 0 swapOut trader.toB256)
    ).afterSstore h.target h.createdPair 12 1
  have hl : [wethTransferLog] ++ [(⟨sevm.currentTarget, [updateSyncTopic],
      (reserve0Read tx2Packed1).toBytes ++ (reserve1Read tx2Packed1).toBytes⟩ : Log)] ++
      [swapEventLog sevm 1000 0 0 swapOut trader.toB256] =
      [wethTransferLog, tx2SyncLog, tx2SwapLog] := by
    unfold swapEventLog
    rw [h.target, h.caller]
    rfl
  have h12 : ((((((tx2SD b).setStorVal pair 9 tx2Acc0).setStorVal pair 10 tx2Acc0).setStorVal pair 8
      (updatePackedWord tx2Packed0 1001000 999004 (updateTimestampWord 1))).getStor pair).get 12) =
      0 := by
    rw [State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide), State.setStorVal_getStor_self,
      Stor.get_set_ne _ (by decide), State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide),
      tx2SD_pair b h.pairStor, Stor.get_set_self]
  have h8 : ((((tx2SD b).setStorVal pair 9 tx2Acc0).setStorVal pair 10 tx2Acc0).getStor pair).get 8 =
      tx2Packed0 := by
    rw [State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide), State.setStorVal_getStor_self,
      Stor.get_set_ne _ (by decide), tx2SD_pair b h.pairStor, Stor.get_set_ne _ (by decide),
      w0PairStor_8]
    rfl
  have hgas : sevm.benvStat.rules.gas = Fork.bpo2.ruleSet.gas := by rw [rules_bpo2 h.fork]
  rw [hl, h12, h8, h.origPair, w0PairStor_12, w0PairStor_8,
    show (Nat.toB256 (1000000 + 1000000 * 2 ^ 112)) = tx2Packed0 from rfl,
    sstoreNewRefundCounter_update _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    refund_unlock hgas] at e5
  exact ⟨_, e5⟩

theorem tx2_updateCharge (n : Nat) (p : B256) :
    swapUpdateCharge sevm d1 n p (Nat.toB256 1000000) (Nat.toB256 1000000) 1001000 999004 =
      swapSyncGas n p + 47998 := by
  have hp := tx2SD_pair b h.pairStor
  have o := tx2_oracle_view h v1
  have e0 := v1.afterSload h.target 8
  have e1 := e0.afterSload h.target 9
  have hv9 : (Blanc.afterSload sevm d1 8).getStorVal sevm.currentTarget 9 = 0 := by
    rw [e0.getStorVal, h.target, hp, Stor.get_set_ne _ (by decide), w0PairStor_9]
  have hel : updateElapsedWord (d1.getStorVal sevm.currentTarget 8) sevm.benvStat.time = tx2Elapsed := by
    rw [tx2_d1_slot8 h v1, h.time]
    rfl
  have e2 := e1.afterSstore h.target h.createdPair 9
    (updateAccumulatorWord 0 (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000)) tx2Elapsed)
  have hv10 : (updateAccumulatorPost sevm (Blanc.afterSload sevm d1 8) 9
      (updatePriceWord (Nat.toB256 1000000) (Nat.toB256 1000000)) tx2Elapsed).getStorVal
        sevm.currentTarget 10 = 0 := by
    unfold updateAccumulatorPost
    rw [hv9, e2.getStorVal, h.target, State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide), hp,
      Stor.get_set_ne _ (by decide), w0PairStor_10]
  have e3 := e2.afterSload h.target 10
  have hfin : updateFinalPackedWord sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000) 1001000 999004 =
      tx2Packed1 := tx2_finalPacked h v1
  unfold swapUpdateCharge swapUpdLoad8 swapUpdStore8 swapUpdLoad9 swapUpdStore9 swapUpdLoad10
    swapUpdStore10 swapUpdAcc0
  rw [ite_eq_left (tx2_oracleActive h v1), hfin, hel, hv9, hv10, tx2_d1_slot8 h v1, h.time,
    o.sloadCost h.target, (o.afterSload h.target 8).sstoreCost h.target h.createdPair,
    e0.sloadCost h.target, e1.sstoreCost h.target h.createdPair, v1.sloadCost h.target]
  unfold updateAccumulatorPost
  rw [hv9, e2.sloadCost h.target, e3.sstoreCost h.target h.createdPair]
  simp only [State.setStorVal_getStor_self, hp, Stor.get_set_ne _ (show (9 : B256) ≠ 8 by decide),
    Stor.get_set_ne _ (show (10 : B256) ≠ 8 by decide), Stor.get_set_ne _ (show (12 : B256) ≠ 8 by decide),
    Stor.get_set_ne _ (show (12 : B256) ≠ 9 by decide), Stor.get_set_ne _ (show (12 : B256) ≠ 10 by decide),
    Stor.get_set_ne _ (show (9 : B256) ≠ 10 by decide), h.origPair, w0PairStor_8, w0PairStor_9,
    w0PairStor_10, Nat.add_assoc]
  exact congrArg (swapSyncGas n p + ·) (by decide +kernel)

/-- The world the unlock store reads. -/
theorem tx2_logged_view : DView b
    (swapLoggedWorld sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000) 1001000 999004 1000 0 0 swapOut
      trader.toB256)
    ((pair, 8) :: (pair, 8) :: (pair, 10) :: (pair, 10) :: (pair, 9) :: (pair, 9) :: (pair, 8) :: tx2K1)
    tx2A1 ((((tx2SD b).setStorVal pair 9 tx2Acc0).setStorVal pair 10 tx2Acc0).setStorVal pair 8
      tx2Packed1)
    (sstoreNewRefundCounter sevm.benvStat.rules.gas tx2Packed1 tx2Packed0 tx2Packed0 4800)
    ([wethTransferLog] ++ [⟨sevm.currentTarget, [updateSyncTopic], (reserve0Read tx2Packed1).toBytes ++
      (reserve1Read tx2Packed1).toBytes⟩] ++ [swapEventLog sevm 1000 0 0 swapOut trader.toB256]) := by
  have o := tx2_oracle_view h v1
  unfold swapLoggedWorld updateWorld updatePackedPost updateSyncPost
  rw [tx2_finalPacked h v1, tx2_oracle_slot8 h v1, h.time]
  have e3 := (o.afterSload h.target 8).afterSstore h.target h.createdPair 8
    (updatePackedWord tx2Packed0 1001000 999004 (updateTimestampWord 1))
  have h8 : ((((tx2SD b).setStorVal pair 9 tx2Acc0).setStorVal pair 10 tx2Acc0).getStor pair).get 8 =
      tx2Packed0 := by
    rw [State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide), State.setStorVal_getStor_self,
      Stor.get_set_ne _ (by decide), tx2SD_pair b h.pairStor, Stor.get_set_ne _ (by decide),
      w0PairStor_8]
    rfl
  rw [h8, h.origPair, w0PairStor_8,
    show (Nat.toB256 (1000000 + 1000000 * 2 ^ 112)) = tx2Packed0 from rfl] at e3
  exact (e3.addLog _).addLog _

theorem tx2_unlockCost :
    swapUnlockCost sevm d1 (Nat.toB256 1000000) (Nat.toB256 1000000) 1001000 999004 1000 0 0 swapOut
      trader.toB256 = 100 := by
  unfold swapUnlockCost
  rw [(tx2_logged_view h v1).sstoreCost h.target h.createdPair, h.origPair, w0PairStor_12,
    State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide), State.setStorVal_getStor_self,
    Stor.get_set_ne _ (by decide), State.setStorVal_getStor_self, Stor.get_set_ne _ (by decide),
    tx2SD_pair b h.pairStor, Stor.get_set_self]
  decide +kernel

theorem tx2_backPostGas (G : Nat) :
    swapBackPostGas sevm d1 (swapRequestSize (swapRequestSize tx2M.size tx2P) tx2P) tx2P tx2W 1001000
      999004 G = G + 53529 := by
  have hin0 : swapInWord 1001000 (Nat.toB256 1000000) 0 = 1000 := by decide +kernel
  have hin1 : swapInWord 999004 (Nat.toB256 1000000) swapOut = 0 := by decide +kernel
  unfold swapBackPostGas
  rw [show tx2W.reserve0 = Nat.toB256 1000000 from rfl, show tx2W.reserve1 = Nat.toB256 1000000 from rfl,
    show tx2W.amount0Out = 0 from rfl, show tx2W.amount1Out = swapOut from rfl,
    show tx2W.recipient = trader.toB256 from rfl, hin0, hin1, tx2_unlockCost h v1, tx2_updateCharge h v1]
  unfold swapEventRunGas
  simp only [Nat.add_assoc]
  refine congrArg (G + ·) ?_
  decide +kernel

end Post

end Blanc.Composition.UniswapV2PairWeth9Instance
