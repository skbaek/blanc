import Blanc.Lift.UniswapV2Pair.BurnPositionalSeven

/-! Incoming storage bindings for the same seven original Burn positions. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem BurnInitialPairH.first_storage {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnInitialPairH root sevm b) (a : Adr) :
    r.first.returned.devm.getStor a = (burnLockedWorldH sevm b).getStor a := by
  rw [r.first_reply.stor]
  simp only [burnInitialWorld0H, Devm.getStor, Devm.getAcct, accountAccessH_state]
  change (burnTokensWorldH sevm (burnInitialReserveWorldH sevm b)).getStor a = _
  rw [burnTokensWorldH, afterSloadH_getStor, afterSloadH_getStor,
    burnInitialReserveWorldH, afterSloadH_getStor]
  rfl

theorem BurnInitialPairH.second_storage {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnInitialPairH root sevm b) (a : Adr) :
    r.second.returned.devm.getStor a = (burnLockedWorldH sevm b).getStor a := by
  rw [r.second_reply.stor]
  simpa only [Devm.getStor, Devm.getAcct, accountAccessH_state]
    using r.first_storage a

theorem BurnInitialPairH.fee_entry_rep {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnInitialPairH root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state) :
    WriterRep K (r.second.returned.devm.getStor sevm.currentTarget)
      { current.state with unlocked := 0 } := by
  rw [r.second_storage]
  exact rep.burn_locked_worldH

theorem BurnInitialPairH.cache_targets {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnInitialPairH root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state) :
    burnInitialReserve0 sevm b = current.state.reserve0.val.toB256 ∧
    burnInitialReserve1 sevm b = current.state.reserve1.val.toB256 ∧
    (burnInitialToken0 sevm b).toAdr = current.state.token0 ∧
    (burnInitialToken1 sevm b).toAdr = current.state.token1 ∧
    (feeFactoryWord sevm (feeBurnWorldH sevm r.second.returned.devm)).toAdr =
      current.state.factory := by
  have locked := rep.burn_locked_world (sevm := sevm)
  have lockedH := rep.burn_locked_worldH (sevm := sevm)
  rcases locked.fixed with ⟨_, _, _, token0, token1, cache0, cache1, _, _, _, _, _⟩
  rcases lockedH.fixed with ⟨_, _, factory, _, _, _, _, _, _, _, _, _⟩
  refine ⟨cache0, cache1, ?_, ?_, ?_⟩
  · rw [burnInitialToken0,
      show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      B256.and_comm, and_mask_word, toAdr_toB256, burnInitialReserveWorld]
    change (((afterSload sevm (burnLockedWorld sevm b) 8).getStor sevm.currentTarget).get 6).toAdr = _
    rw [afterSload_getStor]
    exact token0
  · rw [burnInitialToken1,
      show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask from by decide,
      B256.and_comm, and_mask_word, toAdr_toB256, burnInitialReserveWorld]
    change (((afterSload sevm (afterSload sevm (burnLockedWorld sevm b) 8) 6).getStor
      sevm.currentTarget).get 7).toAdr = _
    rw [afterSload_getStor, afterSload_getStor]
    exact token1
  · rw [feeFactoryWord, toAdr_toB256, feeBurnWorldH]
    change (((afterSloadH sevm r.second.returned.devm _).getStor sevm.currentTarget).get 5).toAdr = _
    rw [afterSloadH_getStor, r.second_storage]
    exact factory

theorem BurnInitialPairH.sampled_liquidity {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnInitialPairH root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget)) :
    feeBurnLiquidity sevm r.second.returned.devm = current.state.balanceOf sevm.currentTarget := by
  have selected := (r.fee_entry_rep rep).selected (.balance sevm.currentTarget) tracked
  change (r.second.returned.devm.getStor sevm.currentTarget).get
    (transferBalanceSlot sevm.currentTarget) = _
  exact selected

end Blanc.Lift.UniswapV2Pair
