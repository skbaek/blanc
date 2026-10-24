import Blanc.Lift.UniswapV2Pair.MintPositionalRoot

/-! Finite storage bindings of the actual Mint call certificate. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem MintRootCallPositions.first_storage {root : Exec.Deriv} {b : Devm}
    (r : MintRootCallPositions root b) (a : Adr) :
    r.first.call.returned.devm.getStor a = (mintLockedWorld root.sevm b).getStor a := by
  calc
    _ = (mintRootFirstWorld root b).getStor a := r.post0.stor a
    _ = (afterSload root.sevm (mintRootReserves root b) 6).getStor a := by
      simp only [mintRootFirstWorld, Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    _ = (mintLockedWorld root.sevm b).getStor a := by
      rw [afterSload_getStor, mintRootReserves, afterSload_getStor]

theorem MintRootCallPositionsH.first_storage {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    (r : MintRootCallPositionsH root b W1 A2 F) (a : Adr) :
    r.first.call.returned.devm.getStor a = (mintLockedWorldH root.sevm b).getStor a := by
  calc
    _ = W1.getStor a := r.post0.stor a
    _ = (mintRootFirstWorldH root b).getStor a := by rw [r.worlds.1]
    _ = (afterSloadH root.sevm (mintRootReservesH root b) 6).getStor a := by
      simp only [mintRootFirstWorldH, Devm.getStor, Devm.getAcct, accountAccessH_state]
    _ = (mintLockedWorldH root.sevm b).getStor a := by
      rw [afterSloadH_getStor, mintRootReservesH, afterSloadH_getStor]

theorem MintRootCallPositions.second_storage {root : Exec.Deriv} {b : Devm}
    (r : MintRootCallPositions root b) (a : Adr) :
    r.second.call.returned.devm.getStor a = (mintLockedWorld root.sevm b).getStor a := by
  calc
    _ = (mintRootSecondWorld r.first).getStor a := r.post1.stor a
    _ = (afterSload r.first.call.returned.sevm r.first.call.returned.devm 7).getStor a := by
      simp only [mintRootSecondWorld, Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    _ = (mintLockedWorld root.sevm b).getStor a := by
      rw [afterSload_getStor, r.first_storage]

theorem MintRootCallPositionsH.second_storage {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    (r : MintRootCallPositionsH root b W1 A2 F) (a : Adr) :
    r.second.call.returned.devm.getStor a = (mintLockedWorldH root.sevm b).getStor a := by
  calc
    _ = (A2 r.first.call.returned.sevm r.first.call.returned.devm).getStor a := r.post1.stor a
    _ = (mintSecondWorldOfH r.first.call.returned.sevm r.first.call.returned.devm).getStor a := by
      rw [r.worlds.2.1 _ _ r.first.returned_sevm]
    _ = (afterSloadH r.first.call.returned.sevm r.first.call.returned.devm 7).getStor a := by
      simp only [mintSecondWorldOfH, Devm.getStor, Devm.getAcct, accountAccessH_state]
    _ = (mintLockedWorldH root.sevm b).getStor a := by
      rw [afterSloadH_getStor, r.first_storage]

/-- Incoming finite state is transported by these particular original static replies. -/
theorem MintRootCallPositions.fee_entry_rep {root : Exec.Deriv} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : MintRootCallPositions root b)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state) :
    WriterRep K (r.second.call.returned.devm.getStor root.sevm.currentTarget)
      { current.state with unlocked := 0 } := by
  rw [r.second_storage]
  exact rep.mint_locked_world

theorem MintRootCallPositionsH.fee_entry_rep {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : MintRootCallPositionsH root b W1 A2 F)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state) :
    WriterRep K (r.second.call.returned.devm.getStor root.sevm.currentTarget)
      { current.state with unlocked := 0 } := by
  rw [r.second_storage]
  exact rep.mint_locked_worldH

/-- The same actual storage reads fix both cached reserves and every request target. -/
theorem MintRootCallPositions.cache_targets {root : Exec.Deriv} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : MintRootCallPositions root b)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state) :
    mintRootReserve0 root b = current.state.reserve0.val.toB256 ∧
    mintRootReserve1 root b = current.state.reserve1.val.toB256 ∧
    (mintRootToken0 root b).toAdr = current.state.token0 ∧
    (mintRootToken1 r.first).toAdr = current.state.token1 ∧
    (feeFactoryWord root.sevm r.second.call.returned.devm).toAdr = current.state.factory := by
  have locked := rep.mint_locked_world (sevm := root.sevm)
  rcases locked.fixed with ⟨_, _, factory, token0, token1, cache0, cache1, _, _, _, _, _⟩
  refine ⟨cache0, cache1, ?_, ?_, ?_⟩
  · rw [mintRootToken0, toAdr_toB256, mintRootReserves]
    change (((afterSload root.sevm (mintLockedWorld root.sevm b) 8).getStor root.sevm.currentTarget).get 6).toAdr = _
    rw [afterSload_getStor]
    exact token0
  · rw [mintRootToken1, toAdr_toB256]
    have env := r.first.returned_sevm
    simp only [env]
    change ((r.first.call.returned.devm.getStor root.sevm.currentTarget).get 7).toAdr = _
    rw [r.first_storage]
    exact token1
  · rw [feeFactoryWord, toAdr_toB256]
    change ((r.second.call.returned.devm.getStor root.sevm.currentTarget).get 5).toAdr = _
    rw [r.second_storage]
    exact factory

theorem MintRootCallPositionsH.cache_targets {root : Exec.Deriv} {b : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : MintRootCallPositionsH root b W1 A2 F)
    (rep : WriterRep K (b.getStor root.sevm.currentTarget) current.state) :
    mintRootReserve0 root b = current.state.reserve0.val.toB256 ∧
    mintRootReserve1 root b = current.state.reserve1.val.toB256 ∧
    (mintRootToken0 root b).toAdr = current.state.token0 ∧
    (mintToken1Of r.first.call.returned).toAdr = current.state.token1 ∧
    (feeFactoryWord root.sevm r.second.call.returned.devm).toAdr = current.state.factory := by
  have locked := rep.mint_locked_world (sevm := root.sevm)
  have lockedH := rep.mint_locked_worldH (sevm := root.sevm)
  rcases locked.fixed with ⟨_, _, _, token0, _, cache0, cache1, _, _, _, _, _⟩
  rcases lockedH.fixed with ⟨_, _, factory, _, token1, _, _, _, _, _, _, _⟩
  refine ⟨cache0, cache1, ?_, ?_, ?_⟩
  · rw [mintRootToken0, toAdr_toB256, mintRootReserves]
    change (((afterSload root.sevm (mintLockedWorld root.sevm b) 8).getStor root.sevm.currentTarget).get 6).toAdr = _
    rw [afterSload_getStor]
    exact token0
  · rw [mintToken1Of, toAdr_toB256]
    have env := r.first.returned_sevm
    simp only [env]
    change ((r.first.call.returned.devm.getStor root.sevm.currentTarget).get 7).toAdr = _
    rw [r.first_storage]
    exact token1
  · rw [feeFactoryWord, toAdr_toB256]
    change ((r.second.call.returned.devm.getStor root.sevm.currentTarget).get 5).toAdr = _
    rw [r.second_storage]
    exact factory

theorem mint_positional_balance_handlersH {sevm : Sevm} {b post : Devm} {W1 : Devm} {A2 F : Sevm → Devm → Devm} {G : Nat}
    {K : WriterKey → Prop} {current : Checkpoint}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (r : MintRootCallPositionsH ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b W1 A2 F)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (invocation : List Nat) (codeEq : sevm.code = code)
    (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) (selector : Blanc.Sevm.selector sevm = 0x6a627842) :
    sevm.value = 0 ∧ sevm.isStatic = false ∧
      MintBalanceHandlerResult current (writerContext sevm invocation)
        (Sevm.dataWord sevm 4).toAdr r.out0 r.out1 := by
  obtain ⟨value, _, _, unlocked, nonstatic⟩ := mint_prefix_guards_of_successH codeEq stateGas bal selector run
  obtain ⟨cache0, cache1, _, _, _⟩ := r.cache_targets rep
  have nat0 : (mintRootReserve0 ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b).toNat =
      current.state.reserve0.val := by
    rw [cache0, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have nat1 : (mintRootReserve1 ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b).toNat =
      current.state.reserve1.val := by
    rw [cache1, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have sourceUnlocked : current.state.unlocked = 1 := by
    rcases rep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, _, fixed⟩
    exact fixed.symm.trans unlocked
  have cover0 : current.state.reserve0.val ≤ (Bytes.toB256 (r.out0.take 32)).toNat := by
    rw [← nat0]
    exact B256.toNat_le_toNat r.cover0
  have cover1 : current.state.reserve1.val ≤ (Bytes.toB256 (r.out1.take 32)).toNat := by
    rw [← nat1]
    exact B256.toNat_le_toNat r.cover1
  exact ⟨value, nonstatic,
    mint_source_balance_handlers value nonstatic sourceUnlocked r.width0 r.width1 cover0 cover1⟩

/-- These retained physical balance replies advance the incoming source state. -/
theorem mint_positional_balance_handlers {sevm : Sevm} {b post : Devm} {G : Nat}
    {K : WriterKey → Prop} {current : Checkpoint}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (r : MintRootCallPositions ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (invocation : List Nat) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork) (selector : Blanc.Sevm.selector sevm = 0x6a627842) :
    sevm.value = 0 ∧ sevm.isStatic = false ∧
      MintBalanceHandlerResult current (writerContext sevm invocation)
        (Sevm.dataWord sevm 4).toAdr r.out0 r.out1 :=
  mint_positional_balance_handlersH run (r.toH fork) rep invocation codeEq fork.rules_stateGas_none fork.rules_bal_none selector


end Blanc.Lift.UniswapV2Pair
