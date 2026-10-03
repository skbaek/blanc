import Blanc.Lift.UniswapV2Pair.MintAfterFeeWalk

/-! Finite source accounting for the complete actual post-fee public mint suffix. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Initial checked pricing agrees with the source square-root subtraction. -/
theorem mintInitialAmount_source {amount0 amount1 : B256} {r0 r1 : Nat}
    (product : B256.Nofm amount0 amount1)
    (cover : (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256) :
    mintAmount amount0 amount1 0 r0 r1 = .ok (mintInitialLiquidity amount0 amount1).toNat := by
  have rootBound : Nat.sqrt (amount0.toNat * amount1.toNat) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sqrt_le_self _) product
  have rootRead : (Nat.sqrt (amount0 * amount1).toNat).toB256.toNat =
      Nat.sqrt (amount0.toNat * amount1.toNat) := by
    rw [B256.toNat_mul_eq_of_nofm product, B256.toNat_toB256_of_lt rootBound]
  have coverNat : 1000 ≤ Nat.sqrt (amount0.toNat * amount1.toNat) := by
    have h := B256.toNat_le_toNat cover
    rw [rootRead] at h
    exact h
  rw [mintAmount, ite_eq_left rfl, ite_eq_left (show amount0.toNat * amount1.toNat < 2 ^ 256 from product), ite_eq_left coverNat]
  rw [mintInitialLiquidity, B256.toNat_sub_eq_of_le _ _ cover, rootRead]
  rfl

/-- Both checked products and real nonzero divisors give the source's two floors. -/
theorem mintLaterAmount_source {amount0 amount1 supply r0 r1 : B256}
    (supplyNonzero : supply ≠ 0)
    (product0 : B256.Nofm amount0 supply) (nonzero0 : r0 ≠ 0)
    (product1 : B256.Nofm amount1 supply) (nonzero1 : r1 ≠ 0) :
    mintAmount amount0 amount1 supply r0.toNat r1.toNat =
      .ok (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)).toNat := by
  have divisor0 : r0.toNat ≠ 0 := fun h => nonzero0 ((B256.toNat_inj _ _ (h.trans B256.toNat_zero.symm)))
  have divisor1 : r1.toNat ≠ 0 := fun h => nonzero1 ((B256.toNat_inj _ _ (h.trans B256.toNat_zero.symm)))
  rw [mintAmount, ite_eq_right supplyNonzero, ite_eq_left (show amount0.toNat * supply.toNat < 2 ^ 256 from product0),
    ite_eq_right divisor0, ite_eq_left (show amount1.toNat * supply.toNat < 2 ^ 256 from product1), ite_eq_right divisor1]
  unfold AMMArithmetic.mintLiquidity mintMinWord
  by_cases less : (amount0 * supply) / r0 < (amount1 * supply) / r1
  · rw [ite_eq_left less, B256.toNat_div nonzero0, B256.toNat_mul_eq_of_nofm product0]
    apply congrArg Except.ok
    apply Nat.min_eq_left
    have h := B256.lt_iff_toNat_lt_toNat.mp less
    rw [B256.toNat_div nonzero0, B256.toNat_div nonzero1,
      B256.toNat_mul_eq_of_nofm product0, B256.toNat_mul_eq_of_nofm product1] at h
    exact Nat.le_of_lt h
  · rw [ite_eq_right less, B256.toNat_div nonzero1, B256.toNat_mul_eq_of_nofm product1]
    apply congrArg Except.ok
    apply Nat.min_eq_right
    have h : ((amount1 * supply) / r1).toNat ≤ ((amount0 * supply) / r0).toNat := by
      have h := less
      rw [B256.lt_iff_toNat_lt_toNat] at h
      exact Nat.le_of_not_gt h
    rw [B256.toNat_div nonzero0, B256.toNat_div nonzero1,
      B256.toNat_mul_eq_of_nofm product0, B256.toNat_mul_eq_of_nofm product1] at h
    exact h


/-- Finite accounting for the actual recipient callee and the already derived full raw return. -/
def MintPricedLPSourceResult (K : WriterKey → Prop) (st : State) (sevm : Sevm)
    (b : Devm) (R : List B256) (M : Mem)
    (supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256) (o : Outcome) : Prop :=
  0 < liquidity.toNat ∧ b0.toNat < 2 ^ 112 ∧ b1.toNat < 2 ^ 112 ∧
    ∃ mintGas residual gas,
      SFunc.Run cert.prog sevm
        (St b (liquidity :: toWord :: 0x1330 :: supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
          liquidity :: toWord :: ρ :: R) M mintGas) t_28ca_c62
        (.returned (lpMintPost sevm b (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 ::
          liquidity :: toWord :: ρ :: R) M toWord liquidity residual)) ∧
      LPMintSourceResult K st sevm b
        (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
        M toWord liquidity residual ∧
      o = .returned (mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ residual gas)

theorem mintPricedLP_source {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem}
    {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {o : Outcome}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched toWord.toAdr))
    (observed : MintPricedResult sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ o) :
    MintPricedLPSourceResult K st sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ o := by
  obtain ⟨positive, accepts, bound0, bound1, mintGas, residual, gas, callee, result⟩ := observed
  exact ⟨positive, bound0, bound1, mintGas, residual, gas, callee,
    lpMint_source_result rep fresh accepts, result⟩

/-- The actual update changes only fixed reserve/oracle words; the finite LP rows survive. -/
theorem WriterRep.mint_update {K : WriterKey → Prop} {st post : State} {ctx : Context}
    {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 : B256} {event : Event} {oracle : OracleUpdate}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : old0.toNat < 2 ^ 112) (oldBound1 : old1.toNat < 2 ^ 112)
    (accepted : st.update ctx balance0 balance1 old0.toNat old1.toNat = .ok (post, event, oracle)) :
    WriterRep K ((updateWorld sevm b old0 old1 balance0 balance1).getStor sevm.currentTarget) post := by
  have slots : ReserveSlotMatches st sevm b := ⟨rep.fixed.2.2.2.2.2.1,
    rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  have cum0 := rep.fixed.2.2.2.2.2.2.2.2.1
  have cum1 := rep.fixed.2.2.2.2.2.2.2.2.2.1
  have correspondence := update_source_result_of_ok slots cum0 cum1 time pair oldBound0 oldBound1 accepted
  obtain ⟨bound0,bound1⟩ := update_source_guards accepted
  unfold State.update at accepted
  rw [dite_eq_left bound0, dite_eq_left bound1] at accepted
  cases accepted
  have unchanged (k : B256) (off : k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10) :
      ((updateWorld sevm b old0 old1 balance0 balance1).getStor sevm.currentTarget).get k =
        (b.getStor sevm.currentTarget).get k := updateWorld_storage_frame (.inr off)
  refine ⟨rep.finite, ?_, ?_, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches]
    rw [unchanged 0 ⟨by decide,by decide,by decide⟩,
      unchanged 3 ⟨by decide,by decide,by decide⟩,
      unchanged 5 ⟨by decide,by decide,by decide⟩,
      unchanged 6 ⟨by decide,by decide,by decide⟩,
      unchanged 7 ⟨by decide,by decide,by decide⟩,
      unchanged 11 ⟨by decide,by decide,by decide⟩,
      unchanged 12 ⟨by decide,by decide,by decide⟩]
    exact ⟨rep.fixed.1,rep.fixed.2.1,rep.fixed.2.2.1,rep.fixed.2.2.2.1,
      rep.fixed.2.2.2.2.1,correspondence.1.1,correspondence.1.2.1,
      correspondence.1.2.2,correspondence.2.1,correspondence.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.2.2.2.2.2⟩
  · intro k nonzero
    by_cases hit : k = 8 ∨ k = 9 ∨ k = 10
    · rcases hit with h | h | h
      · subst k; exact .inl (by decide)
      · subst k; exact .inl (by decide)
      · subst k; exact .inl (by decide)
    · have off : k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10 :=
        ⟨fun h => hit (.inl h), fun h => hit (.inr (.inl h)), fun h => hit (.inr (.inr h))⟩
      rw [unchanged k off] at nonzero
      exact rep.support k nonzero
  · intro k tracked
    have off (n : B256) (fixed : n ∈ writerFixedSlots) : k.slot ≠ n :=
      fun h => rep.apart k tracked (h.symm ▸ fixed)
    rw [unchanged k.slot ⟨off 8 (by decide),off 9 (by decide),off 10 (by decide)⟩]
    cases k <;> exact rep.selected _ tracked
  · intro k outside
    cases k <;> exact rep.logicalZero _ outside



def mintLastSourceState (st : State) : State :=
  { st with kLast := (st.reserve0.val * st.reserve1.val).toB256 }

def mintUnlockedSourceState (st : State) : State := { st with unlocked := 1 }

/-- Only actual slot11 is rewritten after the update, with the new reserve product. -/
theorem WriterRep.mint_last_store {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) :
    WriterRep K (s.set 11 (st.reserve0.val * st.reserve1.val).toB256) (mintLastSourceState st) := by
  have unchanged (n : B256) (off : (11 : B256) ≠ n) :
      (s.set 11 (st.reserve0.val * st.reserve1.val).toB256).get n = s.get n :=
    Stor.get_set_ne s off _
  refine ⟨rep.finite, ?_, ?_, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches, mintLastSourceState]
    rw [unchanged 0 (by decide),unchanged 3 (by decide),unchanged 5 (by decide),
      unchanged 6 (by decide),unchanged 7 (by decide),unchanged 8 (by decide),
      unchanged 9 (by decide),unchanged 10 (by decide),Stor.get_set_self,unchanged 12 (by decide)]
    exact ⟨rep.fixed.1,rep.fixed.2.1,rep.fixed.2.2.1,rep.fixed.2.2.2.1,
      rep.fixed.2.2.2.2.1,rep.fixed.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.2.2.1,rfl,rep.fixed.2.2.2.2.2.2.2.2.2.2.2⟩
  · intro k nonzero
    by_cases hit : k = 11
    · exact .inl (hit.symm ▸ (by decide : (11 : B256) ∈ writerFixedSlots))
    · rw [unchanged k (Ne.symm hit)] at nonzero
      exact rep.support k nonzero
  · intro k tracked
    have off : (11 : B256) ≠ k.slot :=
      fun h => rep.apart k tracked (h ▸ (by decide : (11 : B256) ∈ writerFixedSlots))
    rw [unchanged k.slot off]
    cases k <;> exact rep.selected _ tracked
  · intro k outside
    cases k <;> exact rep.logicalZero _ outside

/-- The final public-mint store unlocks slot12 and preserves every finite LP row. -/
theorem WriterRep.mint_unlock_store {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) : WriterRep K (s.set 12 1) (mintUnlockedSourceState st) := by
  have unchanged (n : B256) (off : (12 : B256) ≠ n) :
      (s.set 12 1).get n = s.get n := Stor.get_set_ne s off 1
  refine ⟨rep.finite, ?_, ?_, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches, mintUnlockedSourceState]
    rw [unchanged 0 (by decide),unchanged 3 (by decide),unchanged 5 (by decide),
      unchanged 6 (by decide),unchanged 7 (by decide),unchanged 8 (by decide),
      unchanged 9 (by decide),unchanged 10 (by decide),unchanged 11 (by decide),Stor.get_set_self]
    exact ⟨rep.fixed.1,rep.fixed.2.1,rep.fixed.2.2.1,rep.fixed.2.2.2.1,
      rep.fixed.2.2.2.2.1,rep.fixed.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.2.2.1,
      rep.fixed.2.2.2.2.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.2.2.2.2.1,rfl⟩
  · intro k nonzero
    by_cases hit : k = 12
    · exact .inl (hit.symm ▸ (by decide : (12 : B256) ∈ writerFixedSlots))
    · rw [unchanged k (Ne.symm hit)] at nonzero
      exact rep.support k nonzero
  · intro k tracked
    have off : (12 : B256) ≠ k.slot :=
      fun h => rep.apart k tracked (h ▸ (by decide : (12 : B256) ∈ writerFixedSlots))
    rw [unchanged k.slot off]
    cases k <;> exact rep.selected _ tracked
  · intro k outside
    cases k <;> exact rep.logicalZero _ outside

theorem WriterRep.mint_conditional_last {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {f : B256} (rep : WriterRep K (b.getStor sevm.currentTarget) st) :
    WriterRep K ((mintConditionalLastWorld sevm b f).getStor sevm.currentTarget)
      (if f = 0 then st else mintLastSourceState st) := by
  unfold mintConditionalLastWorld
  by_cases zero : f = 0
  · simp only [ite_eq_left zero]
    exact rep
  · simp only [ite_eq_right zero]
    have product : reserve0Read (b.getStorVal sevm.currentTarget 8) *
        reserve1Read (b.getStorVal sevm.currentTarget 8) =
        (st.reserve0.val * st.reserve1.val).toB256 := by
      change reserve0Read ((b.getStor sevm.currentTarget).get 8) *
        reserve1Read ((b.getStor sevm.currentTarget).get 8) = _
      rw [rep.fixed.2.2.2.2.2.1,rep.fixed.2.2.2.2.2.2.1]
      apply B256.toNat_inj
      have bounds : B256.Nofm st.reserve0.val.toB256 st.reserve1.val.toB256 :=
        feeReserveProduct_noWrap
          (by rw [B256.toNat_toB256_of_lt (lt_trans st.reserve0.isLt (by decide))]; exact st.reserve0.isLt)
          (by rw [B256.toNat_toB256_of_lt (lt_trans st.reserve1.isLt (by decide))]; exact st.reserve1.isLt)
      have productBound : st.reserve0.val * st.reserve1.val < 2 ^ 256 := by
        simpa only [B256.Nofm,
          B256.toNat_toB256_of_lt (lt_trans st.reserve0.isLt (by decide)),
          B256.toNat_toB256_of_lt (lt_trans st.reserve1.isLt (by decide))] using bounds
      rw [B256.toNat_mul_eq_of_nofm bounds,
        B256.toNat_toB256_of_lt (lt_trans st.reserve0.isLt (by decide)),
        B256.toNat_toB256_of_lt (lt_trans st.reserve1.isLt (by decide)),
        B256.toNat_toB256_of_lt productBound]
    rw [mintKLastWorld,afterSstore_getStor_self,afterSload_getStor,product]
    exact rep.mint_last_store

theorem WriterRep.mint_return {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {amount0 amount1 : B256} (rep : WriterRep K (b.getStor sevm.currentTarget) st) :
    WriterRep K ((mintReturnWorld sevm b amount0 amount1).getStor sevm.currentTarget)
      (mintUnlockedSourceState st) := by
  rw [mintReturnWorld,afterSstore_getStor_self,Devm.addLog_getStor]
  exact rep.mint_unlock_store



def mintFinishedSourceState (st : State) (f : B256) : State :=
  mintUnlockedSourceState (if f = 0 then st else mintLastSourceState st)

/-- The whole actual priced suffix yields source LP/update acceptance and finite final storage. -/
theorem mintPriced_source_result {K : WriterKey → Prop} {st : State} {ctx : Context}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {o : Outcome}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched toWord.toAdr))
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : r0.toNat < 2 ^ 112) (oldBound1 : r1.toNat < 2 ^ 112)
    (observed : MintPricedResult sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ o) :
    0 < liquidity.toNat ∧
    ∃ post event oracle residual gas,
      st.mintLP toWord.toAdr liquidity =
        .ok (lpMintSourceState st toWord.toAdr liquidity, [.transfer 0 toWord.toAdr liquidity]) ∧
      (lpMintSourceState st toWord.toAdr liquidity).update ctx b0 b1 r0.toNat r1.toNat =
        .ok (post,event,oracle) ∧
      WriterRep (WriterExtend K (lpMintTouched toWord.toAdr))
        ((mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ residual gas).getStor sevm.currentTarget)
        (mintFinishedSourceState post f) ∧
      event = .sync b0.toNat b1.toNat ∧
      o = .returned (mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ residual gas) := by
  obtain ⟨positive,bound0,bound1,mintGas,residual,gas,callee,lp,result⟩ :=
    mintPricedLP_source rep fresh observed
  let base := lpMintPost sevm b
    (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
    M toWord liquidity residual
  have lpRep : WriterRep (WriterExtend K (lpMintTouched toWord.toAdr))
      (base.getStor sevm.currentTarget) (lpMintSourceState st toWord.toAdr liquidity) := lp.2.1
  have slots : ReserveSlotMatches (lpMintSourceState st toWord.toAdr liquidity) sevm base :=
    ⟨lpRep.fixed.2.2.2.2.2.1,lpRep.fixed.2.2.2.2.2.2.1,lpRep.fixed.2.2.2.2.2.2.2.1⟩
  obtain ⟨post,event,oracle,accepted,correspondence⟩ := update_source_result slots
    lpRep.fixed.2.2.2.2.2.2.2.2.1 lpRep.fixed.2.2.2.2.2.2.2.2.2.1
    time pair oldBound0 oldBound1 bound0 bound1
  have updated := lpRep.mint_update time pair oldBound0 oldBound1 accepted
  have finished := (updated.mint_conditional_last (f := f)).mint_return
    (amount0 := amount0) (amount1 := amount1)
  refine ⟨positive,post,event,oracle,residual,gas,lp.1,accepted,?_,correspondence.2.2.2.1,result⟩
  change WriterRep (WriterExtend K (lpMintTouched toWord.toAdr))
    ((mintReturnWorld sevm (mintConditionalLastWorld sevm
      (updateWorld sevm base r0 r1 b0 b1) f) amount0 amount1).getStor sevm.currentTarget)
    (mintFinishedSourceState post f)
  exact finished




/-- Exact chronological Transfer, Sync, Mint logs of the complete common suffix. -/
theorem mintPricedPost_logs {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ : B256} {residual gas : Nat}
    (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112) :
    (mintPricedPost sevm b R M supply f amount1 amount0 b1 b0 r1 r0 liquidity toWord ρ residual gas).logs =
      b.logs ++ [lpMintRawLog sevm.currentTarget toWord.toAdr liquidity,
        ⟨sevm.currentTarget,[updateSyncTopic],encodeWords [b0,b1]⟩,mintEventLog sevm amount0 amount1] := by
  let base := lpMintPost sevm b
    (supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
    M toWord liquidity residual
  have unchanged : (mintConditionalLastWorld sevm (updateWorld sevm base r0 r1 b0 b1) f).logs =
      (updateWorld sevm base r0 r1 b0 b1).logs := by
    unfold mintConditionalLastWorld
    split
    · rfl
    · rw [mintKLastWorld,afterSstore_logs,afterSload_logs]
  change (mintReturnWorld sevm (mintConditionalLastWorld sevm
    (updateWorld sevm base r0 r1 b0 b1) f) amount0 amount1).logs = _
  rw [mintReturnWorld,afterSstore_logs]
  change (mintConditionalLastWorld sevm (updateWorld sevm base r0 r1 b0 b1) f).logs ++
    [mintEventLog sevm amount0 amount1] = _
  rw [unchanged,updateWorld_logs bound0 bound1]
  have transfer := (lpMintPost_facts (sevm := sevm) (b := b)
    (R := supply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R)
    (M := M) (toWord := toWord) (value := liquidity) (G := residual)).2.2.1
  change base.logs = b.logs ++ [lpMintRawLog sevm.currentTarget toWord.toAdr liquidity] at transfer
  rw [transfer]
  simp only [List.append_assoc,List.cons_append,List.nil_append]


/-- All model computations and the finite final storage are produced from actual suffix observations. -/
def MintAfterFeeSourceResult (K : WriterKey → Prop) (st : State) (ctx : Context) (sevm : Sevm) (b : Devm) (R : List B256)
    (f amount1 amount0 b1 b0 r1 r0 toWord : B256) (o : Outcome) : Prop :=
  ∃ liquidity : Nat, ∃ keys : WriterKey → Prop,
    ∃ minimum recipient post : State, ∃ minimumEvents recipientEvents : List Event,
    ∃ event : Event, ∃ oracle : OracleUpdate, ∃ d : Devm,
      keys = (if st.totalSupply = 0 then
        WriterExtend (WriterExtend K (lpMintTouched (0 : B256).toAdr)) (lpMintTouched toWord.toAdr)
        else WriterExtend K (lpMintTouched toWord.toAdr)) ∧
      mintAmount amount0 amount1 st.totalSupply r0.toNat r1.toNat = .ok liquidity ∧
      (if st.totalSupply = 0 then st.mintLP 0 1000 else .ok (st,[])) =
        .ok (minimum,minimumEvents) ∧
      0 < liquidity ∧
      minimum.mintLP toWord.toAdr liquidity.toB256 = .ok (recipient,recipientEvents) ∧
      recipient.update ctx b0 b1 r0.toNat r1.toNat = .ok (post,event,oracle) ∧
      WriterRep keys (d.getStor sevm.currentTarget) (mintFinishedSourceState post f) ∧
      event = .sync b0.toNat b1.toNat ∧ o = .returned d ∧
      d.logs = b.logs ++
        (if st.totalSupply = 0 then [lpMintRawLog sevm.currentTarget (0 : B256).toAdr 1000] else []) ++
        [lpMintRawLog sevm.currentTarget toWord.toAdr liquidity.toB256,
          ⟨sevm.currentTarget,[updateSyncTopic],encodeWords [b0,b1]⟩,mintEventLog sevm amount0 amount1] ∧
      d.stack = liquidity.toB256 :: R

/-- Finite freshness is requested only for the actual supply arm's touched LP keys. -/
structure MintAfterFeeFresh (K : WriterKey → Prop) (st : State) (toWord : B256) : Prop where
  initial : st.totalSupply = 0 →
    WriterFreshKeys K (lpMintTouched (0 : B256).toAdr) ∧
    WriterFreshKeys (WriterExtend K (lpMintTouched (0 : B256).toAdr)) (lpMintTouched toWord.toAdr)
  later : st.totalSupply ≠ 0 → WriterFreshKeys K (lpMintTouched toWord.toAdr)

/-- Both supply arms derive the complete finite source result from the SAME actual raw observations. -/
theorem mintAfterFee_source_observed {K : WriterKey → Prop} {st : State} {ctx : Context}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {f amount1 amount0 b1 b0 r1 r0 toWord ρ : B256} {o : Outcome}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : MintAfterFeeFresh K st toWord)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : r0.toNat < 2 ^ 112) (oldBound1 : r1.toNat < 2 ^ 112)
    (observed : MintAfterFeeResult sevm b R M f amount1 amount0 b1 b0 r1 r0 toWord ρ o) :
    MintAfterFeeSourceResult K st ctx sevm b R f amount1 amount0 b1 b0 r1 r0 toWord o := by
  have supply : lpMintSupplyWord sevm b = st.totalSupply := rep.fixed.1
  have loaded : WriterRep K ((afterSload sevm b 0).getStor sevm.currentTarget) st := by
    rw [afterSload_getStor]
    exact rep
  unfold MintAfterFeeResult at observed
  rw [supply] at observed
  by_cases zero : st.totalSupply = 0
  · rw [ite_eq_left zero] at observed
    obtain ⟨product,cover,minimumGas,minimumResidual,callee,minimumAccepts,priced⟩ := observed
    let liquidity := mintInitialLiquidity amount0 amount1
    let cache := st.totalSupply :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: ρ :: R
    let base := lpMintPost sevm (afterSload sevm b 0) cache M 0 1000 minimumResidual
    have minimum := lpMint_source_result (R := cache) (M := M) (G := minimumResidual)
      loaded (fresh.initial zero).1 minimumAccepts
    have minimumRep : WriterRep (WriterExtend K (lpMintTouched (0 : B256).toAdr))
        (base.getStor sevm.currentTarget) (lpMintSourceState st (0 : B256).toAdr 1000) := minimum.2.1
    obtain ⟨positive,post,event,oracle,residual,gas,recipientAccepts,updated,final,eventEq,result⟩ :=
      mintPriced_source_result minimumRep (fresh.initial zero).2 time pair oldBound0 oldBound1 priced
    refine ⟨liquidity.toNat,WriterExtend (WriterExtend K (lpMintTouched (0 : B256).toAdr))
      (lpMintTouched toWord.toAdr),lpMintSourceState st (0 : B256).toAdr 1000,
      lpMintSourceState (lpMintSourceState st (0 : B256).toAdr 1000) toWord.toAdr liquidity,
      post,[.transfer 0 (0 : B256).toAdr 1000],[.transfer 0 toWord.toAdr liquidity],
      event,oracle,_,(by simp only [ite_eq_left zero]),?_,?_,positive,?_,updated,final,eventEq,result,?_,?_⟩
    · rw [zero]
      exact mintInitialAmount_source product cover
    · rw [ite_eq_left zero]
      exact minimum.1
    · rw [toB256_toNat liquidity]
      exact recipientAccepts
    · rw [toB256_toNat liquidity,mintPricedPost_logs priced.2.2.1 priced.2.2.2.1]
      have minimumLog := minimum.2.2.2.2.1
      change base.logs = (afterSload sevm b 0).logs ++
        [lpMintRawLog sevm.currentTarget (0 : B256).toAdr 1000] at minimumLog
      rw [minimumLog,afterSload_logs,ite_eq_left zero]
      simp only [List.append_assoc,List.cons_append,List.nil_append]
      rfl
    · change liquidity :: R = liquidity.toNat.toB256 :: R
      rw [toB256_toNat liquidity]
  · rw [ite_eq_right zero] at observed
    obtain ⟨product0,divisor0,product1,divisor1,priced⟩ := observed
    let liquidity := mintMinWord ((amount1 * st.totalSupply) / r1) ((amount0 * st.totalSupply) / r0)
    obtain ⟨positive,post,event,oracle,residual,gas,recipientAccepts,updated,final,eventEq,result⟩ :=
      mintPriced_source_result loaded (fresh.later zero) time pair oldBound0 oldBound1 priced
    refine ⟨liquidity.toNat,WriterExtend K (lpMintTouched toWord.toAdr),st,
      lpMintSourceState st toWord.toAdr liquidity,post,[],[.transfer 0 toWord.toAdr liquidity],
      event,oracle,_,(by simp only [ite_eq_right zero]),?_,?_,positive,?_,updated,final,eventEq,result,?_,?_⟩
    · exact mintLaterAmount_source zero product0 divisor0 product1 divisor1
    · rw [ite_eq_right zero]
    · rw [toB256_toNat liquidity]
      exact recipientAccepts
    · rw [toB256_toNat liquidity,mintPricedPost_logs priced.2.2.1 priced.2.2.2.1,
        afterSload_logs,ite_eq_right zero,List.append_nil]
    · change liquidity :: R = liquidity.toNat.toB256 :: R
      rw [toB256_toNat liquidity]

/-- The inverse extracts the pricing/callee observations from the successful actual1233 run. -/
theorem mintAfterFee_source_inv {K : WriterKey → Prop} {st : State} {ctx : Context}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : MintAfterFeeFresh K st toWord)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : r0.toNat < 2 ^ 112) (oldBound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.Run cert.prog sevm
      (St b (f :: 0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_1233_c41 o) :
    MintAfterFeeSourceResult K st ctx sevm b R f amount1 amount0 b1 b0 r1 r0 toWord o := by
  exact mintAfterFee_source_observed rep fresh time pair oldBound0 oldBound1
    (mintAfterFee_inv fork mem oldBound0 oldBound1 run)



/-- The produced source computations finish the actual typed mint continuation. -/
theorem mintAfterFee_frame_accept {frame : Frame} {observed : MintObserved} {fee : FeeResult}
    {minimum recipient post : State} {minimumEvents recipientEvents : List Event}
    {liquidity : Nat} {event : Event} {oracle : OracleUpdate} {f : B256}
    (pricing : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val = .ok liquidity)
    (initial : (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000 else .ok (fee.state,[])) =
      .ok (minimum,minimumEvents))
    (positive : 0 < liquidity)
    (minted : minimum.mintLP observed.recipient liquidity.toB256 = .ok (recipient,recipientEvents))
    (updated : recipient.update frame.context observed.balance0 observed.balance1
      observed.reserves.reserve0.val observed.reserves.reserve1.val = .ok (post,event,oracle))
    (flag : f = if fee.feeOn then 1 else 0) :
    Frame.mintAfterFee frame observed fee =
      .finished
        ((((((frame.withEvents fee.state fee.events).withEvents minimum minimumEvents).withEvents
          recipient recipientEvents).withUpdate
          (if f = 0 then post else mintLastSourceState post) event oracle).withEvents
          (if f = 0 then post else mintLastSourceState post)
          [.mint frame.context.sender observed.amount0 observed.amount1]).withEvents
          (mintFinishedSourceState post f) [])
        (encodeWords [liquidity.toB256]) := by
  have last : (if fee.feeOn then mintLastSourceState post else post) =
      (if f = 0 then post else mintLastSourceState post) := by
    by_cases on : fee.feeOn = true
    · rw [ite_eq_left on] at flag ⊢
      rw [flag,ite_eq_right (by decide : (1 : B256) ≠ 0)]
    · rw [ite_eq_right on] at flag ⊢
      rw [flag,ite_eq_left rfl]
  unfold Frame.mintAfterFee
  dsimp only
  rw [pricing]
  dsimp only
  rw [initial]
  dsimp only
  rw [ite_eq_left positive,minted]
  unfold Frame.finishUpdated
  dsimp only [Frame.withEvents]
  rw [updated]
  change ((((((frame.withEvents fee.state fee.events).withEvents minimum minimumEvents).withEvents
    recipient recipientEvents).withUpdate
      (if fee.feeOn then mintLastSourceState post else post) event oracle).withEvents
      (if fee.feeOn then mintLastSourceState post else post)
      [.mint frame.context.sender observed.amount0 observed.amount1]).finishLocked
      (encodeWords [liquidity.toB256])) = _
  rw [last]
  rfl

/-- Genuine primitive affordability constructs the raw run, then derives its finite source result. -/
theorem mintAfterFee_source_exact {K : WriterKey → Prop} {st : State} {ctx : Context}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : MintAfterFeeFresh K st toWord)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : r0.toNat < 2 ^ 112) (oldBound1 : r1.toNat < 2 ^ 112)
    (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112) (room : R.length ≤ 997)
    (env : MintAfterFeeEnv sevm b f toWord amount0 amount1 b0 b1 r0 r1 G) :
    SFunc.RunExact cert.prog sevm
      (St b (f :: 0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (env.armGas + sloadCost sevm b 0 + 28)) t_1233_c41 (.returned (env.post M R ρ)) ∧
    MintAfterFeeSourceResult K st ctx sevm b R f amount1 amount0 b1 b0 r1 r0 toWord (.returned (env.post M R ρ)) := by
  have raw := mintAfterFee_exact (oldLiquidity := oldLiquidity) (ρ := ρ) fork mem
    oldBound0 oldBound1 bound0 bound1 room env
  exact ⟨raw,mintAfterFee_source_inv fork mem rep fresh time pair oldBound0 oldBound1 raw.toRun⟩



/-- Internal typed cache bindings; the public prefix must derive them from its actual observations. -/
structure MintAfterFeeCache (observed : MintObserved) (fee : FeeResult)
    (f amount1 amount0 b1 b0 r1 r0 toWord : B256) : Prop where
  recipient : observed.recipient = toWord.toAdr
  reserve0 : observed.reserves.reserve0.val = r0.toNat
  reserve1 : observed.reserves.reserve1.val = r1.toNat
  balance0 : observed.balance0 = b0
  balance1 : observed.balance1 = b1
  amount0 : observed.amount0 = amount0
  amount1 : observed.amount1 = amount1
  flag : f = if fee.feeOn then 1 else 0

def mintAfterFeeFinishedFrame (frame : Frame) (fee : FeeResult)
    (minimum recipient post : State) (minimumEvents recipientEvents : List Event)
    (event : Event) (oracle : OracleUpdate) (f amount0 amount1 : B256) : Frame :=
  let last := if f = 0 then post else mintLastSourceState post
  let charged := frame.withEvents fee.state fee.events
  let minted := (charged.withEvents minimum minimumEvents).withEvents recipient recipientEvents
  let updated := minted.withUpdate last event oracle
  let logged := updated.withEvents last [.mint frame.context.sender amount0 amount1]
  logged.withEvents (mintFinishedSourceState post f) []

/-- The actual typed frame, finite final storage, exact raw log order and return word agree. -/
def MintAfterFeeFrameResult (K : WriterKey → Prop) (frame : Frame) (observed : MintObserved)
    (fee : FeeResult) (sevm : Sevm) (b : Devm) (R : List B256)
    (amount1 amount0 b1 b0 toWord : B256) (o : Outcome) : Prop :=
  ∃ liquidity : Nat, ∃ keys : WriterKey → Prop, ∃ finished : Frame, ∃ d : Devm,
    keys = (if fee.state.totalSupply = 0 then
      WriterExtend (WriterExtend K (lpMintTouched (0 : B256).toAdr)) (lpMintTouched toWord.toAdr)
      else WriterExtend K (lpMintTouched toWord.toAdr)) ∧
    Frame.mintAfterFee frame observed fee = .finished finished (encodeWords [liquidity.toB256]) ∧
    WriterRep keys (d.getStor sevm.currentTarget) finished.current.state ∧
    o = .returned d ∧ d.stack = liquidity.toB256 :: R ∧
    d.logs = b.logs ++
      (if fee.state.totalSupply = 0 then [lpMintRawLog frame.context.pair (0 : B256).toAdr 1000] else []) ++
      [lpMintRawLog frame.context.pair toWord.toAdr liquidity.toB256,
        ⟨frame.context.pair,[updateSyncTopic],encodeWords [b0,b1]⟩,⟨frame.context.pair,[mintEventTopic,frame.context.sender.toB256],amount0.toBytes ++ amount1.toBytes⟩]

theorem mintAfterFee_source_frame {K : WriterKey → Prop} {frame : Frame} {observed : MintObserved}
    {fee : FeeResult} {sevm : Sevm} {b : Devm} {R : List B256}
    {f amount1 amount0 b1 b0 r1 r0 toWord : B256} {o : Outcome}
    (cache : MintAfterFeeCache observed fee f amount1 amount0 b1 b0 r1 r0 toWord)
    (pair : frame.context.pair = sevm.currentTarget) (sender : frame.context.sender = sevm.caller)
    (source : MintAfterFeeSourceResult K fee.state frame.context sevm b R
      f amount1 amount0 b1 b0 r1 r0 toWord o) :
    MintAfterFeeFrameResult K frame observed fee sevm b R amount1 amount0 b1 b0 toWord o := by
  obtain ⟨liquidity,keys,minimum,recipient,post,minimumEvents,recipientEvents,event,oracle,d,
    footprint,pricing,initial,positive,minted,updated,rep,eventEq,result,logs,stack⟩ := source
  have pricingTyped : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val = .ok liquidity := by
    simpa only [cache.amount0,cache.amount1,cache.reserve0,cache.reserve1] using pricing
  have mintedTyped : minimum.mintLP observed.recipient liquidity.toB256 = .ok (recipient,recipientEvents) := by
    simpa only [cache.recipient] using minted
  have updatedTyped : recipient.update frame.context observed.balance0 observed.balance1
      observed.reserves.reserve0.val observed.reserves.reserve1.val = .ok (post,event,oracle) := by
    simpa only [cache.balance0,cache.balance1,cache.reserve0,cache.reserve1] using updated
  have typed := mintAfterFee_frame_accept pricingTyped initial positive mintedTyped updatedTyped cache.flag
  refine ⟨liquidity,keys,mintAfterFeeFinishedFrame frame fee minimum recipient post
    minimumEvents recipientEvents event oracle f amount0 amount1,d,footprint,?_,rep,result,stack,?_⟩
  · simpa only [cache.amount0,cache.amount1,mintAfterFeeFinishedFrame] using typed
  · simpa only [pair,sender,mintEventLog] using logs

/-- Successful raw1233 derives its full typed continuation, rather than assuming a successful model endpoint. -/
theorem mintAfterFee_frame_inv {K : WriterKey → Prop} {frame : Frame} {observed : MintObserved}
    {fee : FeeResult} {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) fee.state)
    (fresh : MintAfterFeeFresh K fee.state toWord)
    (cache : MintAfterFeeCache observed fee f amount1 amount0 b1 b0 r1 r0 toWord)
    (time : frame.context.timestamp = sevm.benvStat.time) (pair : frame.context.pair = sevm.currentTarget)
    (sender : frame.context.sender = sevm.caller)
    (oldBound0 : r0.toNat < 2 ^ 112) (oldBound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.Run cert.prog sevm
      (St b (f :: 0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R) M G)
      t_1233_c41 o) :
    MintAfterFeeFrameResult K frame observed fee sevm b R amount1 amount0 b1 b0 toWord o := by
  exact mintAfterFee_source_frame cache pair sender
    (mintAfterFee_source_inv fork mem rep fresh time pair oldBound0 oldBound1 run)



/-- The exact raw suffix produces its typed frame and return word from primitive ENV. -/
theorem mintAfterFee_frame_exact {K : WriterKey → Prop} {frame : Frame} {observed : MintObserved}
    {fee : FeeResult} {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) fee.state)
    (fresh : MintAfterFeeFresh K fee.state toWord)
    (cache : MintAfterFeeCache observed fee f amount1 amount0 b1 b0 r1 r0 toWord)
    (time : frame.context.timestamp = sevm.benvStat.time) (pair : frame.context.pair = sevm.currentTarget)
    (sender : frame.context.sender = sevm.caller)
    (oldBound0 : r0.toNat < 2 ^ 112) (oldBound1 : r1.toNat < 2 ^ 112)
    (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112) (room : R.length ≤ 997)
    (env : MintAfterFeeEnv sevm b f toWord amount0 amount1 b0 b1 r0 r1 G) :
    SFunc.RunExact cert.prog sevm
      (St b (f :: 0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: ρ :: R)
        M (env.armGas + sloadCost sevm b 0 + 28)) t_1233_c41 (.returned (env.post M R ρ)) ∧
    MintAfterFeeFrameResult K frame observed fee sevm b R amount1 amount0 b1 b0 toWord
      (.returned (env.post M R ρ)) := by
  obtain ⟨raw,source⟩ := mintAfterFee_source_exact (oldLiquidity := oldLiquidity) (ρ := ρ)
    fork mem rep fresh time pair oldBound0 oldBound1 bound0 bound1 room env
  exact ⟨raw,mintAfterFee_source_frame cache pair sender source⟩

end Blanc.Lift.UniswapV2Pair

