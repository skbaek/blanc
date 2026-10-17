import Blanc.Composition.UniswapV2PairWeth9LiveWorld
import Blanc.Composition.UniswapV2PairWeth9LegsBurn
import Blanc.Composition.UniswapV2PairWeth9LegsBurnFinal

/-!
# C4(b): Burn's worlds and words for the WETH9 = token0 legs (U8d)

The burn row's WETH9 transfer leg (`burnWethLeg0_spec`) is stated at the suffix's entry world
`burnBodyWorld`, after the initial queries, the factory `feeTo` query, the fee mint and the LP burn.
Its balance premise is `amount0 ≤` the Pair's WETH9 balance there; the final query
(`burnWethFinal0_spec`) needs the suffix memory's well-formedness and width after both transfers.
This module supplies them:

* `WethKeeps` across `lpMintPost`, the fee branch, `lpBurnPost` and the whole body
  (`burnBodyWorld_keeps`): the Pair writes only its own storage, and the factory query is a
  `STATICCALL`;
* `burnFee_amount0_le` — under the model's fee, pricing and LP-burn acceptance, the priced
  `amount0` word is at most the initial answer `b0` (`burnAmount_le_balance` at the raw words);
* `burnSuffix_layout` — the suffix memory after both transfers is well-formed and its pointer
  leaves room (the first half of `burnBack_exact`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

namespace WethKeeps

variable {w : Adr} {sevm : Sevm}

theorem lpMintPost (ne : sevm.currentTarget ≠ w) (b : Devm) (R : List B256) (M : Mem)
    (toWord value : B256) (G : Nat) :
    WethKeeps w b (UniswapV2Pair.lpMintPost sevm b R M toWord value G) := by
  unfold UniswapV2Pair.lpMintPost lpMintSupplyPost lpMintCreditPost lpMintCreditBase
    lpMintSupplyBase
  exact (((((WethKeeps.afterSload sevm b 0).trans (WethKeeps.afterSstore ne _ 0 _)).trans
    (WethKeeps.afterSload sevm _ _)).trans (WethKeeps.afterSstore ne _ _ _)).trans
    (WethKeeps.addLog _ _)).trans (WethKeeps.ofSt _ _ _ _)

theorem feeBranchPost (ne : sevm.currentTarget ≠ w) (b : Devm) (R : List B256) (M : Mem)
    (K x r0 r1 : B256) (G : Nat) :
    WethKeeps w b (UniswapV2Pair.feeBranchPost sevm b R M K x r0 r1 G) := by
  unfold UniswapV2Pair.feeBranchPost
  split
  · refine WethKeeps.trans ?_ (WethKeeps.ofSt _ _ _ _)
    unfold feeOffWorld
    split
    · exact refl b
    · exact WethKeeps.afterSstore ne b 11 0
  · unfold feeOnPost
    split
    · exact WethKeeps.ofSt b _ _ _
    · split
      · unfold feeGrowthPost feeLiquidityPost
        refine (WethKeeps.afterSload sevm b 0).trans ?_
        split
        · exact WethKeeps.ofSt _ _ _ _
        · exact lpMintPost ne _ _ _ _ _ _
      · exact WethKeeps.ofSt b _ _ _

theorem lpBurnPost (ne : sevm.currentTarget ≠ w) (b : Devm) (R : List B256) (M : Mem)
    (fromWord value : B256) (G : Nat) :
    WethKeeps w b (UniswapV2Pair.lpBurnPost sevm b R M fromWord value G) := by
  unfold UniswapV2Pair.lpBurnPost lpBurnBalancePost lpBurnSupplyPost lpBurnSupplyBase
    lpBurnBalanceBase
  exact (((((WethKeeps.afterSload sevm b _).trans (WethKeeps.afterSstore ne _ _ _)).trans
    (WethKeeps.afterSload sevm _ 0)).trans (WethKeeps.afterSstore ne _ 0 _)).trans
    (WethKeeps.addLog _ _)).trans (WethKeeps.ofSt _ _ _ _)

end WethKeeps

/-- **Burn's body keeps WETH9's account**: from the second initial query's result `d1` to the
suffix's entry world, through the factory `STATICCALL`, the fee branch and the LP burn. -/
theorem burnBodyWorld_keeps {w : Adr} {sevm : Sevm} {b d0 d1 dF : Devm} {S : List B256} {M : Mem}
    {G : Nat} {g t ii is oi os : B256} (fork : CoveredFork sevm.benvStat.fork)
    (ne : sevm.currentTarget ≠ w)
    (call : Ninst.RunCompiled sevm (St (feeFactoryCallWorld sevm (feeBurnWorld sevm d1))
      (g :: t :: ii :: is :: oi :: os :: S) M G) (.exec .staticcall) dF)
    (nonempty : (d1.getCode w).toList ≠ []) :
    WethKeeps w d1 (burnBodyWorld sevm b d0 d1 dF) := by
  have staged : WethKeeps w d1 (feeFactoryCallWorld sevm (feeBurnWorld sevm d1)) :=
    ((WethKeeps.afterSload sevm d1 _).trans (WethKeeps.afterSload sevm _ 5)).trans
      (WethKeeps.access _ _)
  have toF := staged.trans (WethKeeps.staticcall fork call (by rw [staged.1]; exact nonempty))
  rw [burnBodyWorld_def]
  unfold burnPricedWorld burnFeeWorld
  exact (((toF.trans (WethKeeps.afterSload sevm dF 11)).trans
    (WethKeeps.feeBranchPost ne _ _ _ _ _ _ _ _)).trans (WethKeeps.afterSload sevm _ 0)).trans
    (WethKeeps.lpBurnPost ne _ _ _ _ _ _)

/-- Burn's prefix up to the first initial query keeps WETH9's account. -/
theorem burnRead0World_keeps {w : Adr} (sevm : Sevm) (b : Devm) (ne : sevm.currentTarget ≠ w) :
    WethKeeps w b (burnRead0World sevm b) := by
  unfold burnRead0World burnTokensWorld burnReservedWorld burnLockedWorld
  exact ((((WethKeeps.afterSload sevm b 12).trans (WethKeeps.afterSstore ne _ 12 0)).trans
    (WethKeeps.afterSload sevm _ 8)).trans (WethKeeps.afterSload sevm _ 6)).trans
    (WethKeeps.afterSload sevm _ 7)

/-- **The priced `amount0` word is at most the initial answer.**  Under the locked state's
representation at `d1`, the fee mint the model accepts at the factory's actual answer, and the burn
pricing and LP burn it accepts, the bytecode's `amount0 = liquidity · b0 / supply` is at most `b0`
(the prefix of `burnFeePricing_exact`, then `burnAmount_le_balance`). -/
theorem burnFee_amount0_le {K : WriterKey → Prop} {st post : UniswapV2Pair.State} {fee : FeeResult}
    {events : List Event} {amount0 amount1 : Nat}
    {sevm : Sevm} {d1 dF : Devm} {M : Mem} {b0 t1 t0 r1 r0 toWord extρ : B256} {R : List B256}
    {Gp : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M) (room : R.length ≤ 990)
    (rep : WriterRep K (d1.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget)) (nonstatic : sevm.isStatic = false)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (c : BurnFeeCallee sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp)
    (accepted : mintFee st (Bytes.toB256 (dF.returnData.take 32)).toAdr r0.toNat r1.toNat = .ok fee)
    (fresh : FeeMintFresh K st sevm (feeKLastWorld sevm dF) (Bytes.toB256 (dF.returnData.take 32))
      r0 r1)
    (priced : burnAmounts (st.balanceOf sevm.currentTarget) b0 (feeBurnBalance1 M)
      fee.state.totalSupply = .ok (amount0, amount1))
    (burned : fee.state.burnLP sevm.currentTarget (st.balanceOf sevm.currentTarget) =
      .ok (post, events)) :
    (burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).amount0 ≤ b0 := by
  let FL := burnFeeLocalsAt sevm d1 M b0 t1 t0 r1 r0 toWord extρ R
  let GF := burnFeeResidual sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp
  have rep' : WriterRep K ((feeBurnWorld sevm d1).getStor sevm.currentTarget) st := by
    simpa only [feeBurnWorld, afterSload_getStor] using rep
  have postCall := feeFactoryCompiled_post fork c.call c.success
  have postRep := rep'.fee_factory_post postCall
  have last : feeKLastWord sevm dF = st.kLast := by
    rcases postRep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, lastWord, _⟩
    change (dF.getStor sevm.currentTarget).get 11 = st.kLast
    simpa only [feeKLastWorld, afterSload_getStor] using lastWord
  have sentries := c.sentries
  have returnedGas := c.returnedGas
  rw [last] at sentries returnedGas
  have input : FeeMintForwardInput K st sevm (feeBurnWorld sevm d1) dF FL
      (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2 GF c.factoryGas fee :=
    ⟨fork, feeBurnMemory_ptr mem sevm.currentTarget, rep', bound0, bound1,
      by simp only [FL, burnFeeLocalsAt, burnFeeLocals, List.length_cons]; omega,
      c.code, c.call, c.success, c.width, accepted, fresh,
      ⟨⟨fun _ _ => nonstatic, fun _ _ _ _ => nonstatic⟩, sentries.clearSentry,
        sentries.supplySentry, sentries.creditSentry⟩,
      by rw [returnedGas]; rfl⟩
  obtain ⟨_, source, feeEq⟩ := input.exact
  have cached := input.rep.selected (.balance sevm.currentTarget) tracked
  simp only [feeBurnWorld, afterSload_getStor] at cached
  change feeBurnLiquidity sevm d1 = st.balanceOf sevm.currentTarget at cached
  let bF0 := burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R
  have repF : WriterRep (feeBranchSourceKeys K st sevm (feeKLastWorld sevm dF)
      (Bytes.toB256 (dF.returnData.take 32)) r0 r1) (bF0.getStor sevm.currentTarget) fee.state := by
    have h := source.2.1
    rw [feeEq, ← last, feeBranchPost_St, St_getStor] at h
    exact h
  have supplyEq : bF0.getStorVal sevm.currentTarget 0 = fee.state.totalSupply := repF.fixed.1
  have priced' : burnAmounts (feeBurnLiquidity sevm d1) b0 (feeBurnBalance1 M)
      (bF0.getStorVal sevm.currentTarget 0) = .ok (amount0, amount1) := by
    rw [cached, supplyEq]
    exact priced
  have lp : feeBurnLiquidity sevm d1 ≤ bF0.getStorVal sevm.currentTarget 0 := by
    rw [cached, supplyEq, B256.le_iff_toNat_le_toNat]
    exact (State.burnLP_supply burned).1
  exact (burnAmount_le_balance priced' lp).2.2.1

/-- **The suffix memory after both transfers** is well-formed and its pointer leaves room for a
`balanceOf` request (the layout half of `burnBack_exact`). -/
theorem burnSuffix_layout {sevm : Sevm} {b d0 d1 : Devm} {M : Mem} {n0 : Nat} {p0 : B256}
    {w : BurnSuffixWords} {R : List B256} {callGas0 callGas1 G0 G1 : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p0 n0 M) (sentinel : memWord M 96 = 0)
    (lower : 128 ≤ p0.toNat) (upper : p0.toNat < 2 ^ 161)
    (nonzero0 : w.amount0 ≠ 0) (nonzero1 : w.amount1 ≠ 0) (room : R.length ≤ 980)
    (transfer0 : SwapTransferCallForward sevm b (w.locals w.balance1 w.balance0 R) M M.size p0
      w.amount0 w.recipient w.token0 0x1698 callGas0 G0 d0)
    (transfer1 : SwapTransferCallForward sevm d0 (w.locals w.balance1 w.balance0 R)
      (burnSuffixMem1 M p0 w d0) (burnSuffixMem1 M p0 w d0).size (swapMovedPointer p0 d0.returnData)
      w.amount1 w.recipient w.token1 0x16a3 callGas1 G1 d1) :
    Mem.Wf (burnSuffixMem2 M p0 w d0 d1) ∧ (burnSuffixPtr p0 d0 d1).toNat + 260 < 2 ^ 256 := by
  have roomL : (w.locals w.balance1 w.balance0 R).length ≤ 1000 := by
    simp only [BurnSuffixWords.locals, burnPricedLocals, List.length_cons]
    omega
  obtain ⟨⟨n1, mem1⟩, sentinel1, lower1, upper1, _⟩ :=
    swapFwdOpt_layout (k := 161) (a := w.amount0) (d := d0) fork roomL mem sentinel
      lower upper (by decide) (fun _ => transfer0)
  simp only [swapOptPtr, swapOptMem, nonzero0, ↓reduceIte] at mem1 sentinel1 lower1 upper1
  have mem1' : PtrMem (swapMovedPointer p0 d0.returnData) (burnSuffixMem1 M p0 w d0).size
      (burnSuffixMem1 M p0 w d0) := by
    unfold burnSuffixMem1
    rw [mem1.size]
    exact mem1
  obtain ⟨⟨n2, mem2⟩, _, _, upper2, _⟩ :=
    swapFwdOpt_layout (k := 162) (a := w.amount1) (d := d1) fork roomL mem1' sentinel1
      lower1 (by have : 2 ^ 161 + 2 ^ 161 = 2 ^ 162 := by decide
                 omega) (by decide) (fun _ => transfer1)
  simp only [swapOptPtr, swapOptMem, nonzero1, ↓reduceIte] at mem2 upper2
  refine ⟨?_, ?_⟩
  · unfold burnSuffixMem2
    exact mem2.wf
  · have : 2 ^ 162 + 2 ^ 161 + 260 < 2 ^ 256 := by decide
    unfold burnSuffixPtr
    omega

end Blanc.Composition.UniswapV2PairWeth9Joint
