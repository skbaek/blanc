import Blanc.Lift.UniswapV2Pair.BurnFrameWalk

/-! Actual fee and LP-burn observations produce Burn's first transfer frame. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Pricing retains pre-fee liquidity and uses the actual post-fee supply. -/
def burnPricedSource (observed : BurnObserved) (fee : FeeResult)
    (amount0 amount1 : B256) : BurnPriced :=
  { observed := observed, feeOn := fee.feeOn, feeMinted := fee.minted,
    supply := fee.state.totalSupply, amount0 := amount0, amount1 := amount1 }

/-- Fee events precede the LP debit at the same resumed source origin. -/
def burnPricedFrame (frame : Frame) (observed : BurnObserved) (fee : FeeResult) : Frame :=
  (frame.withEvents fee.state fee.events).withEvents
    (lpBurnSourceState fee.state frame.context.pair observed.liquidity)
    [.transfer frame.context.pair 0 observed.liquidity]

/-- Source acceptance derived from the checked bytecode floors and LP debit. -/
theorem burnAfterFee_source_accept {frame : Frame} {observed : BurnObserved} {fee : FeeResult}
    {amount0 amount1 : B256}
    (amounts : burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply = .ok (amount0.toNat, amount1.toNat))
    (positive0 : 0 < amount0.toNat) (positive1 : 0 < amount1.toNat)
    (burned : fee.state.burnLP frame.context.pair observed.liquidity =
      .ok (lpBurnSourceState fee.state frame.context.pair observed.liquidity,
        [.transfer frame.context.pair 0 observed.liquidity])) :
    frame.burnAfterFee observed fee =
      .suspended (burnPricedFrame frame observed fee)
        (requestFor .burnTransfer0 observed.locals.token0
          (.transfer observed.locals.recipient amount0))
        (.burnTransfer0 (burnPricedSource observed fee amount0 amount1)) := by
  simp only [Frame.burnAfterFee, amounts, ite_eq_left (show amount0.toNat > 0 ∧ amount1.toNat > 0 from ⟨positive0, positive1⟩), burned,
    toB256_toNat]
  rfl

/-- The actual fee branch's Boolean matches its retained bytecode word. -/
theorem feeBranchSourceFee_flag (st : State) (sevm : Sevm) (b : Devm) (w r0 r1 : B256) :
    (feeBranchSourceFee st sevm b w r0 r1).feeOn = decide (feeOnWord w ≠ 0) := by
  by_cases zero : w.toAdr = 0
  · have word : w.toAdr.toB256 = 0 := congrArg Adr.toB256 zero
    have flag : feeOnWord w = 0 := by
      simp only [feeOnWord, B256.eqCheck, ite_eq_left word,
        ite_eq_right (by decide : (1 : B256) ≠ 0)]
    rw [feeBranchSourceFee, ite_eq_left zero, flag]
    rfl
  · have word : w.toAdr.toB256 ≠ 0 := fun h => zero (Adr.toB256_inj h)
    have flag : feeOnWord w = 1 := by
      simp only [feeOnWord, B256.eqCheck, ite_eq_right word, ite_true]
    have on : (feeBranchSourceFee st sevm b w r0 r1).feeOn = true := by
      unfold feeBranchSourceFee
      rw [ite_eq_right zero]
      split
      · rfl
      · split
        · unfold feeGrowthSourceFee
          split <;> rfl
        · rfl
    rw [on, flag]
    rfl

/-- Exact source and physical first-transfer cut produced by one retained fee
return and its real pricing/LP-burn continuation. All cached words are explicit. -/
def BurnFeePricingResult (K : WriterKey → Prop) (st : State) (D : Exec.Deriv)
    (sevm : Sevm) (b feePost : Devm) (R : List B256) (M : Mem) (C : List Nat) (seg : Seg)
    (L b1 b0 token1 token0 r1 r0 toWord extρ : B256)
    (observation : FeeMintSourceObservation K st D sevm b
      (burnFeeLocals L b1 b0 token1 token0 r1 r0 toWord extρ R)
      M r1 r0 0x15e2 (.returned feePost))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) (prior : Frame) : Prop :=
    let observed := feeBurnObserved toWord token1 token0 L b1 b0 r1 r0 bound0 bound1
    let fee := feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1
    let keys := feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1
    let f := feeOnWord (Bytes.toB256 (observation.out.take 32))
    let supply := feePost.getStorVal sevm.currentTarget 0
    let a0 := (L * b0) / supply
    let a1 := (L * b1) / supply
    let locals := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 a1 a0 toWord extρ R
    let resumed := prior.beginResume (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
    let frame := burnPricedFrame resumed observed fee
    let priced := burnPricedSource observed fee a0 a1
    burnAmounts L b0 b1 supply = .ok (a0.toNat, a1.toNat) ∧
    0 < a0.toNat ∧ 0 < a1.toNat ∧ supply = fee.state.totalSupply ∧
    priced.feeOn = decide (f ≠ 0) ∧
    ∃ burnGas residual,
      let post := lpBurnPost sevm (afterSload sevm feePost 0) locals
        feePost.memory sevm.currentTarget.toB256 L residual
      SFunc.RunP (StepIn D) cert.prog sevm
        (St (afterSload sevm feePost 0) (L :: sevm.currentTarget.toB256 :: 0x168d :: locals)
          feePost.memory burnGas) t_2992_c63 (.returned post) ∧
      LPBurnSourceResult keys fee.state sevm (afterSload sevm feePost 0) locals
        feePost.memory sevm.currentTarget.toB256 L residual ∧
      PtrMem 128 192 post.memory ∧ memWord post.memory 96 = 0 ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St post locals post.memory residual) t_168d_c13 seg ∧
      resumeSegment prior (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
        (.burnFee observed) (feeObservedResult observation.out) =
          .suspended frame (requestFor .burnTransfer0 observed.locals.token0
            (.transfer observed.locals.recipient a0)) (.burnTransfer0 priced) ∧
      WriterRep (WriterExtend keys (lpMintTouched sevm.currentTarget))
        (post.getStor sevm.currentTarget) frame.current.state ∧
      frame.checkpoint = prior.checkpoint ∧ frame.context = prior.context

/-- The same actual fee return and pricing continuation derive the represented
first-transfer frame. LP liquidity remains the pre-fee cache, even if the fee
recipient is the Pair; neither source acceptance nor a source endpoint is a
premise. The transfer continuation and its physical LP event remain available. -/
theorem burnFee_pricing_source_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b feePost : Devm} {R : List B256} {M : Mem} {C : List Nat} {seg : Seg}
    {L b1 b0 token1 token0 r1 r0 toWord extρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (notCut13 : 13 ∉ C)
    (mem : PtrMem 128 192 M) (sentinel : memWord M 96 = 0)
    (observation : FeeMintSourceObservation K st D sevm b
      (burnFeeLocals L b1 b0 token1 token0 r1 r0 toWord extρ R) M r1 r0 0x15e2 (.returned feePost))
    (tracked : K (.balance sevm.currentTarget))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (prior : Frame) (state : prior.current.state = st)
    (pair : prior.context.pair = sevm.currentTarget)
    (suffix : SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_15e2_c37 seg) :
    BurnFeePricingResult K st D sevm b feePost R M C seg L b1 b0 token1 token0
      r1 r0 toWord extρ observation bound0 bound1 prior := by
  unfold BurnFeePricingResult
  obtain ⟨rep, ptr, raw, same⟩ := burnFee_pricing_input_inv mem observation suffix
  have trackedAfter : (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1) (.balance sevm.currentTarget) := by
    unfold feeBranchSourceKeys
    split
    · exact tracked
    · split
      · exact tracked
      · split
        · split
          · exact tracked
          · exact Or.inl tracked
        · exact tracked
  have fresh : WriterFreshKeys
      (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1) (lpMintTouched sevm.currentTarget) := by
    apply Blanc.SlotFootprint.FreshKeys.of_universe rep.inj rep.apart (fun _ h => h)
    intro k member
    have eq := List.mem_singleton.mp (show k ∈ [WriterKey.balance sevm.currentTarget] from member)
    subst k
    exact trackedAfter
  obtain ⟨product0, product1, nonzero, supplyEq, amounts, positive0, positive1, mutable,
      burnGas, residual, callee, source, transferTail⟩ :=
    burnPricing_inv (fun h => StepIn.toRun h) fork notCut13 ptr rep fresh raw
  let observed := feeBurnObserved toWord token1 token0 L b1 b0 r1 r0 bound0 bound1
  let fee := feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
    (Bytes.toB256 (observation.out.take 32)) r0 r1
  let supply := feePost.getStorVal sevm.currentTarget 0
  let locals := burnPricedLocals supply (feeOnWord (Bytes.toB256 (observation.out.take 32)))
    L b1 b0 token1 token0 r1 r0 ((L * b1) / supply) ((L * b0) / supply) toWord extρ R
  let post := lpBurnPost sevm (afterSload sevm feePost 0) locals
    feePost.memory sevm.currentTarget.toB256 L residual
  let resumed := prior.beginResume (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
  have sourceAmounts : burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply = .ok (((L * b0) / supply).toNat, ((L * b1) / supply).toNat) := by
    rw [← supplyEq]
    exact amounts
  have burned : fee.state.burnLP resumed.context.pair observed.liquidity =
      .ok (lpBurnSourceState fee.state resumed.context.pair observed.liquidity,
        [.transfer resumed.context.pair 0 observed.liquidity]) := by
    simpa only [resumed, Frame.beginResume, pair, observed, feeBurnObserved, toAdr_toB256]
      using source.1
  have typed := observation.resume_burn prior observed state rfl rfl
  have typedPricing := burnAfterFee_source_accept sourceAmounts positive0 positive1 burned
  have postMem : PtrMem 128 192 post.memory := by
    have image := lpMintMemory_ptr (lpMintScratch_ptr ptr sevm.currentTarget.toB256)
      sevm.currentTarget.toB256 L
    simpa only [post, lpBurnPost, lpBurnBalancePost, lpBurnSupplyPost, St.memory, lpMintMemory]
      using image
  have postSentinel : memWord post.memory 96 = 0 :=
    (burnLP_sentinel ptr.wf).trans (same.trans sentinel)
  have self := St.self (d := post) (S := locals) (M := post.memory) rfl rfl
  have transfer : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St post locals post.memory residual) t_168d_c13 seg :=
    (congrArg (fun start : Devm =>
      SFunc.RunCutP (StepIn D) cert.prog sevm C start t_168d_c13 seg) self).mp transferTail
  have postRep : WriterRep (WriterExtend
      (feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
        (Bytes.toB256 (observation.out.take 32)) r0 r1) (lpMintTouched sevm.currentTarget))
      (post.getStor sevm.currentTarget) (burnPricedFrame resumed observed fee).current.state := by
    simpa only [post, burnPricedFrame, Frame.withEvents, resumed, Frame.beginResume,
      pair, observed, feeBurnObserved, toAdr_toB256] using source.2.1
  exact ⟨amounts, positive0, positive1, supplyEq,
    feeBranchSourceFee_flag st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1,
    burnGas, residual, callee, source, postMem, postSentinel, transfer,
    typed.2.trans typedPricing, postRep, rfl, rfl⟩

/-- The literal initial-balance decoder reads LP liquidity before entering the
factory call. Its same-D fee/pricing observation then produces the exact first
transfer source frame, preserving that cache through feeTo=Pair and every fee
branch. This is the actual caller producer for BurnFeePricingResult. -/
theorem burnFeeCaller_pricing_source_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {seg : Seg}
    {len discarded b0 token1 token0 r1 r0 toWord extρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (notCut13 : 13 ∉ C)
    (mem : PtrMem 128 192 M) (sentinel : memWord M 96 = 0)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (fresh : FeeMintSourceFresh K st D sevm (feeBurnWorld sevm b)
      (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0
        r1 r0 toWord extρ R) (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2)
    (prior : Frame) (state : prior.current.state = st)
    (pair : prior.context.pair = sevm.currentTarget)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (len :: 128 :: discarded :: b0 :: token1 :: token0 :: r1 :: r0 ::
        0 :: 0 :: toWord :: extρ :: R) M G) t_15c3_c37 seg) :
    feeBurnLiquidity sevm b = st.balanceOf prior.context.pair ∧
    ∃ feeGas feePost, ∃ observation : FeeMintSourceObservation K st D sevm (feeBurnWorld sevm b)
      (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0
        r1 r0 toWord extρ R) (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2 (.returned feePost),
      SFunc.RunP (StepIn D) cert.prog sevm
        (St (feeBurnWorld sevm b)
          (r1 :: r0 :: 0x15e2 :: burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M)
            b0 token1 token0 r1 r0 toWord extρ R) (feeBurnMemory M sevm.currentTarget) feeGas)
        t_26ec_c68 (.returned feePost) ∧
      StaticAnswered sevm (feeFactoryCallWorld sevm (feeBurnWorld sevm b)) st.factory
        (requestFor .burnFeeTo st.factory .feeTo).calldata observation.out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_15e2_c37 seg ∧
      BurnFeePricingResult K st D sevm (feeBurnWorld sevm b) feePost R
        (feeBurnMemory M sevm.currentTarget) C seg (feeBurnLiquidity sevm b) (feeBurnBalance1 M)
        b0 token1 token0 r1 r0 toWord extρ observation bound0 bound1 prior := by
  obtain ⟨cached, feeGas, feePost, observation, callee, suffix, answered, _⟩ :=
    feeBurn_typed_caller_inv fork mem rep tracked bound0 bound1 fresh prior state pair run
  have scratch := feeBurnMemory_ptr mem sevm.currentTarget
  have same : memWord (feeBurnMemory M sevm.currentTarget) 96 = 0 :=
    (burnFeeScratch_sentinel mem.wf sevm.currentTarget).trans sentinel
  exact ⟨cached, feeGas, feePost, observation, callee, answered, suffix,
    burnFee_pricing_source_inv fork notCut13 scratch same observation tracked
      bound0 bound1 prior state pair suffix⟩

end Blanc.Lift.UniswapV2Pair
