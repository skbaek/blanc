import Blanc.Lift.UniswapV2Pair.BurnPricingTurns
import Blanc.Lift.UniswapV2Pair.BurnTransferTurns

/-! The actual fee/pricing producer feeds the Burn transfer/source consumer. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

private theorem burnFee_lock_preserved (st : State) (sevm : Sevm) (b : Devm)
    (w r0 r1 : B256) :
    (feeBranchSourceFee st sevm b w r0 r1).state.unlocked = st.unlocked := by
  unfold feeBranchSourceFee
  split
  · rfl
  · split
    · rfl
    · split
      · unfold feeGrowthSourceFee
        split <;> rfl
      · rfl

private theorem burnFee_lpMint_code (sevm : Sevm) (b : Devm) (R : List B256)
    (M : Mem) (w value : B256) (G : Nat) (a : Adr) :
    (lpMintPost sevm b R M w value G).getCode a = b.getCode a := by
  unfold lpMintPost lpMintSupplyPost lpMintCreditPost lpMintCreditBase
  rw [St, Devm.getCode_setMach]
  generalize stored : afterSstore sevm
    (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm b 0)
      (lpMintSupplyWord sevm b + value)) (transferBalanceSlot w.toAdr))
    (transferBalanceSlot w.toAdr)
    (lpMintRecipientWord sevm (afterSload sevm b 0) w
      (lpMintSupplyWord sevm b + value) + value) = c
  change c.getCode a = b.getCode a
  rw [← stored, afterSstore_getCode, afterSload_getCode]
  unfold lpMintSupplyBase
  rw [afterSstore_getCode, afterSload_getCode]

private theorem burnFee_post_code (sevm : Sevm) (b : Devm) (R : List B256)
    (M : Mem) (K w r0 r1 : B256) (G : Nat) (a : Adr) :
    (feeBranchPost sevm b R M K w r0 r1 G).getCode a = b.getCode a := by
  unfold feeBranchPost
  split
  · change (feeOffWorld sevm b K).getCode a = b.getCode a
    unfold feeOffWorld
    split
    · rfl
    · rw [afterSstore_getCode]
  · unfold feeOnPost
    split
    · rfl
    · split
      · unfold feeGrowthPost feeLiquidityPost
        split
        · change (afterSload sevm b 0).getCode a = b.getCode a
          rw [afterSload_getCode]
        · rw [burnFee_lpMint_code, afterSload_getCode]
      · rfl

private theorem burnFee_lpBurn_code (sevm : Sevm) (b : Devm) (R : List B256)
    (M : Mem) (w value : B256) (G : Nat) (a : Adr) :
    (lpBurnPost sevm b R M w value G).getCode a = b.getCode a := by
  unfold lpBurnPost lpBurnBalancePost lpBurnSupplyPost lpBurnSupplyBase
  rw [St, Devm.getCode_setMach]
  generalize stored : afterSstore sevm
    (afterSload sevm (lpBurnBalanceBase sevm
      (afterSload sevm b (transferBalanceSlot w.toAdr)) w
      (lpBurnBalanceWord sevm b w - value)) 0)
    0 (lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot w.toAdr)) w
      (lpBurnBalanceWord sevm b w - value) - value) = c
  change c.getCode a = b.getCode a
  rw [← stored, afterSstore_getCode, afterSload_getCode]
  unfold lpBurnBalanceBase
  rw [afterSstore_getCode, afterSload_getCode]

/-- The actual successful fee reply, pricing and LP debit feed both mutable
transfer queues and the final source return. The initial locked source frame
and its cached entry correspondence remain supplied by the entry producer;
there is no premise for the post-pricing cut or source acceptance. -/
theorem burnFee_pricing_source_finished {U K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {sevm : Sevm} {b feePost : Devm} {R : List B256} {M : Mem}
    {L b1 b0 token1 token0 r1 r0 toWord extρ : B256} {o : Outcome}
    (observation : FeeMintSourceObservation K st D sevm b
      (burnFeeLocals L b1 b0 token1 token0 r1 r0 toWord extρ R)
      M r1 r0 0x15e2 (.returned feePost))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) (prior : Frame)
    (initialMem : PtrMem 128 192 M) (initialSentinel : memWord M 96 = 0)
    (tracked : K (.balance sevm.currentTarget))
    (suffix : SFunc.RunCutP (StepIn D) cert.prog sevm [] feePost t_15e2_c37 (.done o))
    (state : prior.current.state = st) (locked : st.unlocked = 0)
    (nonstatic : prior.context.isStatic = false)
    (time : prior.context.timestamp = sevm.benvStat.time)
    (pair : prior.context.pair = sevm.currentTarget)
    (sender : prior.context.sender = sevm.caller)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (feeTracked : U (.balance (Bytes.toB256 (observation.out.take 32)).toAdr))
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = prior.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    let observed := feeBurnObserved toWord token1 token0 L b1 b0 r1 r0 bound0 bound1
    let fee := feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1
    let keys := feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1
    let supply := feePost.getStorVal sevm.currentTarget 0
    let a0 := (L * b0) / supply
    let a1 := (L * b1) / supply
    let w : BurnFinalWords := ⟨supply, feeOnWord (Bytes.toB256 (observation.out.take 32)),
      L, b1, b0, token1, token0, r1, r0, a1, a0, toWord⟩
    let frame := burnPricedFrame
      (prior.beginResume (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)) observed fee
    let priced := burnPricedSource observed fee a0 a1
    ∃ residual,
      let post := lpBurnPost sevm (afterSload sevm feePost 0) (burnFinalStack w extρ R)
        feePost.memory sevm.currentTarget.toB256 L residual
      BurnTransferCut (WriterExtend keys (lpMintTouched sevm.currentTarget))
        frame priced sevm post w post.memory ∧
      BurnTransferFinished U frame priced D sevm post w post.memory extρ R o ∧
      resumeSegment prior (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
        (.burnFee observed) (feeObservedResult observation.out) =
          .suspended frame (burnTransferRequest0 priced) (.burnTransfer0 priced) := by
  dsimp only
  have pricing := burnFee_pricing_source_inv fork
    (by simp only [List.not_mem_nil, not_false_eq_true]) initialMem initialSentinel
    observation tracked bound0 bound1 prior state pair suffix
  obtain ⟨amounts, positive0, positive1, supplyEq, feeFlag,
      burnGas, residual, callee, lpSource, mem, sentinel, transfer, typed, rep,
      checkpoint, context⟩ := pricing
  let observed := feeBurnObserved toWord token1 token0 L b1 b0 r1 r0 bound0 bound1
  let fee := feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
    (Bytes.toB256 (observation.out.take 32)) r0 r1
  let keys := feeBranchSourceKeys K st sevm (feeKLastWorld sevm observation.d)
    (Bytes.toB256 (observation.out.take 32)) r0 r1
  let supply := feePost.getStorVal sevm.currentTarget 0
  let a0 := (L * b0) / supply
  let a1 := (L * b1) / supply
  let w : BurnFinalWords := ⟨supply, feeOnWord (Bytes.toB256 (observation.out.take 32)),
    L, b1, b0, token1, token0, r1, r0, a1, a0, toWord⟩
  let frame := burnPricedFrame
    (prior.beginResume (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)) observed fee
  let priced := burnPricedSource observed fee a0 a1
  let post := lpBurnPost sevm (afterSload sevm feePost 0) (burnFinalStack w extρ R)
    feePost.memory sevm.currentTarget.toB256 L residual
  have cut : BurnTransferCut (WriterExtend keys (lpMintTouched sevm.currentTarget))
      frame priced sevm post w post.memory :=
    { rep := rep, time := time, pair := pair, sender := sender,
      token0 := by
        change (token0 &&& ~~~ addressMask).toAdr = token0.toAdr
        rw [and_mask_word, toAdr_toB256],
      token1 := by
        change (token1 &&& ~~~ addressMask).toAdr = token1.toAdr
        rw [and_mask_word, toAdr_toB256],
      recipient := rfl, reserve0 := rfl, reserve1 := rfl,
      fee := feeFlag, amount0 := rfl, amount1 := rfl,
      mem := mem, lower := by decide, width := by decide,
      locked := by
        change fee.state.unlocked = 0
        exact (burnFee_lock_preserved st sevm _ _ r0 r1).trans locked,
      nonstatic := nonstatic, sentinel := sentinel }
  have keysSub : ∀ k, keys k → U k := by
    unfold keys feeBranchSourceKeys
    split
    · exact sub
    · split
      · exact sub
      · split
        · split
          · exact sub
          · intro k member
            rcases member with old | added
            · exact sub k old
            · have same := List.mem_singleton.mp added
              subst k
              exact feeTracked
        · exact sub
  have postSub : ∀ k, WriterExtend keys (lpMintTouched sevm.currentTarget) k → U k := by
    intro k member
    rcases member with old | added
    · exact keysSub k old
    · have same := List.mem_singleton.mp added
      subst k
      exact sub _ tracked
  have nonempty : (b.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have beforeCode : (feeFactoryCallWorld sevm b).getCode sevm.currentTarget =
      b.getCode sevm.currentTarget := by
    change (feeFactoryCallWorld sevm b).state.getCode _ = b.state.getCode _
    unfold feeFactoryCallWorld
    rw [temporalAccountAccessBase_state]
    change (feeFactoryLoadWorld sevm b).getCode _ = b.getCode _
    rw [feeFactoryLoadWorld, afterSload_getCode]
  have dCode := Blanc.Lift.StepIn.codePreserve observation.step sevm.currentTarget
    (by change ((feeFactoryCallWorld sevm b).getCode sevm.currentTarget).toList ≠ []
        rw [beforeCode]; exact nonempty)
  have feePostCode : feePost.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [Outcome.returned.inj observation.returned, burnFee_post_code]
    rw [feeKLastWorld, afterSload_getCode, dCode]
    change (feeFactoryCallWorld sevm b).getCode _ = b.getCode _
    exact beforeCode
  have postInstalled : some (post.getCode sevm.currentTarget).toList = sem.image := by
    change some ((lpBurnPost sevm (afterSload sevm feePost 0) _ _ _ _ _).getCode _).toList = _
    rw [burnFee_lpBurn_code, afterSload_getCode, feePostCode]
    exact installed
  exact ⟨residual, cut,
    burnTransfers_source_finished inj apart postSub sem image postInstalled fork cut good
      (fun F member target k touched => staticGood F member target k touched) transfer,
    typed⟩

end Blanc.Lift.UniswapV2Pair
