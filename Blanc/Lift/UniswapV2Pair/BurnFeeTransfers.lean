import Blanc.Lift.UniswapV2Pair.BurnPricingTurns
import Blanc.Lift.UniswapV2Pair.BurnTransferTurns

/-! The actual fee/pricing producer feeds the Burn transfer/source consumer. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Burn's own events and all legal locked child events share one raw image. -/
def burnOwnedRaw (pair : Adr) : Event → Option Log
  | .sync b0 b1 => some ⟨pair, [updateSyncTopic], encodeWords [b0.toB256, b1.toB256]⟩
  | .burn sender a0 a1 recipient => some ⟨pair,
      [burnEventTopic, sender.toB256, recipient.toB256], encodeWords [a0, a1]⟩
  | event => lockedOwnedRaw pair event

private theorem burn_pending_raw_preserves {pair : Adr} {pending : PendingLog} {raw : Log}
    (image : pending.rawWith (lockedOwnedRaw pair) = some raw) :
    pending.rawWith (burnOwnedRaw pair) = some raw := by
  cases pending with
  | foreign origin emitter topics data => exact image
  | owned origin event =>
    cases event <;> simp only [PendingLog.rawWith, lockedOwnedRaw] at image
    all_goals first | exact image | cases image

private theorem burn_pending_logs_preserves {pair : Adr} {added : List PendingLog}
    {raw : List Log}
    (image : added.map (PendingLog.rawWith (lockedOwnedRaw pair)) = raw.map some) :
    added.map (PendingLog.rawWith (burnOwnedRaw pair)) = raw.map some := by
  induction added generalizing raw with
  | nil =>
    cases raw <;> cases image
    rfl
  | cons pending rest ih =>
    cases raw with
    | nil => cases image
    | cons log tail =>
      obtain ⟨head, remaining⟩ := List.cons.inj image
      exact congrArg₂ List.cons (burn_pending_raw_preserves head) (ih remaining)

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

private theorem burnFee_factory_turns {U K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {r1 r0 ρ : B256} {o : Outcome}
    (observation : FeeMintSourceObservation K st D sevm b R M r1 r0 ρ o)
    (prior : Frame) (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (state : prior.current.state = st) (pair : prior.context.pair = sevm.currentTarget)
    (time : prior.context.timestamp = sevm.benvStat.time)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = prior.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    ∃ views : List StaticViewTurn,
      ExactTurns prior (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo) 0
        (staticViewTranscript views .done)
        { complete := true, frame := prior,
          childReturns := staticViewChildReturns prior
            (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo) 0 views } ∧
      PairViewProvenance D sevm prior (feeFactoryWord sevm b) views := by
  obtain ⟨views, turns, authentic, derived⟩ :=
    pair_static_call_turns (frame := prior)
      (request := requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
      inj apart sub sem image observation.step
      (by simpa only [List.append_nil, St.stack] using pref_append _ ([] : List B256))
      (by change some ((feeFactoryCallWorld sevm b).getCode prior.context.pair).toList = _
          rw [pair]
          unfold feeFactoryCallWorld temporalAccountAccessBase
          split <;> change some ((feeFactoryLoadWorld sevm b).getCode sevm.currentTarget).toList = _
          all_goals rw [feeFactoryLoadWorld, afterSload_getCode]; exact installed)
      (by change WriterRep K ((feeFactoryCallWorld sevm b).state.getStor prior.context.pair) _
          unfold feeFactoryCallWorld
          rw [temporalAccountAccessBase_state, pair]
          change WriterRep K ((feeFactoryLoadWorld sevm b).getStor sevm.currentTarget) _
          rw [feeFactoryLoadWorld, afterSload_getStor, state]
          exact rep)
      time fork ⟨1, _, observation.post.stack, by decide⟩ good
  exact ⟨views, turns, authentic, derived⟩

private theorem burnFee_finished_prepend {U : WriterKey → Prop}
    {frame : Frame} {priced : BurnPriced} {D : Exec.Deriv} {sevm : Sevm}
    {b : Devm} {w : BurnFinalWords} {M : Mem} {ρ : B256} {R : List B256} {o : Outcome}
    {start : SegmentResult} {wrap : Transcript → Transcript} {childPrefix : List ChildReturn}
    {oldStart : SegmentResult} {oldWrap : Transcript → Transcript} {oldPrefix : List ChildReturn}
    (finished : BurnTransferFinished U frame priced D sevm b w M ρ R o oldStart oldWrap oldPrefix)
    (reaches : ∀ tail out,
      ExactConsumes oldStart tail out → ExactConsumes start (wrap tail)
          { out with childReturns := childPrefix ++ out.childReturns }) :
    BurnTransferFinished U frame priced D sevm b w M ρ R o start
      (fun tail => wrap (oldWrap tail)) (childPrefix ++ oldPrefix) := by
  obtain ⟨K', d0, d1, entered0, entered1, turns0, turns1, final, rets, transcript,
      post, finalM, gas, n, balance0, balance1, added0, added1, L0, L1,
      sub, calls, prov0, prov1, consumed, returned, rep, checkpoint, context, unlocked,
      mem, covered, bound0, bound1, raw, images0, images1, logs⟩ := finished
  refine ⟨K', d0, d1, entered0, entered1, turns0, turns1, final, rets, transcript,
    post, finalM, gas, n, balance0, balance1, added0, added1, L0, L1,
    sub, calls, prov0, prov1, ?_, returned, rep, checkpoint, context, unlocked,
    mem, covered, bound0, bound1, raw, images0, images1, logs⟩
  simpa only [List.append_assoc] using reaches _ _ consumed

/-- The actual factory fee reply and its authenticated static turns prepend the
complete pricing, transfer and final-return consumer. The source starts at the
factory suspension; initial entry correspondence and finite raw-root admission
remain explicit producer premises. -/
theorem burnFee_source_finished {U K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {sevm : Sevm} {b feePost : Devm} {R : List B256} {M : Mem}
    {L b1 b0 token1 token0 r1 r0 toWord extρ : B256} {o : Outcome}
    (observation : FeeMintSourceObservation K st D sevm b
      (burnFeeLocals L b1 b0 token1 token0 r1 r0 toWord extρ R)
      M r1 r0 0x15e2 (.returned feePost))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) (prior : Frame)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
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
    ∃ residual, ∃ views : List StaticViewTurn,
      let post := lpBurnPost sevm (afterSload sevm feePost 0) (burnFinalStack w extρ R)
        feePost.memory sevm.currentTarget.toB256 L residual
      PairViewProvenance D sevm prior (feeFactoryWord sevm b) views ∧
      BurnTransferCut (WriterExtend keys (lpMintTouched sevm.currentTarget))
        frame priced sevm post w post.memory ∧
      BurnTransferFinished U frame priced D sevm post w post.memory extρ R o
        (.suspended prior (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
          (.burnFee observed))
        (fun tail => .next (feeObservedResult observation.out)
          (staticViewTranscript views .done) tail)
        (staticViewChildReturns prior
          (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo) 0 views) ∧
      resumeSegment prior (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
        (.burnFee observed) (feeObservedResult observation.out) =
          .suspended frame (burnTransferRequest0 priced) (.burnTransfer0 priced) := by
  dsimp only
  obtain ⟨residual, cut, finished, typed⟩ :=
    burnFee_pricing_source_finished observation bound0 bound1 prior initialMem initialSentinel
      tracked suffix state locked nonstatic time pair sender inj apart sub feeTracked
      sem image installed fork good staticGood
  obtain ⟨views, turns, provenance⟩ :=
    burnFee_factory_turns observation prior rep state pair time inj apart sub
      sem image installed fork staticGood
  let observed := feeBurnObserved toWord token1 token0 L b1 b0 r1 r0 bound0 bound1
  let fee := feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
    (Bytes.toB256 (observation.out.take 32)) r0 r1
  let frame := burnPricedFrame
    (prior.beginResume (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)) observed fee
  let priced := burnPricedSource observed fee (L * b0 / feePost.getStorVal sevm.currentTarget 0)
    (L * b1 / feePost.getStorVal sevm.currentTarget 0)
  have reaches : ∀ tail out,
      ExactConsumes (.suspended frame (burnTransferRequest0 priced) (.burnTransfer0 priced)) tail out →
      ExactConsumes (.suspended prior (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
        (.burnFee (feeBurnObserved toWord token1 token0 L b1 b0 r1 r0 bound0 bound1)))
        (.next (feeObservedResult observation.out) (staticViewTranscript views .done) tail)
        { out with childReturns := (staticViewChildReturns prior
          (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo) 0 views ++ out.childReturns) } := by
    intro tail out consumed
    refine ExactConsumes.nextCall (result := feeObservedResult observation.out)
      (by simp only [feeObservedResult, Bool.not_true, Bool.and_false])
      (by intro absent; cases absent) turns ?_
    change ExactConsumes (resumeSegment prior
      (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
      (.burnFee (feeBurnObserved toWord token1 token0 L b1 b0 r1 r0 bound0 bound1))
      (feeObservedResult observation.out)) tail out
    rw [typed]
    exact consumed
  exact ⟨residual, views, provenance, cut,
    by simpa only [id_eq, List.append_nil] using burnFee_finished_prepend finished reaches, typed⟩

/-- The literal balance decoder/LP SLOAD caller produces the factory suspension
and complete Burn source consumption in the original root derivation. Actual
fee-recipient freshness and membership come from that root's finite trace rows;
entry and initial-query correspondence remain for the pc-zero producer. -/
theorem burnFeeCaller_source_finished {U K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {len discarded b0 token1 token0 r1 r0 toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork D.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) (sentinel : memWord M 96 = 0)
    (rep : WriterRep K (b.getStor D.sevm.currentTarget) st)
    (tracked : K (.balance D.sevm.currentTarget))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (prior : Frame) (state : prior.current.state = st) (locked : st.unlocked = 0)
    (nonstatic : prior.context.isStatic = false)
    (time : prior.context.timestamp = D.sevm.benvStat.time)
    (pair : prior.context.pair = D.sevm.currentTarget)
    (sender : prior.context.sender = D.sevm.caller)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys D, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode D.sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = D.sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = prior.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k)
    (run : SFunc.RunCutP (StepIn D) cert.prog D.sevm []
      (St b (len :: 128 :: discarded :: b0 :: token1 :: token0 :: r1 :: r0 ::
        0 :: 0 :: toWord :: extρ :: R) M G) t_15c3_c37 (.done o)) :
    feeBurnLiquidity D.sevm b = st.balanceOf prior.context.pair ∧
    ∃ feeGas feePost, ∃ observation : FeeMintSourceObservation K st D D.sevm
      (feeBurnWorld D.sevm b)
      (burnFeeLocals (feeBurnLiquidity D.sevm b) (feeBurnBalance1 M) b0 token1 token0
        r1 r0 toWord extρ R) (feeBurnMemory M D.sevm.currentTarget) r1 r0 0x15e2
      (.returned feePost),
      SFunc.RunP (StepIn D) cert.prog D.sevm
        (St (feeBurnWorld D.sevm b)
          (r1 :: r0 :: 0x15e2 :: burnFeeLocals (feeBurnLiquidity D.sevm b)
            (feeBurnBalance1 M) b0 token1 token0 r1 r0 toWord extρ R)
          (feeBurnMemory M D.sevm.currentTarget) feeGas) t_26ec_c68 (.returned feePost) ∧
      StaticAnswered D.sevm (feeFactoryCallWorld D.sevm (feeBurnWorld D.sevm b)) st.factory
        (requestFor .burnFeeTo st.factory .feeTo).calldata observation.out ∧
      SFunc.RunCutP (StepIn D) cert.prog D.sevm [] feePost t_15e2_c37 (.done o) ∧
    let observed := feeBurnObserved toWord token1 token0 (feeBurnLiquidity D.sevm b)
      (feeBurnBalance1 M) b0 r1 r0 bound0 bound1
    let fee := feeBranchSourceFee st D.sevm (feeKLastWorld D.sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1
    let keys := feeBranchSourceKeys K st D.sevm (feeKLastWorld D.sevm observation.d)
      (Bytes.toB256 (observation.out.take 32)) r0 r1
    let supply := feePost.getStorVal D.sevm.currentTarget 0
    let a0 := (feeBurnLiquidity D.sevm b * b0) / supply
    let a1 := (feeBurnLiquidity D.sevm b * feeBurnBalance1 M) / supply
    let w : BurnFinalWords := ⟨supply, feeOnWord (Bytes.toB256 (observation.out.take 32)),
      feeBurnLiquidity D.sevm b, feeBurnBalance1 M, b0, token1, token0, r1, r0, a1, a0, toWord⟩
    let frame := burnPricedFrame
      (prior.beginResume
        (requestFor .burnFeeTo (feeFactoryWord D.sevm (feeBurnWorld D.sevm b)).toAdr .feeTo)) observed fee
    let priced := burnPricedSource observed fee a0 a1
    ∃ residual, ∃ views : List StaticViewTurn,
      let post := lpBurnPost D.sevm (afterSload D.sevm feePost 0) (burnFinalStack w extρ R)
        feePost.memory D.sevm.currentTarget.toB256 (feeBurnLiquidity D.sevm b) residual
      PairViewProvenance D D.sevm prior (feeFactoryWord D.sevm (feeBurnWorld D.sevm b)) views ∧
      BurnTransferCut (WriterExtend keys (lpMintTouched D.sevm.currentTarget))
        frame priced D.sevm post w post.memory ∧
      BurnTransferFinished U frame priced D D.sevm post w post.memory extρ R o
        (.suspended prior
          (requestFor .burnFeeTo (feeFactoryWord D.sevm (feeBurnWorld D.sevm b)).toAdr .feeTo)
          (.burnFee observed))
        (fun tail => .next (feeObservedResult observation.out)
          (staticViewTranscript views .done) tail)
        (staticViewChildReturns prior
          (requestFor .burnFeeTo (feeFactoryWord D.sevm (feeBurnWorld D.sevm b)).toAdr .feeTo) 0 views) ∧
      resumeSegment prior (requestFor .burnFeeTo (feeFactoryWord D.sevm (feeBurnWorld D.sevm b)).toAdr .feeTo)
        (.burnFee observed) (feeObservedResult observation.out) =
          .suspended frame (burnTransferRequest0 priced) (.burnTransfer0 priced) := by
  have scratch := feeBurnMemory_ptr mem D.sevm.currentTarget
  have same : memWord (feeBurnMemory M D.sevm.currentTarget) 96 = 0 :=
    (burnFeeScratch_sentinel mem.wf D.sevm.currentTarget).trans sentinel
  have fresh : FeeMintSourceFresh K st D D.sevm (feeBurnWorld D.sevm b)
      (burnFeeLocals (feeBurnLiquidity D.sevm b) (feeBurnBalance1 M) b0 token1 token0
        r1 r0 toWord extρ R) (feeBurnMemory M D.sevm.currentTarget) r1 r0 0x15e2 := by
    intro gw callGas d out call post
    have member := mint_feeReply_mem fork scratch.wf call ⟨1, _, post.stack, by decide⟩
    rw [post.returnData] at member
    exact mint_feeFresh_of_universe inj apart sub (trace _ member) _ _ _ _ _
  obtain ⟨cached, feeGas, feePost, observation, callee, answered, suffix, _⟩ :=
    burnFeeCaller_pricing_source_inv fork
      (by simp only [List.not_mem_nil, not_false_eq_true]) mem sentinel rep tracked
      bound0 bound1 fresh prior state pair run
  have beforeRep : WriterRep K ((feeBurnWorld D.sevm b).getStor D.sevm.currentTarget) st := by
    rw [feeBurnWorld, afterSload_getStor]
    exact rep
  have beforeInstalled :
      some ((feeBurnWorld D.sevm b).getCode D.sevm.currentTarget).toList = sem.image := by
    rw [feeBurnWorld, afterSload_getCode]
    exact installed
  have member := mint_feeReply_mem fork scratch.wf observation.step
    ⟨1, _, observation.post.stack, by decide⟩
  rw [observation.post.returnData] at member
  have finished := burnFee_source_finished observation bound0 bound1 prior beforeRep
    scratch same tracked suffix state locked nonstatic time pair sender inj apart sub
    (trace _ member) sem image beforeInstalled fork good staticGood
  exact ⟨cached, feeGas, feePost, observation, callee, answered, suffix, finished⟩

/-- The first actual balance reply advances only the source segment and cache. -/
theorem burn_resumeInitialBalance0 {frame : Frame} {locals : BurnLocals} {out : Bytes}
    (long : 32 ≤ out.length) :
    resumeSegment frame (requestFor .burnInitialBalance0 locals.token0 (.balanceOf frame.context.pair))
        (.burnInitialBalance0 locals) (feeObservedResult out) =
      .suspended
        (frame.beginResume (requestFor .burnInitialBalance0 locals.token0 (.balanceOf frame.context.pair)))
        (requestFor .burnInitialBalance1 locals.token1 (.balanceOf frame.context.pair))
        (.burnInitialBalance1 locals (Bytes.toB256 (out.take 32))) := by
  simp only [resumeSegment, decodeExternal, requestFor, feeObservedResult,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true, long]
  rfl

/-- The second actual balance reply samples the old LP balance before fee minting. -/
theorem burn_resumeInitialBalance1 {frame : Frame} {locals : BurnLocals} {out : Bytes}
    {balance0 : B256} (long : 32 ≤ out.length) :
    resumeSegment frame (requestFor .burnInitialBalance1 locals.token1 (.balanceOf frame.context.pair))
        (.burnInitialBalance1 locals balance0) (feeObservedResult out) =
      .suspended
        (frame.beginResume (requestFor .burnInitialBalance1 locals.token1 (.balanceOf frame.context.pair)))
        (requestFor .burnFeeTo frame.current.state.factory .feeTo)
        (.burnFee ⟨locals, balance0, Bytes.toB256 (out.take 32),
          frame.current.state.balanceOf frame.context.pair⟩) := by
  simp only [resumeSegment, decodeExternal, requestFor, feeObservedResult,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true, long]
  rfl

/-- Actual initial token replies and their authentic static queues feed the
accepted fee/caller consumer in the original derivation. Cached token/reserve
locals come from the entry representation; no source endpoint is assumed. -/
theorem burnInitialBalances_source_finished {U K : WriterKey → Prop} {st : State}
    {D : Exec.Deriv} {b : Devm} {R : List B256} {M : Mem} {G : Nat}
    {toWord extρ : B256} {o : Outcome}
    (fork : CoveredFork D.sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (sentinel : memWord M 96 = 0)
    (rep : WriterRep K (b.getStor D.sevm.currentTarget) st)
    (tracked : K (.balance D.sevm.currentTarget))
    (prior : Frame) (state : prior.current.state = { st with unlocked := 0 })
    (nonstatic : prior.context.isStatic = false)
    (time : prior.context.timestamp = D.sevm.benvStat.time)
    (pair : prior.context.pair = D.sevm.currentTarget)
    (sender : prior.context.sender = D.sevm.caller)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys D, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode D.sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = D.sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = prior.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k)
    (run : SFunc.RunCutP (StepIn D) cert.prog D.sevm []
      (St b (toWord :: extρ :: R) M G) t_13f5_c37 (.done o)) :
    b.getStorVal D.sevm.currentTarget 12 = 1 ∧ D.sevm.isStatic = false ∧
    let locals : BurnLocals := ⟨toWord.toAdr, st.cachedReserves, st.token0, st.token1⟩
    let request0 := requestFor .burnInitialBalance0 locals.token0 (.balanceOf prior.context.pair)
    let prior1 := prior.beginResume request0
    let request1 := requestFor .burnInitialBalance1 locals.token1 (.balanceOf prior1.context.pair)
    let prior2 := prior1.beginResume request1
    let requestF := requestFor .burnFeeTo st.factory .feeTo
    ∃ (out0 out1 outF : Bytes) (views0 views1 viewsF : List StaticViewTurn)
      (frame : Frame) (priced : BurnPriced) (post : Devm) (w : BurnFinalWords) (N : Mem)
      (added : List PendingLog) (rawPrefix : List Log),
      w.amount0 = priced.amount0 ∧ w.amount1 = priced.amount1 ∧
      frame.checkpoint = prior.checkpoint ∧ frame.context = prior.context ∧
      PairViewProvenance D D.sevm prior st.token0.toB256 views0 ∧
      PairViewProvenance D D.sevm prior1 st.token1.toB256 views1 ∧
      PairViewProvenance D D.sevm prior2 st.factory.toB256 viewsF ∧
      frame.current.logs = prior.current.logs ++ added ∧
      post.logs = b.logs ++ rawPrefix ∧
      added.map (PendingLog.rawWith (burnOwnedRaw D.sevm.currentTarget)) = rawPrefix.map some ∧
      BurnTransferFinished U frame priced D D.sevm post w N extρ R o
        (.suspended prior request0 (.burnInitialBalance0 locals))
        (fun tail => .next (feeObservedResult out0) (staticViewTranscript views0 .done)
          (.next (feeObservedResult out1) (staticViewTranscript views1 .done)
            (.next (feeObservedResult outF) (staticViewTranscript viewsF .done) tail)))
        (staticViewChildReturns prior request0 0 views0 ++
          (staticViewChildReturns prior1 request1 0 views1 ++
            staticViewChildReturns prior2 requestF 0 viewsF)) := by
  obtain ⟨unlocked, mutable, d0, out0, d1, out1, gas, call0, call1, _, _,
    long0, _, long1, _, feeRep, stor1, logs1, _, reply1, bound0, bound1, balance1, decoded⟩ :=
    burnInitialBalances_writer_inv fork mem rep run
  obtain ⟨gw0, cg0, _, step0, post0⟩ := call0
  obtain ⟨gw1, cg1, _, step1, post1⟩ := call1
  let locked := burnLockedWorld D.sevm b
  let reserveWorld := afterSload D.sevm locked 8
  let r0 := reserve0Read (locked.getStorVal D.sevm.currentTarget 8)
  let r1 := reserve1Read (locked.getStorVal D.sevm.currentTarget 8)
  let mask : B256 := 0xffffffffffffffffffffffffffffffffffffffff
  let t0 := mask &&& reserveWorld.getStorVal D.sevm.currentTarget 6
  let t1 := mask &&& (afterSload D.sevm reserveWorld 6).getStorVal D.sevm.currentTarget 7
  let loaded := burnTokensWorld D.sevm reserveWorld
  let locals : BurnLocals := ⟨toWord.toAdr, st.cachedReserves, st.token0, st.token1⟩
  let request0 := requestFor .burnInitialBalance0 locals.token0 (.balanceOf prior.context.pair)
  let prior1 := prior.beginResume request0
  let request1 := requestFor .burnInitialBalance1 locals.token1 (.balanceOf prior1.context.pair)
  let prior2 := prior1.beginResume request1
  let requestF := requestFor .burnFeeTo st.factory .feeTo
  let M0 := balanceReplyMemory M D.sevm.currentTarget out0
  let M1 := balanceReplyMemory M0 D.sevm.currentTarget out1
  change StepIn D D.sevm
    (St (temporalAccountAccessBase loaded t0.toAdr)
      (gw0 :: t0 :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 :: t0 :: 0 ::
        t1 :: t0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M D.sevm.currentTarget) cg0) (.exec .staticcall) d0 at step0
  change StepIn D D.sevm
    (St (temporalAccountAccessBase d0 (t1 &&& mask).toAdr)
      (gw1 :: (t1 &&& mask) :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
        (t1 &&& mask) :: 0 :: Bytes.toB256 (out0.take 32) :: t1 :: t0 :: r1 :: r0 ::
        0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M0 D.sevm.currentTarget) cg1) (.exec .staticcall) d1 at step1
  have lockedRep := rep.burn_locked_world (sevm := D.sevm) (b := b)
  have token0Word : t0 = st.token0.toB256 := by
    change mask &&& reserveWorld.getStorVal D.sevm.currentTarget 6 = st.token0.toB256
    rw [show mask = ~~~ addressMask from by decide, B256.and_comm, and_mask_word]
    change (((afterSload D.sevm locked 8).getStor D.sevm.currentTarget).get 6).toAdr.toB256 = st.token0.toB256
    rw [afterSload_getStor, lockedRep.fixed.2.2.2.1]
  have token1Word : t1 = st.token1.toB256 := by
    change mask &&& (afterSload D.sevm reserveWorld 6).getStorVal D.sevm.currentTarget 7 = st.token1.toB256
    rw [show mask = ~~~ addressMask from by decide, B256.and_comm, and_mask_word]
    change (((afterSload D.sevm (afterSload D.sevm locked 8) 6).getStor D.sevm.currentTarget).get 7).toAdr.toB256 = st.token1.toB256
    rw [afterSload_getStor, afterSload_getStor, lockedRep.fixed.2.2.2.2.1]
  have cache0 : r0.toNat = st.reserve0.val := by
    rw [show r0 = st.reserve0.val.toB256 from lockedRep.fixed.2.2.2.2.2.1,
      B256.toNat_toB256_of_lt (lt_trans st.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have cache1 : r1.toNat = st.reserve1.val := by
    rw [show r1 = st.reserve1.val.toB256 from lockedRep.fixed.2.2.2.2.2.2.1,
      B256.toNat_toB256_of_lt (lt_trans st.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have loadedCode (a : Adr) : loaded.getCode a = b.getCode a := by
    dsimp only [loaded, reserveWorld, locked]
    rw [burnTokensWorld, afterSload_getCode, afterSload_getCode,
      afterSload_getCode, burnLockedWorld, afterSstore_getCode, afterSload_getCode]
  have loadedStor (a : Adr) : loaded.getStor a = locked.getStor a := by
    dsimp only [loaded, reserveWorld]
    rw [burnTokensWorld, afterSload_getStor, afterSload_getStor, afterSload_getStor]
  have stor0 (a : Adr) : d0.getStor a = locked.getStor a := by
    rw [post0.stor]
    change (temporalAccountAccessBase loaded t0.toAdr).state.getStor a = _
    rw [temporalAccountAccessBase_state]
    exact loadedStor a
  have nonempty : (b.getCode D.sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have code0 : d0.getCode D.sevm.currentTarget = b.getCode D.sevm.currentTarget := by
    have preCode : (temporalAccountAccessBase loaded t0.toAdr).getCode D.sevm.currentTarget =
        b.getCode D.sevm.currentTarget := by
      have unchanged : (temporalAccountAccessBase loaded t0.toAdr).getCode D.sevm.currentTarget =
          loaded.getCode D.sevm.currentTarget := by
        simp only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state]
      exact unchanged.trans (loadedCode _)
    have keep := Blanc.Lift.StepIn.codePreserve step0 D.sevm.currentTarget
      (by simpa only [St, Devm.getCode_setMach, preCode] using nonempty)
    simpa only [St, Devm.getCode_setMach, preCode] using keep
  have code1 : d1.getCode D.sevm.currentTarget = b.getCode D.sevm.currentTarget := by
    have preCode : (temporalAccountAccessBase d0 (t1 &&& mask).toAdr).getCode D.sevm.currentTarget =
        b.getCode D.sevm.currentTarget := by
      have unchanged : (temporalAccountAccessBase d0 (t1 &&& mask).toAdr).getCode D.sevm.currentTarget =
          d0.getCode D.sevm.currentTarget := by
        simp only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state]
      exact unchanged.trans code0
    have keep := Blanc.Lift.StepIn.codePreserve step1 D.sevm.currentTarget
      (by simpa only [St, Devm.getCode_setMach, preCode] using nonempty)
    simpa only [St, Devm.getCode_setMach, preCode] using keep
  obtain ⟨views0, turns0, authentic0, derived0⟩ :=
    pair_static_call_turns (frame := prior) (request := request0) inj apart sub sem image
      step0 (by simpa only [List.append_nil, St.stack] using pref_append _ ([] : List B256))
      (by simp only [St, Devm.getCode_setMach]
          simp only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state]
          change some (loaded.getCode prior.context.pair).toList = sem.image
          rw [pair, loadedCode]; exact installed)
      (by simp only [St, Devm.getStor, Devm.getAcct, Devm.setMach_state, temporalAccountAccessBase_state]
          change WriterRep K (loaded.getStor prior.context.pair) prior.current.state
          rw [pair, loadedStor, state]; exact lockedRep)
      time fork ⟨1, _, post0.stack, by decide⟩ staticGood
  obtain ⟨views1, turns1, authentic1, derived1⟩ :=
    pair_static_call_turns (frame := prior1) (request := request1) inj apart sub sem image
      step1 (by simpa only [List.append_nil, St.stack] using pref_append _ ([] : List B256))
      (by simp only [St, Devm.getCode_setMach]
          simp only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state]
          change some (d0.getCode prior.context.pair).toList = sem.image
          rw [pair, code0]; exact installed)
      (by simp only [St, Devm.getStor, Devm.getAcct, Devm.setMach_state, temporalAccountAccessBase_state]
          change WriterRep K (d0.getStor prior.context.pair) prior1.current.state
          rw [pair, stor0]
          change WriterRep K (locked.getStor D.sevm.currentTarget) prior.current.state
          rw [state]; exact lockedRep)
      time fork ⟨1, _, post1.stack, by decide⟩ staticGood
  have same : memWord M1 96 = 0 := by
    rw [burnBalanceReply_sentinel
      (balanceReplyMemory_ptr out0 (balanceRequestMemory_ptr mem D.sevm.currentTarget)).wf,
      burnBalanceReply_sentinel mem.wf]
    exact sentinel
  obtain ⟨cached, feeGas, feePost, observation, _, _, _, residual, viewsF,
      provenanceF, _, finished, _⟩ :=
    burnFeeCaller_source_finished fork reply1 same feeRep tracked bound0 bound1
      prior2 state rfl nonstatic time pair sender inj apart sub trace sem image
      (by rw [code1]; exact installed) good staticGood decoded
  have factoryWord : feeFactoryWord D.sevm (feeBurnWorld D.sevm d1) = st.factory.toB256 := by
    unfold feeFactoryWord feeBurnWorld
    change (((afterSload D.sevm d1 _).getStor D.sevm.currentTarget).get 5).toAdr.toB256 = _
    rw [afterSload_getStor, feeRep.fixed.2.2.1]
  have initialLocals :
      (feeBurnObserved toWord t1 t0 (feeBurnLiquidity D.sevm d1)
        (feeBurnBalance1 M1) (Bytes.toB256 (out0.take 32)) r1 r0 bound0 bound1).locals = locals := by
    simp only [feeBurnObserved, locals, token0Word, token1Word, toAdr_toB256,
      cache0, cache1, State.cachedReserves]
  have observedEq : feeBurnObserved toWord t1 t0 (feeBurnLiquidity D.sevm d1)
      (feeBurnBalance1 M1) (Bytes.toB256 (out0.take 32)) r1 r0 bound0 bound1 =
      ⟨locals, Bytes.toB256 (out0.take 32), Bytes.toB256 (out1.take 32),
        st.balanceOf prior.context.pair⟩ := by
    change BurnObserved.mk
      (feeBurnObserved toWord t1 t0 (feeBurnLiquidity D.sevm d1)
        (feeBurnBalance1 M1) (Bytes.toB256 (out0.take 32)) r1 r0 bound0 bound1).locals
      (Bytes.toB256 (out0.take 32)) (feeBurnBalance1 M1) (feeBurnLiquidity D.sevm d1) = _
    rw [initialLocals]
    change BurnObserved.mk locals (Bytes.toB256 (out0.take 32))
      (feeBurnBalance1 (balanceReplyMemory (balanceReplyMemory M D.sevm.currentTarget out0)
        D.sevm.currentTarget out1)) (feeBurnLiquidity D.sevm d1) = _
    rw [balance1, cached]
    rfl
  have reaches : ∀ tail out,
      ExactConsumes (.suspended prior2
        (requestFor .burnFeeTo (feeFactoryWord D.sevm (feeBurnWorld D.sevm d1)).toAdr .feeTo)
        (.burnFee (feeBurnObserved toWord t1 t0 (feeBurnLiquidity D.sevm d1)
          (feeBurnBalance1 M1) (Bytes.toB256 (out0.take 32)) r1 r0 bound0 bound1))) tail out →
      ExactConsumes (.suspended prior request0 (.burnInitialBalance0 locals))
        (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
          (.next (feeObservedResult out1) (staticViewTranscript views1 .done) tail))
        { out with childReturns := (staticViewChildReturns prior request0 0 views0 ++
          (staticViewChildReturns prior1 request1 0 views1 ++ out.childReturns)) } := by
    intro tail out consumed
    refine ExactConsumes.nextCall (result := feeObservedResult out0)
      (out := { out with childReturns := staticViewChildReturns prior1 request1 0 views1 ++ out.childReturns })
      (by simp only [feeObservedResult, Bool.not_true, Bool.and_false])
      (by intro absent; cases absent) turns0 ?_
    change ExactConsumes (resumeSegment prior request0 (.burnInitialBalance0 locals)
      (feeObservedResult out0)) _ _
    rw [burn_resumeInitialBalance0 long0]
    refine ExactConsumes.nextCall (result := feeObservedResult out1)
      (by simp only [feeObservedResult, Bool.not_true, Bool.and_false])
      (by intro absent; cases absent) turns1 ?_
    change ExactConsumes (resumeSegment prior1 request1
      (.burnInitialBalance1 locals (Bytes.toB256 (out0.take 32))) (feeObservedResult out1)) tail out
    rw [burn_resumeInitialBalance1 long1]
    simpa only [factoryWord, toAdr_toB256, observedEq,
      prior2, prior1, request1, Frame.beginResume, state] using consumed
  let observed := feeBurnObserved toWord t1 t0 (feeBurnLiquidity D.sevm d1)
    (feeBurnBalance1 M1) (Bytes.toB256 (out0.take 32)) r1 r0 bound0 bound1
  let fee := feeBranchSourceFee { st with unlocked := 0 } D.sevm
    (feeKLastWorld D.sevm observation.d) (Bytes.toB256 (observation.out.take 32)) r0 r1
  let supply := feePost.getStorVal D.sevm.currentTarget 0
  let a0 := feeBurnLiquidity D.sevm d1 * Bytes.toB256 (out0.take 32) / supply
  let a1 := feeBurnLiquidity D.sevm d1 * feeBurnBalance1 M1 / supply
  let w : BurnFinalWords := ⟨supply, feeOnWord (Bytes.toB256 (observation.out.take 32)),
    feeBurnLiquidity D.sevm d1, feeBurnBalance1 M1, Bytes.toB256 (out0.take 32),
    t1, t0, r1, r0, a1, a0, toWord⟩
  let frame := burnPricedFrame (prior2.beginResume
    (requestFor .burnFeeTo (feeFactoryWord D.sevm (feeBurnWorld D.sevm d1)).toAdr .feeTo)) observed fee
  let priced := burnPricedSource observed fee a0 a1
  let post := lpBurnPost D.sevm (afterSload D.sevm feePost 0) (burnFinalStack w extρ R)
    feePost.memory D.sevm.currentTarget.toB256 (feeBurnLiquidity D.sevm d1) residual
  have feePostEq := Outcome.returned.inj observation.returned
  rw [observation.last] at feePostEq
  have logsDisj := observation.sourceResult.2.2.2.2
  rw [← feePostEq] at logsDisj
  have baseLogs : (feeKLastWorld D.sevm observation.d).logs = b.logs := by
    rw [feeKLastWorld, afterSload_logs, observation.post.logs, feeFactoryCallWorld,
      temporalAccountAccessBase_logs, feeFactoryLoadWorld, afterSload_logs,
      feeBurnWorld, afterSload_logs, logs1]
  have feeImage : ∃ feeLogs : List Log,
      feePost.logs = b.logs ++ feeLogs ∧
      (fee.events.map (PendingLog.owned frame.origin)).map
        (PendingLog.rawWith (burnOwnedRaw D.sevm.currentTarget)) = feeLogs.map some := by
    rcases logsDisj with ⟨events, raw⟩ | ⟨L, _, events, raw⟩
    · refine ⟨[], by rw [raw, baseLogs, List.append_nil], ?_⟩
      rw [events]
      rfl
    · refine ⟨_, by rw [raw, baseLogs], ?_⟩
      rw [events]
      simp only [List.map_cons, List.map_nil, PendingLog.rawWith, burnOwnedRaw,
        lockedOwnedRaw, transferRawLog, lpMintRawLog]
      rfl
  obtain ⟨feeLogs, feePostLogs, feeImage⟩ := feeImage
  let added := fee.events.map (PendingLog.owned frame.origin) ++
    [PendingLog.owned frame.origin (.transfer D.sevm.currentTarget 0 (feeBurnLiquidity D.sevm d1))]
  let rawPrefix := feeLogs ++
    [lpBurnRawLog D.sevm.currentTarget D.sevm.currentTarget (feeBurnLiquidity D.sevm d1)]
  have pending : frame.current.logs = prior.current.logs ++ added := by
    simp only [frame, burnPricedFrame, Frame.withEvents, Frame.origin, prior2, prior1,
      Frame.beginResume, added, List.map_cons, List.map_nil, pair, List.append_assoc]
    rfl
  have rawPrefixEq : post.logs = b.logs ++ rawPrefix := by
    have lp := (lpBurnPost_facts (sevm := D.sevm) (b := afterSload D.sevm feePost 0)
      (R := burnFinalStack w extρ R) (M := feePost.memory)
      (fromWord := D.sevm.currentTarget.toB256) (value := feeBurnLiquidity D.sevm d1)
      (G := residual)).2.2.1
    change post.logs = _ at lp
    rw [lp, afterSload_logs, feePostLogs, toAdr_toB256, List.append_assoc]
  have prefixImage : added.map (PendingLog.rawWith (burnOwnedRaw D.sevm.currentTarget)) =
      rawPrefix.map some := by
    simp only [added, rawPrefix, List.map_append, feeImage, List.map_cons, List.map_nil,
      PendingLog.rawWith, burnOwnedRaw, lockedOwnedRaw, transferRawLog, lpBurnRawLog]
    rfl
  refine ⟨unlocked, mutable, out0, out1, observation.out, views0, views1, viewsF,
    frame, priced, post, w, post.memory, added, rawPrefix, rfl, rfl, rfl, rfl, ?_, ?_, ?_,
    pending, rawPrefixEq, prefixImage, ?_⟩
  · rw [← token0Word]
    exact ⟨authentic0, derived0⟩
  · have masked : t1 &&& mask = st.token1.toB256 := by
      rw [token1Word, show mask = ~~~ addressMask from by decide, and_mask_word, toAdr_toB256]
    rw [← masked]
    exact ⟨authentic1, derived1⟩
  · rw [← factoryWord]
    exact provenanceF
  · simpa only [List.append_assoc, factoryWord, toAdr_toB256] using
      burnFee_finished_prepend (childPrefix := staticViewChildReturns prior request0 0 views0 ++
        staticViewChildReturns prior1 request1 0 views1) finished
        (fun tail out consumed => by simpa only [List.append_assoc] using reaches tail out consumed)

/-- The entry checkpoint is retained while the first Burn segment holds the lock. -/
def burnSourceLockedFrame (current : Checkpoint) (ctx : Context) (recipient : Adr) : Frame :=
  { Frame.enter current ctx (.burn recipient) with
    current := { current with state := { current.state with unlocked := 0 } } }

/-- Actual successful entry guards select the first balance suspension. -/
theorem burn_startTyped_suspended {current : Checkpoint} {ctx : Context} {recipient : Adr}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (unlocked : current.state.unlocked = 1) :
    startTyped current ctx (.burn recipient) =
      .suspended (burnSourceLockedFrame current ctx recipient)
        (requestFor .burnInitialBalance0 current.state.token0 (.balanceOf ctx.pair))
        (.burnInitialBalance0 ⟨recipient, current.state.cachedReserves,
          current.state.token0, current.state.token1⟩) := by
  have opened : (Frame.enter current ctx (.burn recipient)).lock =
      .ok (burnSourceLockedFrame current ctx recipient) := by
    simp only [Frame.lock, Frame.enter, unlocked, nonstatic, ite_true,
      Bool.false_eq_true, ite_false, burnSourceLockedFrame]
  simp only [startTyped, startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
    getterResult, opened, Frame.suspend]
  rfl

/-- Full entry consumption, represented public return, and chronological raw log image. -/
def BurnEntryFinished (U : WriterKey → Prop) (current : Checkpoint) (D : Exec.Deriv)
    (b : Devm) (o : Outcome) (invocation : List Nat) : Prop :=
  let ctx := mintSourceContext D.sevm invocation
  let recipient := ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
    Sevm.dataWord D.sevm 4).toAdr
  ∃ (K' : WriterKey → Prop) (final : Frame) (nested : Transcript)
    (rets : List ChildReturn) (publicPost : Devm) (amount0 amount1 : B256)
    (added : List PendingLog) (rawLogs : List Log),
    (∀ k, K' k → U k) ∧
    ExactConsumes (startTyped current ctx (.burn recipient)) nested
      { status := .success (encodeWords [amount0, amount1]), frame := final,
        remaining := .done, childReturns := rets } ∧
    o = .halted publicPost ∧ publicPost.output = encodeWords [amount0, amount1] ∧
    WriterRep K' (publicPost.getStor D.sevm.currentTarget) final.current.state ∧
    final.checkpoint = current ∧ final.context = ctx ∧ final.current.state.unlocked = 1 ∧
    final.current.logs = current.logs ++ added ∧ publicPost.logs = b.logs ++ rawLogs ∧
    added.map (PendingLog.rawWith (burnOwnedRaw D.sevm.currentTarget)) = rawLogs.map some

/-- The full observable Burn result with incoming footprint growth. Queue
occurrence attachment is a separate canonical obligation. -/
def BurnEntryTrackedFinished (U K : WriterKey → Prop) (current : Checkpoint) (D : Exec.Deriv)
    (b : Devm) (o : Outcome) (invocation : List Nat) : Prop :=
  let ctx := mintSourceContext D.sevm invocation
  let recipient := ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
    Sevm.dataWord D.sevm 4).toAdr
  ∃ (K' : WriterKey → Prop) (final : Frame) (nested : Transcript)
    (rets : List ChildReturn) (publicPost : Devm) (amount0 amount1 : B256)
    (added : List PendingLog) (rawLogs : List Log),
    (∀ k, K' k → U k) ∧ (∀ k, K k → K' k) ∧
    ExactConsumes (startTyped current ctx (.burn recipient)) nested
      { status := .success (encodeWords [amount0, amount1]), frame := final,
        remaining := .done, childReturns := rets } ∧
    o = .halted publicPost ∧ publicPost.output = encodeWords [amount0, amount1] ∧
    WriterRep K' (publicPost.getStor D.sevm.currentTarget) final.current.state ∧
    final.checkpoint = current ∧ final.context = ctx ∧ final.current.state.unlocked = 1 ∧
    final.current.logs = current.logs ++ added ∧ publicPost.logs = b.logs ++ rawLogs ∧
    added.map (PendingLog.rawWith (burnOwnedRaw D.sevm.currentTarget)) = rawLogs.map some

/-- Forget footprint growth without weakening any observable Burn effect. -/
theorem BurnEntryTrackedFinished.toFinished {U K : WriterKey → Prop}
    {current : Checkpoint} {D : Exec.Deriv} {b : Devm} {o : Outcome} {invocation : List Nat}
    (finished : BurnEntryTrackedFinished U K current D b o invocation) :
    BurnEntryFinished U current D b o invocation := by
  obtain ⟨K', final, nested, rets, post, a0, a1, added, raw,
    sub, _, facts⟩ := finished
  exact ⟨K', final, nested, rets, post, a0, a1, added, raw, sub, facts⟩

/-- Restore the finite incoming rows at the same final storage/state, using
freshness inside the original fixed universe. No fold-growth premise is added. -/
theorem BurnEntryFinished.track {U K : WriterKey → Prop}
    {current : Checkpoint} {D : Exec.Deriv} {b : Devm} {o : Outcome} {invocation : List Nat}
    (incoming : WriterRep K (b.getStor D.sevm.currentTarget) current.state)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (finished : BurnEntryFinished U current D b o invocation) :
    BurnEntryTrackedFinished U K current D b o invocation := by
  obtain ⟨K', final, nested, rets, post, a0, a1, added, raw,
    finalSub, consumed, halted, output, represented, checkpoint, context,
    unlocked, pending, logs, images⟩ := finished
  obtain ⟨rows, finite⟩ := incoming.finite
  have rowInU : ∀ k ∈ rows, U k := fun k member => sub k ((finite k).mpr member)
  have fresh : WriterFreshKeys K' rows :=
    Blanc.SlotFootprint.FreshKeys.of_universe inj apart finalSub rowInU
  refine ⟨WriterExtend K' rows, final, nested, rets, post, a0, a1, added, raw,
    ?_, ?_, consumed, halted, output, represented.extend fresh,
    checkpoint, context, unlocked, pending, logs, images⟩
  · intro k member
    rcases member with old | row
    · exact finalSub k old
    · exact rowInU k row
  · intro k old
    exact Or.inr ((finite k).mp old)

/-- The real pc-zero route supplies entry guards, all external queues, the ABI
return, and the fee/LP/child/Sync/Burn log image in the unchanged derivation D. -/
theorem burnPc0_source_finished {U K : WriterKey → Prop} {current : Checkpoint}
    {D : Exec.Deriv} {b : Devm} {G : Nat} {o : Outcome}
    (invocation : List Nat) (fork : CoveredFork D.sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector D.sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor D.sevm.currentTarget) current.state)
    (tracked : K (.balance D.sevm.currentTarget))
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys D, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode D.sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = D.sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = D.sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k)
    (run : SFunc.RunP (StepIn D) cert.prog D.sevm (St b [] Mem.empty G) t_0000_c0 o) :
    BurnEntryFinished U current D b o invocation := by
  obtain ⟨value, _, calleeGas, calleeOutcome, callee, tail⟩ := burnPc0_caller_inv selector run
  let toWord := (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord D.sevm 4
  let ctx := mintSourceContext D.sevm invocation
  let prior := burnSourceLockedFrame current ctx toWord.toAdr
  have calleeCut := SFunc.runP_iff_runCutP_nil.mp callee
  obtain ⟨unlocked, mutable, _⟩ :=
    burnInitialBalances_writer_inv fork getterInitMemory_ptr rep calleeCut
  obtain ⟨_, _, out0, out1, outF, views0, views1, viewsF, frame, priced, pricingPost, w, N,
      prefixAdded, prefixRaw, amount0, amount1, checkpoint, context, prov0, prov1, provF,
      prefixPending, prefixLogs, prefixImage, finished⟩ :=
    burnInitialBalances_source_finished fork getterInitMemory_ptr burnEntryMemory_sentinel
      rep tracked prior rfl mutable rfl rfl rfl inj apart sub trace sem image installed
      good staticGood calleeCut
  obtain ⟨K', d0, d1, entered0, entered1, turns0, turns1, final, rets, transcript,
      post, finalM, gas, n, balance0, balance1, added0, added1, L0, L1,
      sub', calls, mutable0, mutable1, consumed, returned, finalRep, finalCheckpoint,
      finalContext, finalUnlocked, ptr, _, bound0, bound1, _, images0, images1,
      finalLogs, low, high, finalPending⟩ := finished
  rw [returned] at tail
  have canonical : SFunc.RunCutP (StepIn D) cert.prog D.sevm []
      (St post (w.amount1 :: w.amount0 :: [0x89afcb44]) finalM gas) t_053d_c83 (.done o) := tail
  obtain ⟨abiGas, publicPost, halted, terminal, output, stor, logs⟩ :=
    burnAbi_return_inv (fun h => StepIn.toRun h) ptr low high canonical
  have lockState : current.state.unlocked = 1 := by
    rcases rep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, _, lock⟩
    exact lock.symm.trans unlocked
  have typed := burn_startTyped_suspended (current := current) (ctx := ctx)
    (recipient := toWord.toAdr) value mutable lockState
  let suffixEvents := [PendingLog.owned final.origin (.sync balance0.toNat balance1.toNat),
    PendingLog.owned final.origin (.burn frame.context.sender priced.amount0 priced.amount1
      priced.observed.locals.recipient)]
  let suffixRaw : List Log :=
    [⟨frame.context.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩,
     ⟨frame.context.pair,
      [burnEventTopic, frame.context.sender.toB256, priced.observed.locals.recipient.toB256],
      encodeWords [priced.amount0, priced.amount1]⟩]
  have pair : frame.context.pair = D.sevm.currentTarget := congrArg Context.pair context
  have suffixImage : suffixEvents.map (PendingLog.rawWith (burnOwnedRaw D.sevm.currentTarget)) =
      suffixRaw.map some := by
    simp only [suffixEvents, suffixRaw, List.map_cons, List.map_nil, PendingLog.rawWith,
      burnOwnedRaw, toB256_toNat, pair]
  let added := prefixAdded ++ added0 ++ added1 ++ suffixEvents
  let rawLogs := prefixRaw ++ L0 ++ L1 ++ suffixRaw
  let request0 := requestFor .burnInitialBalance0 current.state.token0 (.balanceOf ctx.pair)
  let prior1 := prior.beginResume request0
  let request1 := requestFor .burnInitialBalance1 current.state.token1 (.balanceOf ctx.pair)
  let prior2 := prior1.beginResume request1
  let nested := Transcript.next (feeObservedResult out0) (staticViewTranscript views0 .done)
    (.next (feeObservedResult out1) (staticViewTranscript views1 .done)
      (.next (feeObservedResult outF) (staticViewTranscript viewsF .done) transcript))
  let allReturns := (staticViewChildReturns prior request0 0 views0 ++
    (staticViewChildReturns prior1 request1 0 views1 ++
      staticViewChildReturns prior2 (requestFor .burnFeeTo current.state.factory .feeTo) 0 viewsF)) ++ rets
  refine ⟨K', final, nested, allReturns, publicPost, priced.amount0, priced.amount1, added, rawLogs,
    sub', ?_, Seg.done.inj halted, ?_, ?_, finalCheckpoint.trans checkpoint,
    finalContext.trans context, finalUnlocked, ?_, ?_, ?_⟩
  · rw [typed]
    exact consumed
  · simpa only [amount0, amount1, encodeWords, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] using output
  · rw [stor]
    exact finalRep
  · rw [finalPending, prefixPending]
    simp only [added, suffixEvents, prior, burnSourceLockedFrame, List.append_assoc]
  · rw [logs, finalLogs, prefixLogs]
    simp only [rawLogs, suffixRaw, List.append_assoc]
  · simp only [added, rawLogs, List.map_append, prefixImage,
      burn_pending_logs_preserves images0, burn_pending_logs_preserves images1, suffixImage]

/-- The supplied raw invocation is the root used by the lift and every source
producer. U remains the caller's fixed HASH-T universe, including this root's
actual fee trace and all admitted descendants; no phase-local universe is made. -/
theorem burnRaw_source_finished {U K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b publicPost : Devm} {G : Nat}
    (invocation : List Nat) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok publicPost))
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots run,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    BurnEntryFinished U current ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩
      b (.halted publicPost) invocation := by
  obtain ⟨f, entry, lifted⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  exact burnPc0_source_finished invocation fork selector rep tracked inj apart sub trace
    sem image installed good staticGood lifted

/-- The actual pc-zero source consumer also preserves every incoming key. -/
theorem burnPc0_source_tracked_finished {U K : WriterKey → Prop} {current : Checkpoint}
    {D : Exec.Deriv} {b : Devm} {G : Nat} {o : Outcome}
    (invocation : List Nat) (fork : CoveredFork D.sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector D.sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor D.sevm.currentTarget) current.state)
    (tracked : K (.balance D.sevm.currentTarget))
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys D, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode D.sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = D.sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = D.sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k)
    (run : SFunc.RunP (StepIn D) cert.prog D.sevm (St b [] Mem.empty G) t_0000_c0 o) :
    BurnEntryTrackedFinished U K current D b o invocation := by
  exact (burnPc0_source_finished invocation fork selector rep tracked inj apart sub trace
    sem image installed good staticGood run).track rep inj apart sub

/-- The same supplied raw root, full entry result and incoming footprint growth. -/
theorem burnRaw_source_tracked_finished {U K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b publicPost : Devm} {G : Nat}
    (invocation : List Nat) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok publicPost))
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots run,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    BurnEntryTrackedFinished U K current ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩
      b (.halted publicPost) invocation := by
  exact (burnRaw_source_finished invocation codeEq fork selector rep tracked run inj apart sub
    trace sem image installed good staticGood).track rep inj apart sub

end Blanc.Lift.UniswapV2Pair
