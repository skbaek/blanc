import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.UniswapV2Pair.StaticViewTurns

/-!
# Canonical mint frame

Every successful raw mint run at the Pair code consumes the typed source mint over its three
external observations (both token `balanceOf` replies and the factory `feeTo` reply), with
turn queues DERIVED from the actual child executions of the same pc-zero derivation. The
finite-storage freshness obligations of the protocol-fee recipient, the address-zero minimum
liquidity holder and the LP recipient are discharged from one trace-local (HASH-T) key
universe; no freshness premise is exported.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- HASH-T universe rows of a mint run: the decoded rows of every actually entered Pair frame,
the two LP rows the entry may write (address zero, the decoded recipient) and the LP row of the
fee recipient observed in the actual factory reply `feeReply`. -/
def mintTraceKeys (root : Exec.Deriv) (feeReply : Bytes) : List WriterKey :=
  ((Exec.rawFrameRoots root.exc).flatMap fun F =>
    if F.sevm.currentTarget = root.sevm.currentTarget then staticViewDecodedKeys F.sevm else []) ++
  (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord root.sevm 4).toAdr ++
    lpMintTouched (Bytes.toB256 (feeReply.take 32)).toAdr)

theorem mintTraceKeys_frame {root : Exec.Deriv} {feeReply : Bytes} {F : Exec.Deriv}
    (member : F ∈ Exec.rawFrameRoots root.exc)
    (target : F.sevm.currentTarget = root.sevm.currentTarget) :
    ∀ k ∈ staticViewDecodedKeys F.sevm, k ∈ mintTraceKeys root feeReply := by
  intro k touched
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨F, member, ?_⟩
  rw [ite_eq_left target]
  exact touched

theorem mintTraceKeys_rows (root : Exec.Deriv) (feeReply : Bytes) :
    WriterKey.balance (0 : B256).toAdr ∈ mintTraceKeys root feeReply ∧
    WriterKey.balance (Sevm.dataWord root.sevm 4).toAdr ∈ mintTraceKeys root feeReply ∧
    WriterKey.balance (Bytes.toB256 (feeReply.take 32)).toAdr ∈ mintTraceKeys root feeReply := by
  simp only [mintTraceKeys, lpMintTouched, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, true_or, or_true, and_self]

/-- Every list of universe rows is fresh against every tracked subset of the universe. -/
private theorem mint_fresh_of_universe {U K : WriterKey → Prop} {ks : List WriterKey}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (touched : ∀ k ∈ ks, U k) : WriterFreshKeys K ks :=
  Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub touched

private theorem mint_single_row {U : WriterKey → Prop} {a : Adr}
    (row : U (.balance a)) : ∀ k ∈ lpMintTouched a, U k := by
  intro k member
  simp only [lpMintTouched, List.mem_cons, List.not_mem_nil, or_false] at member
  rw [member]
  exact row

/-- The fee recipient's touched-row obligation holds in the trace universe. -/
theorem mint_feeFresh_of_trace {K : WriterKey → Prop} {root : Exec.Deriv} {feeReply : Bytes}
    (inj : WriterInj (WriterExtend K (mintTraceKeys root feeReply)))
    (apart : WriterApart (WriterExtend K (mintTraceKeys root feeReply)))
    (st : State) (sevm : Sevm) (b : Devm) (r0 r1 : B256) :
    FeeMintFresh K st sevm b (Bytes.toB256 (feeReply.take 32)) r0 r1 := by
  intro _ _ _ _
  exact mint_fresh_of_universe inj apart (fun _ tracked => Or.inl tracked)
    (mint_single_row (Or.inr (mintTraceKeys_rows root feeReply).2.2))

/-- The fee branch's tracked rows stay inside the trace universe. -/
theorem mint_feeKeys_sub {K : WriterKey → Prop} {root : Exec.Deriv} {feeReply : Bytes}
    (st : State) (sevm : Sevm) (b : Devm) (r0 r1 : B256) :
    ∀ k, feeBranchSourceKeys K st sevm b (Bytes.toB256 (feeReply.take 32)) r0 r1 k →
      WriterExtend K (mintTraceKeys root feeReply) k := by
  intro k tracked
  have extended : WriterExtend K (lpMintTouched (Bytes.toB256 (feeReply.take 32)).toAdr) k →
      WriterExtend K (mintTraceKeys root feeReply) k := by
    intro member
    rcases member with old | new
    · exact Or.inl old
    · exact mint_single_row (U := WriterExtend K (mintTraceKeys root feeReply))
        (Or.inr (mintTraceKeys_rows root feeReply).2.2) k new
  unfold feeBranchSourceKeys at tracked
  split at tracked
  · exact Or.inl tracked
  · split at tracked
    · exact Or.inl tracked
    · split at tracked
      · split at tracked
        · exact Or.inl tracked
        · exact extended tracked
      · exact Or.inl tracked

/-- Both supply arms' LP-row obligations hold for every tracked subset of the trace universe. -/
theorem mint_afterFeeFresh_of_trace {K K' : WriterKey → Prop} {root : Exec.Deriv}
    {feeReply : Bytes}
    (inj : WriterInj (WriterExtend K (mintTraceKeys root feeReply)))
    (apart : WriterApart (WriterExtend K (mintTraceKeys root feeReply)))
    (sub : ∀ k, K' k → WriterExtend K (mintTraceKeys root feeReply) k) (st : State) :
    MintAfterFeeFresh K' st (Sevm.dataWord root.sevm 4).toAdr.toB256 := by
  have rows := mintTraceKeys_rows root feeReply
  have zero : ∀ k ∈ lpMintTouched (0 : B256).toAdr,
      WriterExtend K (mintTraceKeys root feeReply) k := mint_single_row (Or.inr rows.1)
  have recipient : ∀ k ∈ lpMintTouched (Sevm.dataWord root.sevm 4).toAdr.toB256.toAdr,
      WriterExtend K (mintTraceKeys root feeReply) k := by
    rw [toAdr_toB256]
    exact mint_single_row (Or.inr rows.2.1)
  have subZero : ∀ k, WriterExtend K' (lpMintTouched (0 : B256).toAdr) k →
      WriterExtend K (mintTraceKeys root feeReply) k := by
    intro k member
    rcases member with old | new
    · exact sub k old
    · exact zero k new
  refine ⟨fun _ => ⟨mint_fresh_of_universe inj apart sub zero,
    mint_fresh_of_universe inj apart subZero recipient⟩,
    fun _ => mint_fresh_of_universe inj apart sub recipient⟩

/-- A successful mint pricing segment keeps the frame's checkpoint and context and unlocks. -/
theorem mintAfterFee_finished_shape {frame : Frame} {observed : MintObserved} {fee : FeeResult}
    {finished : Frame} {bytes : Bytes}
    (result : frame.mintAfterFee observed fee = .finished finished bytes) :
    finished.checkpoint = frame.checkpoint ∧ finished.context = frame.context ∧
      finished.current.state.unlocked = 1 := by
  unfold Frame.mintAfterFee at result
  dsimp only at result
  split at result
  · simp only [Frame.fail, reduceCtorEq] at result
  · split at result
    · simp only [Frame.fail, reduceCtorEq] at result
    · split at result
      · split at result
        · simp only [Frame.fail, reduceCtorEq] at result
        · unfold Frame.finishUpdated at result
          split at result
          · simp only [Frame.fail, reduceCtorEq] at result
          · simp only [Frame.finishLocked, Frame.finish, Frame.withEvents, Frame.withUpdate,
              SegmentResult.finished.injEq] at result
            obtain ⟨frameEq, _⟩ := result
            subst frameEq
            exact ⟨rfl, rfl, rfl⟩
      · simp only [Frame.fail, reduceCtorEq] at result

/-- The three observed replies, each preceded by a turn queue that leaves its frame unchanged,
consume the typed source mint exactly up to its finished pricing segment. -/
theorem mint_source_exact_consumption {current : Checkpoint} {ctx : Context} {recipient : Adr}
    {out0 out1 outF : Bytes} {T0 T1 TF : Transcript} {e0 e1 eF : TurnsResult}
    {finished : Frame} {bytes : Bytes}
    (handlers : MintBalanceHandlerResult current ctx recipient out0 out1)
    (fee : resumeSegment (mintSourceFeeFrame current ctx recipient)
      (requestFor .mintFeeTo current.state.factory .feeTo)
      (.mintFee (mintBalanceObserved current.state recipient (Bytes.toB256 (out0.take 32))
        (Bytes.toB256 (out1.take 32))))
      (feeObservedResult outF) = .finished finished bytes)
    (turns0 : ExactTurns (mintSourceLockedFrame current ctx recipient)
      (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)) 0 T0 e0)
    (frame0 : e0.frame = mintSourceLockedFrame current ctx recipient)
    (turns1 : ExactTurns ((mintSourceLockedFrame current ctx recipient).beginResume
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)))
      (requestFor .mintBalance1 current.state.token1 (.balanceOf ctx.pair)) 0 T1 e1)
    (frame1 : e1.frame = (mintSourceLockedFrame current ctx recipient).beginResume
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)))
    (turnsF : ExactTurns (mintSourceFeeFrame current ctx recipient)
      (requestFor .mintFeeTo current.state.factory .feeTo) 0 TF eF)
    (frameF : eF.frame = mintSourceFeeFrame current ctx recipient) :
    ExactConsumes (startTyped current ctx (.mint recipient))
      (.next (feeObservedResult out0) T0 (.next (feeObservedResult out1) T1
        (.next (feeObservedResult outF) TF .done)))
      { status := .success bytes, frame := finished, remaining := .done,
        childReturns := e0.childReturns ++ (e1.childReturns ++ (eF.childReturns ++ [])) } := by
  obtain ⟨start, resume0, resume1⟩ := handlers
  rw [start]
  have last : ExactConsumes (.suspended (mintSourceFeeFrame current ctx recipient)
      (requestFor .mintFeeTo current.state.factory .feeTo)
      (.mintFee (mintBalanceObserved current.state recipient (Bytes.toB256 (out0.take 32))
        (Bytes.toB256 (out1.take 32)))))
      (.next (feeObservedResult outF) TF .done)
      { status := .success bytes, frame := finished, remaining := .done,
        childReturns := eF.childReturns ++ [] } := by
    refine ExactConsumes.nextCall (result := feeObservedResult outF)
      (out := ⟨.success bytes, finished, .done, []⟩) rfl
      (fun absent => by cases absent) turnsF ?_
    simp only [feeObservedResult, ite_true, frameF]
    change ExactConsumes (resumeSegment _ _ _ (feeObservedResult outF)) _ _
    rw [fee]
    exact ExactConsumes.finished finished bytes
  have middle : ExactConsumes (resumeSegment (mintSourceLockedFrame current ctx recipient)
      (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair))
      (.mintBalance0 recipient current.state.cachedReserves) (feeObservedResult out0))
      (.next (feeObservedResult out1) T1 (.next (feeObservedResult outF) TF .done))
      { status := .success bytes, frame := finished, remaining := .done,
        childReturns := e1.childReturns ++ (eF.childReturns ++ []) } := by
    rw [resume0]
    refine ExactConsumes.nextCall (result := feeObservedResult out1)
      (out := ⟨.success bytes, finished, .done, eF.childReturns ++ []⟩) rfl
      (fun absent => by cases absent) turns1 ?_
    simp only [feeObservedResult, ite_true, frame1]
    rw [show (feeObservedResult out1 : ExternalResult) =
      { success := true, returndata := out1, codeExists := true, recoveryOutput := 0 } from rfl]
      at resume1
    rw [resume1]
    exact last
  refine ExactConsumes.nextCall (result := feeObservedResult out0)
      (out := ⟨.success bytes, finished, .done, e1.childReturns ++ (eF.childReturns ++ [])⟩) rfl
      (fun absent => by cases absent) turns0 ?_
  simp only [feeObservedResult, ite_true, frame0]
  exact middle

private theorem mint_St_getStor (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    Devm.getStor (St x S M g) a = Devm.getStor x a := rfl

private theorem mint_St_getCode (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    (St x S M g).getCode a = x.getCode a := rfl

private theorem mint_operands (x : Devm) (S : List B256) (M : Mem) (g : Nat) :
    S <<+ (St x S M g).stack := by
  simpa only [List.append_nil, St.stack] using pref_append S ([] : List B256)

private theorem mint_tAAB_getStor (base : Devm) (a x : Adr) :
    Devm.getStor (temporalAccountAccessBase base a) x = Devm.getStor base x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem mint_tAAB_getCode (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem mint_size_ne {c : ByteArray} (bit : c.size.toB256 ≠ 0) : c.size ≠ 0 := by
  intro empty
  rw [empty] at bit
  exact bit rfl

/-- The three actual STATICCALL steps of a mint run, at the typed targets, with their reply
buffers and the actual extcodesize bits of the two tokens (the factory bit is in
`MintFactoryStep`). -/
def MintObservedSteps (D : Exec.Deriv) (current : Checkpoint) (sevm : Sevm)
    (out0 out1 outF : Bytes) : Prop :=
  ∃ (g0 g1 gF : B256) (S0 S1 SF : List B256) (M0 M1 MF : Mem) (c0 c1 cF : Nat)
    (w0 w1 wF d0 d1 dF : Devm),
    Blanc.Lift.StepIn D sevm (St w0 (g0 :: current.state.token0.toB256 :: S0) M0 c0)
      (.exec .staticcall) d0 ∧ d0.returnData = out0 ∧ (w0.getCode current.state.token0).size ≠ 0 ∧
    Blanc.Lift.StepIn D sevm (St w1 (g1 :: current.state.token1.toB256 :: S1) M1 c1)
      (.exec .staticcall) d1 ∧ d1.returnData = out1 ∧ (w1.getCode current.state.token1).size ≠ 0 ∧
    Blanc.Lift.StepIn D sevm (St wF (gF :: current.state.factory.toB256 :: SF) MF cF)
      (.exec .staticcall) dF ∧ dF.returnData = outF

/-- The actual factory STATICCALL step with its reply buffer and the actual extcodesize bit
checked by the bytecode before the call. -/
def MintFactoryStep (D : Exec.Deriv) (current : Checkpoint) (sevm : Sevm) (outF : Bytes) : Prop :=
  ∃ (gF : B256) (SF : List B256) (MF : Mem) (cF : Nat) (wF dF : Devm),
    Blanc.Lift.StepIn D sevm (St wF (gF :: current.state.factory.toB256 :: SF) MF cF)
      (.exec .staticcall) dF ∧ dF.returnData = outF ∧ (wF.getCode current.state.factory).size ≠ 0

/-- Per-call static-view provenance: an empty queue at an enabled precompile, or exactly the
retained static Pair turns of the actually committed child. -/
def MintViewProvenance (root : Exec.Deriv) (pair target : Adr) (views : List StaticViewTurn) :
    Prop :=
  views = [] ∧ root.sevm.benvStat.rules.isPrecomp target ∨
    ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw),
      Execution.commits raw = true ∧
      (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
      views.map Prod.fst = (Exec.retainedTargetTurnsAt pair [] childRun).filterMap Sum.getRight?

/-- **Canonical mint frame.** Every successful raw mint run at the Pair code consumes the typed
source mint over its three actual observations (token0 and token1 `balanceOf`, factory `feeTo`)
with static-view turn queues derived from the actual children of the same derivation. Under
trace-local HASH-T over the run's key universe (which includes the fee recipient row observed in
the actual factory reply), it yields the exact Pair storage, the exact raw log list (fee mint,
first-mint minimum to address zero, recipient mint, Sync, Mint), the return word, the final
unlock and the original checkpoint. -/
theorem mint_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let ctx := writerContext sevm invocation
    let recipient := (Sevm.dataWord sevm 4).toAdr
    sevm.value = 0 ∧ sevm.isStatic = false ∧
    ∃ (out0 out1 outF : Bytes), MintObservedSteps root current sevm out0 out1 outF ∧
      (WriterInj (WriterExtend K (mintTraceKeys root outF)) →
        WriterApart (WriterExtend K (mintTraceKeys root outF)) →
      let balance0 := Bytes.toB256 (out0.take 32)
      let balance1 := Bytes.toB256 (out1.take 32)
      let feeTo := (Bytes.toB256 (outF.take 32)).toAdr
      ∃ (views0 views1 viewsF : List StaticViewTurn) (final : Frame) (rets : List ChildReturn)
        (K' : WriterKey → Prop) (liquidity : Nat) (fee : FeeResult) (feeLogs : List Log),
        ExactConsumes (startTyped current ctx (.mint recipient))
          (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
            (.next (feeObservedResult out1) (staticViewTranscript views1 .done)
              (.next (feeObservedResult outF) (staticViewTranscript viewsF .done) .done)))
          { status := .success (encodeWords [liquidity.toB256]), frame := final,
            remaining := .done, childReturns := rets } ∧
        final.checkpoint = current ∧ final.context = ctx ∧
        final.current.state.unlocked = 1 ∧
        (∀ k, K' k → WriterExtend K (mintTraceKeys root outF) k) ∧
        WriterRep K' (post.getStor sevm.currentTarget) final.current.state ∧
        mintFee { current.state with unlocked := 0 } feeTo current.state.reserve0.val
          current.state.reserve1.val = .ok fee ∧
        ((fee.events = [] ∧ feeLogs = []) ∨ ∃ L : B256, L ≠ 0 ∧
          fee.events = [.transfer 0 feeTo L] ∧
          feeLogs = [lpMintRawLog sevm.currentTarget feeTo L]) ∧
        post.logs = b.logs ++ feeLogs ++
          (if fee.state.totalSupply = 0 then
            [lpMintRawLog sevm.currentTarget (0 : B256).toAdr 1000] else []) ++
          [lpMintRawLog sevm.currentTarget recipient liquidity.toB256,
            ⟨sevm.currentTarget, [updateSyncTopic], encodeWords [balance0, balance1]⟩,
            ⟨sevm.currentTarget, [mintEventTopic, sevm.caller.toB256],
              (balance0 - current.state.reserve0.val.toB256).toBytes ++
                (balance1 - current.state.reserve1.val.toB256).toBytes⟩] ∧
        post.output = encodeWords [liquidity.toB256] ∧
        MintFactoryStep root current sevm outF ∧
        (∀ picked ∈ views0 ++ views1 ++ viewsF,
          Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
          picked.1.frame.sevm.currentTarget = sevm.currentTarget ∧
          picked.1.frame.sevm.isStatic = true) ∧
        MintViewProvenance root sevm.currentTarget current.state.token0 views0 ∧
        MintViewProvenance root sevm.currentTarget current.state.token1 views1 ∧
        MintViewProvenance root sevm.currentTarget current.state.factory viewsF) := by
  intro root ctx recipient
  have source := (mintBytecode_public_source_inv (K := K) (current := current) codeEq fork rep
    invocation selector run).1
  unfold MintPublicSourceResult at source
  dsimp only at source
  obtain ⟨value, _, _, calleeGas, calleePost, callee, mem, unlockedRaw, nonstatic,
    gw0, callGas0, d0, out0, decodedGas0, gw1, callGas1, d1, out1, decodedGas1, feeGas, feePost,
    code0, call0, post0, long0, width0, answered0, decoded0, code1, call1, post1, long1, width1,
    answered1, stor0, stor1, logs1, output1, decoded1, cover0, cover1, feeRun, suffix,
    bound0, bound1, typedFinished, handlers, cache0, cache1, token0Target, token1Target,
    factoryTarget⟩ := source
  unfold MintPublicTypedFeeFinished at typedFinished
  obtain ⟨gwF, callGasF, dF, outF, callF, postF, widthF, boundF, answerF, feeImplication⟩ :=
    typedFinished
  -- raw worlds and code
  have nonemptyList : (b.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have lockedRep := rep.mint_locked_world (sevm := sevm) (b := b)
  have lockedCode : ∀ a, (mintLockedWorld sevm b).getCode a = b.getCode a := by
    intro a
    rw [mintLockedWorld, afterSstore_getCode, afterSload_getCode]
  have codeD0 : d0.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [Blanc.Lift.StepIn.codePreserve call0 sevm.currentTarget
      (by rw [mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, afterSload_getCode,
        lockedCode]; exact nonemptyList),
      mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, afterSload_getCode, lockedCode]
  have codeD1 : d1.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [Blanc.Lift.StepIn.codePreserve call1 sevm.currentTarget
      (by rw [mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, codeD0]; exact nonemptyList),
      mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, codeD0]
  have natCache0 : (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat =
      current.state.reserve0.val := by
    rw [cache0, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have natCache1 : (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat =
      current.state.reserve1.val := by
    rw [cache1, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have word0 : ((afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr.toB256 =
      current.state.token0.toB256 := by
    rw [← token0Target, toAdr_toB256]
  have word1 : (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 = current.state.token1.toB256 := by
    rw [← token1Target, toAdr_toB256]
  have wordF : feeFactoryWord sevm d1 = current.state.factory.toB256 := by
    rw [← factoryTarget]
    unfold feeFactoryWord
    rw [toAdr_toB256]
  have call0' := call0
  rw [word0] at call0'
  have call1' := call1
  rw [word1] at call1'
  have callF' := callF
  rw [wordF] at callF'
  refine ⟨value, nonstatic, out0, out1, outF,
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, call0', post0.returnData,
      by rw [mint_tAAB_getCode, ← token0Target]; exact mint_size_ne code0,
      call1', post1.returnData,
      by rw [mint_tAAB_getCode, ← token1Target]; exact mint_size_ne code1,
      callF', postF.returnData⟩, ?_⟩
  intro inj apart
  -- the three static-view turn queues
  let ctxM := mintSourceContext sevm invocation
  have good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, WriterExtend K (mintTraceKeys root outF) k :=
    fun F member target k touched => Or.inr (mintTraceKeys_frame member target k touched)
  have sub : ∀ k, K k → WriterExtend K (mintTraceKeys root outF) k := fun _ tracked => Or.inl tracked
  obtain ⟨views0, turns0, auth0, prov0⟩ :=
    pair_static_call_turns (frame := mintSourceLockedFrame current ctxM recipient)
      (request := requestFor .mintBalance0 current.state.token0 (.balanceOf ctxM.pair))
      inj apart sub sem image call0 (mint_operands _ _ _ _)
      (by rw [mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, afterSload_getCode,
        lockedCode]; exact installed)
      (by rw [mint_St_getStor, mint_tAAB_getStor, afterSload_getStor, afterSload_getStor]
          exact lockedRep)
      rfl fork ⟨1, _, post0.stack, by decide⟩ good
  obtain ⟨views1, turns1, auth1, prov1⟩ :=
    pair_static_call_turns (frame := (mintSourceLockedFrame current ctxM recipient).beginResume
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctxM.pair)))
      (request := requestFor .mintBalance1 current.state.token1 (.balanceOf ctxM.pair))
      inj apart sub sem image call1 (mint_operands _ _ _ _)
      (by change some (Devm.getCode _ sevm.currentTarget).toList = _
          rw [mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, codeD0]; exact installed)
      (by rw [mint_St_getStor, mint_tAAB_getStor, afterSload_getStor, stor0]
          exact lockedRep)
      rfl fork ⟨1, _, post1.stack, by decide⟩ good
  obtain ⟨viewsF, turnsF, authF, provF⟩ :=
    pair_static_call_turns (frame := mintSourceFeeFrame current ctxM recipient)
      (request := requestFor .mintFeeTo current.state.factory .feeTo)
      inj apart sub sem image callF (mint_operands _ _ _ _)
      (by change some (Devm.getCode _ sevm.currentTarget).toList = _
          rw [mint_St_getCode, feeFactoryCallWorld, mint_tAAB_getCode, feeFactoryLoadWorld,
            afterSload_getCode, codeD1]; exact installed)
      (by rw [mint_St_getStor, feeFactoryCallWorld, mint_tAAB_getStor, feeFactoryLoadWorld,
        afterSload_getStor, stor1]
          exact lockedRep)
      rfl fork ⟨1, _, postF.stack, by decide⟩ good
  -- discharge both freshness obligations in the trace universe
  obtain ⟨observation, dEq, outEq, rest⟩ :=
    feeImplication (mint_feeFresh_of_trace inj apart _ _ _ _ _)
  obtain ⟨frameResult, liquidity, finished, feeEq⟩ :=
    rest (mint_afterFeeFresh_of_trace inj apart (mint_feeKeys_sub _ _ _ _ _) _)
  have consumed := mint_source_exact_consumption handlers feeEq turns0 rfl turns1 rfl turnsF rfl
  obtain ⟨liq', keys, fin', d, keysEq, typedEq, wrep, halted, output, logs⟩ := frameResult
  have resume := observation.resume_mint (mintSourceFeeFrame current ctxM recipient)
    (mintBalanceObserved current.state recipient (Bytes.toB256 (out0.take 32))
      (Bytes.toB256 (out1.take 32))) rfl natCache0.symm natCache1.symm
  rw [factoryTarget, dEq, outEq] at resume
  have same := feeEq.symm.trans (resume.2.trans typedEq)
  injection same with finEq bytesEq
  subst finEq
  rw [bytesEq] at consumed
  have shape := mintAfterFee_finished_shape typedEq
  have dPost : post = d := Outcome.halted.inj halted
  subst dPost
  -- the fee branch's actual post
  have sourceResult := observation.sourceResult
  have feePostEq := Outcome.returned.inj observation.returned
  rw [observation.last, dEq, outEq] at feePostEq
  rw [dEq, outEq] at sourceResult
  obtain ⟨accept, _, _, _, logsDisj⟩ := sourceResult
  have baseLogs : (feeKLastWorld sevm dF).logs = b.logs := by
    rw [feeKLastWorld, afterSload_logs, postF.logs, feeFactoryCallWorld,
      temporalAccountAccessBase_logs, feeFactoryLoadWorld, afterSload_logs, logs1]
  rw [← feePostEq] at logsDisj
  have feeLogsFact : ∃ feeLogs : List Log, feePost.logs = b.logs ++ feeLogs ∧
      (((feeBranchSourceFee { current.state with unlocked := 0 } sevm (feeKLastWorld sevm dF)
          (Bytes.toB256 (outF.take 32))
          (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
          (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))).events = [] ∧
          feeLogs = []) ∨ ∃ L : B256, L ≠ 0 ∧
        (feeBranchSourceFee { current.state with unlocked := 0 } sevm (feeKLastWorld sevm dF)
          (Bytes.toB256 (outF.take 32))
          (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
          (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))).events =
          [.transfer 0 (Bytes.toB256 (outF.take 32)).toAdr L] ∧
        feeLogs = [lpMintRawLog sevm.currentTarget (Bytes.toB256 (outF.take 32)).toAdr L]) := by
    rcases logsDisj with ⟨events, feeLogsEq⟩ | ⟨L, nonzero, events, feeLogsEq⟩
    · exact ⟨[], by rw [feeLogsEq, baseLogs, List.append_nil], Or.inl ⟨events, rfl⟩⟩
    · exact ⟨_, by rw [feeLogsEq, baseLogs], Or.inr ⟨L, nonzero, events, rfl⟩⟩
  obtain ⟨feeLogs, feePostLogs, feeLogsShape⟩ := feeLogsFact
  rw [natCache0, natCache1] at accept
  rw [cache0, cache1] at accept feeLogsShape
  have rows := mintTraceKeys_rows root outF
  have keysSub : ∀ k, keys k → WriterExtend K (mintTraceKeys root outF) k := by
    rw [keysEq]
    intro k tracked
    split at tracked
    · rcases tracked with (old | zeroRow) | toRow
      · exact mint_feeKeys_sub _ _ _ _ _ k old
      · exact mint_single_row (Or.inr rows.1) k zeroRow
      · rw [toAdr_toB256] at toRow
        exact mint_single_row (Or.inr rows.2.1) k toRow
    · rcases tracked with old | toRow
      · exact mint_feeKeys_sub _ _ _ _ _ k old
      · rw [toAdr_toB256] at toRow
        exact mint_single_row (Or.inr rows.2.1) k toRow
  rw [cache0, cache1, toAdr_toB256, feePostLogs] at logs
  intro balance0 balance1 feeTo
  refine ⟨views0, views1, viewsF, finished,
    staticViewChildReturns (mintSourceLockedFrame current ctxM recipient)
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctxM.pair)) 0 views0 ++
      (staticViewChildReturns ((mintSourceLockedFrame current ctxM recipient).beginResume
          (requestFor .mintBalance0 current.state.token0 (.balanceOf ctxM.pair)))
          (requestFor .mintBalance1 current.state.token1 (.balanceOf ctxM.pair)) 0 views1 ++
        (staticViewChildReturns (mintSourceFeeFrame current ctxM recipient)
          (requestFor .mintFeeTo current.state.factory .feeTo) 0 viewsF ++ [])),
    keys, liq', _, feeLogs, ?_,
    ?_, ?_, ?_, ?_, ?_, accept, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact consumed
  · exact shape.1
  · exact shape.2.1
  · exact shape.2.2
  · exact keysSub
  · exact wrep
  · exact feeLogsShape
  · exact logs
  · exact output
  · refine ⟨gwF, _, _, callGasF, _, dF, callF', postF.returnData, ?_⟩
    rw [feeFactoryCallWorld, mint_tAAB_getCode, ← factoryTarget]
    exact mint_size_ne observation.code
  · intro picked member
    rcases List.mem_append.mp member with left | right
    · rcases List.mem_append.mp left with first | second
      · exact ⟨(auth0 picked first).2.2.2.2.2.1, (auth0 picked first).1,
          (auth0 picked first).2.2.2.1⟩
      · exact ⟨(auth1 picked second).2.2.2.2.2.1, (auth1 picked second).1,
          (auth1 picked second).2.2.2.1⟩
    · exact ⟨(authF picked right).2.2.2.2.2.1, (authF picked right).1,
        (authF picked right).2.2.2.1⟩
  · rcases prov0 with ⟨empty, native⟩ | derived
    · exact Or.inl ⟨empty, token0Target ▸ native⟩
    · exact Or.inr derived
  · rcases prov1 with ⟨empty, native⟩ | derived
    · exact Or.inl ⟨empty, token1Target ▸ native⟩
    · exact Or.inr derived
  · rcases provF with ⟨empty, native⟩ | derived
    · exact Or.inl ⟨empty, factoryTarget ▸ native⟩
    · exact Or.inr derived

end Blanc.Lift.UniswapV2Pair
