import Blanc.Lift.UniswapV2Pair.BurnFinalTurns
import Blanc.Lift.UniswapV2Pair.LockedSupply
import Blanc.Lift.UniswapV2Pair.SkimSource

/-! Actual mutable transfer queues for the Burn source continuation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- A successful mutable call either executes an enabled precompile without a
code frame, or its committed child supplies exactly the retained ordered turns.
The Boolean records this distinction for the source's no-code turn control. -/
def PairMutableProvenance (D : Exec.Deriv) (sevm : Sevm) (token : B256)
    (entered : Bool) (turns : List MutableTurn) : Prop :=
  (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
  ((entered = false ∧ turns = [] ∧ sevm.benvStat.rules.isPrecomp token.toAdr) ∨
    (entered = true ∧ ∃ (child : Evm) (raw : Execution)
      (childRun : Exec child.pc child.sta child.dyna raw)
      (committed : Execution.commits raw = true),
      (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
      turns.map MutableTurn.event = Exec.targetLogEventsFrom sevm.currentTarget [] 0 childRun committed))

private theorem locked_success_call_turns {U : WriterKey → Prop}
    {D : Exec.Deriv} {frame : Frame} {request : Request} {sevm : Sevm} {pre d : Devm}
    {g token value ii sz oi os : B256} {xs : List B256}
    (inj : WriterInj U) (apart : WriterApart U) (sem : CodeSem)
    (image : sem.image = some code.toList)
    (call : StepIn D sevm pre (.exec .call) d)
    (operands : (g :: token :: value :: ii :: sz :: oi :: os :: xs) <<+ pre.stack)
    (flag : ∃ f rest, d.stack = f :: rest ∧ f ≠ 0)
    (pair : frame.context.pair = sevm.currentTarget)
    (mutable : externalStatic frame request = false)
    (installed : some (pre.getCode sevm.currentTarget).toList = sem.image)
    (rep : LockedRep U frame.current.state (pre.getStor sevm.currentTarget))
    (time : frame.context.timestamp = sevm.benvStat.time)
    (fork : CoveredFork sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F) :
    ∃ (turns : List MutableTurn) (c : Checkpoint) (added : List PendingLog)
      (rets : List ChildReturn) (entered : Bool),
      ExactTurns frame request 0 (mutableTranscript turns .done)
        { complete := true, frame := { frame with current := c }, childReturns := rets } ∧
      LockedRep U c.state (d.getStor sevm.currentTarget) ∧
      c.logs = frame.current.logs ++ added ∧
      (∃ L : List Log, d.logs = pre.logs ++ L ∧
        added.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L.map some) ∧
      PairMutableProvenance D sevm token entered turns ∧
      (entered = false → mutableTranscript turns .done = .done) := by
  obtain ⟨turns, c, added, rets, during, auth, rep', logs, raw, derived⟩ :=
    mutable_call_turns (frame := frame) (request := request)
      (lockedPairSupply inj apart sem image sevm.currentTarget)
      (fun _ _ _ same h => LockedRep.congr same h) sem image call (Or.inl rfl)
      pair mutable installed rep time fork good
  rcases derived with ⟨empty, _, _, reason⟩ |
    ⟨child, execution, childRun, committed, _, roots, events, _⟩
  · rcases reason with none | ⟨child, execution, childRun, rolled⟩
    · refine ⟨turns, c, added, rets, false, during, rep', logs, raw,
        ⟨auth, Or.inl ⟨rfl, empty, Xinst.call_none_precompile fork operands none flag⟩⟩, ?_⟩
      intro _
      rw [empty]
      rfl
    · exact (rolled (Xinst.call_run_flag_commits fork (Or.inl rfl) childRun flag)).elim
  · exact ⟨turns, c, added, rets, true, during, rep', logs, raw,
      ⟨auth, Or.inr ⟨rfl, child, execution, childRun, committed, roots, events⟩⟩,
      fun h => Bool.noConfusion h⟩

/-- A transfer result retains the actual complete reply and frame-entry bit. -/
def burnTransferResult (out : Bytes) (entered : Bool) : ExternalResult :=
  { success := true, returndata := out, codeExists := entered, recoveryOutput := 0 }

def burnTransferRequest0 (priced : BurnPriced) : Request :=
  requestFor .burnTransfer0 priced.observed.locals.token0
    (.transfer priced.observed.locals.recipient priced.amount0)

def burnTransferRequest1 (priced : BurnPriced) : Request :=
  requestFor .burnTransfer1 priced.observed.locals.token1
    (.transfer priced.observed.locals.recipient priced.amount1)

private theorem burn_resumeTransfer0 {frame : Frame} {priced : BurnPriced}
    {out : Bytes} {entered : Bool} (accepted : SkimTransferAccepted out) :
    resumeSegment frame (burnTransferRequest0 priced) (.burnTransfer0 priced)
        (burnTransferResult out entered) =
      .suspended (frame.beginResume (burnTransferRequest0 priced))
        (burnTransferRequest1 priced) (.burnTransfer1 priced) := by
  have decoded : decodeExternal (burnTransferRequest0 priced) (burnTransferResult out entered) =
      .ok .unit := skim_decodeTransfer rfl rfl rfl accepted
  simp only [resumeSegment, decoded, Frame.suspend, burnTransferRequest1]

private theorem burn_resumeTransfer1 {frame : Frame} {priced : BurnPriced}
    {out : Bytes} {entered : Bool} (accepted : SkimTransferAccepted out) :
    resumeSegment frame (burnTransferRequest1 priced) (.burnTransfer1 priced)
        (burnTransferResult out entered) =
      .suspended (frame.beginResume (burnTransferRequest1 priced))
        (burnFinalRequest0 (frame.beginResume (burnTransferRequest1 priced)) priced)
        (.burnFinalBalance0 priced) := by
  have decoded : decodeExternal (burnTransferRequest1 priced) (burnTransferResult out entered) =
      .ok .unit := skim_decodeTransfer rfl rfl rfl accepted
  simp only [resumeSegment, decoded, Frame.suspend, burnFinalRequest0]

/-- The pre-transfer frame shares the cached final locals and initial pointer,
with the Pair lock still held and the transfer decoder's zero sentinel intact. -/
structure BurnTransferCut (K : WriterKey → Prop) (frame : Frame) (priced : BurnPriced)
    (sevm : Sevm) (b : Devm) (w : BurnFinalWords) (M : Mem) : Prop
    extends BurnFinalCut K frame priced sevm b w 128 192 M where
  locked : frame.current.state.unlocked = 0
  nonstatic : frame.context.isStatic = false
  sentinel : memWord M 96 = 0

/-- The two real transfer CALLs, including success flags and exact ABI inputs. -/
def BurnTransferCalls (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (w : BurnFinalWords)
    (M : Mem) (ρ : B256) (R : List B256) (d0 d1 : Devm) : Prop :=
  let locals := burnFinalStack w ρ R
  let t0 := w.token0 &&& 0xffffffffffffffffffffffffffffffffffffffff
  let t1 := w.token1 &&& 0xffffffffffffffffffffffffffffffffffffffff
  let mid := if d0.returnData = [] then d0.memory else safeTransfer_reply292Memory d0.memory d0.returnData
  let p := burnFirstTransferPointer d0.returnData
  let N := safeTransfer_dynamicCallMemory mid p w.amount1 w.recipient
  ∃ (gw0 gw1 : B256) (cg0 cg1 : Nat),
    StepIn D sevm (St b (gw0 :: t0 :: 0 :: 292 :: 68 :: 292 :: 0 ::
      360 :: t0 :: 96 :: 0 :: w.amount0 :: w.recipient :: w.token0 :: 0x1698 :: locals)
      (safeTransfer_call128Memory M w.amount0 w.recipient) cg0) (.exec .call) d0 ∧
    StepIn D sevm (St d0 (gw1 :: t1 :: 0 :: (p + 164) :: 68 :: (p + 164) :: 0 ::
      (68 + (p + 164)) :: t1 :: 96 :: 0 :: w.amount1 :: w.recipient :: w.token1 :: 0x16a3 :: locals)
      N cg1) (.exec .call) d1 ∧
    d0.stack = 1 :: 360 :: t0 :: 96 :: 0 :: w.amount0 :: w.recipient :: w.token0 :: 0x1698 :: locals ∧
    d1.stack = 1 :: (68 + (p + 164)) :: t1 :: 96 :: 0 :: w.amount1 :: w.recipient ::
      w.token1 :: 0x16a3 :: locals ∧
    ((safeTransfer_call128Memory M w.amount0 w.recipient).read 292 68).1 =
      abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& w.recipient).toBytes ++ w.amount0.toBytes ∧
    (N.read (p + 164).toNat 68).1 = abiSelectorBytes 0xa9059cbb ++
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& w.recipient).toBytes ++ w.amount1.toBytes ∧
    d0.returnData.length < 2 ^ 160 ∧ d1.returnData.length < 2 ^ 160 ∧
    SkimTransferAccepted d0.returnData ∧ SkimTransferAccepted d1.returnData

/-- **Actual Burn transfers produce the final source cut.** Each mutable queue
comes from its own CALL, admits all legal locked Pair reentries and retains foreign
logs in order. Cached tokens, reserves and payout amounts survive child state changes.
The final pointer width is derived from the two independent actual replies. -/
theorem burnTransfers_source_cut {U K : WriterKey → Prop} {frame : Frame} {priced : BurnPriced}
    {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnFinalWords} {ρ : B256}
    {G : Nat} {M : Mem} {R : List B256} {o : Outcome}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork) (cut : BurnTransferCut K frame priced sevm b w M)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (burnFinalStack w ρ R) M G) t_168d_c13 (.done o)) :
    ∃ (K2 : WriterKey → Prop) (d0 d1 : Devm) (entered0 entered1 : Bool)
      (turns0 turns1 : List MutableTurn) (rets0 rets1 : List ChildReturn)
      (afterTransfers : Frame) (N : Mem) (n gas : Nat),
      (∀ k, K2 k → U k) ∧
      BurnTransferCalls D sevm b w M ρ R d0 d1 ∧
      PairMutableProvenance D sevm (w.token0 &&& 0xffffffffffffffffffffffffffffffffffffffff)
        entered0 turns0 ∧
      PairMutableProvenance D sevm (w.token1 &&& 0xffffffffffffffffffffffffffffffffffffffff)
        entered1 turns1 ∧
      afterTransfers.checkpoint = frame.checkpoint ∧ afterTransfers.context = frame.context ∧
      BurnFinalCut K2 afterTransfers priced sevm d1 w
        (burnSecondTransferPointer d0.returnData d1.returnData) n N ∧
      some (d1.getCode sevm.currentTarget).toList = sem.image ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm [] (St d1 (burnFinalStack w ρ R) N gas)
        t_16a3_c13 (.done o) ∧
      (∃ (added0 added1 : List PendingLog) (L0 L1 : List Log),
        afterTransfers.current.logs = frame.current.logs ++ added0 ++ added1 ∧
        d1.logs = b.logs ++ L0 ++ L1 ∧
        added0.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L0.map some ∧
        added1.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L1.map some) ∧
      ∀ (tail : Transcript) (out : RunResult),
        ExactConsumes (.suspended afterTransfers (burnFinalRequest0 afterTransfers priced)
          (.burnFinalBalance0 priced)) tail out →
        ExactConsumes (.suspended frame (burnTransferRequest0 priced) (.burnTransfer0 priced))
          (.next (burnTransferResult d0.returnData entered0) (mutableTranscript turns0 .done)
            (.next (burnTransferResult d1.returnData entered1) (mutableTranscript turns1 .done) tail))
          { out with childReturns := rets0 ++ (rets1 ++ out.childReturns) } := by
  obtain ⟨gw0, cg0, d0, residual0, gw1, cg1, d1, residual1,
      call0, call1, flag0, flag1, data0, data1, mem0, mem1, output0, output1,
      width0, width1, accepted0, accepted1, _, _, _, finalMem, _, tail⟩ :=
    burnTransfers_caller_inv (fun h => StepIn.toRun h) fork cut.mem cut.sentinel run
  have accepted0' : SkimTransferAccepted d0.returnData := by
    rcases accepted0 with empty | ⟨long, nonzero⟩
    · exact Or.inl empty
    · refine Or.inr ⟨long, ?_⟩
      simpa only [List.sliceD, List.drop_zero, List.takeD_eq_take _ long] using nonzero
  have accepted1' : SkimTransferAccepted d1.returnData := by
    rcases accepted1 with empty | ⟨long, nonzero⟩
    · exact Or.inl empty
    · refine Or.inr ⟨long, ?_⟩
      simpa only [List.sliceD, List.drop_zero, List.takeD_eq_take _ long] using nonzero
  have nonemptyList : (b.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have code0 : d0.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    exact StepIn.codePreserve call0 sevm.currentTarget nonemptyList
  have code1 : d1.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    have nonempty0 : (d0.getCode sevm.currentTarget).toList ≠ [] := by
      rw [code0]
      exact nonemptyList
    exact (StepIn.codePreserve call1 sevm.currentTarget nonempty0).trans code0
  obtain ⟨turns0, c0, added0, rets0, entered0, during0, rep0, logs0, ⟨L0, raw0, images0⟩,
      provenance0, noCode0⟩ :=
    locked_success_call_turns (frame := frame) (request := burnTransferRequest0 priced)
      inj apart sem image call0 (by simpa only [List.append_nil, St.stack] using pref_append _ ([] : List B256)) ⟨1, _, flag0, by decide⟩ cut.pair
      (by simp only [externalStatic, burnTransferRequest0, requestFor, cut.nonstatic,
          Bool.false_or]; rfl) installed ⟨K, sub, cut.rep, cut.locked⟩ cut.time fork good
  let frame1 := ({ frame with current := c0 } : Frame).beginResume (burnTransferRequest0 priced)
  obtain ⟨K1, sub1, wrep0, locked0⟩ := rep0
  obtain ⟨turns1, c1, added1, rets1, entered1, during1, rep1, logs1, ⟨L1, raw1, images1⟩,
      provenance1, noCode1⟩ :=
    locked_success_call_turns (frame := frame1) (request := burnTransferRequest1 priced)
      inj apart sem image call1 (by simpa only [List.append_nil, St.stack] using pref_append _ ([] : List B256)) ⟨1, _, flag1, by decide⟩ cut.pair
      (by simp only [externalStatic, burnTransferRequest1, requestFor, frame1,
          Frame.beginResume, cut.nonstatic, Bool.false_or]; rfl)
      (by change some (d0.getCode sevm.currentTarget).toList = _; rw [code0]; exact installed)
      ⟨K1, sub1, wrep0, locked0⟩ cut.time fork good
  obtain ⟨K2, sub2, wrep1, locked1⟩ := rep1
  let frame2 := ({ frame1 with current := c1 } : Frame).beginResume (burnTransferRequest1 priced)
  obtain ⟨lower, width⟩ := burnFinalPointer_bounds width0 width1
  have finalCut : BurnFinalCut K2 frame2 priced sevm d1 w
      (burnSecondTransferPointer d0.returnData d1.returnData) _ _ :=
    ⟨wrep1, cut.time, cut.pair, cut.sender, cut.token0, cut.token1, cut.recipient,
      cut.reserve0, cut.reserve1, cut.fee, cut.amount0, cut.amount1, finalMem, lower, width⟩
  refine ⟨K2, d0, d1, entered0, entered1, turns0, turns1, rets0, rets1, frame2, _, _, residual1,
    sub2, ⟨gw0, gw1, cg0, cg1, call0, call1, flag0, flag1, data0, data1,
      width0, width1, accepted0', accepted1'⟩, provenance0, provenance1, rfl, rfl, finalCut,
    ?_, tail, ⟨added0, added1, L0, L1, ?_, ?_, images0, images1⟩, ?_⟩
  · rw [code1]
    exact installed
  · change c1.logs = _
    rw [logs1]
    change c0.logs ++ added1 = _
    rw [logs0]
  · change d1.logs = d0.logs ++ L1 at raw1
    change d0.logs = b.logs ++ L0 at raw0
    rw [raw1, raw0]
  · intro tail out rest
    refine ExactConsumes.nextCall (result := burnTransferResult d0.returnData entered0)
      (out := { out with childReturns := rets1 ++ out.childReturns }) rfl noCode0 during0 ?_
    change ExactConsumes (resumeSegment { frame with current := c0 }
      (burnTransferRequest0 priced) (.burnTransfer0 priced)
      (burnTransferResult d0.returnData entered0)) _ _
    rw [burn_resumeTransfer0 accepted0']
    refine ExactConsumes.nextCall (result := burnTransferResult d1.returnData entered1)
      (out := out) rfl noCode1 during1 ?_
    change ExactConsumes (resumeSegment { frame1 with current := c1 }
      (burnTransferRequest1 priced) (.burnTransfer1 priced)
      (burnTransferResult d1.returnData entered1)) _ _
    rw [burn_resumeTransfer1 accepted1']
    exact rest

/-- Complete observable result of the actual transfer/final-balance source suffix. -/
def BurnTransferFinished (U : WriterKey → Prop) (frame : Frame) (priced : BurnPriced)
    (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (w : BurnFinalWords)
    (M : Mem) (ρ : B256) (R : List B256) (o : Outcome)
    (start : SegmentResult := .suspended frame (burnTransferRequest0 priced) (.burnTransfer0 priced))
    (wrap : Transcript → Transcript := id) (childPrefix : List ChildReturn := []) : Prop :=
    ∃ (K' : WriterKey → Prop) (d0 d1 : Devm) (entered0 entered1 : Bool)
      (turns0 turns1 : List MutableTurn) (final : Frame) (rets : List ChildReturn)
      (transcript : Transcript) (post : Devm) (finalM : Mem) (gas n : Nat)
      (balance0 balance1 : B256) (added0 added1 : List PendingLog) (L0 L1 : List Log),
      (∀ k, K' k → U k) ∧ BurnTransferCalls D sevm b w M ρ R d0 d1 ∧
      PairMutableProvenance D sevm (w.token0 &&& 0xffffffffffffffffffffffffffffffffffffffff)
        entered0 turns0 ∧
      PairMutableProvenance D sevm (w.token1 &&& 0xffffffffffffffffffffffffffffffffffffffff)
        entered1 turns1 ∧
      ExactConsumes start (wrap transcript)
        { status := .success (encodeWords [priced.amount0, priced.amount1]),
          frame := final, remaining := .done, childReturns := childPrefix ++ rets } ∧
      o = .returned (St post (w.amount1 :: w.amount0 :: R) finalM gas) ∧
      WriterRep K' (post.getStor sevm.currentTarget) final.current.state ∧
      final.checkpoint = frame.checkpoint ∧ final.context = frame.context ∧
      final.current.state.unlocked = 1 ∧
      PtrMem (burnSecondTransferPointer d0.returnData d1.returnData) n finalM ∧
      (burnSecondTransferPointer d0.returnData d1.returnData).toNat + 64 ≤ n ∧
      balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧
      d1.logs = b.logs ++ L0 ++ L1 ∧
      added0.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L0.map some ∧
      added1.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L1.map some ∧
      post.logs = b.logs ++ L0 ++ L1 ++
        [⟨frame.context.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩,
         ⟨frame.context.pair,
           [burnEventTopic, frame.context.sender.toB256, priced.observed.locals.recipient.toB256],
           encodeWords [priced.amount0, priced.amount1]⟩] ∧
      96 ≤ (burnSecondTransferPointer d0.returnData d1.returnData).toNat ∧
      (burnSecondTransferPointer d0.returnData d1.returnData).toNat + 64 < 2 ^ 256 ∧
      final.current.logs = frame.current.logs ++ added0 ++ added1 ++
        [PendingLog.owned final.origin (.sync balance0.toNat balance1.toNat),
         PendingLog.owned final.origin (.burn frame.context.sender priced.amount0
          priced.amount1 priced.observed.locals.recipient)]

/-- **Burn transfers through the final source return.** Starting at the produced
post-pricing cut, the actual mutable queues and final balance views consume the
source to its exact payout, represented returned world and unlock. Full pc-zero
entry, initial queries and the fee-source prefix remain separate producers. -/
theorem burnTransfers_source_finished {U K : WriterKey → Prop} {frame : Frame} {priced : BurnPriced}
    {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnFinalWords} {ρ : B256}
    {G : Nat} {M : Mem} {R : List B256} {o : Outcome}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork) (cut : BurnTransferCut K frame priced sevm b w M)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = frame.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (burnFinalStack w ρ R) M G) t_168d_c13 (.done o)) :
    BurnTransferFinished U frame priced D sevm b w M ρ R o := by
  obtain ⟨K2, d0, d1, entered0, entered1, turns0, turns1, rets0, rets1, frame2, N, n, gas,
      sub2, calls, provenance0, provenance1, checkpoint2, context2, finalCut,
      installed2, tail, ⟨added0, added1, L0, L1, pending, raw, images0, images1⟩, lift⟩ :=
    burnTransfers_source_cut inj apart sub sem image installed fork cut good run
  obtain ⟨gw0, cg0, q0, out0, gw1, cg1, q1, out1, views0, views1, final, rets,
      finalGas, finalSize, _, _, _, _, _, _, _, _, _, _, _, _,
      consumed, _, _, returned, finalMem, covered, checkpoint, context, unlocked,
      finalRep, finalLogs, _, bound0, bound1, finalPending⟩ :=
    burnFinal_exact_consumes inj apart sub2 sem image installed2 fork finalCut
      (fun F member target k touched => staticGood F member (target.trans (congrArg Context.pair context2)) k touched)
      tail
  have finished := lift _ _ consumed
  refine ⟨K2, d0, d1, entered0, entered1, turns0, turns1, final,
    rets0 ++ (rets1 ++ rets), _, _, _, finalGas, finalSize,
    Bytes.toB256 (out0.take 32), Bytes.toB256 (out1.take 32), added0, added1, L0, L1,
    sub2, calls, provenance0, provenance1, finished, returned, finalRep,
    checkpoint.trans checkpoint2, context.trans context2, unlocked,
    finalMem, covered, bound0, bound1, raw, images0, images1, ?_,
    finalCut.lower, (by have width := finalCut.width; omega), ?_⟩
  · rw [finalLogs, raw, context2]
  · rw [finalPending, pending, context2]

end Blanc.Lift.UniswapV2Pair
