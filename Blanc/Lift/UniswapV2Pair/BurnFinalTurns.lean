import Blanc.Lift.UniswapV2Pair.BurnSource
import Blanc.Lift.UniswapV2Pair.StaticViewTurns

/-! Typed consumption of Burn's two actual post-transfer balance calls. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Raw locals retained at the literal post-transfer Burn cut. -/
structure BurnFinalWords where
  supply : B256
  fee : B256
  liquidity : B256
  balance1 : B256
  balance0 : B256
  token1 : B256
  token0 : B256
  reserve1 : B256
  reserve0 : B256
  amount1 : B256
  amount0 : B256
  recipient : B256

/-- The literal stack at `0x16a3`, before the first final balance request. -/
def burnFinalStack (w : BurnFinalWords) (ρ : B256) (R : List B256) : List B256 :=
  burnPricedLocals w.supply w.fee w.liquidity w.balance1 w.balance0 w.token1 w.token0
    w.reserve1 w.reserve0 w.amount1 w.amount0 w.recipient ρ R

/-- Internal cut correspondence; the full Burn entry proof must produce this
from its fee, pricing, LP-burn and settled transfer observations. -/
structure BurnFinalCut (K : WriterKey → Prop) (frame : Frame) (priced : BurnPriced)
    (sevm : Sevm) (b : Devm) (w : BurnFinalWords) (p : B256) (n : Nat) (M : Mem) : Prop where
  rep : WriterRep K (b.getStor sevm.currentTarget) frame.current.state
  time : frame.context.timestamp = sevm.benvStat.time
  pair : frame.context.pair = sevm.currentTarget
  sender : frame.context.sender = sevm.caller
  token0 : (w.token0 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr =
    priced.observed.locals.token0
  token1 : (w.token1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr =
    priced.observed.locals.token1
  recipient : w.recipient.toAdr = priced.observed.locals.recipient
  reserve0 : w.reserve0.toNat = priced.observed.locals.reserves.reserve0.val
  reserve1 : w.reserve1.toNat = priced.observed.locals.reserves.reserve1.val
  fee : priced.feeOn = decide (w.fee ≠ 0)
  amount0 : w.amount0 = priced.amount0
  amount1 : w.amount1 = priced.amount1
  mem : PtrMem p n M
  lower : 96 ≤ p.toNat
  width : p.toNat + 1024 < 2 ^ 256

/-- The actual source request for the first post-transfer balance. -/
def burnFinalRequest0 (frame : Frame) (priced : BurnPriced) : Request :=
  requestFor .burnFinalBalance0 priced.observed.locals.token0 (.balanceOf frame.context.pair)

/-- The actual source request for the second post-transfer balance. -/
def burnFinalRequest1 (frame : Frame) (priced : BurnPriced) : Request :=
  requestFor .burnFinalBalance1 priced.observed.locals.token1 (.balanceOf frame.context.pair)

/-- A complete first reply advances only the segment and cached balance. -/
theorem burn_resumeFinalBalance0 {frame : Frame} {priced : BurnPriced} {out : Bytes}
    (long : 32 ≤ out.length) :
    resumeSegment frame (burnFinalRequest0 frame priced) (.burnFinalBalance0 priced)
        (feeObservedResult out) =
      .suspended (frame.beginResume (burnFinalRequest0 frame priced))
        (burnFinalRequest1 (frame.beginResume (burnFinalRequest0 frame priced)) priced)
        (.burnFinalBalance1 priced (Bytes.toB256 (out.take 32))) := by
  simp only [resumeSegment, decodeExternal, burnFinalRequest0, burnFinalRequest1, requestFor,
    feeObservedResult, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
    long]
  rfl

/-- The complete second reply reaches the accepted actual source finisher. -/
theorem burn_resumeFinalBalance1 {frame : Frame} {priced : BurnPriced} {out : Bytes}
    {balance0 f toWord : B256} {post : State} {event : Event} {oracle : OracleUpdate}
    (long : 32 ≤ out.length) (fee : priced.feeOn = decide (f ≠ 0))
    (recipient : toWord.toAdr = priced.observed.locals.recipient)
    (updated : frame.current.state.update frame.context balance0 (Bytes.toB256 (out.take 32))
      priced.observed.locals.reserves.reserve0.val priced.observed.locals.reserves.reserve1.val =
        .ok (post, event, oracle)) :
    resumeSegment frame (burnFinalRequest1 frame priced) (.burnFinalBalance1 priced balance0)
        (feeObservedResult out) =
      .finished (burnFinishedFrame (frame.beginResume (burnFinalRequest1 frame priced))
        post event oracle f toWord priced.amount0 priced.amount1)
        (encodeWords [priced.amount0, priced.amount1]) := by
  simp only [resumeSegment, decodeExternal, burnFinalRequest1, requestFor,
    feeObservedResult, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
    long]
  rw [fee, ← recipient]
  exact burnFinish_frame_accept updated


/-- **Burn final calls and source frame.** The literal successful continuation
supplies both replies and bounds. Its actual STATICCALLs supply exactly the
child-view queues consumed by the source, followed by the represented reserve,
oracle, kLast, Burn-log and unlock suffix. This is an internal post-transfer cut;
entry-to-cut correspondence is deliberately still a separate obligation. -/
theorem burnFinal_exact_consumes {U K : WriterKey → Prop} {frame : Frame} {priced : BurnPriced}
    {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnFinalWords} {p ρ : B256} {n G : Nat}
    {M : Mem} {R : List B256} {o : Outcome}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (cut : BurnFinalCut K frame priced sevm b w p n M)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = frame.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (burnFinalStack w ρ R) M G) t_16a3_c13 (.done o)) :
    ∃ (gw0 : B256) (cg0 : Nat) (d0 : Devm) (out0 : Bytes)
        (gw1 : B256) (cg1 : Nat) (d1 : Devm) (out1 : Bytes)
        (views0 views1 : List StaticViewTurn) (final : Frame) (rets : List ChildReturn)
        (gas finalSize : Nat),
      let t0 := w.token0 &&& 0xffffffffffffffffffffffffffffffffffffffff
      let t1 := w.token1 &&& 0xffffffffffffffffffffffffffffffffffffffff
      let Q0 := skimRequestMemory M p sevm.currentTarget
      let Q1 := skimRequestMemory (burnBalanceReplyMemory Q0 p out0) p sevm.currentTarget
      let locals0 := burnFinalStack w ρ R
      let locals1 := burnPricedLocals w.supply w.fee w.liquidity w.balance1
        (Bytes.toB256 (out0.take 32)) w.token1 w.token0 w.reserve1 w.reserve0
        w.amount1 w.amount0 w.recipient ρ R
      let access0 := temporalAccountAccessBase b t0.toAdr
      let access1 := temporalAccountAccessBase d0 t1.toAdr
      let finalM := burnSuffixMemory sevm d1 (burnBalanceReplyMemory Q1 p out1) p
        w.reserve0 w.reserve1 (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32))
        w.amount0 w.amount1
      (b.getCode t0.toAdr).size.toB256 ≠ 0 ∧ (d0.getCode t1.toAdr).size.toB256 ≠ 0 ∧
      StepIn D sevm (St access0 (gw0 :: t0 :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: t0 :: locals0) Q0 cg0) (.exec .staticcall) d0 ∧
      StepIn D sevm (St access1 (gw1 :: t1 :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: t1 :: locals1) Q1 cg1) (.exec .staticcall) d1 ∧
      StaticCallPost access0 d0 ((p + 36) :: 0x70a08231 :: t0 :: locals0) Q0 p 36 p 32 1 out0 ∧
      StaticCallPost access1 d1 ((p + 36) :: 0x70a08231 :: t1 :: locals1) Q1 p 36 p 32 1 out1 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      StaticAnswered sevm access0 t0.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out0 ∧
      StaticAnswered sevm access1 t1.toAdr (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      ExactConsumes (.suspended frame (burnFinalRequest0 frame priced) (.burnFinalBalance0 priced))
        (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
          (.next (feeObservedResult out1) (staticViewTranscript views1 .done) .done))
        { status := .success (encodeWords [priced.amount0, priced.amount1]), frame := final,
          remaining := .done, childReturns := rets } ∧
      PairViewProvenance D sevm frame t0 views0 ∧
      PairViewProvenance D sevm (frame.beginResume (burnFinalRequest0 frame priced)) t1 views1 ∧
      o = .returned (St (burnSuffixPost sevm d1 w.reserve0 w.reserve1
          (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32)) w.fee w.recipient
          w.amount0 w.amount1) (w.amount1 :: w.amount0 :: R) finalM gas) ∧
      PtrMem p finalSize finalM ∧ p.toNat + 64 ≤ finalSize ∧
      final.checkpoint = frame.checkpoint ∧ final.context = frame.context ∧
      final.current.state.unlocked = 1 ∧
      WriterRep K ((burnSuffixPost sevm d1 w.reserve0 w.reserve1
        (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32)) w.fee w.recipient
        w.amount0 w.amount1).getStor sevm.currentTarget) final.current.state ∧
      (burnSuffixPost sevm d1 w.reserve0 w.reserve1
        (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32)) w.fee w.recipient
        w.amount0 w.amount1).logs = b.logs ++
        [⟨frame.context.pair, [updateSyncTopic],
          encodeWords [Bytes.toB256 (out0.take 32), Bytes.toB256 (out1.take 32)]⟩,
         ⟨frame.context.pair,
           [burnEventTopic, frame.context.sender.toB256, priced.observed.locals.recipient.toB256],
           encodeWords [priced.amount0, priced.amount1]⟩] ∧
      (burnSuffixPost sevm d1 w.reserve0 w.reserve1
        (Bytes.toB256 (out0.take 32)) (Bytes.toB256 (out1.take 32)) w.fee w.recipient
        w.amount0 w.amount1).output = b.output ∧
      (Bytes.toB256 (out0.take 32)).toNat < 2 ^ 112 ∧
      (Bytes.toB256 (out1.take 32)).toNat < 2 ^ 112 ∧
      final.current.logs = frame.current.logs ++
        [PendingLog.owned final.origin (.sync (Bytes.toB256 (out0.take 32)).toNat
          (Bytes.toB256 (out1.take 32)).toNat),
         PendingLog.owned final.origin (.burn frame.context.sender priced.amount0
          priced.amount1 priced.observed.locals.recipient)] := by
  obtain ⟨gw0, cg0, d0, out0, gw1, cg1, d1, out1, tailGas,
      code0, code1, call0, call1, post0, post1, long0, width0, long1, width1,
      answered0, answered1, mem1, tail⟩ :=
    burnFinalBalances_inv (fun h => StepIn.toRun h) fork cut.mem cut.lower cut.width run
  obtain ⟨bound0, bound1, _, updateCallGas, updateGas, gas, _, returned, finalMem, covered⟩ :=
    burnSuffix_inv (fun h => StepIn.toRun h) fork mem1 cut.lower
      (by have width := cut.width; omega) (by simp only [List.not_mem_nil, not_false_eq_true]) tail
  have stor0 : ∀ a, d0.getStor a = b.getStor a := fun a => by
    rw [post0.stor]
    change (temporalAccountAccessBase b _).state.getStor a = b.state.getStor a
    rw [temporalAccountAccessBase_state]
  have stor1 : ∀ a, d1.getStor a = b.getStor a := fun a => by
    rw [post1.stor]
    change (temporalAccountAccessBase d0 _).state.getStor a = b.state.getStor a
    rw [temporalAccountAccessBase_state]
    exact stor0 a
  have nonemptyList : (b.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have sameCode : d0.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    have keep := Blanc.Lift.StepIn.codePreserve call0 sevm.currentTarget
      (by change ((temporalAccountAccessBase b _).getCode _).toList ≠ []
          unfold temporalAccountAccessBase
          split <;> exact nonemptyList)
    rw [keep]
    unfold temporalAccountAccessBase
    split <;> rfl
  let frame1 := frame.beginResume (burnFinalRequest0 frame priced)
  let request1 := burnFinalRequest1 frame1 priced
  let frame2 := frame1.beginResume request1
  obtain ⟨views0, turns0, auth0, derived0⟩ :=
    pair_static_call_turns (frame := frame) (request := burnFinalRequest0 frame priced) inj apart sub
      sem image call0 (by simpa only [List.append_nil, St.stack] using pref_append _ ([] : List B256))
      (by change some ((temporalAccountAccessBase b _).getCode frame.context.pair).toList = _
          rw [cut.pair]
          unfold temporalAccountAccessBase
          split <;> exact installed)
      (by change WriterRep K ((temporalAccountAccessBase b _).getStor frame.context.pair) _
          change WriterRep K ((temporalAccountAccessBase b _).state.getStor frame.context.pair) _
          rw [temporalAccountAccessBase_state, cut.pair]
          exact cut.rep)
      cut.time fork ⟨1, _, post0.stack, by decide⟩ good
  obtain ⟨views1, turns1, auth1, derived1⟩ :=
    pair_static_call_turns (frame := frame1) (request := request1) inj apart sub
      sem image call1 (by simpa only [List.append_nil, St.stack] using pref_append _ ([] : List B256))
      (by change some ((temporalAccountAccessBase d0 _).getCode frame.context.pair).toList = _
          rw [cut.pair]
          unfold temporalAccountAccessBase
          split <;> change some (d0.getCode sevm.currentTarget).toList = sem.image
          all_goals rw [sameCode]; exact installed)
      (by change WriterRep K ((temporalAccountAccessBase d0 _).getStor frame.context.pair) _
          change WriterRep K ((temporalAccountAccessBase d0 _).state.getStor frame.context.pair) _
          rw [temporalAccountAccessBase_state]
          change WriterRep K (d0.getStor frame.context.pair) frame.current.state
          rw [cut.pair, stor0]
          exact cut.rep)
      cut.time fork ⟨1, _, post1.stack, by decide⟩ good
  have rep1 : WriterRep K (d1.getStor sevm.currentTarget) frame2.current.state := by
    rw [stor1]
    exact cut.rep
  obtain ⟨sourcePost, event, oracle, updated, _, finishedRep, finishedLogs, finishedOutput⟩ :=
    burnSuffix_source_result (frame := frame2) (f := w.fee) (toWord := w.recipient)
      (amount0 := w.amount0) (amount1 := w.amount1) rep1 cut.time cut.pair cut.sender
      cut.reserve0 cut.reserve1 bound0 bound1
  let final := burnFinishedFrame frame2 sourcePost event oracle w.fee w.recipient
    priced.amount0 priced.amount1
  have logs1 : d1.logs = b.logs := by
    rw [post1.logs, temporalAccountAccessBase_logs, post0.logs, temporalAccountAccessBase_logs]
  have output1 : d1.output = b.output := by
    rw [post1.output rfl, temporalAccountAccessBase_output, post0.output rfl,
      temporalAccountAccessBase_output]
  refine ⟨gw0, cg0, d0, out0, gw1, cg1, d1, out1, views0, views1, final,
    staticViewChildReturns frame (burnFinalRequest0 frame priced) 0 views0 ++
      (staticViewChildReturns frame1 request1 0 views1 ++ []),
    gas, _, code0, code1, call0, call1, post0, post1, long0, width0, long1, width1,
    answered0, answered1, ?_, ⟨auth0, derived0⟩, ⟨auth1, derived1⟩,
    Seg.done.inj returned, finalMem, covered, rfl, rfl, rfl, ?_, ?_, ?_, bound0, bound1, ?_⟩
  · refine ExactConsumes.nextCall (result := feeObservedResult out0)
      (out := ⟨.success (encodeWords [priced.amount0, priced.amount1]), final, Transcript.done,
        staticViewChildReturns frame1 request1 0 views1 ++ []⟩) rfl
      (fun h => Bool.noConfusion h) turns0 ?_
    change ExactConsumes (resumeSegment frame (burnFinalRequest0 frame priced) (.burnFinalBalance0 priced)
      (feeObservedResult out0)) _ _
    rw [burn_resumeFinalBalance0 long0]
    refine ExactConsumes.nextCall (result := feeObservedResult out1)
      (out := ⟨.success (encodeWords [priced.amount0, priced.amount1]), final, Transcript.done, []⟩) rfl
      (fun h => Bool.noConfusion h) turns1 ?_
    change ExactConsumes (resumeSegment frame1 request1
      (.burnFinalBalance1 priced (Bytes.toB256 (out0.take 32))) (feeObservedResult out1)) _ _
    rw [burn_resumeFinalBalance1 (frame := frame1) long1 cut.fee cut.recipient updated]
    exact ExactConsumes.finished _ _
  · simpa only [cut.amount0, cut.amount1] using finishedRep
  · simpa only [frame2, frame1, Frame.beginResume, logs1, cut.recipient,
      cut.amount0, cut.amount1] using finishedLogs
  · exact finishedOutput.trans output1
  · have eventEq : event = .sync (Bytes.toB256 (out0.take 32)).toNat
        (Bytes.toB256 (out1.take 32)).toNat := by
      have accepted := updated
      simp only [State.update, bound0, bound1, dite_true, Except.ok.injEq,
        Prod.mk.injEq] at accepted
      exact accepted.2.1.symm
    simp only [final, burnFinishedFrame, Frame.withEvents, Frame.withUpdate,
      Frame.origin, frame2, frame1, Frame.beginResume, eventEq, cut.recipient,
      List.map_cons, List.map_nil, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append]

end Blanc.Lift.UniswapV2Pair
