import Blanc.Lift.UniswapV2Pair.SwapBack
import Blanc.Lift.UniswapV2Pair.StaticViewTurns
import Blanc.AddressSlotProofs

/-! The swap back half's typed consumption: from the suspended frame whose next
request is `balanceOf(pair)` to `token0`, the two authentic static-view turn
queues, both source resumes and the finished frame, with exact Pair storage,
logs and empty output. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

private theorem swap_tAAB_getStor (base : Devm) (a x : Adr) :
    Devm.getStor (temporalAccountAccessBase base a) x = Devm.getStor base x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem swap_tAAB_getCode (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem swap_operands (x : Devm) (S : List B256) (M : Mem) (g : Nat) :
    S <<+ (St x S M g).stack := by
  simpa only [List.append_nil, St.stack] using pref_append S ([] : List B256)

private theorem swap_addLog_logs (devm : Devm) (l : Log) :
    (devm.addLog l).logs = devm.logs ++ [l] := rfl

private theorem swap_addLog_output (devm : Devm) (l : Log) :
    (devm.addLog l).output = devm.output := rfl

/-- A masked address word is the address itself. -/
theorem swapTokenWord_adr (a : Adr) : swapTokenWord a.toB256 = a.toB256 := by
  unfold swapTokenWord
  rw [B256.and_comm, show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask
    from by decide]
  change addressSlotReadWord a.toB256 = _
  rw [addressSlotReadWord_eq_toAdr_toB256, toAdr_toB256]

/-- The provenance a static-view turn queue carries for one actual STATICCALL. -/
def SwapViewProvenance (D : Exec.Deriv) (sevm : Sevm) (frame : Frame) (t : B256)
    (views : List StaticViewTurn) : Prop :=
  (∀ picked ∈ views, picked.Authentic frame) ∧
  (views = [] ∧ sevm.benvStat.rules.isPrecomp t.toAdr ∨ ∃ (child : Evm) (raw : Execution)
    (childRun : Exec child.pc child.sta child.dyna raw),
    Execution.commits raw = true ∧
    (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
    views.map Prod.fst =
      (Exec.retainedTargetTurnsAt frame.context.pair [] childRun).filterMap Sum.getRight?)

/-- The raw Sync log of the shared update. -/
def swapSyncLog (pair : Adr) (bal0 bal1 : B256) : Jaune.Log :=
  ⟨pair, [updateSyncTopic], encodeWords [bal0, bal1]⟩

/-- `swapBack_exact_consumes` together with the uint112 guard of the same run: both observed
post-callback balances are below `2^112`. -/
theorem swapBack_exact_consumes_bounds {U K : WriterKey → Prop} {frame : Frame} {locals : SwapLocals}
    {D : Exec.Deriv} {sevm : Sevm} {d : Devm} {w : SwapCutWords} {p ρ : B256} {n G : Nat}
    {M : Mem} {R : List B256} {o : Outcome}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (d.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (cut : SwapCut K frame locals sevm d w p n M)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = frame.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St d (swapCutStack w ρ R) M G) t_09c3_c5 (.done o)) :
    ∃ (out0 out1 : Bytes) (views0 views1 : List StaticViewTurn) (final : Frame)
      (rets : List ChildReturn) (post : Devm) (M' : Mem) (G' : Nat) (d0 d1 : Devm),
      SwapBalanceCall D sevm d M p w.token0
        (w.token1 :: w.token0 :: 0 :: 0 :: w.reserve1 :: w.reserve0 :: w.dataLength ::
          w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: ρ :: R) d0 out0 ∧
      SwapBalanceCall D sevm d0 (swapBalanceReply M p sevm.currentTarget out0) p w.token1
        (w.token1 :: w.token0 :: 0 :: swapBalanceWord out0 :: w.reserve1 :: w.reserve0 ::
          w.dataLength :: w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: ρ :: R)
        d1 out1 ∧
      (swapTokenWord w.token0).toAdr = locals.token0 ∧
      (swapTokenWord w.token1).toAdr = locals.token1 ∧
      swapTokenWord w.recipient = locals.recipient.toB256 ∧
      ExactConsumes (.suspended frame (swapRequest0 frame locals) (.swapBalance0 locals))
        (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
          (.next (feeObservedResult out1) (staticViewTranscript views1 .done) .done))
        { status := .success [], frame := final, remaining := .done, childReturns := rets } ∧
      SwapViewProvenance D sevm frame (swapTokenWord w.token0) views0 ∧
      SwapViewProvenance D sevm (frame.beginResume (swapRequest0 frame locals))
        (swapTokenWord w.token1) views1 ∧
      o = .returned (St post R M' G') ∧
      final.checkpoint = frame.checkpoint ∧ final.context = frame.context ∧
      final.current.state.unlocked = 1 ∧
      WriterRep K (post.getStor sevm.currentTarget) final.current.state ∧
      (∀ a, a ≠ sevm.currentTarget → post.getStor a = d.getStor a) ∧
      (∃ origin, final.current.logs = frame.current.logs ++
        [.owned origin (.sync (swapBalanceWord out0).toNat (swapBalanceWord out1).toNat),
         .owned origin (swapSourceEvent frame locals (swapBalanceWord out0) (swapBalanceWord out1))]) ∧
      post.logs = d.logs ++
        [swapSyncLog sevm.currentTarget (swapBalanceWord out0) (swapBalanceWord out1),
         swapEventLog sevm
          (swapInWord (swapBalanceWord out0) w.reserve0 w.amount0Out)
          (swapInWord (swapBalanceWord out1) w.reserve1 w.amount1Out)
          w.amount0Out w.amount1Out w.recipient] ∧
      post.output = [] ∧
      (swapBalanceWord out0).toNat < 2 ^ 112 ∧ (swapBalanceWord out1).toNat < 2 ^ 112 := by
  obtain ⟨d0, d1, out0, out1, call0, call1, guard, k, bound0, bound1, static, M', G', returned⟩ :=
    swapBack_raw_inv fork cut.mem cut.lower cut.width run
  have call0' := call0
  have call1' := call1
  obtain ⟨_, gw0, cg0, step0, post0, long0, _, _⟩ := call0
  obtain ⟨_, gw1, cg1, step1, post1, long1, _, _⟩ := call1
  have pairEq : frame.context.pair = sevm.currentTarget := cut.pair
  -- storage, code, logs and output across both static calls
  have stor0 : ∀ a, d0.getStor a = d.getStor a := fun a => by
    rw [post0.stor, swap_tAAB_getStor]
  have stor1 : ∀ a, d1.getStor a = d.getStor a := fun a => by
    rw [post1.stor, swap_tAAB_getStor, stor0]
  have nonemptyList : (d.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have code0 : d0.getCode sevm.currentTarget = d.getCode sevm.currentTarget := by
    have keep := Blanc.Lift.StepIn.codePreserve step0 sevm.currentTarget
      (by change ((temporalAccountAccessBase d _).getCode _).toList ≠ []
          rw [swap_tAAB_getCode]; exact nonemptyList)
    rw [keep]
    exact swap_tAAB_getCode _ _ _
  -- the two static-view turn queues
  let frame1 := frame.beginResume (swapRequest0 frame locals)
  obtain ⟨views0, turns0, auth0, derived0⟩ :=
    pair_static_call_turns (frame := frame) (request := swapRequest0 frame locals) inj apart sub
      sem image step0 (swap_operands _ _ _ _)
      (by change some ((temporalAccountAccessBase d _).getCode frame.context.pair).toList = _
          rw [pairEq, swap_tAAB_getCode]; exact installed)
      (by change WriterRep K ((temporalAccountAccessBase d _).getStor frame.context.pair) _
          rw [pairEq, swap_tAAB_getStor]; exact cut.rep)
      cut.time fork ⟨1, _, post0.stack, by decide⟩ good
  obtain ⟨views1, turns1, auth1, derived1⟩ :=
    pair_static_call_turns (frame := frame1) (request := swapRequest1 frame1 locals) inj apart sub
      sem image step1 (swap_operands _ _ _ _)
      (by change some ((temporalAccountAccessBase d0 _).getCode frame.context.pair).toList = _
          rw [pairEq, swap_tAAB_getCode, code0]; exact installed)
      (by change WriterRep K ((temporalAccountAccessBase d0 _).getStor frame.context.pair) _
          rw [pairEq, swap_tAAB_getStor, stor0]; exact cut.rep)
      cut.time fork ⟨1, _, post1.stack, by decide⟩ good
  -- source acceptance of the pricing check and the update
  have rb0 := locals.reserves.reserve0.isLt
  have rb1 := locals.reserves.reserve1.isLt
  rw [cut.reserve0, cut.reserve1, cut.amount0Out, cut.amount1Out] at guard k
  have check := swapCheck_source rb0 rb1 cut.out0 cut.out1 guard k
  have rep1 : WriterRep K (d1.getStor sevm.currentTarget) frame.current.state := by
    rw [stor1]; exact cut.rep
  have slots : ReserveSlotMatches frame.current.state sevm d1 := ⟨rep1.fixed.2.2.2.2.2.1,
    rep1.fixed.2.2.2.2.2.2.1, rep1.fixed.2.2.2.2.2.2.2.1⟩
  have old0 : w.reserve0.toNat = locals.reserves.reserve0.val := by
    rw [cut.reserve0, B256.toNat_toB256_of_lt (by omega)]
  have old1 : w.reserve1.toNat = locals.reserves.reserve1.val := by
    rw [cut.reserve1, B256.toNat_toB256_of_lt (by omega)]
  obtain ⟨post, event, oracle, accepted, _, _, _, eventEq, updLogs⟩ :=
    update_source_result slots rep1.fixed.2.2.2.2.2.2.2.2.1 rep1.fixed.2.2.2.2.2.2.2.2.2.1
      cut.time cut.pair (by rw [old0]; exact rb0) (by rw [old1]; exact rb1) bound0 bound1
  have postRep := (rep1.mint_update cut.time cut.pair (by rw [old0]; exact rb0)
    (by rw [old1]; exact rb1) accepted).mint_unlock_store
  rw [old0, old1] at accepted
  subst eventEq
  have logs0 : d0.logs = d.logs := by rw [post0.logs, temporalAccountAccessBase_logs]
  have logs1 : d1.logs = d.logs := by rw [post1.logs, temporalAccountAccessBase_logs, logs0]
  have output0 : d0.output = d.output := by
    rw [post0.output rfl, temporalAccountAccessBase_output]
  have output1 : d1.output = d.output := by
    rw [post1.output rfl, temporalAccountAccessBase_output, output0]
  let request1 := swapRequest1 frame1 locals
  let final := swapFinishedFrame (frame1.beginResume request1) post
    (.sync (swapBalanceWord out0).toNat (swapBalanceWord out1).toNat) oracle
    (swapSourceEvent frame1 locals (swapBalanceWord out0) (swapBalanceWord out1))
  refine ⟨out0, out1, views0, views1, final,
    staticViewChildReturns frame (swapRequest0 frame locals) 0 views0 ++
      (staticViewChildReturns frame1 request1 0 views1 ++ []),
    _, M', G', d0, d1, call0', call1',
    by rw [cut.token0, swapTokenWord_adr, toAdr_toB256],
    by rw [cut.token1, swapTokenWord_adr, toAdr_toB256],
    by rw [cut.recipient, swapTokenWord_adr], ?_, ⟨auth0, derived0⟩, ⟨auth1, derived1⟩, returned, rfl, rfl, rfl, ?_, ?_,
    ⟨(frame1.beginResume request1).origin, ?_⟩, ?_, ?_, bound0, bound1⟩
  · refine ExactConsumes.nextCall (result := feeObservedResult out0)
      (out := ⟨.success [], final, Transcript.done,
        staticViewChildReturns frame1 request1 0 views1 ++ []⟩) rfl
      (fun h => Bool.noConfusion h) turns0 ?_
    change ExactConsumes (resumeSegment frame (swapRequest0 frame locals) (.swapBalance0 locals)
      (feeObservedResult out0)) _ _
    rw [swap_resumeBalance0 long0]
    refine ExactConsumes.nextCall (result := feeObservedResult out1)
      (out := ⟨.success [], final, Transcript.done, []⟩) rfl
      (fun h => Bool.noConfusion h) turns1 ?_
    change ExactConsumes (resumeSegment frame1 request1
      (.swapBalance1 locals (swapBalanceWord out0)) (feeObservedResult out1)) _ _
    rw [swap_resumeBalance1 (frame := frame1) long1 check accepted]
    exact ExactConsumes.finished _ _
  · rw [afterSstore_getStor_self, Devm.addLog_getStor]
    exact postRep
  · intro a foreign
    rw [afterSstore_getStor_ne sevm _ 12 1 a (Ne.symm foreign), Devm.addLog_getStor]
    unfold Devm.getStor
    rw [updateWorld_account_frame foreign]
    exact stor1 a
  · simp only [final, swapFinishedFrame, Frame.withEvents, Frame.withUpdate, List.map_cons,
      List.map_nil, List.append_assoc, List.append_nil, List.cons_append, List.nil_append]
    rfl
  · rw [afterSstore_logs, swap_addLog_logs, updLogs, logs1, pairEq, List.append_assoc]
    rfl
  · rw [afterSstore_output, swap_addLog_output, updateWorld_output, output1, cut.output]

/-- **Swap back half, typed consumption.** From the post-callback cut, a
successful run of the actual body returns, and the suspended source frame
consumes exactly two `balanceOf(pair)` replies, each with the static-view turn
queue of the same actual STATICCALL, finishing with no return bytes. The Pair
storage represents the finished state (unlocked), foreign storage is untouched,
the raw logs are the `Sync` and `Swap` images, and the output stays empty. -/
theorem swapBack_exact_consumes {U K : WriterKey → Prop} {frame : Frame} {locals : SwapLocals}
    {D : Exec.Deriv} {sevm : Sevm} {d : Devm} {w : SwapCutWords} {p ρ : B256} {n G : Nat}
    {M : Mem} {R : List B256} {o : Outcome}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (d.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (cut : SwapCut K frame locals sevm d w p n M)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = frame.context.pair →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St d (swapCutStack w ρ R) M G) t_09c3_c5 (.done o)) :
    ∃ (out0 out1 : Bytes) (views0 views1 : List StaticViewTurn) (final : Frame)
      (rets : List ChildReturn) (post : Devm) (M' : Mem) (G' : Nat) (d0 d1 : Devm),
      SwapBalanceCall D sevm d M p w.token0
        (w.token1 :: w.token0 :: 0 :: 0 :: w.reserve1 :: w.reserve0 :: w.dataLength ::
          w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: ρ :: R) d0 out0 ∧
      SwapBalanceCall D sevm d0 (swapBalanceReply M p sevm.currentTarget out0) p w.token1
        (w.token1 :: w.token0 :: 0 :: swapBalanceWord out0 :: w.reserve1 :: w.reserve0 ::
          w.dataLength :: w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: ρ :: R)
        d1 out1 ∧
      (swapTokenWord w.token0).toAdr = locals.token0 ∧
      (swapTokenWord w.token1).toAdr = locals.token1 ∧
      swapTokenWord w.recipient = locals.recipient.toB256 ∧
      ExactConsumes (.suspended frame (swapRequest0 frame locals) (.swapBalance0 locals))
        (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
          (.next (feeObservedResult out1) (staticViewTranscript views1 .done) .done))
        { status := .success [], frame := final, remaining := .done, childReturns := rets } ∧
      SwapViewProvenance D sevm frame (swapTokenWord w.token0) views0 ∧
      SwapViewProvenance D sevm (frame.beginResume (swapRequest0 frame locals))
        (swapTokenWord w.token1) views1 ∧
      o = .returned (St post R M' G') ∧
      final.checkpoint = frame.checkpoint ∧ final.context = frame.context ∧
      final.current.state.unlocked = 1 ∧
      WriterRep K (post.getStor sevm.currentTarget) final.current.state ∧
      (∀ a, a ≠ sevm.currentTarget → post.getStor a = d.getStor a) ∧
      (∃ origin, final.current.logs = frame.current.logs ++
        [.owned origin (.sync (swapBalanceWord out0).toNat (swapBalanceWord out1).toNat),
         .owned origin (swapSourceEvent frame locals (swapBalanceWord out0) (swapBalanceWord out1))]) ∧
      post.logs = d.logs ++
        [swapSyncLog sevm.currentTarget (swapBalanceWord out0) (swapBalanceWord out1),
         swapEventLog sevm
          (swapInWord (swapBalanceWord out0) w.reserve0 w.amount0Out)
          (swapInWord (swapBalanceWord out1) w.reserve1 w.amount1Out)
          w.amount0Out w.amount1Out w.recipient] ∧
      post.output = [] := by
  obtain ⟨out0, out1, views0, views1, final, rets, post, M', G', d0, d1, call0, call1, token0,
    token1, recipient, consumed, prov0, prov1, returned, checkpoint, context, unlocked, rep, foreign,
    logs, rawLogs, output, _, _⟩ :=
    swapBack_exact_consumes_bounds inj apart sub sem image installed fork cut good run
  exact ⟨out0, out1, views0, views1, final, rets, post, M', G', d0, d1, call0, call1, token0, token1,
    recipient, consumed, prov0, prov1, returned, checkpoint, context, unlocked, rep, foreign, logs,
    rawLogs, output⟩

end Blanc.Lift.UniswapV2Pair
