import Blanc.Lift.UniswapV2Pair.SwapSourceOccurrenceBalance

/-! The source suffix uses the same two observed replies and actual final image. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Source acceptance and finite storage use these same observed balance words. -/
structure SwapSourceUpdate {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    (r : SwapBalances root root.sevm b)
    (queries : SwapBalancePairSource r U (writerContext root.sevm invocation) current b frame index) where
  state : State
  event : Event
  oracle : OracleUpdate
  keys : WriterKey → Prop
  grown : ∀ k, keys k → U k
  check : let locals := swapFrontLocals root.sevm current.state
    swapCheck r.balance0 r.balance1
      (swapInputs r.balance0 r.balance1 locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val).1
      (swapInputs r.balance0 r.balance1 locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val).2
      locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok ()
  accepted : (swapPhysicalBalanceFrame1 r frame).current.state.update
    (swapPhysicalBalanceFrame1 r frame).context r.balance0 r.balance1
    current.state.reserve0.val current.state.reserve1.val = .ok (state, event, oracle)
  sync : event = .sync r.balance0.toNat r.balance1.toNat
  storage : WriterRep keys (r.finalWorld.getStor root.sevm.currentTarget) {state with unlocked := 1}
  updateLogs : (updateWorld root.sevm r.second.step.returned.devm
      (swapRawReserve0 root.sevm b) (swapRawReserve1 root.sevm b) r.balance0 r.balance1).logs =
    r.second.step.returned.devm.logs ++ [swapSyncLog root.sevm.currentTarget r.balance0 r.balance1]

/-- Pricing, update acceptance and final finite representation derive from the
original guards and the SAME physical suffix facts and carried static frame. -/
theorem swap_source_update {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    (r : SwapBalances root root.sevm b)
    (entryFacts : SwapSourcePrefix U current invocation root.sevm b)
    (queries : SwapBalancePairSource r U (writerContext root.sevm invocation) current b frame index)
    (facts : SwapSuffixFacts r) : Nonempty (SwapSourceUpdate r queries) := by
  let locals := swapFrontLocals root.sevm current.state
  let frame1 := swapPhysicalBalanceFrame1 r frame
  have raw0 : swapRawReserve0 root.sevm b = Nat.toB256 locals.reserves.reserve0.val := entryFacts.reserve0
  have raw1 : swapRawReserve1 root.sevm b = Nat.toB256 locals.reserves.reserve1.val := entryFacts.reserve1
  have boundOld0 := locals.reserves.reserve0.isLt
  have boundOld1 := locals.reserves.reserve1.isLt
  have old0 : (swapRawReserve0 root.sevm b).toNat = locals.reserves.reserve0.val := by
    rw [raw0, B256.toNat_toB256_of_lt (by omega)]
  have old1 : (swapRawReserve1 root.sevm b).toNat = locals.reserves.reserve1.val := by
    rw [raw1, B256.toNat_toB256_of_lt (by omega)]
  have guard := facts.input
  have pricing := facts.pricing
  simp only [SwapBalances.input0, SwapBalances.input1] at guard pricing
  rw [raw0, raw1] at guard pricing
  have check := swapCheck_source boundOld0 boundOld1 entryFacts.liquidity0 entryFacts.liquidity1 guard pricing
  obtain ⟨keys, sub, rep, locked⟩ := queries.second.invariant.rep
  have pair : frame1.context.pair = root.sevm.currentTarget := by
    rw [queries.second.invariant.context]; rfl
  have time : frame1.context.timestamp = root.sevm.benvStat.time := by
    rw [queries.second.invariant.context]; rfl
  have slots : ReserveSlotMatches frame1.current.state root.sevm r.second.step.returned.devm :=
    ⟨rep.fixed.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.1, rep.fixed.2.2.2.2.2.2.2.1⟩
  obtain ⟨state, event, oracle, accepted, _, _, _, sync, updateLogs⟩ :=
    update_source_result slots rep.fixed.2.2.2.2.2.2.2.2.1 rep.fixed.2.2.2.2.2.2.2.2.2.1
      time pair (by rw [old0]; exact boundOld0) (by rw [old1]; exact boundOld1)
      facts.bound0 facts.bound1
  have finalRep := (rep.mint_update time pair (by rw [old0]; exact boundOld0)
    (by rw [old1]; exact boundOld1) accepted).mint_unlock_store
  rw [old0, old1] at accepted
  refine ⟨⟨state, event, oracle, keys, sub, check, accepted, sync, ?_, ?_⟩⟩
  · rw [SwapBalances.finalWorld, afterSstore_getStor_self, Devm.addLog_getStor]
    exact finalRep
  · rw [pair] at updateLogs
    exact updateLogs

def SwapBalancePairSource.transcript {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    {r : SwapBalances root root.sevm b}
    (queries : SwapBalancePairSource r U (writerContext root.sevm invocation) current b frame index) :
    Transcript :=
  .next (feeObservedResult r.first.out) (staticViewTranscript queries.first.views .done)
    (.next (feeObservedResult r.second.out) (staticViewTranscript queries.second.views .done) .done)

def SwapBalancePairSource.childReturns {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    {r : SwapBalances root root.sevm b}
    (queries : SwapBalancePairSource r U (writerContext root.sevm invocation) current b frame index) :
    List ChildReturn :=
  let locals := swapFrontLocals root.sevm current.state
  let frame1 := swapPhysicalBalanceFrame1 r frame
  staticViewChildReturns frame (swapRequest0 frame locals) 0 queries.first.views ++
    (staticViewChildReturns frame1 (swapRequest1 frame1 locals) 0 queries.second.views ++ [])

def SwapSourceUpdate.finalFrame {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    {r : SwapBalances root root.sevm b}
    {queries : SwapBalancePairSource r U (writerContext root.sevm invocation) current b frame index}
    (updated : SwapSourceUpdate r queries) : Frame :=
  let locals := swapFrontLocals root.sevm current.state
  let frame1 := swapPhysicalBalanceFrame1 r frame
  swapFinishedFrame (frame1.beginResume (swapRequest1 frame1 locals)) updated.state updated.event
    updated.oracle (swapSourceEvent frame1 locals r.balance0 r.balance1)

/-- Both static continuations and the terminal return use these SAME observed
queues, full replies, update result and actual call-free suffix. -/
theorem swap_source_suffix_admitted {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    (r : SwapBalances root root.sevm b)
    (entryFacts : SwapSourcePrefix U current invocation root.sevm b)
    (queries : SwapBalancePairSource r U (writerContext root.sevm invocation) current b frame index)
    (updated : SwapSourceUpdate r queries) (fork : CoveredFork root.sevm.benvStat.fork) :
    AdmittedSourceConsumes LockedAuth root r.optional.callback.next index
      (swapBalancePhaseStart frame (swapFrontLocals root.sevm current.state)) queries.transcript
      {status := .success [], frame := updated.finalFrame, remaining := .done,
        childReturns := queries.childReturns} := by
  let locals := swapFrontLocals root.sevm current.state
  let frame1 := swapPhysicalBalanceFrame1 r frame
  have token0 : (swapInitialToken0 root.sevm b).toAdr = locals.token0 := by
    rw [entryFacts.token0, toAdr_toB256]; rfl
  have token1 : (swapInitialToken1 root.sevm b).toAdr = locals.token1 := by
    rw [entryFacts.token1, toAdr_toB256]; rfl
  have source0 : ∃ observed : SourceCallAt root frame (swapRequest0 frame locals)
      (feeObservedResult r.first.out) index,
      observed.call = r.first.step ∧ queries.first.views.map Prod.fst = observed.paths ∧
      ExactTurns frame (swapRequest0 frame locals) 0 (staticViewTranscript queries.first.views .done)
        {complete := true, frame := frame, childReturns :=
          staticViewChildReturns frame (swapRequest0 frame locals) 0 queries.first.views} := by
    have packet : ∃ observed : SourceCallAt root frame
        (requestFor .swapBalance0 (swapInitialToken0 root.sevm b).toAdr (.balanceOf frame.context.pair))
        (feeObservedResult r.first.out) index,
        observed.call = r.first.step ∧ queries.first.views.map Prod.fst = observed.paths ∧
        ExactTurns frame (requestFor .swapBalance0 (swapInitialToken0 root.sevm b).toAdr
          (.balanceOf frame.context.pair)) 0 (staticViewTranscript queries.first.views .done)
          {complete := true, frame := frame, childReturns := staticViewChildReturns frame
            (requestFor .swapBalance0 (swapInitialToken0 root.sevm b).toAdr
              (.balanceOf frame.context.pair)) 0 queries.first.views} :=
      ⟨queries.first.observed, queries.first.same, queries.first.mapped, queries.first.during⟩
    rw [token0] at packet
    exact packet
  have source1 : ∃ observed : SourceCallAt root frame1 (swapRequest1 frame1 locals)
      (feeObservedResult r.second.out) (index + 1),
      observed.call = r.second.step ∧ queries.second.views.map Prod.fst = observed.paths ∧
      ExactTurns frame1 (swapRequest1 frame1 locals) 0 (staticViewTranscript queries.second.views .done)
        {complete := true, frame := frame1, childReturns :=
          staticViewChildReturns frame1 (swapRequest1 frame1 locals) 0 queries.second.views} := by
    have packet : ∃ observed : SourceCallAt root frame1
        (requestFor .swapBalance1 (swapInitialToken1 root.sevm b).toAdr (.balanceOf frame1.context.pair))
        (feeObservedResult r.second.out) (index + 1),
        observed.call = r.second.step ∧ queries.second.views.map Prod.fst = observed.paths ∧
        ExactTurns frame1 (requestFor .swapBalance1 (swapInitialToken1 root.sevm b).toAdr
          (.balanceOf frame1.context.pair)) 0 (staticViewTranscript queries.second.views .done)
          {complete := true, frame := frame1, childReturns := staticViewChildReturns frame1
            (requestFor .swapBalance1 (swapInitialToken1 root.sevm b).toAdr
              (.balanceOf frame1.context.pair)) 0 queries.second.views} :=
      ⟨queries.second.observed, queries.second.same, queries.second.mapped, queries.second.during⟩
    rw [token1] at packet
    exact packet
  obtain ⟨observed0, same0, mapped0, during0⟩ := source0
  obtain ⟨observed1, same1, mapped1, during1⟩ := source1
  have last := AdmittedSourceConsumes.finished (Auth := LockedAuth) (root := root)
    (start := r.second.step.returned) (index := (index + 1) + 1) updated.finalFrame [] (r.noExecTail fork)
  have resume1 := swap_resumeBalance1 (frame := frame1) (locals := locals) r.second.long
    updated.check updated.accepted
  change resumeSegment frame1 (swapRequest1 frame1 locals) (.swapBalance1 locals r.balance0)
    (feeObservedResult r.second.out) = .finished updated.finalFrame [] at resume1
  have second := AdmittedSourceConsumes.nextCall (continuation := .swapBalance1 locals r.balance0)
    observed1 (by rw [same1]; exact r.second.gap)
    (by simp only [externalStatic, swapRequest1, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro impossible; cases impossible)
    (PositionalTurns.staticViews queries.second.views mapped1 queries.second.authentic during1)
    (by
      change AdmittedSourceConsumes LockedAuth root observed1.call.returned ((index + 1) + 1)
        (resumeSegment frame1 (swapRequest1 frame1 locals) (.swapBalance1 locals r.balance0)
          (feeObservedResult r.second.out)) .done
        {status := .success [], frame := updated.finalFrame, remaining := .done, childReturns := []}
      rw [same1]
      exact Eq.mpr (congrArg (fun segment => AdmittedSourceConsumes LockedAuth root
        r.second.step.returned ((index + 1) + 1) segment .done
        {status := .success [], frame := updated.finalFrame, remaining := .done, childReturns := []})
        resume1) last)
  have resume0 := swap_resumeBalance0 (frame := frame) (locals := locals) r.first.long
  have frameEq : frame.beginResume (swapRequest0 frame locals) = frame1 := by
    dsimp only [frame1, swapPhysicalBalanceFrame1]
    rw [token0]; rfl
  rw [frameEq] at resume0
  have first := AdmittedSourceConsumes.nextCall (continuation := .swapBalance0 locals)
    observed0 (by rw [same0]; exact r.first.gap)
    (by simp only [externalStatic, swapRequest0, requestFor, BEq.rfl, Bool.or_true]) rfl
    (by intro impossible; cases impossible)
    (PositionalTurns.staticViews queries.first.views mapped0 queries.first.authentic during0)
    (by
      change AdmittedSourceConsumes LockedAuth root observed0.call.returned (index + 1)
        (resumeSegment frame (swapRequest0 frame locals) (.swapBalance0 locals)
          (feeObservedResult r.first.out))
        (.next (feeObservedResult r.second.out) (staticViewTranscript queries.second.views .done) .done)
        {status := .success [], frame := updated.finalFrame, remaining := .done,
          childReturns := staticViewChildReturns frame1 (swapRequest1 frame1 locals) 0
            queries.second.views ++ []}
      rw [same0]
      exact Eq.mpr (congrArg (fun segment => AdmittedSourceConsumes LockedAuth root
        r.first.step.returned (index + 1) segment
        (.next (feeObservedResult r.second.out) (staticViewTranscript queries.second.views .done) .done)
        {status := .success [], frame := updated.finalFrame, remaining := .done,
          childReturns := staticViewChildReturns frame1 (swapRequest1 frame1 locals) 0
            queries.second.views ++ []}) resume0) second)
  exact first

/-- The final source frame retains the original checkpoint and writer context. -/
theorem SwapSourceUpdate.frame_facts {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    {r : SwapBalances root root.sevm b}
    {queries : SwapBalancePairSource r U (writerContext root.sevm invocation) current b frame index}
    (updated : SwapSourceUpdate r queries) :
    updated.finalFrame.checkpoint = current ∧
    updated.finalFrame.context = writerContext root.sevm invocation ∧
    updated.finalFrame.current.state.unlocked = 1 := by
  refine ⟨?_, ?_, rfl⟩
  · simpa only [SwapSourceUpdate.finalFrame, swapFinishedFrame, Frame.beginResume,
      Frame.withUpdate, Frame.withEvents] using queries.second.invariant.checkpoint
  · simpa only [SwapSourceUpdate.finalFrame, swapFinishedFrame, Frame.beginResume,
      Frame.withUpdate, Frame.withEvents] using queries.second.invariant.context

/-- The SAME source frame and physical final world have the full matching log images. -/
theorem SwapSourceUpdate.logs {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    {r : SwapBalances root root.sevm b}
    {queries : SwapBalancePairSource r U (writerContext root.sevm invocation) current b frame index}
    (updated : SwapSourceUpdate r queries)
    (entryFacts : SwapSourcePrefix U current invocation root.sevm b)
    (facts : SwapSuffixFacts r) :
    ∃ (added : List PendingLog) (raw : List Log),
      updated.finalFrame.current.logs = current.logs ++ added ∧
      r.finalWorld.logs = b.logs ++ raw ∧
      added.map (PendingLog.rawWith (swapOwnedRaw root.sevm.currentTarget)) = raw.map some := by
  let locals := swapFrontLocals root.sevm current.state
  let frame1 := swapPhysicalBalanceFrame1 r frame
  let origin := (frame1.beginResume (swapRequest1 frame1 locals)).origin
  obtain ⟨added, raw, source, rawEq, images⟩ := queries.second.invariant.logs
  have sender : frame1.context.sender = root.sevm.caller := by
    rw [queries.second.invariant.context]; rfl
  have recipient : swapTokenWord (swapRecipientWord root.sevm) = locals.recipient.toB256 := by
    rw [swapRecipientWord_eq, swapTokenWord_adr]; rfl
  have swapImage : swapOwnedRaw root.sevm.currentTarget
      (swapSourceEvent frame1 locals r.balance0 r.balance1) =
      some (swapEventLog root.sevm r.input0 r.input1 (swapAmount0Out root.sevm)
        (swapAmount1Out root.sevm) (swapRecipientWord root.sevm)) := by
    simp only [swapSourceEvent, swapOwnedRaw, swapEventLog, swapInputs,
      SwapBalances.input0, SwapBalances.input1]
    have raw0 : swapRawReserve0 root.sevm b = Nat.toB256 locals.reserves.reserve0.val := entryFacts.reserve0
    have raw1 : swapRawReserve1 root.sevm b = Nat.toB256 locals.reserves.reserve1.val := entryFacts.reserve1
    rw [raw0, raw1,
      ← swap_input_word locals.reserves.reserve0.isLt entryFacts.liquidity0,
      ← swap_input_word locals.reserves.reserve1.isLt entryFacts.liquidity1, sender, recipient]
    rfl
  refine ⟨added ++ [.owned origin (.sync r.balance0.toNat r.balance1.toNat),
    .owned origin (swapSourceEvent frame1 locals r.balance0 r.balance1)],
    raw ++ [swapSyncLog root.sevm.currentTarget r.balance0 r.balance1,
      swapEventLog root.sevm r.input0 r.input1 (swapAmount0Out root.sevm)
        (swapAmount1Out root.sevm) (swapRecipientWord root.sevm)], ?_, ?_, ?_⟩
  · change ((frame1.current.logs ++ [.owned origin updated.event]) ++
      [.owned origin (swapSourceEvent frame1 locals r.balance0 r.balance1)]) ++ [] = _
    have source' : frame1.current.logs = current.logs ++ added := source
    rw [source', updated.sync]
    simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
  · rw [SwapBalances.finalWorld, afterSstore_logs]
    change (updateWorld root.sevm r.second.step.returned.devm (swapRawReserve0 root.sevm b)
      (swapRawReserve1 root.sevm b) r.balance0 r.balance1).logs ++ [_] = _
    rw [updated.updateLogs, rawEq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [List.map_append, List.map_append, swap_rawWith_images images]
    simp only [List.map_cons, List.map_nil, PendingLog.rawWith,
      swap_sync_image facts.bound0 facts.bound1]
    exact congrArg (fun x => raw.map some ++ [some _, x]) swapImage

/-- The actual post storage represents this SAME unlocked final source frame. -/
theorem SwapSourceUpdate.post_storage {root : Exec.Deriv} {b post : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {frame : Frame} {index : Nat}
    {physical : SwapPhysicalResult root b post}
    {queries : SwapBalancePairSource physical.balances U (writerContext root.sevm invocation)
      current b frame index}
    (updated : SwapSourceUpdate physical.balances queries) :
    WriterRep updated.keys (post.getStor root.sevm.currentTarget) updated.finalFrame.current.state := by
  obtain ⟨M, gas, image⟩ := physical.image
  have postStor : post.getStor root.sevm.currentTarget =
      physical.balances.finalWorld.getStor root.sevm.currentTarget := by
    simpa only [St, Devm.getStor, Devm.getAcct, Devm.setMach_state] using
      congrArg (fun d : Devm => d.getStor root.sevm.currentTarget) image
  exact Eq.mpr (congrArg (fun storage => WriterRep updated.keys storage
    updated.finalFrame.current.state) postStor)
    (by simpa only [SwapSourceUpdate.finalFrame, swapFinishedFrame, Frame.withUpdate,
      Frame.withEvents, Frame.beginResume] using updated.storage)

/-- The actual post preserves foreign storage from the SAME post-callback world. -/
theorem SwapPhysicalResult.foreign_storage {root : Exec.Deriv} {b post : Devm}
    (physical : SwapPhysicalResult root b post) :
    ∀ a, a ≠ root.sevm.currentTarget →
      post.getStor a = physical.balances.optional.callback.world.getStor a := by
  intro a foreign
  obtain ⟨M, gas, image⟩ := physical.image
  have postStor : post.getStor a = physical.balances.finalWorld.getStor a := by
    simpa only [St, Devm.getStor, Devm.getAcct, Devm.setMach_state] using
      congrArg (fun d : Devm => d.getStor a) image
  rw [postStor, SwapBalances.finalWorld,
    afterSstore_getStor_ne root.sevm _ 12 1 a (Ne.symm foreign), Devm.addLog_getStor]
  unfold Devm.getStor
  rw [updateWorld_account_frame foreign]
  change physical.balances.second.step.returned.devm.getStor a = _
  rw [physical.balances.second.reply.stor, Blanc.Lift.temporalAccountAccessBase_getStor,
    physical.balances.first.reply.stor, Blanc.Lift.temporalAccountAccessBase_getStor]
  rfl

end Blanc.Lift.UniswapV2Pair
