import Blanc.Lift.UniswapV2Pair.PairWriterAbsorb
import Blanc.Lift.UniswapV2Pair.BurnPositionalLogs
import Blanc.Lift.UniswapV2Pair.BurnLogImage
import Blanc.Lift.UniswapV2Pair.BurnPositionalEntry
import Blanc.Lift.UniswapV2Pair.BurnPositionalMutable
import Blanc.Lift.UniswapV2Pair.BurnPositionalFinalSource

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Both final static calls preserve the represented Pair storage of the
same second mutable return. -/
theorem BurnSevenCalls.finalStorage {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnSevenCalls root sevm b) :
    r.final1.call.returned.devm.getStor sevm.currentTarget =
      r.five.second.returned.devm.getStor sevm.currentTarget := by
  rw [r.final1.reply.stor]
  simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
  change r.final0.call.returned.devm.getStor sevm.currentTarget =
    r.five.second.returned.devm.getStor sevm.currentTarget
  rw [r.final0.reply.stor]
  simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]

/-- The two actual static replies leave the selected second-transfer logs
unchanged before the Burn/Sync suffix. -/
theorem BurnSevenCalls.finalLogs {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnSevenCalls root sevm b) :
    r.final1.call.returned.devm.logs = r.five.second.returned.devm.logs := by
  rw [r.final1.reply.logs, temporalAccountAccessBase_logs,
    r.final0.reply.logs, temporalAccountAccessBase_logs]

/-- The transcript reads all seven retained replies; the two mutable subtrees
are exactly the selected full-slot folds. -/
def burnPositionalTranscript {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (r : BurnSevenCalls root root.sevm b)
    (first : BurnFirstMutable r.five.four U current invocation) (second : BurnSecondMutable r.five first)
    (views0 views1 viewsF finalViews0 finalViews1 : List StaticViewTurn) : Transcript :=
  .next (feeObservedResult r.five.four.three.initial.out0) (staticViewTranscript views0 .done)
    (.next (feeObservedResult r.five.four.three.initial.out1) (staticViewTranscript views1 .done)
      (.next (feeObservedResult r.five.four.three.fee.out) (staticViewTranscript viewsF .done)
        (.next (burnTransferResult r.five.four.transfer.returned.devm.returnData
          r.five.four.transfer.occurrence.slot.isSome) (mutableTranscript first.turns .done)
          (.next (burnTransferResult r.five.second.returned.devm.returnData
            r.five.second.occurrence.slot.isSome) (mutableTranscript second.turns .done)
            (.next (feeObservedResult r.final0.out) (staticViewTranscript finalViews0 .done)
              (.next (feeObservedResult r.final1.out) (staticViewTranscript finalViews1 .done) .done))))))

def burnPositionalFinalFrame {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (r : BurnSevenCalls root root.sevm b)
    {first : BurnFirstMutable r.five.four U current invocation} (second : BurnSecondMutable r.five first) : Frame :=
  let priced := r.five.four.sourcePriced current
  let frame1 := second.finalFrame.beginResume (burnFinalRequest0 second.finalFrame priced)
  frame1.beginResume (burnFinalRequest1 frame1 priced)

def burnPositionalSuffixPending {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (r : BurnSevenCalls root root.sevm b)
    {first : BurnFirstMutable r.five.four U current invocation} (second : BurnSecondMutable r.five first) :
    List PendingLog :=
  let frame := burnPositionalFinalFrame r second
  let priced := r.five.four.sourcePriced current
  [.owned frame.origin (.sync (Bytes.toB256 (r.final0.out.take 32)).toNat
      (Bytes.toB256 (r.final1.out.take 32)).toNat),
   .owned frame.origin (.burn root.sevm.caller priced.amount0 priced.amount1
      (Sevm.dataWord root.sevm 4).toAdr)]

def burnPositionalSuffixRaw {root : Exec.Deriv} {b : Devm}
    (r : BurnSevenCalls root root.sevm b) (current : Checkpoint) : List Log :=
  let priced := r.five.four.sourcePriced current
  [⟨root.sevm.currentTarget, [updateSyncTopic],
     encodeWords [Bytes.toB256 (r.final0.out.take 32), Bytes.toB256 (r.final1.out.take 32)]⟩,
   ⟨root.sevm.currentTarget,
     [burnEventTopic, root.sevm.caller.toB256, (Sevm.dataWord root.sevm 4).toAdr.toB256],
     encodeWords [priced.amount0, priced.amount1]⟩]

/-- The final frame uses the checkpoint returned by the second actual mutable
fold and the accepted update of the two actual final balance replies. -/
def burnPositionalFinished {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (r : BurnSevenCalls root root.sevm b)
    {first : BurnFirstMutable r.five.four U current invocation} (second : BurnSecondMutable r.five first)
    (updated : State) (event : Event) (oracle : OracleUpdate) : Frame :=
  let priced := r.five.four.sourcePriced current
  let frame1 := second.finalFrame.beginResume (burnFinalRequest0 second.finalFrame priced)
  let frame2 := frame1.beginResume (burnFinalRequest1 frame1 priced)
  burnFinishedFrame frame2 updated event oracle
    (feeOnWord (Bytes.toB256 (r.five.four.three.fee.out.take 32)))
    (Sevm.dataWord root.sevm 4).toAdr.toB256 priced.amount0 priced.amount1

theorem burnPositionalFinished_logs {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (r : BurnSevenCalls root root.sevm b)
    {first : BurnFirstMutable r.five.four U current invocation} (second : BurnSecondMutable r.five first)
    (updated : State) (event : Event) (oracle : OracleUpdate)
    (eventEq : event = .sync (Bytes.toB256 (r.final0.out.take 32)).toNat
      (Bytes.toB256 (r.final1.out.take 32)).toNat) :
    (burnPositionalFinished r second updated event oracle).current.logs =
      second.checkpoint.logs ++ burnPositionalSuffixPending r second := by
  simp only [burnPositionalFinished, burnFinishedFrame, Frame.withEvents, Frame.withUpdate,
    Frame.origin, Frame.beginResume, burnPositionalSuffixPending, burnPositionalFinalFrame,
    BurnSecondMutable.finalFrame, BurnFirstMutable.secondFrame, eventEq, List.map_cons,
    List.map_nil, List.append_nil, List.append_assoc, toAdr_toB256]
  rfl

def burnPositionalResult {root : Exec.Deriv} {b : Devm} {U : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} (r : BurnSevenCalls root root.sevm b)
    (first : BurnFirstMutable r.five.four U current invocation) (second : BurnSecondMutable r.five first)
    (updated : State) (event : Event) (oracle : OracleUpdate)
    (views0 views1 viewsF finalViews0 finalViews1 : List StaticViewTurn) : RunResult :=
  let frame0 := burnSourceLockedFrame current (writerContext root.sevm invocation)
    (Sevm.dataWord root.sevm 4).toAdr
  let request0 := requestFor .burnInitialBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)
  let frame1 := frame0.beginResume request0
  let request1 := requestFor .burnInitialBalance1 current.state.token1 (.balanceOf root.sevm.currentTarget)
  let priced := r.five.four.sourcePriced current
  let finalFrame1 := second.finalFrame.beginResume (burnFinalRequest0 second.finalFrame priced)
  {status := .success (encodeWords [priced.amount0, priced.amount1]),
    frame := burnPositionalFinished r second updated event oracle, remaining := .done,
    childReturns := staticViewChildReturns frame0 request0 0 views0 ++
      (staticViewChildReturns frame1 request1 0 views1 ++
        (staticViewChildReturns (burnPositionalFeeFrame current invocation root.sevm)
          (requestFor .burnFeeTo current.state.factory .feeTo) 0 viewsF ++
          (first.rets ++ (second.rets ++
            (staticViewChildReturns second.finalFrame (burnFinalRequest0 second.finalFrame priced) 0
              finalViews0 ++ staticViewChildReturns finalFrame1 (burnFinalRequest1 finalFrame1 priced) 0
                finalViews1)))))}

/-- One selected seven-call source result and its complete mutable queues. -/
structure BurnPositionalCanonicalResult (U K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (root : Exec.Deriv) (b post : Devm) where
  positions : BurnSevenCalls root root.sevm b
  first : BurnFirstMutable positions.five.four U current invocation
  second : BurnSecondMutable positions.five first
  views0 : List StaticViewTurn
  views1 : List StaticViewTurn
  viewsF : List StaticViewTurn
  finalViews0 : List StaticViewTurn
  finalViews1 : List StaticViewTurn
  updated : State
  event : Event
  oracle : OracleUpdate
  admitted : AdmittedSourceConsumes LockedAuth root root 0
    (startTyped current (writerContext root.sevm invocation) (.burn (Sevm.dataWord root.sevm 4).toAdr))
    (burnPositionalTranscript positions first second views0 views1 viewsF finalViews0 finalViews1)
    (burnPositionalResult positions first second updated event oracle
      views0 views1 viewsF finalViews0 finalViews1)
  eventEq : event = .sync (Bytes.toB256 (positions.final0.out.take 32)).toNat
    (Bytes.toB256 (positions.final1.out.take 32)).toNat
  success : root.exn = .ok post
  checkpoint : (burnPositionalFinished positions second updated event oracle).checkpoint = current
  context : (burnPositionalFinished positions second updated event oracle).context =
    writerContext root.sevm invocation
  unlocked : (burnPositionalFinished positions second updated event oracle).current.state.unlocked = 1
  keys : WriterKey → Prop
  grown : ∀ k, K k → keys k
  inside : ∀ k, keys k → U k
  storage : WriterRep keys (post.getStor root.sevm.currentTarget)
    (burnPositionalFinished positions second updated event oracle).current.state
  output : post.output = encodeWords [(positions.five.four.sourcePriced current).amount0,
    (positions.five.four.sourcePriced current).amount1]
  added : List PendingLog
  raw : List Log
  sourceLogs : (burnPositionalFinished positions second updated event oracle).current.logs =
    current.logs ++ added
  rawLogs : post.logs = b.logs ++ raw
  image : added.map (PendingLog.rawWith (burnOwnedRaw root.sevm.currentTarget)) = raw.map some

/-- Original successful-run assumptions select one admitted Burn execution,
including incoming-key growth through both actual mutable returned states. -/
theorem burn_positional_canonical {U K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots run,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    Nonempty (BurnPositionalCanonicalResult U K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  have staticFresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys K (staticViewDecodedKeys F.sevm) :=
    fun F member target => Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub
      (staticGood F member target)
  obtain ⟨positions⟩ := burn_seven_occurrences_of_success codeEq fork selector run
  obtain ⟨first⟩ := positions.five.four.firstMutable rep tracked invocation inj apart sub trace
    sem image installed rfl fork good
  obtain ⟨second⟩ := positions.five.secondMutable first rep inj apart sem image installed rfl fork good
  obtain ⟨J, insideJ, returnedRep, _⟩ := second.rep
  obtain ⟨keys, grown, inside, finalInputRep⟩ :=
    writerRep_absorb inj apart sub rep insideJ returnedRep
  have finalFresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys keys (staticViewDecodedKeys F.sevm) :=
    fun F member target => Blanc.SlotFootprint.FreshKeys.of_universe inj apart inside
      (staticGood F member target)
  obtain ⟨updated, event, oracle, finalViews0, finalViews1, accepted, finalConsumed, storage, output, logs⟩ :=
    positions.finalSourceData (Auth := LockedAuth) (frame := second.finalFrame) rep finalInputRep
      invocation rfl sem image installed rfl fork finalFresh
  let priced := positions.five.four.sourcePriced current
  let frame1 := second.finalFrame.beginResume (burnFinalRequest0 second.finalFrame priced)
  let frame2 := frame1.beginResume (burnFinalRequest1 frame1 priced)
  have lastRep : WriterRep keys (positions.final1.call.returned.devm.getStor sevm.currentTarget)
      frame2.current.state := by
    rw [positions.finalStorage]
    exact finalInputRep
  have old0 : (Nat.toB256 current.state.cachedReserves.reserve0.val).toNat =
      current.state.cachedReserves.reserve0.val :=
    B256.toNat_toB256_of_lt (lt_trans current.state.reserve0.isLt
      (by decide : 2 ^ 112 < 2 ^ 256))
  have old1 : (Nat.toB256 current.state.cachedReserves.reserve1.val).toNat =
      current.state.cachedReserves.reserve1.val :=
    B256.toNat_toB256_of_lt (lt_trans current.state.reserve1.isLt
      (by decide : 2 ^ 112 < 2 ^ 256))
  have updateResult := update_source_result_of_ok
    (old0 := Nat.toB256 current.state.cachedReserves.reserve0.val)
    (old1 := Nat.toB256 current.state.cachedReserves.reserve1.val)
    (ctx := frame2.context) (sevm := sevm) (b := positions.final1.call.returned.devm)
    ⟨lastRep.fixed.2.2.2.2.2.1, lastRep.fixed.2.2.2.2.2.2.1,
      lastRep.fixed.2.2.2.2.2.2.2.1⟩
    lastRep.fixed.2.2.2.2.2.2.2.2.1 lastRep.fixed.2.2.2.2.2.2.2.2.2.1 rfl rfl
    (by rw [old0]; exact current.state.reserve0.isLt)
    (by rw [old1]; exact current.state.reserve1.isLt)
    (by simpa only [old0, old1] using accepted)
  have secondConsumed := second.consume rfl fork finalConsumed
  have firstConsumed := first.consume secondConsumed
  obtain ⟨feeFresh, _⟩ := positions.five.four.three.feeUniverse current fork inj apart sub trace
  obtain ⟨viewsF, feeConsumed⟩ := positions.five.four.feeSource rep feeFresh tracked invocation
    sem image installed rfl fork staticFresh firstConsumed
  obtain ⟨views0, views1, consumed⟩ := positions.five.four.three.initialSource rep invocation
    sem image installed fork staticFresh feeConsumed
  obtain ⟨prefixAdded, prefixRaw, prefixPending, prefixLogs, prefixImage⟩ :=
    positions.five.four.prefixLogs rep feeFresh tracked invocation rfl fork
  obtain ⟨raw0, logs0, image0⟩ := first.rawLogs
  obtain ⟨raw1, logs1, image1⟩ := second.rawLogs
  let added := prefixAdded ++ first.added ++ second.added ++ burnPositionalSuffixPending positions second
  let raw := prefixRaw ++ raw0 ++ raw1 ++ burnPositionalSuffixRaw positions current
  have suffixImage : (burnPositionalSuffixPending positions second).map
      (PendingLog.rawWith (burnOwnedRaw sevm.currentTarget)) =
      (burnPositionalSuffixRaw positions current).map some := by
    simp only [burnPositionalSuffixPending, burnPositionalSuffixRaw, List.map_cons, List.map_nil,
      PendingLog.rawWith, burnOwnedRaw, toB256_toNat]
  have suffixLogs : post.logs = positions.five.second.returned.devm.logs ++
      burnPositionalSuffixRaw positions current := by
    have pair : second.finalFrame.context.pair = sevm.currentTarget := rfl
    have sender : second.finalFrame.context.sender = sevm.caller := rfl
    simpa only [burnPositionalSuffixRaw, positions.finalLogs, toAdr_toB256, pair, sender] using logs
  exact ⟨{
    positions := positions
    first := first
    second := second
    views0 := views0
    views1 := views1
    viewsF := viewsF
    finalViews0 := finalViews0
    finalViews1 := finalViews1
    updated := updated
    event := event
    oracle := oracle
    admitted := by
      rw [burn_start_segment_of_success invocation codeEq fork selector rep run]
      exact consumed
    eventEq := updateResult.2.2.2.1
    success := rfl
    checkpoint := rfl
    context := rfl
    unlocked := rfl
    keys := keys
    grown := grown
    inside := inside
    storage := storage
    output := output
    added := added
    raw := raw
    sourceLogs := by
      rw [burnPositionalFinished_logs positions second updated event oracle updateResult.2.2.2.1,
        second.sourceLogs, first.sourceLogs, prefixPending]
      simp only [added, List.append_assoc]
    rawLogs := by
      rw [suffixLogs, logs1, positions.five.input, St, Devm.setMach_logs, logs0, prefixLogs]
      simp only [raw, List.append_assoc]
    image := by
      simp only [added, raw, List.map_append, prefixImage,
        burn_pending_logs_preserves image0, burn_pending_logs_preserves image1, suffixImage]
  }⟩

end Blanc.Lift.UniswapV2Pair
