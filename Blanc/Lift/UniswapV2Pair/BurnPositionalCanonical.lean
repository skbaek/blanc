import Blanc.Lift.UniswapV2Pair.PairWriterAbsorb
import Blanc.Lift.UniswapV2Pair.BurnLogImage
import Blanc.Lift.UniswapV2Pair.BurnPositionalEntry
import Blanc.Lift.UniswapV2Pair.BurnPositionalMutable
import Blanc.Lift.UniswapV2Pair.BurnPositionalFinalSource

namespace Blanc.Lift.UniswapV2Pair
open Jaune

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
  obtain ⟨updated, event, oracle, finalViews0, finalViews1, finalConsumed, storage, output, logs⟩ :=
    positions.finalSource (Auth := LockedAuth) (frame := second.finalFrame) rep finalInputRep
      invocation rfl sem image installed rfl fork finalFresh
  have secondConsumed := second.consume rfl fork finalConsumed
  have firstConsumed := first.consume secondConsumed
  obtain ⟨feeFresh, _⟩ := positions.five.four.three.feeUniverse current fork inj apart sub trace
  obtain ⟨viewsF, feeConsumed⟩ := positions.five.four.feeSource rep feeFresh tracked invocation
    sem image installed rfl fork staticFresh firstConsumed
  obtain ⟨views0, views1, consumed⟩ := positions.five.four.three.initialSource rep invocation
    sem image installed fork staticFresh feeConsumed
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
    success := rfl
    checkpoint := rfl
    context := rfl
    unlocked := rfl
    keys := keys
    grown := grown
    inside := inside
    storage := storage
    output := output
  }⟩

end Blanc.Lift.UniswapV2Pair
