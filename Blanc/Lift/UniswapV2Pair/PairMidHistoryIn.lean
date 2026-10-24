import Blanc.Lift.UniswapV2Pair.PairHistoryIn
import Blanc.ExecutionAccountingMidHistoryIn
import Blanc.ExecutionMidHistoryInFacts

/-!
# The Uniswap V2 Pair's committed history from the middle of a block

The committed-history results of `PairHistoryIn.lean` over a history that starts right after one
transaction of a retained configured block (`MidHistoryTraceIn`):

* `pairMidTouchedKeysIn`, `committedPairFramesMidIn` — the HASH-T rows and the committed
  non-static Pair frames of a mid history, as `pairHistoryTouchedKeysIn` and
  `committedPairFramesIn`;
* `pair_mid_admittedIn` — every Pair frame root of a mid history is admitted, each per-root fact
  read from the retained block holding the root (`MidHistoryTraceIn.rawFrames_entered`,
  `rootEntryIn`, `calldata_bound`);
* `pair_mid_history_committed_withIn` and `pair_mid_history_initialized_withIn` — the statements
  of `pair_history_committed_withIn` and `pair_history_initialized_withIn` over a mid history,
  with the start state in place of the checkpoint state (`midHistoryIn`).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- HASH-T rows of a mid history: the rows of every Pair frame entered below every raw Pair frame
root of the trace, rolled-back frames included. -/
noncomputable def pairMidTouchedKeysIn {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (pair : Adr) (trace : MidHistoryTraceIn F cfg start future) :
    List WriterKey :=
  trace.rawFrames.flatMap fun D => if D.sevm.currentTarget = pair then pairDerivKeys D else []

/-- The settlement-committed non-static Pair frames of a mid history, in trace order. -/
def committedPairFramesMidIn {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (pair : Adr) (trace : MidHistoryTraceIn F cfg start future) :
    List Exec.Frame :=
  trace.settledFrames.flatMap (pairFrameObs pair)

/-- Every Pair frame root of a mid history is admitted by `pairEntry` over a universe holding the
history's touched rows; calldata is short on a domain whose nonzero calldata byte costs at least
16 gas. -/
theorem pair_mid_admittedIn {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} {pair : Adr} {U : WriterKey → Prop}
    (trace : MidHistoryTraceIn F cfg start future)
    (capabilities : BodyStageCapabilities F)
    (hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero)
    (touched : ∀ k ∈ pairMidTouchedKeysIn pair trace, U k) :
    trace.FrameAdmitted pair (pairEntry U) := by
  apply (trace.frameAdmitted_iff_rawFrames pair _).2
  intro root member target
  refine ⟨trace.rawFrames_entered (E := Exec.FreshEntry) enteredCondition_fresh root member,
    trace.rawFrames_entered (E := fun _ pre => pre.output = []) enteredCondition_output root member,
    trace.calldata_bound capabilities hdata root member,
    Exec.derivEntry_of_deriv (trace.rootEntryIn root member).1 (pairGood_of_keys ?_)⟩
  intro k row
  apply touched k
  apply List.mem_flatMap.mpr
  refine ⟨root, member, ?_⟩
  rw [ite_eq_left target]
  exact row

/-- **The Pair model replays the committed part of a mid history.** The statement of
`pair_history_committed_withIn` for a history that starts right after one transaction of a
retained block: the runtime stays installed, and authenticated steps whose committed subtrees are
exactly the history's committed non-static Pair frames replay from `st₀` to a model state the
future Pair storage represents, over rows growing from `K₀` within `K₀ ∪ touched`. -/
theorem pair_mid_history_committed_withIn
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWithH Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {F : Fork → Prop} (hF : ∀ {f : Fork}, F f → NeutralFork f)
    (capabilities : BodyStageCapabilities F)
    (hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero)
    {pair : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : MidHistoryTraceIn F cfg start future)
    (installed : some (start.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (start.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairMidTouchedKeysIn pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) =
        committedPairFramesMidIn pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith Auth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith Consumes st₀ steps finish ∧
        SourceReplay st₀ (steps.map PairStep.source) finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        (∀ k, K₀ k → K' k) ∧
        (∀ k, K' k → WriterExtend K₀ (pairMidTouchedKeysIn pair trace) k) ∧
        WriterRep K' (future.state.getStor pair) finish := by
  let U := WriterExtend K₀ (pairMidTouchedKeysIn pair trace)
  have extended : WriterRep U (start.state.getStor pair) st₀ := initial.extend fresh
  have supply := supplies U extended.inj extended.apart
  have admitted : trace.FrameAdmitted pair (pairEntry U) :=
    pair_mid_admittedIn trace capabilities hdata (fun k row => Or.inr row)
  have startInv : (pairSpec U).StateInv pair start.state :=
    ⟨installed, trivial, ⟨st₀, K₀, fun _ h => Or.inl h, initial⟩⟩
  have rewards := trace.rewardCreditsFunded capabilities
  have finishInv := trace.stateInv_admitted_semIn
    (pairSpec_preservesAdmittedWithIn F hF pair supply) capabilities admitted rewards startInv
    installedCert pairSem_image
  obtain ⟨frames, replay, observed⟩ :=
    (pairLadderWithIn F hF pair supply).midHistoryIn trace admitted capabilities rewards
      startInv installedCert pairSem_image
  change PairReplayWith Consumes Auth pair U (start.state.getStor pair).get frames
    (future.state.getStor pair).get at replay
  change frames.flatMap (pairSubtreeFrames pair) =
    trace.settledFrames.flatMap (pairFrameObs pair) at observed
  obtain ⟨steps, framesEq, auth, finish, K', source, grows, inside, s, view, rep⟩ :=
    replay st₀ K₀ (fun _ h => Or.inl h) ⟨_, rfl, initial⟩
  refine ⟨finishInv.code, steps, ?_, auth, finish, K', source, source.sourceReplay weaken,
    (source.sourceReplay weaken).realizes, grows, inside,
    WriterRep.congr (fun k => (congrFun view k).symm) rep⟩
  rw [← framesEq, List.flatMap_map] at observed
  exact observed

/-- `pair_mid_history_committed_withIn` from the initialized checkpoint: the replay starts at
`initializedState factory domain token0 token1` with no initially tracked row. -/
theorem pair_mid_history_initialized_withIn
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWithH Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {F : Fork → Prop} (hF : ∀ {f : Fork}, F f → NeutralFork f)
    (capabilities : BodyStageCapabilities F)
    (hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero)
    {pair : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    {factory token0 token1 : Adr} {domain : B256}
    (trace : MidHistoryTraceIn F cfg start future)
    (installed : some (start.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (start.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairMidTouchedKeysIn pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) =
        committedPairFramesMidIn pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith Auth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith Consumes (initializedState factory domain token0 token1) steps finish ∧
        SourceReplay (initializedState factory domain token0 token1)
          (steps.map PairStep.source) finish ∧
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        (∀ k, K' k → k ∈ pairMidTouchedKeysIn pair trace) ∧
        WriterRep K' (future.state.getStor pair) finish := by
  obtain ⟨code, steps, observed, auth, finish, K', matched, source, realized, _, inside, rep⟩ :=
    pair_mid_history_committed_withIn supplies weaken hF capabilities hdata trace installed
      initial fresh
  refine ⟨code, steps, observed, auth, finish, K', matched, source, realized, ?_, rep⟩
  intro k tracked
  rcases inside k tracked with none | row
  · exact none.elim
  · exact row

end Blanc.Lift.UniswapV2Pair
