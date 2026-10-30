import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.ExecutionWholeFrameAccountingIn
import Blanc.ExecutionAccountingHistoryIn

/-!
# The Uniswap V2 Pair's committed history over a selected fork domain

The counterpart of the committed-history results of `PairHistory.lean` over a configured history
`ConfiguredHistoryTraceIn F` whose forks satisfy the neutral rule facts (`NeutralFork`), with the
body-stage capabilities and the calldata gas floor the trace admission reads:

* `pair_spawnKindsIn` — Pair frames spawn only by `CALL`/`STATICCALL`, from `stateGas = none`;
* `pairLadderWithIn` — the Pair's accounting ladder over `F` (`wholeFrameLadderIn`), from the
  historical supply `PairStepSupplyWithH`;
* `pair_history_committed_withIn` — the authenticated committed-frame replay of the history (the
  `ConfiguredHistoryTraceIn` rung `configuredHistoryIn`), and its corollary
  `pair_history_initialized_withIn`;
* the `…Hist` instances on `HistFork`, from `pairAdmittedSupplyH`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- Pair frames spawn only by `CALL`/`STATICCALL` over a domain without state gas. -/
theorem pair_spawnKindsIn (F : Fork → Prop)
    (hsgF : ∀ {f : Fork}, F f → (Fork.ruleSet f).stateGas = none) (pair : Adr) :
    SpawnKindsIn F pair pairSem := by
  intro sevm pre post run hrun _ fork _ node chain x hat
  obtain ⟨κ, reach, ok⟩ := Blanc.Lift.cursor_of_parentPrefix_noStateGas cert_check
    (F := ⟨0, sevm, pre, .ok post, run⟩) rfl hrun (hsgF fork) chain
  exact ok.exec_call_or_staticcall (Cursor.callOnly_of_reach cert_callOnly reach) hat

/-- **The accounting ladder of the Pair over a neutral fork domain** `F`, from the historical
supply. -/
def pairLadderWithIn
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop} (F : Fork → Prop)
    (hF : ∀ {f : Fork}, F f → NeutralFork f) (pair : Adr) {U : WriterKey → Prop}
    (supply : PairStepSupplyWithH Consumes Auth U (fun _ => True)) :
    AccountingLadderAdmittedIn F (pairSpec U) pair (pairEntry U) :=
  wholeFrameLadderIn (c := pairSpec U) (pairCarrierWith Consumes Auth pair U)
    (pairObservationWith Consumes Auth pair U)
    PairReplayWith.append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun h => funext h) (fun _ h => pairFrameObs_static h)
    (fun _ h => pairFrameObs_foreign h) (fun h => (hF h).stateGas)
    (pair_spawnKindsIn F (fun h => (hF h).stateGas) pair)
    (pair_wholeFrameReplayWithIn F hF pair supply)
    (pairSpec_preservesAdmittedWithIn F hF pair supply)

/-- The settlement-committed non-static Pair frames of a selected-domain history, in trace
order. -/
def committedPairFramesIn {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (pair : Adr) (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) : List Exec.Frame :=
  trace.settledFrames.flatMap (pairFrameObs pair)

/-- **The Pair model replays the committed history over a neutral fork domain.** The statement
of `pair_history_committed_with` for a `ConfiguredHistoryTraceIn F` history: the runtime stays
installed, and authenticated steps whose committed subtrees are exactly the history's committed
non-static Pair frames replay from `st₀` to a model state the future Pair storage represents,
over rows growing from `K₀` within `K₀ ∪ touched`. -/
theorem pair_history_committed_withIn
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWithH Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {F : Fork → Prop} (hF : ∀ {f : Fork}, F f → NeutralFork f)
    (capabilities : BodyStageCapabilities F)
    (hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeysIn pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFramesIn pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith Auth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith Consumes st₀ steps finish ∧
        SourceReplay st₀ (steps.map PairStep.source) finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        (∀ k, K₀ k → K' k) ∧
        (∀ k, K' k → WriterExtend K₀ (pairHistoryTouchedKeysIn pair trace) k) ∧
        WriterRep K' (future.state.getStor pair) finish := by
  let U := WriterExtend K₀ (pairHistoryTouchedKeysIn pair trace)
  have extended : WriterRep U (checkpoint.state.getStor pair) st₀ := initial.extend fresh
  have supply := supplies U extended.inj extended.apart
  have admitted : trace.FrameAdmitted pair (pairEntry U) :=
    pair_trace_admittedIn trace capabilities hdata (fun k row => Or.inr row)
  have start : (pairSpec U).StateInv pair checkpoint.state :=
    ⟨installed, trivial, ⟨st₀, K₀, fun _ h => Or.inl h, initial⟩⟩
  have rewards := trace.rewardCreditsFunded capabilities
  have finishInv := trace.stateInv_admitted_semIn
    (pairSpec_preservesAdmittedWithIn F hF pair supply) capabilities admitted rewards start
    installedCert pairSem_image
  obtain ⟨frames, replay, observed⟩ :=
    (pairLadderWithIn F hF pair supply).configuredHistoryIn trace admitted capabilities rewards
      start installedCert pairSem_image
  change PairReplayWith Consumes Auth pair U (checkpoint.state.getStor pair).get frames
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

/-- `pair_history_committed_withIn` from the initialized checkpoint: the replay starts at
`initializedState factory domain token0 token1` with no initially tracked row. -/
theorem pair_history_initialized_withIn
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop}
    (supplies : ∀ (U : WriterKey → Prop), WriterInj U → WriterApart U →
      PairStepSupplyWithH Consumes Auth U (fun _ => True))
    (weaken : ∀ root segment transcript out,
      Consumes root segment transcript out → ExactConsumes segment transcript out)
    {F : Fork → Prop} (hF : ∀ {f : Fork}, F f → NeutralFork f)
    (capabilities : BodyStageCapabilities F)
    (hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero)
    {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {factory token0 token1 : Adr} {domain : B256}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeysIn pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFramesIn pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith Auth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith Consumes (initializedState factory domain token0 token1) steps finish ∧
        SourceReplay (initializedState factory domain token0 token1)
          (steps.map PairStep.source) finish ∧
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        (∀ k, K' k → k ∈ pairHistoryTouchedKeysIn pair trace) ∧
        WriterRep K' (future.state.getStor pair) finish := by
  obtain ⟨code, steps, observed, auth, finish, K', matched, source, realized, _, inside, rep⟩ :=
    pair_history_committed_withIn supplies weaken hF capabilities hdata trace installed initial
      fresh
  refine ⟨code, steps, observed, auth, finish, K', matched, source, realized, ?_, rep⟩
  intro k tracked
  rcases inside k tracked with none | row
  · exact none.elim
  · exact row

/-! ## The historical domain `HistFork` -/

/-- `PairAdmittedConsumesH` consumption retains an exact source consumption. -/
theorem PairAdmittedConsumesH.exact {root : Exec.Deriv} {segment : SegmentResult}
    {transcript : Transcript} {out : RunResult}
    (admitted : PairAdmittedConsumesH root segment transcript out) :
    ExactConsumes segment transcript out :=
  admitted.elim fun selected _ => selected.forget

/-- **The Pair model replays a committed `HistFork` history**, every step consumed with
`PairAdmittedConsumesH` and authenticated by `PairEntryAuth`. -/
theorem pair_history_committedHist {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeysIn pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFramesIn pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumesH st₀ steps finish ∧
        SourceReplay st₀ (steps.map PairStep.source) finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        (∀ k, K₀ k → K' k) ∧
        (∀ k, K' k → WriterExtend K₀ (pairHistoryTouchedKeysIn pair trace) k) ∧
        WriterRep K' (future.state.getStor pair) finish :=
  pair_history_committed_withIn
    (fun _ inj apart => pairAdmittedSupplyH inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed.exact) HistFork.neutral BodyStageCapabilities.historical
    (fun _ hf => hf.dataNonZero_ge) trace installed initial fresh

/-- **The Pair history from its initialized checkpoint, through a `HistFork` history**: the
replay starts at `initializedState factory domain token0 token1`, the storage
`Creation.pair_create2_initializedH` establishes, with no initially tracked row. -/
theorem pair_history_initializedReplayHist {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {factory token0 token1 : Adr} {domain : B256}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeysIn pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFramesIn pair trace ∧
      (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        PairObservedReplayWith PairAdmittedConsumesH (initializedState factory domain token0 token1)
          steps finish ∧
        SourceReplay (initializedState factory domain token0 token1)
          (steps.map PairStep.source) finish ∧
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        (∀ k, K' k → k ∈ pairHistoryTouchedKeysIn pair trace) ∧
        WriterRep K' (future.state.getStor pair) finish :=
  pair_history_initialized_withIn
    (fun _ inj apart => pairAdmittedSupplyH inj apart pairSem pairSem_image)
    (fun _ _ _ _ consumed => consumed.exact) HistFork.neutral BodyStageCapabilities.historical
    (fun _ hf => hf.dataNonZero_ge) trace installed initial fresh

end Blanc.Lift.UniswapV2Pair
