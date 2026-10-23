import Blanc.ExecutionStagedBodyStateTrace
import Blanc.ExecutionHistory

/-!
Contract-neutral exact state chronology for configured In-history blocks.

Each retained `ConfiguredBlockTraceIn` keeps its actual selected fork, exact
staged body trace and reward-inclusive budget; the only additional witness a
block chronology retains is the D1 staged-body chronology. Histories append
prior-then-block replay along the Type-valued occurrence spine. Never erase
that spine into Prop reachability: the same executions are retained.

Premise account: per-block existence discharges its `stateGas = none` from
the history's own capability evidence
(`BodyStageCapabilities.stateGas_none`), never from a global modern premise.
`requests_covered` is not needed (extraction already happened), nor any sum
bound, admission, `HistFork` beyond the carrier's own `forkIn`, endpoint
invariant, `ConfiguredRewardBudget` change, or `ReachUsing` rewrite.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

structure ConfiguredBlockStateChronologyIn
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) where
  body : StagedBodyStateChronology trace.bodyTrace

inductive ConfiguredBlockStateBoundaryOriginIn where
  | preparation {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
      {trace : ConfiguredBlockTraceIn F cfg pre post}
      (chronology : ConfiguredBlockStateChronologyIn trace)
  | body {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
      {trace : ConfiguredBlockTraceIn F cfg pre post}
      (chronology : ConfiguredBlockStateChronologyIn trace)
      (origin : StagedBodyStateBoundaryOrigin)

abbrev ConfiguredBlockStateBoundaryIn :=
  StateTransition ConfiguredBlockStateBoundaryOriginIn

/-- Block boundaries: the actual `initBenv` preparation event (`pre.state`
to the opening body state, definitionally `pre.state`) plus the mapped D1
body replay. -/
def ConfiguredBlockStateChronologyIn.stateBoundaries
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {trace : ConfiguredBlockTraceIn F cfg pre post}
    (chronology : ConfiguredBlockStateChronologyIn trace) :
    List ConfiguredBlockStateBoundaryIn :=
  { origin := .preparation chronology
    before := pre.state
    after := (initBenv trace.fork pre trace.block.header).state } ::
  chronology.body.stateBoundaries.map
    (StateTransition.mapOrigin
      (ConfiguredBlockStateBoundaryOriginIn.body chronology))

/-- Every retained In-block supplies its staged-body chronology, with the
per-block `stateGas = none` discharged from the history's own capability
evidence. -/
theorem ConfiguredBlockTraceIn.exists_stateChronology
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) :
    Nonempty (ConfiguredBlockStateChronologyIn trace) := by
  rcases trace.bodyTrace.exists_stagedStateChronology
    (capabilities.stateGas_none trace.forkIn) with ⟨body⟩
  exact ⟨⟨body⟩⟩

theorem ConfiguredBlockStateChronologyIn.stateReplay
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {trace : ConfiguredBlockTraceIn F cfg pre post}
    (chronology : ConfiguredBlockStateChronologyIn trace) :
    StateReplay pre.state chronology.stateBoundaries post.state := by
  let preparation : ConfiguredBlockStateBoundaryIn :=
    { origin := .preparation chronology
      before := pre.state
      after := (initBenv trace.fork pre trace.block.header).state }
  have bodyReplay := StateReplay.mapOrigin
    (ConfiguredBlockStateBoundaryOriginIn.body chronology)
    chronology.body.stateReplay
  have replay := StateReplay.cons preparation bodyReplay
  have postStateEq : trace.bodyState = post.state :=
    (congrArg (fun chain : BlockChain => chain.state) trace.postEq).symm
  exact replay.castPost postStateEq

/-- Exact per-block chronology witnesses aligned with one retained
configured In-history. -/
inductive ConfiguredHistoryStateChronologyIn
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint : BlockChain} :
    {future : BlockChain} →
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) → Type
  | refl (hcfg : cfg.Valid) (hctx : checkpoint.ValidContext)
      (hid : cfg.chainId = checkpoint.chainId) :
      ConfiguredHistoryStateChronologyIn
        (.refl hcfg hctx hid)
  | step {current future : BlockChain}
      {prior : ConfiguredHistoryTraceIn F cfg checkpoint current}
      {block : ConfiguredBlockTraceIn F cfg current future}
      (priorChronology : ConfiguredHistoryStateChronologyIn prior)
      (blockChronology : ConfiguredBlockStateChronologyIn block) :
      ConfiguredHistoryStateChronologyIn (.step prior block)

def ConfiguredHistoryStateChronologyIn.stateBoundaries
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronologyIn history) :
    List ConfiguredBlockStateBoundaryIn :=
  match chronology with
  | .refl _ _ _ => []
  | .step prior block =>
      prior.stateBoundaries ++ block.stateBoundaries

theorem ConfiguredHistoryTraceIn.exists_stateChronology
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) :
    Nonempty (ConfiguredHistoryStateChronologyIn history) := by
  induction history with
  | refl hcfg hctx hid => exact ⟨.refl hcfg hctx hid⟩
  | step prior block ih =>
      rcases ih with ⟨priorChronology⟩
      rcases block.exists_stateChronology capabilities with
        ⟨blockChronology⟩
      exact ⟨.step priorChronology blockChronology⟩

theorem ConfiguredHistoryStateChronologyIn.stateReplay
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronologyIn history) :
    StateReplay checkpoint.state chronology.stateBoundaries future.state := by
  induction chronology with
  | refl _ _ _ => exact .nil _
  | step prior block ih => exact ih.append block.stateReplay

end ExecutionTrace

end Blanc
