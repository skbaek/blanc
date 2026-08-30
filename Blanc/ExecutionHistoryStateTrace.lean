import Blanc.ExecutionBodyStateTrace
import Blanc.ExecutionHistory

/-!
Contract-neutral exact state chronology for configured block histories.

The selected fork rules and complete retained body trace remain attached to
every boundary.  Histories may cross schedule activations; no global fork is
hard-coded into the carrier.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

structure ConfiguredBlockStateChronology
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) where
  body : AppliedBodyStateChronology trace.bodyTrace

inductive ConfiguredBlockStateBoundaryOrigin where
  | preparation {cfg : ChainConfig} {pre post : BlockChain}
      {trace : ConfiguredBlockTrace cfg pre post}
      (chronology : ConfiguredBlockStateChronology trace)
  | body {cfg : ChainConfig} {pre post : BlockChain}
      {trace : ConfiguredBlockTrace cfg pre post}
      (chronology : ConfiguredBlockStateChronology trace)
      (origin : AppliedBodyStateBoundaryOrigin)

abbrev ConfiguredBlockStateBoundary :=
  StateTransition ConfiguredBlockStateBoundaryOrigin

def ConfiguredBlockStateChronology.stateBoundaries
    {cfg : ChainConfig} {pre post : BlockChain}
    {trace : ConfiguredBlockTrace cfg pre post}
    (chronology : ConfiguredBlockStateChronology trace) :
    List ConfiguredBlockStateBoundary :=
  { origin := .preparation chronology
    before := pre.state
    after := (initBenv trace.rules pre trace.block.header).state } ::
  chronology.body.stateBoundaries.map
    (StateTransition.mapOrigin
      (ConfiguredBlockStateBoundaryOrigin.body chronology))

theorem ConfiguredBlockTrace.exists_stateChronology
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    Nonempty (ConfiguredBlockStateChronology trace) := by
  rcases trace.bodyTrace.exists_stateChronology with ⟨body⟩
  exact ⟨⟨body⟩⟩

theorem ConfiguredBlockStateChronology.stateReplay
    {cfg : ChainConfig} {pre post : BlockChain}
    {trace : ConfiguredBlockTrace cfg pre post}
    (chronology : ConfiguredBlockStateChronology trace) :
    StateReplay pre.state chronology.stateBoundaries post.state := by
  let preparation : ConfiguredBlockStateBoundary :=
    { origin := .preparation chronology
      before := pre.state
      after := (initBenv trace.rules pre trace.block.header).state }
  have bodyReplay := StateReplay.mapOrigin
    (ConfiguredBlockStateBoundaryOrigin.body chronology)
    chronology.body.stateReplay
  have replay := StateReplay.cons preparation bodyReplay
  have postStateEq : trace.bodyState = post.state :=
    (congrArg (fun chain : BlockChain => chain.state) trace.postEq).symm
  exact replay.castPost postStateEq

/-- Exact per-block chronology witnesses aligned with one retained configured
history. -/
inductive ConfiguredHistoryStateChronology
    {cfg : ChainConfig} {checkpoint : BlockChain} :
    {future : BlockChain} →
    (history : ConfiguredHistoryTrace cfg checkpoint future) → Type
  | refl {hcfg : cfg.Valid} {hctx : checkpoint.ValidContext}
      {hid : cfg.chainId = checkpoint.chainId} :
      ConfiguredHistoryStateChronology (.refl hcfg hctx hid)
  | step {current future : BlockChain}
      {prior : ConfiguredHistoryTrace cfg checkpoint current}
      {block : ConfiguredBlockTrace cfg current future}
      (priorChronology : ConfiguredHistoryStateChronology prior)
      (blockChronology : ConfiguredBlockStateChronology block) :
      ConfiguredHistoryStateChronology (.step prior block)

def ConfiguredHistoryStateChronology.stateBoundaries
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history) :
    List ConfiguredBlockStateBoundary :=
  match chronology with
  | .refl => []
  | .step prior block =>
      prior.stateBoundaries ++ block.stateBoundaries

theorem ConfiguredHistoryTrace.exists_stateChronology
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future) :
    Nonempty (ConfiguredHistoryStateChronology history) := by
  induction history with
  | refl => exact ⟨.refl⟩
  | step prior block ih =>
      rcases ih with ⟨priorChronology⟩
      rcases block.exists_stateChronology with ⟨blockChronology⟩
      exact ⟨.step priorChronology blockChronology⟩

theorem ConfiguredHistoryStateChronology.stateReplay
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTrace cfg checkpoint future}
    (chronology : ConfiguredHistoryStateChronology history) :
    StateReplay checkpoint.state chronology.stateBoundaries future.state := by
  induction chronology with
  | refl => exact .nil _
  | step prior block ih => exact ih.append block.stateReplay

end ExecutionTrace

end Blanc
