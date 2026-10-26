import Blanc.Lift.UniswapV2Pair.PairPositionalCalls
import Blanc.Lift.UniswapV2Pair.PairMidHistoryIn

/-!
# Pair child selectors over historical configured and mid histories

The historical replay supplies the actual settled frames and their rooted positional
consumptions. Every mutable child of a mutable Pair frame carries the transfer or callback
selector. This needs installed code, writer representation and finite touched-key freshness.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- Every mutable child of a settled mutable Pair frame in a historical configured
history is called by the Pair with the transfer or callback selector. -/
theorem pair_history_children_shapeHist {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeysIn pair trace)) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ c ∈ Exec.childFrames G.run, c.sevm.isStatic = false →
        c.sevm.caller = pair ∧
          (getDelegatedCodeAddress (c.pre.getCode c.sevm.currentTarget) = none →
            c.sevm.codeAddress = some c.sevm.currentTarget) ∧
          (Blanc.Sevm.selector c.sevm = 0xa9059cbb ∨ Blanc.Sevm.selector c.sevm = 0x10d1e85c) := by
  obtain ⟨-, steps, observedEq, auth, finish, K', replay, -⟩ :=
    pair_history_committedHist trace installed initial fresh
  exact pair_replay_children_shape (Consumes := PairAdmittedConsumesH)
    (fun _ _ _ _ consumed => consumed.1) observedEq auth replay

/-- The same selector classification from the actual starting storage of a historical
mid history, including re-entered Pair frames through positional completeness. -/
theorem pair_mid_history_children_shapeHist {pair : Adr} {cfg : ChainConfig}
    {start : Benv} {future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (start.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairMidTouchedKeysIn pair trace)) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ c ∈ Exec.childFrames G.run, c.sevm.isStatic = false →
        c.sevm.caller = pair ∧
          (getDelegatedCodeAddress (c.pre.getCode c.sevm.currentTarget) = none →
            c.sevm.codeAddress = some c.sevm.currentTarget) ∧
          (Blanc.Sevm.selector c.sevm = 0xa9059cbb ∨ Blanc.Sevm.selector c.sevm = 0x10d1e85c) := by
  obtain ⟨-, steps, observedEq, auth, finish, K', replay, -⟩ :=
    pair_mid_history_committed_withIn
      (fun _ inj apart => pairAdmittedSupplyH inj apart pairSem pairSem_image)
      (fun _ _ _ _ consumed => consumed.exact) HistFork.neutral
      BodyStageCapabilities.historical (fun _ hf => hf.dataNonZero_ge)
      trace installed initial fresh
  exact pair_replay_children_shape (Consumes := PairAdmittedConsumesH)
    (fun _ _ _ _ consumed => consumed.1) observedEq auth replay

end Blanc.Lift.UniswapV2Pair
