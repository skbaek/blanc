import Blanc.ExecutionHistoryCommittedCell
import Blanc.ExecutionHistoryInForkFacts
import Blanc.LadderReached

/-! Historical stage facts from actual schedule selections and chain-tip bounds. -/

namespace Blanc

open Jaune

/-- A successful mainnet selection before Cancun's timestamp is in a
pre-Cancun era. Block-number activations and failed lookups remain intact. -/
theorem mainnetChainConfig_preCancun_of_timestamp_lt
    {number timestamp : Nat} {f : Fork}
    (selected : mainnetChainConfig.forkAt number timestamp = .ok f)
    (early : timestamp < mainnetCancunTimestamp) : PreCancun f := by
  have valid : mainnetChainConfig.validate = .ok () := by decide
  have someFork : mainnetChainConfig.forkAt? number timestamp = some f := by
    rw [ChainConfig.forkAt, valid] at selected
    cases lookup : mainnetChainConfig.forkAt? number timestamp with
    | none => simp only [lookup, Except.mapError, bind, Except.bind] at selected; cases selected
    | some g =>
      simp only [lookup, Except.mapError, bind, Except.bind, Except.ok.injEq] at selected
      rw [selected]
  obtain ⟨activation, last, rfl⟩ := Option.map_eq_some_iff.mp someFork
  obtain ⟨member, reached⟩ := List.mem_filter.mp (List.mem_of_getLast? last)
  simp only [mainnetChainConfig, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals
    clear selected last someFork valid
    first
      | decide
      | (exfalso
         simp only [ForkCriterion.reached, decide_eq_true_eq] at reached
         simp only [mainnetCancunTimestamp, mainnetPragueTimestamp, mainnetOsakaTimestamp,
           mainnetBpo1Timestamp, mainnetBpo2Timestamp] at reached early
         omega)

namespace ExecutionTrace

/-- The actual selected mainnet fork supplies all three disabled stage bits. -/
theorem ConfiguredBlockTraceIn.systemStagesDisabled_of_mainnet_timestamp_lt
    {F : Fork → Prop} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F mainnetChainConfig pre post)
    (early : block.block.header.timestamp < mainnetCancunTimestamp) :
    block.bodyTrace.SystemStagesDisabled := by
  have historical := mainnet_histFork block.forkAt
  have beforeCancun := mainnetChainConfig_preCancun_of_timestamp_lt block.forkAt early
  exact ⟨historical.sys_beaconRoots_false_of_preCancun beforeCancun,
    historical.sys_historyStorage_false_of_prePrague beforeCancun.toPrePrague,
    historical.header_requestsHash_false_of_prePrague beforeCancun.toPrePrague⟩

/-- A final mainnet tip before Cancun bounds every actual earlier block by
accepted-header chronology. No per-block era or stage-bit oracle is supplied. -/
theorem ConfiguredHistoryTraceIn.systemStagesDisabled_of_mainnet_tip_before_cancun
    {F : Fork → Prop} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F mainnetChainConfig checkpoint future)
    {tip : Block} (last : future.blocks.getLast? = some tip)
    (early : tip.header.timestamp < mainnetCancunTimestamp) :
    history.SystemStagesDisabled := by
  induction history generalizing tip with
  | refl => simp only [ConfiguredHistoryTraceIn.SystemStagesDisabled]
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.SystemStagesDisabled]
    obtain ⟨_, _, _, ⟨parent, parentEq, parentLt⟩, postTip⟩ :=
      stateTransitionUsing_reachedStep block.transition
    have tipEq := Option.some.inj (postTip.symm.trans last)
    have blockEarly : block.block.header.timestamp < mainnetCancunTimestamp := by
      rw [tipEq]
      exact early
    exact ⟨ih parentEq (Nat.lt_trans parentLt blockEarly),
      block.systemStagesDisabled_of_mainnet_timestamp_lt blockEarly⟩

end ExecutionTrace

end Blanc
