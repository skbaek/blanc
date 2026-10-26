import Blanc.Lift.Usdc.V1MidHistoryContinuity
import Blanc.ExecutionHistoryInEraBounds

/-! Exact-cut V1 continuity with stage facts derived from mainnet chronology. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The mainnet interval ending before Cancun supplies its own disabled-stage
facts. Actual fork selection and accepted-header chronology replace all three
stage premises of the exact-cut theorem; historical identity and receipts stay
explicit inputs to the caller. -/
theorem ConfiguredHistoryTraceIn.v1_between_txSplits_preserves_mainnet
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {P I : Adr} {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys P history initial)
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    {i : Nat} (afterCut : first.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    {j : Nat} (beforeCut : last.bodyTrace.transactions.TxSplit j)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ history.settledRoots)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    (proxy : afterCut.afterBenv.state.getCode P = Proxy.code)
    (impl : afterCut.afterBenv.state.getCode I = ImplV1.code)
    (slot : ((afterCut.afterBenv.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, ¬ ∃ entry ∈ R.post.logs,
        entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    (((MidHistoryTraceIn.tail first afterCut).append later).OutputNotDeleted P ∧
      beforeCut.before.OutputNotDeleted P) ∧
      beforeCut.benv.state.getCode P = Proxy.code ∧
      beforeCut.benv.state.getCode I = ImplV1.code ∧
      (beforeCut.benv.state.getStor P).get implSlot =
        (afterCut.afterBenv.state.getStor P).get implSlot ∧
      ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (afterCut.afterBenv.state.getStor P).get implSlot := by
  obtain ⟨_, _, _, _, firstTip⟩ := stateTransitionUsing_reachedStep first.transition
  obtain ⟨_, _, _, ⟨parent, parentTip, parentLt⟩, _⟩ :=
    stateTransitionUsing_reachedStep last.transition
  have parentEarly := Nat.lt_trans parentLt early
  have laterDisabled := later.systemStagesDisabled_of_mainnet_tip_before_cancun
    parentTip parentEarly
  obtain ⟨tip, tipEq, firstLe⟩ := later.toReachUsing.tip_floor
    ⟨first.block, firstTip, Nat.le_refl _⟩
  have sameTip := Option.some.inj (tipEq.symm.trans parentTip)
  have firstEarly : first.block.header.timestamp < mainnetCancunTimestamp := by
    rw [sameTip] at firstLe
    exact Nat.lt_of_le_of_lt firstLe parentEarly
  have firstDisabled := first.systemStagesDisabled_of_mainnet_timestamp_lt firstEarly
  have lastDisabled := last.systemStagesDisabled_of_mainnet_timestamp_lt early
  exact ConfiguredHistoryTraceIn.v1_between_txSplits_preserves history
    BodyStageCapabilities.historical (fun h => h.bal_none) initialApart fresh
    first afterCut later last beforeCut rootsIn firstDisabled.2.2 laterDisabled
    ⟨lastDisabled.1, lastDisabled.2.1⟩ proxy impl slot noUpgraded

end Blanc.Lift.Usdc
