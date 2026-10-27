import Blanc.Lift.Usdc.V1MainnetContinuity
import Blanc.ExecutionHistoryReceiptLogs

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Approved committed-log absence on the exact receipt interval preserves V1
control between the original cuts. Neither the first selected transaction nor the
last selected transaction is included in that absence premise. -/
theorem ConfiguredHistoryTraceIn.v1_between_txSplits_preserves_from_receipts
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
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween (i + 1) first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 j,
      ¬ (entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])) :
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
  have rootLogs := ConfiguredHistoryTraceIn.root_logs_between_txSplits_of_mainnet_receipts
    first afterCut later last beforeCut early
    (fun entry => ¬ (entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])) noUpgraded
  apply ConfiguredHistoryTraceIn.v1_between_txSplits_preserves_mainnet history
    initialApart fresh first afterCut later last beforeCut rootsIn early proxy impl slot
  intro R member upgraded
  obtain ⟨entry, present, event⟩ := upgraded
  exact rootLogs R member entry present event

/-- Receipt evidence strictly after the supplied cut preserves Proxy/V1 control
through the actual remaining transactions and final body stages. Mainnet
chronology discharges the request-stage condition. -/
theorem ConfiguredHistoryTraceIn.v1_tail_preserves_from_receipts
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {P I : Adr} {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys P history initial)
    {origin completed : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    {i : Nat} (cut : block.bodyTrace.transactions.TxSplit i)
    (rootsIn : ∀ R ∈ (MidHistoryTraceIn.tail block cut).settledRoots,
      R ∈ history.settledRoots)
    (early : block.block.header.timestamp < mainnetCancunTimestamp)
    (proxy : cut.afterBenv.state.getCode P = Proxy.code)
    (impl : cut.afterBenv.state.getCode I = ImplV1.code)
    (slot : ((cut.afterBenv.state.getStor P).get implSlot).toAdr = I)
    (noUpgraded : ∀ entry ∈ block.receiptLogsBetween (i + 1) block.bodyTrace.decodedTxs.length,
      ¬ (entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])) :
    (MidHistoryTraceIn.tail block cut).OutputNotDeleted P ∧
      completed.state.getCode P = Proxy.code ∧ completed.state.getCode I = ImplV1.code ∧
      (completed.state.getStor P).get implSlot = (cut.afterBenv.state.getStor P).get implSlot ∧
      ∀ R ∈ (MidHistoryTraceIn.tail block cut).settledRoots,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (cut.afterBenv.state.getStor P).get implSlot := by
  have disabled := (block.systemStagesDisabled_of_mainnet_timestamp_lt early).2.2
  have rootLogs := block.after_txSplit_root_logs_of_receipts cut block.forkIn.stateGas_none
    (fun entry => ¬ (entry.address = P ∧ entry.topics = [Proxy.upgradedTopic])) (by
      intro index lower upper receipt lookup entry member
      exact noUpgraded entry
        (block.mem_receiptLogsBetween (by omega) upper upper lookup member))
  apply ConfiguredHistoryTraceIn.v1_tail_preserves history BodyStageCapabilities.historical
    (fun h => h.bal_none) initialApart fresh block cut rootsIn disabled proxy impl slot
  intro R member upgraded
  have requestRoots := block.bodyTrace.requests.settledRoots_eq_nil_of_disabled disabled
  simp only [MidHistoryTraceIn.settledRoots, requestRoots, List.append_nil] at member
  obtain ⟨entry, logged, event⟩ := upgraded
  exact rootLogs R member entry logged event

end Blanc.Lift.Usdc
