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

end Blanc.Lift.Usdc
