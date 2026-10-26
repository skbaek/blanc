import Blanc.Lift.Usdc.ProxyCreation.HistoryCut
import Blanc.Lift.Usdc.V1ReceiptAllowanceZero

/-!
# Original constructor receipt to the pre-Pair transaction cut

This composition derives the original proxy code, implementation slot and zero
allowance seed from the actual constructor transaction at index22, then carries
them through its block suffix, the actual middle history and the prefix before
transaction38. No independently supplied zero state at C or D is used.

This is an internal producer interface, not the complete historical instance.
The actual C/D identities and authenticated receipts, initial V1 code, finite
separation and pre-D approve evidence still need their own producers.
Neither caller exclusion nor the receipt-value alternative follows from R3
or Pair target emptiness; no historical event predicate is adopted here.
The selected D transaction and its settlement are outside this interval.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The exact constructor storage supplies its implementation word. -/
theorem ProxyCreation.OriginalConstructorSeed.implementation
    {state : State} {pair : Adr} {tracked : Adr → Prop}
    (seed : ProxyCreation.OriginalConstructorSeed state pair tracked) :
    (state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation := by
  rw [seed.storage, Stor.get_set_ne _ (by decide : adminSlot ≠ implSlot),
    Stor.get_set_self]

/-- Derive the V1 control and tracked zero rows just before the original
Pair-deployment transaction from the same actual constructor's successful
receipt. The independent pre-D approve-evidence obligation remains visible;
this theorem does not adopt it as a new final environmental premise. -/
theorem ConfiguredHistoryTraceIn.original_v1_seed_before_cut38_of_constructor_receipt_and_approve_evidence
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {pair : Adr} {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys usdcProxy history initial)
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    (afterCut : first.bodyTrace.transactions.TxSplit 22)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (beforeCut : last.bodyTrace.transactions.TxSplit 38)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ history.settledRoots)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    (receiver : afterCut.tx.type.receiver? = none)
    (input : afterCut.tx.data = ProxyCreation.code.toList) (value : afterCut.tx.value = 0)
    (sender : afterCut.head.sender = ProxyCreation.originalCreator)
    (nonce : afterCut.tx.nonce = 20)
    {receipt : Fin 5 × Receipt}
    (receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (slotsApart : ProxySlotsApart pair Tr)
    (impl : afterCut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code)
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween 23 first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 38,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
    (proxyApart : ProxyRowsApart usdcProxy pair Tr history.rawNodes)
    (rowSep : UsdcRowSep usdcProxy pair Tr history.rawFrames)
    (initApart : InitRowsApart usdcProxy pair Tr history.rawFrames)
    (approveEvidence :
      (∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
        G.sevm.currentTarget = usdcProxy → Sevm.selector G.sevm = 0x095ea7b3 →
        G.sevm.caller ≠ pair) ∨
      (∀ entry ∈ first.receiptLogsBetween 23 first.bodyTrace.decodedTxs.length ++
          later.receiptLogs ++ last.receiptLogsBetween 0 38,
        V1ApprovalZeroFor usdcProxy pair Tr entry)) :
    beforeCut.benv.state.getCode usdcProxy = Proxy.code ∧
      beforeCut.benv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      (beforeCut.benv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.benv.state.getStor usdcProxy).get (allowSlot pair g) = 0 := by
  obtain ⟨_, seed⟩ := ProxyCreation.original_constructor_seed_of_receipt_cut22
    first afterCut first.forkIn.stateGas_none receiver input value sender nonce
    receiptAt succeeded slotsApart
  have word := seed.implementation
  have slot : ((afterCut.afterBenv.state.getStor usdcProxy).get implSlot).toAdr =
      ProxyCreation.initialImplementation.toAdr := congrArg B256.toAdr word
  have control := ConfiguredHistoryTraceIn.v1_between_txSplits_preserves_from_receipts
    history initialApart fresh first afterCut later last beforeCut rootsIn early
    seed.runtime impl slot noUpgraded
  refine ⟨control.2.1, control.2.2.1, control.2.2.2.1.trans word, ?_⟩
  intro g tracked
  exact ConfiguredHistoryTraceIn.v1_allowance_zero_between_txSplits_from_approve_evidence
    history initialApart fresh first afterCut later last beforeCut rootsIn early
    seed.runtime impl slot noUpgraded proxyApart rowSep initApart approveEvidence tracked
    (seed.allowance g tracked)

/-- Compatibility interface preserving the original caller-exclusion statement. -/
theorem ConfiguredHistoryTraceIn.original_v1_seed_before_cut38_of_constructor_receipt
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {pair : Adr} {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys usdcProxy history initial)
    {origin completed pre post : BlockChain}
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    (afterCut : first.bodyTrace.transactions.TxSplit 22)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (beforeCut : last.bodyTrace.transactions.TxSplit 38)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ history.settledRoots)
    (early : last.block.header.timestamp < mainnetCancunTimestamp)
    (receiver : afterCut.tx.type.receiver? = none)
    (input : afterCut.tx.data = ProxyCreation.code.toList) (value : afterCut.tx.value = 0)
    (sender : afterCut.head.sender = ProxyCreation.originalCreator)
    (nonce : afterCut.tx.nonce = 20)
    {receipt : Fin 5 × Receipt}
    (receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (slotsApart : ProxySlotsApart pair Tr)
    (impl : afterCut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code)
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween 23 first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 38,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
    (proxyApart : ProxyRowsApart usdcProxy pair Tr history.rawNodes)
    (rowSep : UsdcRowSep usdcProxy pair Tr history.rawFrames)
    (initApart : InitRowsApart usdcProxy pair Tr history.rawFrames)
    (noCaller : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
        last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
      G.sevm.currentTarget = usdcProxy → Sevm.selector G.sevm = 0x095ea7b3 →
      G.sevm.caller ≠ pair) :
    beforeCut.benv.state.getCode usdcProxy = Proxy.code ∧
      beforeCut.benv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code ∧
      (beforeCut.benv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.benv.state.getStor usdcProxy).get (allowSlot pair g) = 0 :=
  ConfiguredHistoryTraceIn.original_v1_seed_before_cut38_of_constructor_receipt_and_approve_evidence
    history initialApart fresh first afterCut later last beforeCut rootsIn early
    receiver input value sender nonce receiptAt succeeded slotsApart impl noUpgraded
    proxyApart rowSep initApart (.inl noCaller)

end Blanc.Lift.Usdc
