import Blanc.Lift.Usdc.V1ConstructorReceiptZero
import Blanc.Lift.UniswapV2Factory.CreatePairForeignHistory

/-!
# Original USDC constructor to the settled Pair-deployment seed

The same C transaction receipt supplies the constructor seed; the original
C suffix, middle history and D prefix carry it to D; the actual factory
transaction then preserves the foreign USDC account through settlement.
No zero-at-C, zero-before-D or zero-after-D hypothesis is consumed.

This internal composition still requires the original historical provenance,
initial V1 implementation code, finite separation and a genuine producer of
pre-D approve safety. The caller-exclusion or exact receipt-value alternative is not an adopted
new premise. Historical evidence must establish the selected alternative.
Neither D freshness nor R3 establishes absence of earlier Pair incarnations.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc

/-- Derive the actual after-D proxy code, implementation word and zero tracked
Pair allowance rows from the actual constructor receipt and exact C-to-D
interval. The factory's admitted execution supplies D preservation, rather
than a supplied foreign-storage equality. -/
theorem original_pair_allowance_seed_of_constructor_receipt_and_approve_evidence
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
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
    (receiver : afterCut.tx.type.receiver? = none)
    (input : afterCut.tx.data = ProxyCreation.code.toList) (value : afterCut.tx.value = 0)
    (sender : afterCut.head.sender = ProxyCreation.originalCreator)
    (nonce : afterCut.tx.nonce = 20)
    {receipt : Fin 5 × Receipt}
    (receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (slotsApart : ProxySlotsApart UniswapV2Pair.Creation.pairAddress Tr)
    (impl : afterCut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code)
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween 23 first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 38,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
    (proxyApart : ProxyRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawNodes)
    (rowSep : UsdcRowSep usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawFrames)
    (initApart : InitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawFrames)
    (approveEvidence :
      (∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
        G.sevm.currentTarget = usdcProxy → Sevm.selector G.sevm = 0x095ea7b3 →
        G.sevm.caller ≠ UniswapV2Pair.Creation.pairAddress) ∨
      (∀ entry ∈ first.receiptLogsBetween 23 first.bodyTrace.decodedTxs.length ++
          later.receiptLogs ++ last.receiptLogsBetween 0 38,
        V1ApprovalZeroFor usdcProxy UniswapV2Pair.Creation.pairAddress Tr entry))
    (hnumber : last.block.header.number = 10008355)
    (htime : last.block.header.timestamp = 1588710145) {gasPrice : Nat}
    (htype : beforeCut.tx.type = .zero gasPrice (some UniswapV2Pair.Creation.factory))
    (hdata : beforeCut.tx.data = UniswapV2Factory.createPairData)
    (hvalue : beforeCut.tx.value = 0) (hnonce : beforeCut.tx.nonce = 205)
    (hfunds : (beforeCut.tx.gas * beforeCut.head.effectiveGasPrice).toB256 ≤
      beforeCut.benv.state.bal beforeCut.head.sender)
    (hgas : beforeCut.head.intrinsicGas + 2600000 ≤ beforeCut.tx.gas)
    (hgasb : beforeCut.tx.gas < 2 ^ 64)
    (hfactory : beforeCut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    (hfnonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max)
    (hpairNonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0)
    (hpairCode : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0)
    (hpairStor : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).stor.size = 0)
    (hslot2 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 = 0)
    (hslot5 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk5 = 0) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0 := by
  have early : last.block.header.timestamp < mainnetCancunTimestamp := by
    rw [htime]
    decide
  obtain ⟨proxy, _, word, zero⟩ :=
    ConfiguredHistoryTraceIn.original_v1_seed_before_cut38_of_constructor_receipt_and_approve_evidence
      history initialApart fresh first afterCut later last beforeCut rootsIn early
      receiver input value sender nonce receiptAt succeeded slotsApart impl noUpgraded
      proxyApart rowSep initApart approveEvidence
  have nonempty : (beforeCut.benv.state.getCode usdcProxy).toList ≠ [] := by
    rw [proxy]
    exact (show UsdcContextCode Proxy.code from .inl rfl).ne_nil
  obtain ⟨code, storage⟩ := UniswapV2Factory.createPair_block_preserves_foreign_installed
    last hnumber htime beforeCut htype hdata hvalue hnonce hfunds hgas hgasb hfactory
    hfnonce hpairNonce hpairCode hpairStor hslot2 hslot5 usdcProxy (by decide) (by decide) nonempty
  refine ⟨code.trans proxy, ?_, ?_⟩
  · rw [storage]
    exact word
  · intro g tracked
    rw [storage]
    exact zero g tracked

/-- Compatibility interface preserving the original caller-exclusion statement. -/
theorem original_pair_allowance_seed_of_constructor_receipt
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
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
    (receiver : afterCut.tx.type.receiver? = none)
    (input : afterCut.tx.data = ProxyCreation.code.toList) (value : afterCut.tx.value = 0)
    (sender : afterCut.head.sender = ProxyCreation.originalCreator)
    (nonce : afterCut.tx.nonce = 20)
    {receipt : Fin 5 × Receipt}
    (receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (slotsApart : ProxySlotsApart UniswapV2Pair.Creation.pairAddress Tr)
    (impl : afterCut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code)
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween 23 first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 38,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
    (proxyApart : ProxyRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawNodes)
    (rowSep : UsdcRowSep usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawFrames)
    (initApart : InitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawFrames)
    (noCaller : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
        last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
      G.sevm.currentTarget = usdcProxy → Sevm.selector G.sevm = 0x095ea7b3 →
      G.sevm.caller ≠ UniswapV2Pair.Creation.pairAddress)
    (hnumber : last.block.header.number = 10008355)
    (htime : last.block.header.timestamp = 1588710145) {gasPrice : Nat}
    (htype : beforeCut.tx.type = .zero gasPrice (some UniswapV2Pair.Creation.factory))
    (hdata : beforeCut.tx.data = UniswapV2Factory.createPairData)
    (hvalue : beforeCut.tx.value = 0) (hnonce : beforeCut.tx.nonce = 205)
    (hfunds : (beforeCut.tx.gas * beforeCut.head.effectiveGasPrice).toB256 ≤
      beforeCut.benv.state.bal beforeCut.head.sender)
    (hgas : beforeCut.head.intrinsicGas + 2600000 ≤ beforeCut.tx.gas)
    (hgasb : beforeCut.tx.gas < 2 ^ 64)
    (hfactory : beforeCut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    (hfnonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max)
    (hpairNonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0)
    (hpairCode : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0)
    (hpairStor : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).stor.size = 0)
    (hslot2 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 = 0)
    (hslot5 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk5 = 0) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0 :=
  original_pair_allowance_seed_of_constructor_receipt_and_approve_evidence
    history initialApart fresh first afterCut later last beforeCut rootsIn
    receiver input value sender nonce receiptAt succeeded slotsApart impl noUpgraded
    proxyApart rowSep initApart (.inl noCaller) hnumber htime htype hdata hvalue hnonce
    hfunds hgas hgasb hfactory hfnonce hpairNonce hpairCode hpairStor hslot2 hslot5

end Blanc.Composition.UniswapV2PairUsdcWeth9
