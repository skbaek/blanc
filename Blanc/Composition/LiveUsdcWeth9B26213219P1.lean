import Blanc.Composition.LiveUsdcWeth9B26213219Anchor
import Blanc.Composition.UniswapV2PairUsdcWeth9P1

/-!
# Original USDC history inputs for the concrete live Pair

This record contains the existing constructor-to-Pair-to-B producer inputs,
including the actual original histories, finite checks and evidence boundaries.
It contains no final allowance-zero or joint-checkpoint premise. Packaging these
inputs does not establish their truth. In particular, the raw upgrade check is
still unresolved and is not implied by retained-only governance evidence.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc
  Blanc.Composition.UniswapV2PairUsdcWeth9

/-- Original producer inputs, all tied to the endpoint B and the consumed future
trace. Historical query populations and transaction cuts are unchanged. -/
structure OriginalUsdcHistory {B future : BlockChain}
    (trace : ConfiguredHistoryTrace mainnetChainConfig B future) where
  checkpoint : BlockChain
  initial : HistoricalMappingKey → Prop
  W : List UsdcDeployedEntry
  v1Origin : BlockChain
  v1Completed : BlockChain
  origin : BlockChain
  completed : BlockChain
  pre : BlockChain
  post : BlockChain
  beforeV1 : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint v1Origin
  v1Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig v1Origin v1Completed
  v1Cut : v1Block.bodyTrace.transactions.TxSplit 30
  v1ToC : ConfiguredHistoryTraceIn HistFork mainnetChainConfig v1Completed origin
  first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed
  afterCut : first.bodyTrace.transactions.TxSplit 22
  later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre
  last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post
  beforeCut : last.bodyTrace.transactions.TxSplit 38
  postD : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post B
  initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial
  v1Fresh : V1MappingFreshKeys usdcProxy ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD) initial
  cBody : first.block.txs = HistoryAnchorBody.cBody
  dBody : last.block.txs = HistoryAnchorBody.dBody
  cBloom : first.block.header.bloom = HistoricalBloomExclusion.observedCBloom
  dBloom : last.block.header.bloom = HistoricalBloomExclusion.observedDBloom
  receipt : Fin 5 × Receipt
  receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt
  succeeded : receipt.2.succeeded = true
  slotsApart : ProxySlotsApart UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
  constructorOutput : v1Cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code
  noUpgraded : ∀ entry ∈ later.receiptLogs,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic])
  v1Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (actualV1MappingKeys usdcProxy
        ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)) = true
  v1FixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      v1FixedWriteSlots = true
  v2Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (actualV2CoveredKeys usdcProxy
        ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)) = true
  v21Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (actualV2_1CoveredKeys usdcProxy
        ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)) = true
  v22Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (actualV22CoveredKeys usdcProxy
        ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)) = true
  modernFixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      modernFixedWriteSlots = true
  initCheck : checkInitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress
      (pairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD).rawFrames = true
  approveEvidence : (∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
        G.sevm.currentTarget = usdcProxy → Sevm.selector G.sevm = 0x095ea7b3 →
        G.sevm.caller ≠ UniswapV2Pair.Creation.pairAddress) ∨
      (∀ entry ∈ later.receiptLogs,
        V1ApprovalZeroFor usdcProxy UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace) entry)
  hnumber : last.block.header.number = 10008355
  htime : last.block.header.timestamp = 1588710145
  hfactory : beforeCut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code
  dReceipt : Fin 5 × Receipt
  dReceiptAt : last.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
      some dReceipt
  dSucceeded : dReceipt.2.succeeded = true
  dLogs : dReceipt.2.logs = [⟨UniswapV2Pair.Creation.factory,
      [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2],
      UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes⟩]
  boundary : ∀ e ∈ W, ((later.step last).append postD).BoundaryAt e.base e.pre
  installed : ∀ e ∈ W, e.base.getCode e.adr = e.code
  impls : ∀ e ∈ W, UsdcImplCode e.code
  apart : ∀ e ∈ W, e.adr ≠ usdcProxy
  lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ originalV1WorldEntries completed.state W,
        l.adr = usdcLib ∧ l.code = Lib.code ∧ l.Active e.pre
  upgradeCheck : checkUpgradesWithinFrom usdcProxy (originalV1WorldEntries completed.state W)
      ((later.step last).append postD).rawNodes = true
  modernFresh : ∀ version, ModernMappingFreshKeys version usdcProxy
      ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD) initial
  senderExcluded : ∀ query ∈ ((MidHistoryTraceIn.tail last beforeCut).append postD).senderQueries,
      query.recover ≠ .ok UniswapV2Pair.Creation.pairAddress
  pairFresh : UniswapV2Pair.WriterFreshKeys (fun _ => False)
      (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
        ((MidHistoryTraceIn.tail last beforeCut).append postD))
  excluded : ∀ query : RetainedOldOwnerNativeQuery ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)
        usdcProxy UniswapV2Pair.Creation.pairAddress,
      executeEcrecover query.actualEvm ≠
        .ok gasEcrecover UniswapV2Pair.Creation.pairAddress.toB256.toBytes
  oldReady : ∀ (G : Exec.Frame), G ∈ ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD).settledFrames →
      G.sevm.currentTarget = usdcProxy →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = UniswapV2Pair.Creation.pairAddress →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none

/-- The original D body, successful receipt and admission construct the live
Pair deployment record. Its cut and post-D continuation are the very same
ones used for USDC history. No additional funding, gas, Pair-storage or factory
mapping observation is supplied. Receipt/body authentication remains explicit. -/
def OriginalUsdcHistory.pairDeployment {B future : BlockChain}
    {trace : ConfiguredHistoryTrace mainnetChainConfig B future}
    (history : OriginalUsdcHistory trace) : PairDeploymentTo B := by
  obtain ⟨factoryNonce, pairNonce, pairCode, guard⟩ :=
    original_factory_preconditions_of_receipt history.last history.beforeCut history.dBody
      history.hnumber history.htime history.hfactory history.dReceiptAt
      history.dSucceeded history.dLogs
  obtain ⟨txType, data, value, nonce, funds, gas, gasBound, _⟩ :=
    original_factory_admission_of_body history.last history.beforeCut history.dBody
      history.hnumber history.htime
  exact {
    pre := history.pre
    completed := history.post
    block := history.last
    number := history.hnumber
    time := history.htime
    cut := history.beforeCut
    gasPrice := 4000000000
    txType := txType
    data := data
    value := value
    nonce := nonce
    funds := funds
    gas := gas
    gasBound := gasBound
    factoryCode := history.hfactory
    factoryNonce := factoryNonce
    pairNonce := pairNonce
    pairCode := pairCode
    slot2 := guard
    history := history.postD
    fresh := history.pairFresh }

/-- The receipt-produced record keeps the original deployment suffix exactly. -/
theorem OriginalUsdcHistory.pairDeployment_trace {B future : BlockChain}
    {trace : ConfiguredHistoryTrace mainnetChainConfig B future}
    (history : OriginalUsdcHistory trace) :
    history.pairDeployment.trace =
      (MidHistoryTraceIn.tail history.last history.beforeCut).append history.postD := rfl

/-- The live checkpoint now uses the same original Pair receipt as the USDC
history producer. WETH receipt correspondence and sender-query exclusion remain
explicit; this construction adds no observations or final invariant premise. -/
theorem OriginalUsdcHistory.checkpoint_of_receipts {B future : BlockChain}
    {trace : ConfiguredHistoryTrace mainnetChainConfig B future}
    (history : OriginalUsdcHistory trace) (anchor : ObservedCheckpoint B)
    (wd : WethDeploymentTo B) (link : DeploymentHistoryLink wd history.pairDeployment)
    (holderFresh : SlotFootprint.Fresh Weth9.Key.slot Weth9.fixedSlots wd.keys (.bal pair))
    (excluded : ∀ query ∈ wd.trace.senderQueries, query.recover ≠ .ok pair)
    (logs : ∀ (spender : Adr) (data : Bytes),
      Log.mk weth [Weth9.approvalTopic, pair.toB256, spender.toB256] data ∉
        link.beforePairReceiptLogs) :
    JointCheckpoint2F pair usdc weth (FiniteCheckpoint.rowKeys usdcRows) wd.keys
      history.pairDeployment.keys history.pairDeployment.model B.state :=
  checkpoint_at_bound_deployment_model_of_receipts anchor wd history.pairDeployment link
    holderFresh excluded logs

/-- The frozen proxy address is the historical USDC producer's address. -/
theorem usdc_history_address : usdc = Usdc.usdcProxy := by
  decide +kernel

/-- Derive touched-row P1 from the original-history producer. No final P1 field
is stored in the input record, and no failed old-recovery condition is added. -/
theorem OriginalUsdcHistory.quiet {B future : BlockChain}
    {trace : ConfiguredHistoryTrace mainnetChainConfig B future}
    (history : OriginalUsdcHistory trace) : PairUsdcAllowQuiet pair usdc trace := by
  rw [pair_creation_address, usdc_history_address]
  exact pairUsdcAllowQuiet_of_connected_original_receipts_of_actualKeys_constructor_bootstrap
    history.beforeV1 history.v1Block history.v1Cut history.v1ToC history.first
    history.afterCut history.later history.last history.beforeCut history.postD
    trace history.initialApart history.v1Fresh history.cBody history.dBody
    history.cBloom history.dBloom history.receiptAt history.succeeded history.slotsApart
    history.constructorOutput history.noUpgraded history.v1Faithful history.v1FixedApart history.v2Faithful
    history.v21Faithful history.v22Faithful history.modernFixedApart history.initCheck history.approveEvidence
    history.hnumber history.htime history.hfactory history.dReceiptAt history.dSucceeded
    history.dLogs history.boundary history.installed history.impls history.apart
    history.lib history.upgradeCheck history.modernFresh history.senderExcluded history.pairFresh
    history.excluded history.oldReady

end Blanc.Composition.LiveUsdcWeth9B26213219
