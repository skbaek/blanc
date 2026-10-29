import Blanc.Composition.UniswapV2PairUsdcWeth9P1
import Blanc.Composition.UniswapV2PairUsdcCallersIn

/-! Initial runtime readiness and retained P1 from the original USDC history. -/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc

/-- The original V1 constructor runtime survives to the settled Pair deployment
cut. No installed-code premise is needed at an intervening boundary. -/
theorem original_v1_ready_at_pair_cut
    {v1Origin v1Completed origin completed pre post : BlockChain}
    (v1Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig v1Origin v1Completed)
    (v1Cut : v1Block.bodyTrace.transactions.TxSplit 30)
    (v1ToC : ConfiguredHistoryTraceIn HistFork mainnetChainConfig v1Completed origin)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (beforeCut : last.bodyTrace.transactions.TxSplit 38)
    (constructorOutput : v1Cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code) :
    UsdcEntriesReady [⟨ProxyCreation.initialImplementation.toAdr, ImplV1.code, completed.state, []⟩] beforeCut.afterBenv.state := by
  let span := (((MidHistoryTraceIn.tail v1Block v1Cut).append v1ToC).step first).append later
  have before := span.code_before_txSplit_of_installedCert ImplV1Lifetime.installedCert
    last beforeCut BodyStageCapabilities.historical constructorOutput
  have hsg : beforeCut.benv.stat.rules.stateGas = none := by
    change beforeCut.afterBenv.stat.rules.stateGas = none
    rw [last.txSplit_stat beforeCut]
    exact last.forkIn.stateGas_none
  have after := (beforeCut.head.noDel_of_installedCert ImplV1.cert_check
    ImplV1.cert_callOnly ImplV1.cert_noSelfdestruct
    ImplV1Lifetime.installedCert.notDelegation ImplV1Lifetime.installedCert.nonempty
    hsg before (last.txSplit_notCreated beforeCut _)).2.2
  intro e member
  have same := List.mem_singleton.mp member
  subst e
  refine ⟨after, ?_⟩
  intro impossible
  exact False.elim ((by decide +kernel : ImplV1.code.size ≠ Impl.code.size)
    (congrArg ByteArray.size impossible))

/-- P1 from the original constructor/receipt chronology and retained USDC
installations. Key, initializer and native-query evidence keeps the full original
history population; only governance and installation transport use the actual
post-Pair cut. The tracked rows are exactly those the future trace touches. -/
theorem pairUsdcAllowQuiet_of_connected_original_receipts_of_retained_actualKeys_constructor_bootstrap
    {checkpoint B future : BlockChain} {cfg : ChainConfig}
    {initial : HistoricalMappingKey → Prop} {entries : List UsdcDeployedEntry}
    {v1Origin v1Completed origin completed pre post : BlockChain}
    (beforeV1 : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint v1Origin)
    (v1Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig v1Origin v1Completed)
    (v1Cut : v1Block.bodyTrace.transactions.TxSplit 30)
    (v1ToC : ConfiguredHistoryTraceIn HistFork mainnetChainConfig v1Completed origin)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    (afterCut : first.bodyTrace.transactions.TxSplit 22)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (beforeCut : last.bodyTrace.transactions.TxSplit 38)
    (postD : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post B)
    (trace : ConfiguredHistoryTrace cfg B future)
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (v1Fresh : V1MappingFreshKeys usdcProxy ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD) initial)
    (cBody : first.block.txs = HistoryAnchorBody.cBody)
    (dBody : last.block.txs = HistoryAnchorBody.dBody)
    (cBloom : first.block.header.bloom = HistoricalBloomExclusion.observedCBloom)
    (dBloom : last.block.header.bloom = HistoricalBloomExclusion.observedDBloom)
    {receipt : Fin 5 × Receipt}
    (receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (slotsApart : ProxySlotsApart UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace))
    (constructorOutput : v1Cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code)
    (noUpgraded : ∀ entry ∈ later.receiptLogs,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
    (v1Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (actualV1MappingKeys usdcProxy
        ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)) = true)
    (v1FixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      v1FixedWriteSlots = true)
    (v2Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (actualV2CoveredKeys usdcProxy
        ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)) = true)
    (v21Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (actualV2_1CoveredKeys usdcProxy
        ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)) = true)
    (v22Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (actualV22CoveredKeys usdcProxy
        ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)) = true)
    (modernFixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      modernFixedWriteSlots = true)
    (initCheck : checkInitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress
      (pairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD).rawFrames = true)
    (approveEvidence :
      (∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
        G.sevm.currentTarget = usdcProxy → Sevm.selector G.sevm = 0x095ea7b3 →
        G.sevm.caller ≠ UniswapV2Pair.Creation.pairAddress) ∨
      (∀ entry ∈ later.receiptLogs,
        V1ApprovalZeroFor usdcProxy UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace) entry))
    (hnumber : last.block.header.number = 10008355)
    (htime : last.block.header.timestamp = 1588710145)
    (hfactory : beforeCut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    {dReceipt : Fin 5 × Receipt}
    (dReceiptAt : last.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
      some dReceipt)
    (dSucceeded : dReceipt.2.succeeded = true)
    (dLogs : dReceipt.2.logs = [⟨UniswapV2Pair.Creation.factory,
      [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2],
      UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes⟩])
    (impls : ∀ e ∈ originalV1WorldEntries completed.state entries, UsdcImplCode e.code)
    (lib : ∀ e ∈ originalV1WorldEntries completed.state entries, e.code = Impl.code →
      ∃ l ∈ originalV1WorldEntries completed.state entries,
        l.adr = usdcLib ∧ l.code = Lib.code)
    (governance : UsdcGovernanceF2primeOn usdcProxy
      ((MidHistoryTraceIn.tail last beforeCut).append postD).settledFrames)
    (origins : UsdcMidHistoryOrigins usdcProxy (originalV1WorldEntries completed.state entries)
      ((MidHistoryTraceIn.tail last beforeCut).append postD))
    (installations : UsdcGuardedInstallations usdcProxy
      (originalV1WorldEntries completed.state entries)
      ((MidHistoryTraceIn.tail last beforeCut).append postD).settledRoots)
    (modernFresh : ∀ version, ModernMappingFreshKeys version usdcProxy
      ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD) initial)
    (senderExcluded : ∀ query ∈ ((MidHistoryTraceIn.tail last beforeCut).append postD).senderQueries,
      query.recover ≠ .ok UniswapV2Pair.Creation.pairAddress)
    (pairFresh : UniswapV2Pair.WriterFreshKeys (fun _ => False)
      (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
        ((MidHistoryTraceIn.tail last beforeCut).append postD)))
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD)
        usdcProxy UniswapV2Pair.Creation.pairAddress,
      executeEcrecover query.actualEvm ≠
        .ok gasEcrecover UniswapV2Pair.Creation.pairAddress.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD).settledFrames →
      G.sevm.currentTarget = usdcProxy →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = UniswapV2Pair.Creation.pairAddress →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none) :
    PairUsdcAllowQuiet UniswapV2Pair.Creation.pairAddress usdcProxy trace := by
  let prior := ((((beforeV1.step v1Block).append v1ToC).step first).append later)
  let full := (prior.step last).append postD
  let mid := (MidHistoryTraceIn.tail last beforeCut).append postD
  have initApart : InitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace) full.rawFrames :=
    initRowsApart_of_check (fun g observed => (mem_pairTouchedSpenders trace).mpr observed) initCheck
  have v1Class : V1RawWriteClass usdcProxy UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace) full.rawFrames :=
    ConfiguredHistoryTraceIn.v1RawWriteClass_of_actualKeys full BodyStageCapabilities.historical
      (pairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (fun g observed => (mem_pairTouchedSpenders trace).mpr observed) v1Faithful v1FixedApart
  obtain ⟨selected, seed⟩ := original_pair_selected_zero_of_v1_constructor_output_of_v1Class
    full entries initialApart v1Fresh v1Block v1Cut v1ToC first afterCut later last beforeCut
    (fun R member => ConfiguredHistoryTraceIn.mem_settledRoots_of_between_txSplits
      ((beforeV1.step v1Block).append v1ToC) first afterCut later last beforeCut postD member)
    cBody dBody cBloom dBloom receiptAt succeeded slotsApart constructorOutput
    noUpgraded v1Class initApart approveEvidence hnumber htime hfactory
    dReceiptAt dSucceeded dLogs
  obtain ⟨installed, initialized⟩ := original_pair_checkpoint_of_receipt
    last beforeCut dBody hnumber htime hfactory dReceiptAt dSucceeded dLogs
  have proxyApart := ConfiguredHistoryTraceIn.proxyRowsApart (P := usdcProxy)
    full BodyStageCapabilities.historical (fun selected => selected.bal_none) slotsApart
  have knownFull := ConfiguredHistoryTraceIn.knownImplSlotApart_of_actualKeys
    full BodyStageCapabilities.historical (fun _ selected => HistFork.neutral selected)
    initialApart v1Fresh modernFresh
  have knownApart : ∀ R ∈ mid.settledRoots,
      KnownImplSlotApart usdcProxy (Exec.retainedNodes R.run) := by
    intro R root node member target code write found
    have rootInFull := MidHistoryTraceIn.settledRoots_subset_full prior last beforeCut postD root
    have rawRoot := full.mem_rawFrames_of_mem_settledRoots R rootInFull
    have rawNode := full.rawNodes_of_mem_rawFrames _ rawRoot node
      ((Exec.retainedNodes_sublist_rawNodes R.run).subset member)
    exact knownFull node rawNode target code write found
  have result :=
    UniswapV2PairUsdcCallers.mid_allowance_zero_from_pair_history_of_retained_origins_of_actualKeys
      prior last beforeCut postD impls lib governance installations knownApart
      (by decide) senderExcluded (by decide) (by intro f _; cases f <;> decide)
      (by rw [UniswapV2Pair.pairSem_image, installed]) initialized pairFresh proxyApart
      (pairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      (fun g observed => (mem_pairTouchedSpenders trace).mpr observed)
      v1Faithful v2Faithful v21Faithful v22Faithful v1FixedApart modernFixedApart
      initApart excluded oldReady selected origins seed
  exact result.2

end Blanc.Composition.UniswapV2PairUsdcWeth9
