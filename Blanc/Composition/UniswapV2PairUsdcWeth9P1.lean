import Blanc.Composition.UniswapV2PairUsdcOriginSeed
import Blanc.Composition.UniswapV2PairUsdcWeth9CheckpointF
import Blanc.Lift.Usdc.InitRowsHistory
import Blanc.Lift.Usdc.GovernanceHistory
import Blanc.Composition.UniswapV2PairUsdcHistoryZeroIn

/-!
# L1's P1 from the D→B USDC history

`PairUsdcAllowQuiet pair usdc trace` (`UniswapV2PairUsdcWeth9CheckpointF.lean`) is L1's
consumed premise P1: every allowance row of the Pair that the post-B trace touches reads
zero at B. `pairUsdcAllowQuiet_of_history` derives it from a historical-domain history from a
checkpoint `D` to `B` (the L3 history) through the Pair allowance law
`usdc_pairAllowance_noIncrease_deployed_apart` (`InitRowsHistory.lean`): on the spenders the
post-B trace touches (`PairTouchedSpenders`, a finite list), no tracked row rises from `D` to
`B`, so a zero seed at `D` stays zero at `B`.

The admin premise of that law comes from F2′ (`adminUpgradesWithinFrom_of_f2prime`,
`GovernanceHistory.lean`); `bal` and `capabilities` are discharged on `HistFork`. Every other
premise is a named hypothesis: the zero seed at `D` (`seedZero`) and the D→B premises of the
law. None is bundled.

`pairUsdcAllowQuiet_of_mid_history` instead consumes the genuine transaction
cut and retained-root zero transport. It keeps the original full-history
world and exclusion populations and seeds the exact after-cut state. Its
full-history upgrade input is not a broader pre-deployment F2′ restriction.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Usdc

/-- The spenders whose Pair allowance row the trace touches at `usdc`: membership in the
finite list `Usdc.historyTouchedKeys usdc trace`. -/
def PairTouchedSpenders (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (g : Adr) : Prop :=
  (Usdc.Key.allow pair g) ∈ Usdc.historyTouchedKeys usdc trace


/-- The exact finite spender population of `PairTouchedSpenders`, preserving duplicates
and order from the consumed post-checkpoint trace's touched-key list. -/
noncomputable def pairTouchedSpenders (pair usdc : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Adr :=
  (Usdc.historyTouchedKeys usdc trace).filterMap fun key =>
    match key with
    | .allow owner spender => if owner = pair then some spender else none
    | _ => none

theorem mem_pairTouchedSpenders {pair usdc spender : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    spender ∈ pairTouchedSpenders pair usdc trace ↔ PairTouchedSpenders pair usdc trace spender := by
  constructor
  · intro member
    obtain ⟨key, touched, selected⟩ := List.mem_filterMap.mp member
    cases key with
    | allow owner other =>
        change (if owner = pair then some other else none) = some spender at selected
        split at selected
        next equal =>
          subst owner
          cases selected
          exact touched
        next => cases selected
    | _ => cases selected
  · intro touched
    exact List.mem_filterMap.mpr ⟨.allow pair spender, touched, if_pos rfl⟩

/-- Historical key representation of precisely the allowance rows demanded by P1. -/
noncomputable def pairTouchedHistoricalAllowanceKeys (pair usdc : Adr) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    List HistoricalMappingKey :=
  (pairTouchedSpenders pair usdc trace).map (fun g => .modern (.allow pair g))

/-- The actual V1 source reduction uses the exact final P1 population, rather than
an independently supplied list. Both finite arithmetic checks remain explicit duties. -/
theorem v1_allowance_write_source_of_pairTouched
    {F : Fork → Prop} {cfgH cfg : ChainConfig} {checkpoint B future : BlockChain}
    {pair usdc spender : Adr}
    (history : ConfiguredHistoryTraceIn F cfgH checkpoint B)
    (capabilities : BodyStageCapabilities F) (trace : ConfiguredHistoryTrace cfg B future)
    (faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys pair usdc trace) (actualV1MappingKeys usdc history) = true)
    (fixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys pair usdc trace) v1FixedWriteSlots = true)
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = usdc) (code : node.sevm.code = ImplV1.code)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write)
    (observed : PairTouchedSpenders pair usdc trace spender)
    (tracked : allowSlot pair spender = write.key) :
    Sevm.selector node.sevm = 0x3357162b ∨
      (Sevm.selector node.sevm = 0x095ea7b3 ∧ node.sevm.caller = pair) ∨
      (Sevm.selector node.sevm = 0x23b872dd ∧ node.pc = 0x14e2 ∧
        (Sevm.dataWord node.sevm 4).toAdr = pair ∧ node.sevm.caller = spender) := by
  exact ConfiguredHistoryTraceIn.v1_allowance_write_source history capabilities
    (pairTouchedSpenders pair usdc trace) faithful fixedApart member target code found
    ((mem_pairTouchedSpenders trace).mpr observed) tracked

/-- **P1 from the D→B history.** For a historical-domain history from `D` to `B` over the
deployed world at `D`, F2′ at its implementation-slot writes with the deployment-before-upgrade order of
the F2′ implementations, the D→B premises of the Pair allowance law for the spenders the
post-B `trace` touches, and those rows zero at `D` (`seedZero`), the Pair's touched USDC
allowance rows read zero at `B`. -/
theorem pairUsdcAllowQuiet_of_history {pair usdc : Adr} {cfgH cfg : ChainConfig}
    {D B future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfgH D B)
    (trace : ConfiguredHistoryTrace cfg B future)
    {W : List UsdcDeployedEntry}
    (world : UsdcDeployedWorld history.BoundaryAt usdc W D.state)
    (governance : UsdcGovernanceF2primeAtImplWrites usdc history.rawFrames history.rawNodes)
    (deployedFirst : UpgradeTargetsDeployedFirst usdc W)
    (apartSlot : ImplSlotApart usdc history.rawNodes)
    (slotsApart : ProxySlotsApart pair (PairTouchedSpenders pair usdc trace))
    (rowSep : UsdcRowSep usdc pair (PairTouchedSpenders pair usdc trace) history.rawFrames)
    (noPairException : NoPairExceptionWrites usdc pair (PairTouchedSpenders pair usdc trace)
      history.rawFrames history.rawNodes)
    (initApart : InitRowsApart usdc pair (PairTouchedSpenders pair usdc trace) history.rawFrames)
    (seedZero : ∀ g, PairTouchedSpenders pair usdc trace g →
      (D.state.getStor usdc).get (Usdc.allowSlot pair g) = 0) :
    PairUsdcAllowQuiet pair usdc trace := by
  intro g hg
  have bal : ∀ {fork}, HistFork fork → fork.ruleSet.bal = none := fun h => HistFork.bal_none h
  have law := (ConfiguredHistoryTraceIn.usdc_pairAllowance_noIncrease_deployed_apart history
    BodyStageCapabilities.historical bal world
    (ConfiguredHistoryTraceIn.adminUpgradesWithinFrom_of_f2prime history
      BodyStageCapabilities.historical bal world governance deployedFirst)
    apartSlot slotsApart rowSep noPairException initApart ⟨g, hg, rfl⟩).2
  rw [seedZero g hg, B256.toNat_zero] at law
  exact B256.toNat_inj _ 0 ((Nat.le_zero.mp law).trans B256.toNat_zero.symm)

/-- **P1 from the genuine post-deployment cut.** The tracked rows are exactly
those touched by the consumed post-B trace. The original full-history world,
upgrades, native-query population and independent R4 premise are kept; sender
exclusion covers only the original post-cut suffix and later blocks.
Pair installation and the initial zero seed refer to the actual selected
transaction's after-state. No block-end replacement, per-root zero or supplied
NoPairExceptionWrites premise is needed. Actual deployment-seed and freshness
discharge remain separate obligations of the complete historical instance. -/
theorem pairUsdcAllowQuiet_of_mid_history_of_mid_senderQueries
    {cfgH cfg : ChainConfig} {checkpoint pre completed B future : BlockChain} {i : Nat}
    {usdc pair : Adr} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (prior : ConfiguredHistoryTraceIn HistFork cfgH checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfgH pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfgH completed B)
    (trace : ConfiguredHistoryTrace cfg B future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt usdc W checkpoint.state)
    (upgrades : UpgradesWithinFrom usdc W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart usdc ((prior.step block).append later).rawNodes)
    (apart : pair ≠ usdc)
    (senderExcluded : ∀ query ∈ ((MidHistoryTraceIn.tail block cut).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later)))
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair)
    (proxyApart : ProxyRowsApart usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawNodes)
    (rowSep : UsdcRowSep usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawFrames)
    (initApart : InitRowsApart usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawFrames)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) usdc pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = usdc →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (seedZero : ∀ g, PairTouchedSpenders pair usdc trace g →
      (cut.afterBenv.state.getStor usdc).get (allowSlot pair g) = 0) :
    PairUsdcAllowQuiet pair usdc trace := by
  intro g tracked
  exact UniswapV2PairUsdcOwners.mid_history_allowance_zero_of_mid_senderQueries
    prior block cut later world upgrades apartSlot apart senderExcluded notSystem
    installed initial fresh notPre proxyApart rowSep initApart excluded oldReady
    tracked (seedZero g tracked)

/-- P1 with V1 separation scoped to actual stores and the exact consumed spender
population. Modern row separation, original full-history R3/R4, initializer duties,
and genuine post-cut sender scope are unchanged. Both finite checks are explicit;
neither an arbitrary classifier nor a new endpoint premise is supplied. -/
theorem pairUsdcAllowQuiet_of_mid_history_of_actualV1Keys
    {cfgH cfg : ChainConfig} {checkpoint pre completed B future : BlockChain} {i : Nat}
    {usdc pair : Adr} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (prior : ConfiguredHistoryTraceIn HistFork cfgH checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfgH pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfgH completed B)
    (trace : ConfiguredHistoryTrace cfg B future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt usdc W checkpoint.state)
    (upgrades : UpgradesWithinFrom usdc W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart usdc ((prior.step block).append later).rawNodes)
    (apart : pair ≠ usdc)
    (senderExcluded : ∀ query ∈ ((MidHistoryTraceIn.tail block cut).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later)))
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair)
    (proxyApart : ProxyRowsApart usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawNodes)
    (modernSep : UsdcModernRowSep usdc pair (PairTouchedSpenders pair usdc trace)
      ((prior.step block).append later).rawFrames)
    (v1Faithful : SlotFootprint.checkFaithfulOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys pair usdc trace)
      (actualV1MappingKeys usdc ((prior.step block).append later)) = true)
    (v1FixedApart : SlotFootprint.checkApartOn HistoricalMappingKey.slot
      (pairTouchedHistoricalAllowanceKeys pair usdc trace) v1FixedWriteSlots = true)
    (initApart : InitRowsApart usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawFrames)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) usdc pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = usdc →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (seedZero : ∀ g, PairTouchedSpenders pair usdc trace g →
      (cut.afterBenv.state.getStor usdc).get (allowSlot pair g) = 0) :
    PairUsdcAllowQuiet pair usdc trace := by
  have codes := ConfiguredHistoryTraceIn.usdc_nodeCodes
    ((prior.step block).append later) BodyStageCapabilities.historical
    (fun selected => selected.bal_none) world upgrades apartSlot
  have rawClass : UsdcRawRowWriteClass usdc pair (PairTouchedSpenders pair usdc trace)
      ((prior.step block).append later).rawFrames ((prior.step block).append later).rawNodes :=
    ConfiguredHistoryTraceIn.usdcRawRowWriteClass_of_actualV1Keys
    ((prior.step block).append later) BodyStageCapabilities.historical codes proxyApart modernSep
    (pairTouchedSpenders pair usdc trace)
    (fun g observed => (mem_pairTouchedSpenders trace).mpr observed) v1Faithful v1FixedApart
  intro g tracked
  exact UniswapV2PairUsdcOwners.mid_history_allowance_zero_of_rawClass
    prior block cut later world upgrades apartSlot apart senderExcluded notSystem
    installed initial fresh notPre rawClass initApart excluded oldReady
    tracked (seedZero g tracked)

/-- Original full-history sender interface, restricted to the actual post-cut
queries before invoking the endpoint proof. -/
theorem pairUsdcAllowQuiet_of_mid_history
    {cfgH cfg : ChainConfig} {checkpoint pre completed B future : BlockChain} {i : Nat}
    {usdc pair : Adr} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (prior : ConfiguredHistoryTraceIn HistFork cfgH checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfgH pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfgH completed B)
    (trace : ConfiguredHistoryTrace cfg B future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt usdc W checkpoint.state)
    (upgrades : UpgradesWithinFrom usdc W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart usdc ((prior.step block).append later).rawNodes)
    (apart : pair ≠ usdc)
    (senderExcluded : ∀ query ∈ ((prior.step block).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later)))
    (notPre : ∀ {f : Fork}, HistFork f → ¬ f.ruleSet.isPrecomp pair)
    (proxyApart : ProxyRowsApart usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawNodes)
    (rowSep : UsdcRowSep usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawFrames)
    (initApart : InitRowsApart usdc pair (PairTouchedSpenders pair usdc trace) ((prior.step block).append later).rawFrames)
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step block).append later) usdc pair,
      executeEcrecover query.actualEvm ≠ .ok gasEcrecover pair.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step block).append later).settledFrames →
      G.sevm.currentTarget = usdc →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = pair →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none)
    (seedZero : ∀ g, PairTouchedSpenders pair usdc trace g →
      (cut.afterBenv.state.getStor usdc).get (allowSlot pair g) = 0) :
    PairUsdcAllowQuiet pair usdc trace := by
  exact pairUsdcAllowQuiet_of_mid_history_of_mid_senderQueries
    prior block cut later trace world upgrades apartSlot apart
    (fun query member => senderExcluded query
      (MidHistoryTraceIn.senderQueries_subset_full prior block cut later member))
    notSystem installed initial fresh notPre proxyApart rowSep initApart excluded oldReady seedZero

/-- Original receipt-derived seeds imply P1 for the exact spenders touched by
the consumed post-B trace. The full-history exclusion populations and genuine
post-D sender scope are unchanged; historical authentication remains separate. -/
theorem pairUsdcAllowQuiet_of_original_receipts
    {checkpoint B future : BlockChain} {cfg : ChainConfig}
    {initial : HistoricalMappingKey → Prop} {W : List UsdcDeployedEntry}
    {v1Origin v1Completed origin completed pre post : BlockChain}
    (v1Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig v1Origin v1Completed)
    (v1Cut : v1Block.bodyTrace.transactions.TxSplit 30)
    (v1ToC : ConfiguredHistoryTraceIn HistFork mainnetChainConfig v1Completed origin)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    (afterCut : first.bodyTrace.transactions.TxSplit 22)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (beforeCut : last.bodyTrace.transactions.TxSplit 38)
    (prior : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint pre)
    (postD : ConfiguredHistoryTraceIn HistFork mainnetChainConfig post B)
    (trace : ConfiguredHistoryTrace cfg B future)
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (v1Fresh : V1MappingFreshKeys usdcProxy ((prior.step last).append postD) initial)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ ((prior.step last).append postD).settledRoots)
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
    (rowSep : UsdcRowSep usdcProxy UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      ((prior.step last).append postD).rawFrames)
    (initApart : InitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      ((prior.step last).append postD).rawFrames)
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
    (world : UsdcDeployedWorld ((prior.step last).append postD).BoundaryAt usdcProxy W checkpoint.state)
    (upgrades : UpgradesWithinFrom usdcProxy W ((prior.step last).append postD).rawNodes)
    (apartSlot : ImplSlotApart usdcProxy ((prior.step last).append postD).rawNodes)
    (senderExcluded : ∀ query ∈ ((MidHistoryTraceIn.tail last beforeCut).append postD).senderQueries,
      query.recover ≠ .ok UniswapV2Pair.Creation.pairAddress)
    (pairFresh : UniswapV2Pair.WriterFreshKeys (fun _ => False)
      (UniswapV2Pair.pairMidTouchedKeysIn UniswapV2Pair.Creation.pairAddress
        ((MidHistoryTraceIn.tail last beforeCut).append postD)))
    (excluded : ∀ query : RetainedOldOwnerNativeQuery ((prior.step last).append postD)
        usdcProxy UniswapV2Pair.Creation.pairAddress,
      executeEcrecover query.actualEvm ≠
        .ok gasEcrecover UniswapV2Pair.Creation.pairAddress.toB256.toBytes)
    (oldReady : ∀ (G : Exec.Frame), G ∈ ((prior.step last).append postD).settledFrames →
      G.sevm.currentTarget = usdcProxy →
      ((G.sevm.code = ImplV2.code ∧ Sevm.selector G.sevm ∈ selV2.owners) ∨
        (G.sevm.code = ImplV2_1.code ∧ Sevm.selector G.sevm ∈ selV2_1.owners)) →
      (Sevm.dataWord G.sevm 4).toAdr = UniswapV2Pair.Creation.pairAddress →
      G.sevm.benvStat.rules.delegatedCodeAddress (G.pre.getCode 1) = none) :
    PairUsdcAllowQuiet UniswapV2Pair.Creation.pairAddress usdcProxy trace := by
  obtain ⟨_, _, seed⟩ := original_pair_allowance_seed_of_v1_constructor_output
    ((prior.step last).append postD) initialApart v1Fresh v1Block v1Cut v1ToC
    first afterCut later last beforeCut rootsIn cBody dBody cBloom dBloom receiptAt
    succeeded slotsApart constructorOutput noUpgraded rowSep initApart approveEvidence
    hnumber htime hfactory dReceiptAt dSucceeded dLogs
  obtain ⟨installed, initialized⟩ := original_pair_checkpoint_of_receipt
    last beforeCut dBody hnumber htime hfactory dReceiptAt dSucceeded dLogs
  have proxyApart := ConfiguredHistoryTraceIn.proxyRowsApart (P := usdcProxy)
    ((prior.step last).append postD) BodyStageCapabilities.historical
    (fun selected => selected.bal_none) slotsApart
  exact pairUsdcAllowQuiet_of_mid_history_of_mid_senderQueries
    prior last beforeCut postD trace world upgrades apartSlot (by decide)
    senderExcluded (by decide)
    (by rw [UniswapV2Pair.pairSem_image, installed]) initialized pairFresh
    (by intro f _; cases f <;> decide)
    proxyApart rowSep initApart excluded oldReady seed

/-- The original V1 deployment, proxy constructor, Pair deployment and later
history are one connected trace. Their actual transaction cuts derive the
receipt interval's root membership; no independent population premise is needed.
The deployed-world invariant starts after the proxy constructor's block;
the original creation/seed history remains separate and connected to that suffix.
All historical evidence, separation and full-history R3/R4 duties remain. -/
theorem pairUsdcAllowQuiet_of_connected_original_receipts
    {checkpoint B future : BlockChain} {cfg : ChainConfig}
    {initial : HistoricalMappingKey → Prop} {W : List UsdcDeployedEntry}
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
    (rowSep : UsdcRowSep usdcProxy UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD).rawFrames)
    (initApart : InitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress
      (PairTouchedSpenders UniswapV2Pair.Creation.pairAddress usdcProxy trace)
      ((((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD).rawFrames)
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
    (world : UsdcDeployedWorld ((later.step last).append postD).BoundaryAt usdcProxy W completed.state)
    (upgrades : UpgradesWithinFrom usdcProxy W ((later.step last).append postD).rawNodes)
    (apartSlot : ImplSlotApart usdcProxy ((later.step last).append postD).rawNodes)
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
  let full := (((((beforeV1.step v1Block).append v1ToC).step first).append later).step last).append postD
  let front := ((beforeV1.step v1Block).append v1ToC).step first
  let deployed := (later.step last).append postD
  have rawEq : full.rawFrames = front.rawFrames ++ deployed.rawFrames := by
    simp only [full, front, deployed, ConfiguredHistoryTraceIn.rawFrames_append,
      ConfiguredHistoryTraceIn.rawFrames, List.append_assoc]
  have settledEq : full.settledFrames = front.settledFrames ++ deployed.settledFrames := by
    simp only [full, front, deployed, ConfiguredHistoryTraceIn.settledFrames_append,
      ConfiguredHistoryTraceIn.settledFrames, List.append_assoc]
  obtain ⟨_, _, seed⟩ := original_pair_allowance_seed_of_v1_constructor_output
    full initialApart v1Fresh v1Block v1Cut v1ToC first afterCut later last beforeCut
    (fun R member => ConfiguredHistoryTraceIn.mem_settledRoots_of_between_txSplits
      ((beforeV1.step v1Block).append v1ToC) first afterCut later last beforeCut postD member)
    cBody dBody cBloom dBloom receiptAt succeeded slotsApart constructorOutput
    noUpgraded rowSep initApart approveEvidence hnumber htime hfactory
    dReceiptAt dSucceeded dLogs
  obtain ⟨installed, initialized⟩ := original_pair_checkpoint_of_receipt
    last beforeCut dBody hnumber htime hfactory dReceiptAt dSucceeded dLogs
  have proxyApart := ConfiguredHistoryTraceIn.proxyRowsApart (P := usdcProxy)
    deployed BodyStageCapabilities.historical (fun selected => selected.bal_none) slotsApart
  have excludedPost : ∀ query : RetainedOldOwnerNativeQuery deployed usdcProxy
      UniswapV2Pair.Creation.pairAddress,
      executeEcrecover query.actualEvm ≠
        .ok gasEcrecover UniswapV2Pair.Creation.pairAddress.toB256.toBytes := by
    intro query
    let original : RetainedOldOwnerNativeQuery full usdcProxy
        UniswapV2Pair.Creation.pairAddress :=
      { query with
        before := front.settledFrames ++ query.before
        position := by rw [settledEq, query.position, List.append_assoc] }
    exact excluded original
  exact pairUsdcAllowQuiet_of_mid_history_of_mid_senderQueries
    later last beforeCut postD trace world upgrades apartSlot (by decide)
    senderExcluded (by decide)
    (by rw [UniswapV2Pair.pairSem_image, installed]) initialized pairFresh
    (by intro f _; cases f <;> decide) proxyApart
    (fun G member target => rowSep G
      (by rw [rawEq]; exact List.mem_append_right _ member) target)
    (fun G member target => initApart G
      (by rw [rawEq]; exact List.mem_append_right _ member) target)
    excludedPost
    (fun G member => oldReady G
      (by rw [settledEq]; exact List.mem_append_right _ member)) seed

end Blanc.Composition.UniswapV2PairUsdcWeth9
