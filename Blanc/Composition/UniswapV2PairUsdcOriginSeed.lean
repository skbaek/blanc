import Blanc.Lift.Usdc.V1ConstructorReceiptZero
import Blanc.Lift.Usdc.HistoryAnchorCSender
import Blanc.Lift.Usdc.HistoryAnchorCCode
import Blanc.Lift.Usdc.ImplV1Lifetime
import Blanc.Lift.Usdc.HistoricalBloomExclusion
import Blanc.ExecutionBlockLogs
import Blanc.ExecutionTraceRootFrame
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

/-- The original D receipt identifies the retained factory execution root.
Entry code still needs its genuine historical producer; no Pair freshness or
successful raw-execution premise is used to extract this same root. -/
theorem original_factory_root_of_receipt
    {pre post : BlockChain}
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (cut : last.bodyTrace.transactions.TxSplit 38)
    (dBody : last.block.txs = HistoryAnchorBody.dBody)
    (hnumber : last.block.header.number = 10008355)
    (htime : last.block.header.timestamp = 1588710145)
    (hfactory : cut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    {receipt : Fin 5 × Receipt}
    (receiptAt : last.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true) :
    ∃ root, cut.head.settledRoots = [root] ∧ root.pc = 0 ∧
      root.sevm = initSevm cut.head.msg ∧ root.pre = initDevm cut.head.msg ∧
      root.sevm.code = UniswapV2Factory.code ∧
      root.sevm.currentTarget = UniswapV2Pair.Creation.factory ∧
      root.sevm.data = UniswapV2Factory.createPairData ∧ root.sevm.value = 0 ∧
      root.sevm.isStatic = false ∧ root.sevm.depth = 1024 ∧
      root.sevm.benvStat.fork = .muirGlacier ∧
      root.pre.stack = [] ∧ root.pre.memory = Mem.empty ∧
      root.pre.state = cut.head.debitState := by
  have dtx := (HistoryAnchorBody.d_original_cut last cut dBody).2
  have dtype : cut.tx.type = .zero 4000000000 (some UniswapV2Pair.Creation.factory) := by
    rw [dtx]
    rfl
  have ddata : cut.tx.data = UniswapV2Factory.createPairData := by
    rw [dtx]
    decide +kernel
  have dvalue : cut.tx.value = 0 := by
    rw [dtx]
    rfl
  have hstat : cut.benv.stat = (initBenv last.fork pre last.block.header).stat :=
    cut.before.stat_eq
  have hfork : mainnetChainConfig.forkAt 10008355 1588710145 = .ok cut.benv.stat.fork := by
    have h := last.forkAt
    rw [hnumber, htime] at h
    rw [hstat]
    exact h
  have hmuir : cut.benv.stat.fork = .muirGlacier :=
    Except.ok.inj (hfork.symm.trans UniswapV2Pair.pair_deployment_fork)
  have hrules : cut.benv.stat.rules = Fork.ruleSet .muirGlacier := by
    rw [BenvStat.rules, hmuir]
  have actual := last.receipt_of_txSplit_settledRoots cut last.forkIn.stateGas_none
    (by decide) (by decide)
  rw [← cut.putIndex_eq.1] at receiptAt
  have same := Option.some.inj (actual.symm.trans receiptAt)
  have status := congrArg (fun r : Fin 5 × Receipt => r.2.succeeded) same
  change cut.head.messageOut.error.isNone = receipt.2.succeeded at status
  have clean : cut.head.messageOut.error = none := by
    rw [succeeded] at status
    cases error : cut.head.messageOut.error with
    | none => rfl
    | some halt => rw [error] at status; contradiction
  have prepared : cut.head.msg =
      callMessage { cut.benv.beginTransaction with state := cut.head.debitState }
        (transactionTenv cut.benv.beginTransaction cut.tx cut.index cut.head.sender
          cut.head.effectiveGasPrice cut.head.intrinsicGas cut.head.blobVersionedHashes)
        cut.tx UniswapV2Pair.Creation.factory := by
    exact Except.ok.inj (cut.head.prepared.symm.trans
      (prepareMessage_call (by rw [dtype]; rfl)))
  have msgRules : cut.head.msg.benv.stat.rules = Fork.ruleSet .muirGlacier := by
    rw [prepared]
    exact hrules
  have msgHsg : cut.head.msg.benv.stat.rules.stateGas = none := by rw [msgRules]; rfl
  have disabled : cut.head.msg.benv.stat.rules.delegationEnabled = false := by
    rw [msgRules]
    rfl
  have delegation : messageCallDelegation cut.head.msg = .ok (cut.head.msg, 0) :=
    processMessageCall.legacyAuthorization_disabled cut.head.msg disabled
  have direct : messageCallExecutionMessage cut.head.msg = cut.head.msg :=
    Msg.resolveCodeDelegation_disabled cut.head.msg disabled
  have target : cut.head.msg.target.isNone = false := by rw [prepared]; rfl
  have zero : cut.head.msg.value = 0 := by
    rw [prepared]
    change cut.tx.value.toB256 = 0
    rw [dvalue]
    rfl
  have entry : (Frame.ofCall cut.head.msg).enter = .run (initEvm cut.head.msg) := by
    apply Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero zero)
      (adr := UniswapV2Pair.Creation.factory)
    · rw [prepared]
      rfl
    · change cut.head.msg.benv.stat.rules.isPrecomp UniswapV2Pair.Creation.factory = false
      rw [msgRules]
      decide +kernel
  obtain ⟨root, roots, pc, sevm, devm⟩ :=
    cut.head.message.exists_root_of_clean_call msgHsg target clean delegation direct entry
  refine ⟨root, roots, pc, sevm, devm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sevm, prepared]
    change cut.head.debitState.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code
    rw [(State.of_subBal cut.head.debit).2, State.setBal_getCode]
    change ((cut.benv.state.incrNonce cut.head.sender).get UniswapV2Pair.Creation.factory).code = _
    rw [State.incrNonce_get_code]
    exact hfactory
  · rw [sevm, prepared]; rfl
  · rw [sevm, prepared]; exact ddata
  · rw [sevm]; exact zero
  · rw [sevm, prepared]; rfl
  · rw [sevm, prepared]; rfl
  · rw [sevm, prepared]; exact hmuir
  · rw [devm]; rfl
  · rw [devm]; rfl
  · rw [devm, prepared]; rfl

/-- Derive the actual after-D proxy code, implementation word and zero tracked
Pair allowance rows from the actual constructor receipt and exact C-to-D
interval. The factory's admitted execution supplies D preservation, rather
than a supplied foreign-storage equality. The fixed proxy-slot separation
also derives write separation over the actual history. -/
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
    (hslot2 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 &&& (0xffffffffffffffffffffffffffffffffffffffff : B256) = 0) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0 := by
  have early : last.block.header.timestamp < mainnetCancunTimestamp := by
    rw [htime]
    decide
  have proxyApart :
      ProxyRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawNodes :=
    ConfiguredHistoryTraceIn.proxyRowsApart history BodyStageCapabilities.historical
      (fun selected => selected.bal_none) slotsApart
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
    hfnonce hpairNonce hpairCode hslot2 usdcProxy (by decide) (by decide) nonempty
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
    (hslot2 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 &&& (0xffffffffffffffffffffffffffffffffffffffff : B256) = 0) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0 :=
  original_pair_allowance_seed_of_constructor_receipt_and_approve_evidence
    history initialApart fresh first afterCut later last beforeCut rootsIn
    receiver input value sender nonce receiptAt succeeded slotsApart impl noUpgraded
    rowSep initApart (.inl noCaller) hnumber htime htype hdata hvalue hnonce
    hfunds hgas hgasb hfactory hfnonce hpairNonce hpairCode hslot2

/-- Connect both exact frozen body identities to the actual after-D seed.
The original C/D cuts supply their decoded fields and the C signature supplies
the admitted sender. The successful receipt and constructor transport preserve
V1 code from the exact pre-C cut. The successful debit supplies
funding, and validation at the configured D fork supplies its exact intrinsic
charge and gas margin. Body identity,
original receipt authentication, state and historical write-safety
obligations remain explicit internal conditions, not adopted final ENV facts. -/
theorem original_pair_allowance_seed_of_bodies_and_constructor_receipt
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
    (cBody : first.block.txs = HistoryAnchorBody.cBody)
    (dBody : last.block.txs = HistoryAnchorBody.dBody)
    {receipt : Fin 5 × Receipt}
    (receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (slotsApart : ProxySlotsApart UniswapV2Pair.Creation.pairAddress Tr)
    (impl : afterCut.benv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code)
    (noUpgraded : ∀ entry ∈
      first.receiptLogsBetween 23 first.bodyTrace.decodedTxs.length ++
        later.receiptLogs ++ last.receiptLogsBetween 0 38,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
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
    (htime : last.block.header.timestamp = 1588710145)
    (hfactory : beforeCut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    (hfnonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max)
    (hpairNonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0)
    (hpairCode : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0)
    (hslot2 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 &&& (0xffffffffffffffffffffffffffffffffffffffff : B256) = 0) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0 := by
  have sender := HistoryAnchorBody.c_original_cut_sender_mainnet first afterCut cBody
  obtain ⟨_, cnonce, creceiver, cvalue, cinput, _⟩ :=
    HistoryAnchorBody.c_original_cut_fields first afterCut cBody
  have clean := (ProxyCreation.original_constructor_seed_of_receipt_cut22
    first afterCut first.forkIn.stateGas_none creceiver cinput cvalue sender cnonce
    receiptAt succeeded slotsApart).1
  have nonempty :
      (afterCut.benv.state.getCode ProxyCreation.initialImplementation.toAdr).toList ≠ [] := by
    rw [impl]
    exact (show UsdcContextCode ImplV1.code from .inr (.inl rfl)).ne_nil
  have implAfter := (HistoryAnchorBody.c_original_cut_initialImplementation_code
    first afterCut cBody first.forkIn.stateGas_none clean nonempty).trans impl
  have dtx := (HistoryAnchorBody.d_original_cut last beforeCut dBody).2
  have dtype : beforeCut.tx.type =
      .zero 4000000000 (some UniswapV2Pair.Creation.factory) := by
    rw [dtx]
    rfl
  have ddata : beforeCut.tx.data = UniswapV2Factory.createPairData := by
    rw [dtx]
    decide +kernel
  have dvalue : beforeCut.tx.value = 0 := by
    rw [dtx]
    rfl
  have dnonce : beforeCut.tx.nonce = 205 := by
    rw [dtx]
    rfl
  have dgas : beforeCut.tx.gas < 2 ^ 64 := by
    rw [dtx]
    decide +kernel
  have hblob : transactionBlobGasFee beforeCut.benv beforeCut.tx = 0 := by
    simp only [transactionBlobGasFee, Tx.isTypeThree, dtype, Bool.false_eq_true,
      ↓reduceIte]
  have hfunds : (beforeCut.tx.gas * beforeCut.head.effectiveGasPrice).toB256 ≤
      beforeCut.benv.state.bal beforeCut.head.sender := by
    simpa only [hblob, Nat.add_zero, State.incrNonce_bal] using
      (State.of_subBal beforeCut.head.debit).1
  have hstat : beforeCut.benv.stat = (initBenv last.fork pre last.block.header).stat :=
    beforeCut.before.stat_eq
  have hfork : mainnetChainConfig.forkAt 10008355 1588710145 =
      .ok beforeCut.benv.stat.fork := by
    have h := last.forkAt
    rw [hnumber, htime] at h
    rw [hstat]
    exact h
  have hmuir : beforeCut.benv.stat.fork = .muirGlacier :=
    Except.ok.inj (hfork.symm.trans UniswapV2Pair.pair_deployment_fork)
  have hrules : beforeCut.benv.stat.rules = Fork.ruleSet .muirGlacier := by
    rw [BenvStat.rules, hmuir]
  have hsg : beforeCut.benv.stat.rules.stateGas = none := by
    rw [hrules]
    rfl
  have hvalid : validateTransaction beforeCut.benv.stat.rules beforeCut.tx 0 =
      .ok (beforeCut.head.intrinsicGas, beforeCut.head.calldataFloorGasCost) :=
    (validateTransaction_sender_congr_none hsg).trans beforeCut.head.validation
  have evaluated : validateTransaction (Fork.ruleSet .muirGlacier)
      HistoryAnchorBody.d38Tx 0 = .ok (21800, 0) := by
    decide +kernel
  rw [hrules] at hvalid
  conv at hvalid => lhs; rw [dtx]
  have intrinsic : beforeCut.head.intrinsicGas = 21800 :=
    (Prod.mk.inj (Except.ok.inj (hvalid.symm.trans evaluated))).1
  have hgas : beforeCut.head.intrinsicGas + 2600000 ≤ beforeCut.tx.gas := by
    rw [intrinsic, dtx]
    decide +kernel
  exact original_pair_allowance_seed_of_constructor_receipt_and_approve_evidence
    history initialApart fresh first afterCut later last beforeCut rootsIn
    creceiver cinput cvalue sender cnonce receiptAt succeeded slotsApart implAfter noUpgraded
    rowSep initApart approveEvidence hnumber htime dtype ddata dvalue dnonce
    hfunds hgas dgas hfactory hfnonce hpairNonce hpairCode hslot2

/-- The original C/D bloom identities discharge both boundary receipt scans.
Only the intervening history needs Upgraded absence and, for the receipt-value
alternative, Approval safety. Original header/body/receipt identification,
initial pre-C state and finite separation remain explicit internal obligations. -/
theorem original_pair_allowance_seed_of_boundary_blooms
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
    (cBody : first.block.txs = HistoryAnchorBody.cBody)
    (dBody : last.block.txs = HistoryAnchorBody.dBody)
    (cBloom : first.block.header.bloom = HistoricalBloomExclusion.observedCBloom)
    (dBloom : last.block.header.bloom = HistoricalBloomExclusion.observedDBloom)
    {receipt : Fin 5 × Receipt}
    (receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (slotsApart : ProxySlotsApart UniswapV2Pair.Creation.pairAddress Tr)
    (impl : afterCut.benv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code)
    (noUpgraded : ∀ entry ∈ later.receiptLogs,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
    (rowSep : UsdcRowSep usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawFrames)
    (initApart : InitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawFrames)
    (approveEvidence :
      (∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
        G.sevm.currentTarget = usdcProxy → Sevm.selector G.sevm = 0x095ea7b3 →
        G.sevm.caller ≠ UniswapV2Pair.Creation.pairAddress) ∨
      (∀ entry ∈ later.receiptLogs,
        V1ApprovalZeroFor usdcProxy UniswapV2Pair.Creation.pairAddress Tr entry))
    (hnumber : last.block.header.number = 10008355)
    (htime : last.block.header.timestamp = 1588710145)
    (hfactory : beforeCut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    (hfnonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max)
    (hpairNonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0)
    (hpairCode : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0)
    (hslot2 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 &&& (0xffffffffffffffffffffffffffffffffffffffff : B256) = 0) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0 := by
  have firstMissing : ¬ LogBloom.ContainsAddress first.block.header.bloom usdcProxy := by
    rw [cBloom]
    exact HistoricalBloomExclusion.observedC_missing
  have lastMissing : ¬ LogBloom.ContainsAddress last.block.header.bloom usdcProxy := by
    rw [dBloom]
    exact HistoricalBloomExclusion.observedD_missing
  have noUpgradedFull := ConfiguredHistoryTraceIn.receiptLogs_between_of_boundary_bloom_missing
    first later last first.forkIn.stateGas_none last.forkIn.stateGas_none
    firstMissing lastMissing (firstLo := 23) (firstHi := first.bodyTrace.decodedTxs.length)
    (lastLo := 0) (lastHi := 38)
    (fun entry => ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
    (fun _ different matched => different matched.1) noUpgraded
  refine original_pair_allowance_seed_of_bodies_and_constructor_receipt
    history initialApart fresh first afterCut later last beforeCut rootsIn cBody dBody
    receiptAt succeeded slotsApart impl noUpgradedFull rowSep initApart
    ?_ hnumber htime hfactory hfnonce hpairNonce hpairCode hslot2
  rcases approveEvidence with callers | logs
  · exact Or.inl callers
  · apply Or.inr
    apply ConfiguredHistoryTraceIn.receiptLogs_between_of_boundary_bloom_missing
      first later last first.forkIn.stateGas_none last.forkIn.stateGas_none
      firstMissing lastMissing
      (property := V1ApprovalZeroFor usdcProxy UniswapV2Pair.Creation.pairAddress Tr)
      _ logs
    intro entry different spender value _ matched
    exact False.elim (different (congrArg Log.address matched))

/-- Internal composition from the actual V1 constructor's settled output to
the original after-D allowance seed. The source transaction remainder, entire
V1-to-C history and C prefix supply pre-C implementation code internally.

`constructorOutput` must be proved by the genuine V1 constructor producer;
it is not a new final environmental premise or a code-observation adoption.
Original trace/anchor identification, middle-history evidence and finite
separation remain the same unfulfilled producer obligations. -/
theorem original_pair_allowance_seed_of_v1_constructor_output
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {Tr : Adr → Prop} {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : V1MappingFreshKeys usdcProxy history initial)
    {v1Origin v1Completed origin completed pre post : BlockChain}
    (v1Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig v1Origin v1Completed)
    (v1Cut : v1Block.bodyTrace.transactions.TxSplit 30)
    (v1ToC : ConfiguredHistoryTraceIn HistFork mainnetChainConfig v1Completed origin)
    (first : ConfiguredBlockTraceIn HistFork mainnetChainConfig origin completed)
    (afterCut : first.bodyTrace.transactions.TxSplit 22)
    (later : ConfiguredHistoryTraceIn HistFork mainnetChainConfig completed pre)
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (beforeCut : last.bodyTrace.transactions.TxSplit 38)
    (rootsIn : ∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
      last.rootsBeforeTxSplit beforeCut, R ∈ history.settledRoots)
    (cBody : first.block.txs = HistoryAnchorBody.cBody)
    (dBody : last.block.txs = HistoryAnchorBody.dBody)
    (cBloom : first.block.header.bloom = HistoricalBloomExclusion.observedCBloom)
    (dBloom : last.block.header.bloom = HistoricalBloomExclusion.observedDBloom)
    {receipt : Fin 5 × Receipt}
    (receiptAt : first.blockOutput.receiptsTrie[BLT.toBytes (.bytes (22 : Nat).toBytes)]? =
      some receipt)
    (succeeded : receipt.2.succeeded = true)
    (slotsApart : ProxySlotsApart UniswapV2Pair.Creation.pairAddress Tr)
    (constructorOutput : v1Cut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr =
      ImplV1.code)
    (noUpgraded : ∀ entry ∈ later.receiptLogs,
      ¬ (entry.address = usdcProxy ∧ entry.topics = [Proxy.upgradedTopic]))
    (rowSep : UsdcRowSep usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawFrames)
    (initApart : InitRowsApart usdcProxy UniswapV2Pair.Creation.pairAddress Tr history.rawFrames)
    (approveEvidence :
      (∀ R ∈ ((MidHistoryTraceIn.tail first afterCut).append later).settledRoots ++
          last.rootsBeforeTxSplit beforeCut, ∀ G ∈ Exec.committedFrames R.run,
        G.sevm.currentTarget = usdcProxy → Sevm.selector G.sevm = 0x095ea7b3 →
        G.sevm.caller ≠ UniswapV2Pair.Creation.pairAddress) ∨
      (∀ entry ∈ later.receiptLogs,
        V1ApprovalZeroFor usdcProxy UniswapV2Pair.Creation.pairAddress Tr entry))
    (hnumber : last.block.header.number = 10008355)
    (htime : last.block.header.timestamp = 1588710145)
    (hfactory : beforeCut.benv.state.getCode UniswapV2Pair.Creation.factory = UniswapV2Factory.code)
    (hfnonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max)
    (hpairNonce : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0)
    (hpairCode : (beforeCut.benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0)
    (hslot2 : (beforeCut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 &&& (0xffffffffffffffffffffffffffffffffffffffff : B256) = 0) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0  := by
  have impl := ImplV1Lifetime.code_before_c22_of_creation_cut v1Block v1Cut v1ToC
    first afterCut BodyStageCapabilities.historical constructorOutput
  exact original_pair_allowance_seed_of_boundary_blooms history initialApart fresh
    first afterCut later last beforeCut rootsIn cBody dBody cBloom dBloom receiptAt
    succeeded slotsApart impl noUpgraded rowSep initApart approveEvidence
    hnumber htime hfactory hfnonce hpairNonce hpairCode hslot2

end Blanc.Composition.UniswapV2PairUsdcWeth9
