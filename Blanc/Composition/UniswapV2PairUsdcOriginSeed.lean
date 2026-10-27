import Blanc.Lift.Usdc.V1ConstructorReceiptZero
import Blanc.Lift.Usdc.HistoryAnchorCSender
import Blanc.Lift.Usdc.HistoryAnchorCCode
import Blanc.Lift.Usdc.ImplV1Lifetime
import Blanc.Lift.Usdc.HistoricalBloomExclusion
import Blanc.ExecutionBlockLogs
import Blanc.ExecutionTraceRootFrame
import Blanc.ExecutionTransactionDebitInverse
import Blanc.Lift.UniswapV2Factory.CreatePairInverseReceipt
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

/-- The original D receipt derives the factory guard and both accounts' entry
conditions. Pair collision exclusion is transported backwards through the
same admitted debit, so neither Pair freshness nor sender separation is an
input. Body, receipt and factory-code authentication remain producer duties. -/
theorem original_factory_preconditions_of_receipt
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
    (succeeded : receipt.2.succeeded = true)
    (receiptLogs : receipt.2.logs = [⟨UniswapV2Pair.Creation.factory,
      [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2],
      UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes⟩]) :
    (cut.benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max ∧
      (cut.benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0 ∧
      (cut.benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0 ∧
      ((cut.benv.state.get UniswapV2Pair.Creation.factory).stor.get UniswapV2Factory.fk2 &&&
        (0xffffffffffffffffffffffffffffffffffffffff : B256)) = 0 := by
  obtain ⟨root, roots, pc, sevm, devm, code, target, data, value, static, depth, fork,
    stack, memory, state⟩ :=
    original_factory_root_of_receipt last cut dBody hnumber htime hfactory receiptAt succeeded
  have retained : root ∈ cut.head.settledFrames := by
    rw [cut.head.settledFrames_eq, roots]
    simp only [rootFrames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Exec.Frame.committedFrames_self, List.mem_cons, true_or]
  obtain ⟨rawPost, outcome⟩ := root.exists_ok
  have rootRules : root.sevm.benvStat.rules = Fork.ruleSet .muirGlacier := by
    rw [BenvStat.rules, fork]
  have blockFork : cut.benv.stat.fork = .muirGlacier := by
    have same := fork
    rw [sevm] at same
    change cut.head.msg.benv.stat.fork = .muirGlacier at same
    rw [prepareMessage_benv cut.head.prepared] at same
    exact same
  have blockRules : cut.benv.stat.rules = Fork.ruleSet .muirGlacier := by
    rw [BenvStat.rules, blockFork]
  have blockSg : cut.benv.stat.rules.stateGas = none := by rw [blockRules]; rfl
  have finalReceipt := last.receipt_of_txSplit_settledRoots cut last.forkIn.stateGas_none
    (by decide) (by decide)
  rw [← cut.putIndex_eq.1] at receiptAt
  have lookup : cut.txBout.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt :=
    (cut.head.receipt_of_settledRoots blockSg).trans (finalReceipt.symm.trans receiptAt)
  have singleton : receipt.2.logs =
      [UniswapV2Factory.CreatePairInverse.symbolicPairCreated root.sevm
        UniswapV2Pair.Creation.pairAddress.toB256 1] := by
    rw [UniswapV2Factory.CreatePairInverse.symbolicPairCreated, target]
    exact receiptLogs
  obtain ⟨guard, fresh, nonce, _creation⟩ :=
    UniswapV2Factory.CreatePairInverse.entry_receipt_inverse cut.head blockSg retained
      (root := Exec.Frame.rootDeriv root) rfl pc code stack memory outcome root.committed
      (by change root.sevm.benvStat.rules.stateGas = none; rw [rootRules]; rfl)
      (by change root.sevm.benvStat.rules.bal = none; rw [rootRules]; rfl)
      (by change root.sevm.benvStat.rules.op.create2 = true; rw [rootRules]; rfl)
      value (by change root.sevm.data.length.toB256 = 0x44; rw [data]; decide +kernel)
      (by change Sevm.dataWord root.sevm 0 = _; rw [Sevm.dataWord, data]; decide +kernel)
      (by change Sevm.dataWord root.sevm 4 = _; rw [Sevm.dataWord, data]; decide +kernel)
      (by change Sevm.dataWord root.sevm 0x24 = _; rw [Sevm.dataWord, data]; decide +kernel)
      lookup singleton
  change ¬ State.Protected root.pre.state UniswapV2Pair.Creation.pairAddress at fresh
  rw [state] at fresh
  have pairFresh : (cut.head.debitState.get UniswapV2Pair.Creation.pairAddress).nonce = 0 ∧
      (cut.head.debitState.get UniswapV2Pair.Creation.pairAddress).code.size = 0 := by
    simpa only [State.Protected, not_or, not_not] using fresh
  have account := (cut.head.account_eq_of_debit_nonce_zero pairFresh.1).2
  rw [account] at pairFresh
  have senderCode : (cut.benv.state.get cut.head.sender).code.isEmpty = true :=
    checkTransaction_sender_code_emptyH (benv := cut.benv.beginTransaction)
      (by change cut.benv.stat.rules.delegationEnabled = false; rw [blockRules]; rfl)
      cut.head.checked
  have factorySize : (cut.benv.state.get UniswapV2Pair.Creation.factory).code.size = 13859 := by
    change (cut.benv.state.getCode UniswapV2Pair.Creation.factory).size = 13859
    rw [hfactory, ByteArray.size_eq_length_toList, UniswapV2Factory.code_toList_length]
  have senderApart : cut.head.sender ≠ UniswapV2Pair.Creation.factory := by
    intro same
    rw [same] at senderCode
    have empty : (cut.benv.state.get UniswapV2Pair.Creation.factory).code.size = 0 := by
      simpa only [ByteArray.isEmpty, beq_iff_eq] using senderCode
    rw [factorySize] at empty
    exact absurd empty (by decide)
  have factoryAccount : cut.head.debitState.get UniswapV2Pair.Creation.factory =
      cut.benv.state.get UniswapV2Pair.Creation.factory := by
    rw [(State.of_subBal cut.head.debit).2]
    exact debit_get_ne senderApart
  change (root.pre.state.get root.sevm.currentTarget).nonce ≠ UInt64.max at nonce
  rw [state, target, factoryAccount] at nonce
  change root.pre.getStorVal root.sevm.currentTarget UniswapV2Factory.fk2 &&&
    (0xffffffffffffffffffffffffffffffffffffffff : B256) = 0 at guard
  change (root.pre.state.getStor root.sevm.currentTarget).get UniswapV2Factory.fk2 &&&
    (0xffffffffffffffffffffffffffffffffffffffff : B256) = 0 at guard
  rw [state, target, cut.head.debitState_getStor_eq] at guard
  exact ⟨nonce, pairFresh.1, pairFresh.2, guard⟩


/-- The original D body and actual admission supply the forward factory inputs,
including the gas margin. No sender, funding or gas premise is supplied. -/
theorem original_factory_admission_of_body
    {pre post : BlockChain}
    (last : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (cut : last.bodyTrace.transactions.TxSplit 38)
    (dBody : last.block.txs = HistoryAnchorBody.dBody)
    (hnumber : last.block.header.number = 10008355)
    (htime : last.block.header.timestamp = 1588710145) :
    cut.tx.type = .zero 4000000000 (some UniswapV2Pair.Creation.factory) ∧
    cut.tx.data = UniswapV2Factory.createPairData ∧ cut.tx.value = 0 ∧ cut.tx.nonce = 205 ∧
    (cut.tx.gas * cut.head.effectiveGasPrice).toB256 ≤ cut.benv.state.bal cut.head.sender ∧
    cut.head.intrinsicGas + 2600000 ≤ cut.tx.gas ∧ cut.tx.gas < 2 ^ 64 ∧
    mainnetChainConfig.forkAt 10008355 1588710145 = .ok cut.benv.stat.fork ∧
    validateTransaction cut.benv.stat.rules cut.tx 0 =
      .ok (cut.head.intrinsicGas, cut.head.calldataFloorGasCost) := by
  have dtx := (HistoryAnchorBody.d_original_cut last cut dBody).2
  have dtype : cut.tx.type =
      .zero 4000000000 (some UniswapV2Pair.Creation.factory) := by
    rw [dtx]
    rfl
  have ddata : cut.tx.data = UniswapV2Factory.createPairData := by
    rw [dtx]
    decide +kernel
  have dvalue : cut.tx.value = 0 := by
    rw [dtx]
    rfl
  have dnonce : cut.tx.nonce = 205 := by
    rw [dtx]
    rfl
  have dgas : cut.tx.gas < 2 ^ 64 := by
    rw [dtx]
    decide +kernel
  have hblob : transactionBlobGasFee cut.benv cut.tx = 0 := by
    simp only [transactionBlobGasFee, Tx.isTypeThree, dtype, Bool.false_eq_true,
      ↓reduceIte]
  have hfunds : (cut.tx.gas * cut.head.effectiveGasPrice).toB256 ≤
      cut.benv.state.bal cut.head.sender := by
    simpa only [hblob, Nat.add_zero, State.incrNonce_bal] using
      (State.of_subBal cut.head.debit).1
  have hstat : cut.benv.stat = (initBenv last.fork pre last.block.header).stat :=
    cut.before.stat_eq
  have hfork : mainnetChainConfig.forkAt 10008355 1588710145 =
      .ok cut.benv.stat.fork := by
    have h := last.forkAt
    rw [hnumber, htime] at h
    rw [hstat]
    exact h
  have hmuir : cut.benv.stat.fork = .muirGlacier :=
    Except.ok.inj (hfork.symm.trans UniswapV2Pair.pair_deployment_fork)
  have hrules : cut.benv.stat.rules = Fork.ruleSet .muirGlacier := by
    rw [BenvStat.rules, hmuir]
  have hsg : cut.benv.stat.rules.stateGas = none := by
    rw [hrules]
    rfl
  have hvalid : validateTransaction cut.benv.stat.rules cut.tx 0 =
      .ok (cut.head.intrinsicGas, cut.head.calldataFloorGasCost) :=
    (validateTransaction_sender_congr_none hsg).trans cut.head.validation
  have evaluated : validateTransaction (Fork.ruleSet .muirGlacier)
      HistoryAnchorBody.d38Tx 0 = .ok (21800, 0) := by
    decide +kernel
  have validation := hvalid
  rw [hrules] at hvalid
  conv at hvalid => lhs; rw [dtx]
  have intrinsic : cut.head.intrinsicGas = 21800 :=
    (Prod.mk.inj (Except.ok.inj (hvalid.symm.trans evaluated))).1
  have hgas : cut.head.intrinsicGas + 2600000 ≤ cut.tx.gas := by
    rw [intrinsic, dtx]
    decide +kernel
  exact ⟨dtype, ddata, dvalue, dnonce, hfunds, hgas, dgas, hfork, validation⟩

/-- The original D receipt and body produce the initialized Pair checkpoint at
the same settled transaction cut. The actual forward result is identified by
determinism; no installed-code, initialized-state or Pair-freshness input is used. -/
theorem original_pair_checkpoint_of_receipt
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
    (succeeded : receipt.2.succeeded = true)
    (receiptLogs : receipt.2.logs = [⟨UniswapV2Pair.Creation.factory,
      [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2],
      UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes⟩]) :
    (cut.afterBenv.state.getCode UniswapV2Pair.Creation.pairAddress).toList =
      UniswapV2Pair.code.toList ∧
    UniswapV2Pair.InitializedCheckpoint
      (cut.afterBenv.state.getStor UniswapV2Pair.Creation.pairAddress)
      UniswapV2Pair.Creation.factory
      (UniswapV2Pair.Creation.domainSeparator cut.benv.stat.chainId.toB256
        UniswapV2Pair.Creation.pairAddress)
      UniswapV2Pair.Creation.token0 UniswapV2Pair.Creation.token1 := by
  obtain ⟨nonce, pairNonce, pairCode, guard⟩ :=
    original_factory_preconditions_of_receipt last cut dBody hnumber htime hfactory
      receiptAt succeeded receiptLogs
  obtain ⟨dtype, data, value, txNonce, funds, gas, gasBound, fork, valid⟩ :=
    original_factory_admission_of_body last cut dBody hnumber htime
  obtain ⟨state, output, result, installed, initialized⟩ :=
    UniswapV2Factory.pair_createPair_transaction_muirGlacier fork dtype data value txNonce
      valid cut.head.checked funds gas gasBound hfactory nonce pairNonce pairCode guard
  have same : state = cut.txState :=
    (Prod.mk.inj (Except.ok.inj (result.symm.trans cut.head.result))).1
  subst state
  exact ⟨installed, initialized⟩

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
charge and gas margin. The same original D receipt supplies the factory guard
and nonce/code collision exclusions through actual CREATE2 inversion. Body identity,
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
    {dReceipt : Fin 5 × Receipt}
    (dReceiptAt : last.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
      some dReceipt)
    (dSucceeded : dReceipt.2.succeeded = true)
    (dLogs : dReceipt.2.logs = [⟨UniswapV2Pair.Creation.factory,
      [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2],
      UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes⟩]) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0 := by
  obtain ⟨hfnonce, hpairNonce, hpairCode, hslot2⟩ :=
    original_factory_preconditions_of_receipt last beforeCut dBody hnumber htime hfactory
      dReceiptAt dSucceeded dLogs
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
  obtain ⟨dtype, ddata, dvalue, dnonce, hfunds, hgas, dgas, _, _⟩ :=
    original_factory_admission_of_body last beforeCut dBody hnumber htime
  exact original_pair_allowance_seed_of_constructor_receipt_and_approve_evidence
    history initialApart fresh first afterCut later last beforeCut rootsIn
    creceiver cinput cvalue sender cnonce receiptAt succeeded slotsApart implAfter noUpgraded
    rowSep initApart approveEvidence hnumber htime dtype ddata dvalue dnonce
    hfunds hgas dgas hfactory hfnonce hpairNonce hpairCode hslot2

/-- The original C/D bloom identities discharge both boundary receipt scans.
Only the intervening history needs Upgraded absence and, for the receipt-value
alternative, Approval safety. Original header/body/receipt identification,
initial pre-C state and finite separation remain explicit internal obligations.
The original D receipt, rather than assumed factory/Pair entry conditions,
feeds the factory inverse. -/
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
    {dReceipt : Fin 5 × Receipt}
    (dReceiptAt : last.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
      some dReceipt)
    (dSucceeded : dReceipt.2.succeeded = true)
    (dLogs : dReceipt.2.logs = [⟨UniswapV2Pair.Creation.factory,
      [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2],
      UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes⟩]) :
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
    ?_ hnumber htime hfactory dReceiptAt dSucceeded dLogs
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
separation remain the same unfulfilled producer obligations. The same D receipt
derives the factory guard and pre-debit collision exclusions internally. -/
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
    {dReceipt : Fin 5 × Receipt}
    (dReceiptAt : last.blockOutput.receiptsTrie[BLT.toBytes (.bytes (38 : Nat).toBytes)]? =
      some dReceipt)
    (dSucceeded : dReceipt.2.succeeded = true)
    (dLogs : dReceipt.2.logs = [⟨UniswapV2Pair.Creation.factory,
      [0xd3648bd0f6ba80134a33ba9275ac585d9d315f0ad8355cddefde31afa28d0e9,
       0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48,
       0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2],
      UniswapV2Pair.Creation.pairAddress.toB256.toBytes ++ (1 : B256).toBytes⟩]) :
    beforeCut.afterBenv.state.getCode usdcProxy = Proxy.code ∧
      (beforeCut.afterBenv.state.getStor usdcProxy).get implSlot = ProxyCreation.initialImplementation ∧
      ∀ g, Tr g → (beforeCut.afterBenv.state.getStor usdcProxy).get
        (allowSlot UniswapV2Pair.Creation.pairAddress g) = 0  := by
  have impl := ImplV1Lifetime.code_before_c22_of_creation_cut v1Block v1Cut v1ToC
    first afterCut BodyStageCapabilities.historical constructorOutput
  exact original_pair_allowance_seed_of_boundary_blooms history initialApart fresh
    first afterCut later last beforeCut rootsIn cBody dBody cBloom dBloom receiptAt
    succeeded slotsApart impl noUpgraded rowSep initApart approveEvidence
    hnumber htime hfactory dReceiptAt dSucceeded dLogs

end Blanc.Composition.UniswapV2PairUsdcWeth9
