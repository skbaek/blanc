import Blanc.ExecutionHistory
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistoryEffects
import Blanc.RequestsOutput

/-!
Contract-neutral forward construction of one configured block.

Every theorem here turns proof-produced evidence about the parts of a block body
(the two unchecked system calls, the transaction fold, the two checked request
calls) into Jaune's own `applyBody`, `stateTransitionUsing` and
`ConfiguredBlockTrace` results. Header commitments are equalities the caller
discharges by construction (`stateRoot := st.root`, `requestsHash := some
(computeRequestsHash bout.requests)`, …), so no root, bloom or hash is ever
evaluated. Nothing here names a contract or a fork beyond `CoveredFork`.
-/

namespace Blanc.BlockForward

open Jaune ExecutionTrace

/-! ## Deposit requests -/

/-- Receipts without logs contribute no deposit request: the key list is
generalized so the fold can be followed one receipt at a time. -/
private theorem parseDepositRequests_keys {bout : BlockOutput} :
    ∀ keys : List Bytes,
      (∀ key ∈ keys, ∃ entry, bout.receiptsTrie[key]? = some entry ∧ entry.2.logs = []) →
      parseDepositRequests { bout with receiptKeys := keys } = .ok []
  | [], _ => by
    unfold parseDepositRequests
    dsimp only
    rw [List.forIn_nil]
    rfl
  | key :: keys, h => by
    obtain ⟨entry, hentry, hlogs⟩ := h key List.mem_cons_self
    have ih := parseDepositRequests_keys keys (fun k hk => h k (List.mem_cons_of_mem key hk))
    unfold parseDepositRequests at ih ⊢
    dsimp only at ih ⊢
    rw [List.forIn_cons, hentry]
    simp only [Option.toExcept, bind, Except.bind, hlogs, List.forIn_nil, pure, Except.pure]
    exact ih

/-- A block whose every receipt carries no log parses no deposit request. -/
theorem parseDepositRequests_of_no_logs {bout : BlockOutput}
    (h : ∀ key ∈ bout.receiptKeys,
      ∃ entry, bout.receiptsTrie[key]? = some entry ∧ entry.2.logs = []) :
    parseDepositRequests bout = .ok [] := by
  have := parseDepositRequests_keys bout.receiptKeys h
  cases bout
  exact this

/-- A loop body that yields its accumulator unchanged on every log away from the
deposit contract leaves the accumulator unchanged over such a log list. -/
theorem forIn_logs_yield_of_skip {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : Log → Bytes → m (ForInStep Bytes))
    (hf : ∀ log acc, log.address ≠ depositContractAddress → f log acc = pure (.yield acc)) :
    ∀ (logs : List Log) (acc : Bytes),
      (∀ log ∈ logs, log.address ≠ depositContractAddress) → forIn logs acc f = pure acc
  | [], _, _ => List.forIn_nil
  | log :: logs, acc, h => by
    rw [List.forIn_cons, hf log acc (h log List.mem_cons_self), pure_bind]
    exact forIn_logs_yield_of_skip f hf logs acc (fun l hl => h l (List.mem_cons_of_mem log hl))

/-- Receipts whose logs avoid the deposit contract contribute no deposit request,
generalized over the key list as above. -/
private theorem parseDepositRequests_keys_of_no_deposit {bout : BlockOutput} :
    ∀ keys : List Bytes,
      (∀ key ∈ keys, ∃ entry, bout.receiptsTrie[key]? = some entry ∧
        ∀ log ∈ entry.2.logs, log.address ≠ depositContractAddress) →
      parseDepositRequests { bout with receiptKeys := keys } = .ok []
  | [], _ => by
    unfold parseDepositRequests
    dsimp only
    rw [List.forIn_nil]
    rfl
  | key :: keys, h => by
    obtain ⟨entry, hentry, hlogs⟩ := h key List.mem_cons_self
    have ih := parseDepositRequests_keys_of_no_deposit keys
      (fun k hk => h k (List.mem_cons_of_mem key hk))
    unfold parseDepositRequests at ih ⊢
    dsimp only at ih ⊢
    generalize hF : (fun (log : Log) (depositRequests : Bytes) =>
      if log.address = depositContractAddress ∧
          log.topics[0]? = some depositEventSignatureHash then do
        let request ← Except.mapError TransitionError.block (extractDepositData log.data)
        pure (ForInStep.yield (depositRequests ++ request))
      else pure (ForInStep.yield depositRequests)) = F at ih ⊢
    have hskip : ∀ log acc, log.address ≠ depositContractAddress → F log acc = pure (.yield acc) := by
      intro log acc hne
      have hc : ¬ (log.address = depositContractAddress ∧
          log.topics[0]? = some depositEventSignatureHash) := fun hc => hne hc.1
      rw [← hF]
      simp only [hc, ite_false]
    rw [List.forIn_cons, hentry]
    simp only [Option.toExcept, bind, Except.bind]
    rw [forIn_logs_yield_of_skip F hskip entry.2.logs [] hlogs]
    simp only [pure, Except.pure]
    exact ih

/-- A block whose every receipt's logs avoid the deposit contract parses no deposit
request. -/
theorem parseDepositRequests_of_no_deposit_logs {bout : BlockOutput}
    (h : ∀ key ∈ bout.receiptKeys, ∃ entry, bout.receiptsTrie[key]? = some entry ∧
      ∀ log ∈ entry.2.logs, log.address ≠ depositContractAddress) :
    parseDepositRequests bout = .ok [] := by
  have := parseDepositRequests_keys_of_no_deposit bout.receiptKeys h
  cases bout
  exact this

/-- A block without transactions parses no deposit request. -/
theorem parseDepositRequests_of_no_receipts {bout : BlockOutput}
    (h : bout.receiptKeys = []) : parseDepositRequests bout = .ok [] := by
  apply parseDepositRequests_of_no_logs
  rw [h]
  intro key hkey
  exact absurd hkey (List.not_mem_nil)

/-! ## The request pass -/

/-- Appending an optional request entry is the conditional append Jaune's fold
performs. -/
theorem append_optionalRequestEntry (acc : List Bytes) (requestType : UInt8)
    (payload : Bytes) :
    (if payload.length > 0 then acc ++ [[requestType] ++ payload] else acc) =
      acc ++ optionalRequestEntry requestType payload := by
  unfold optionalRequestEntry
  by_cases h : payload.length > 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, List.append_nil]

theorem pragueRequests_eq :
    pragueRequests =
      [(1, withdrawalRequestPredeployAddress), (2, consolidationRequestPredeployAddress)] := by
  decide

/-- The two Prague-shape checked request calls, each from proof-produced
evidence, under rules without a block-level access list. -/
theorem runRequestContracts_prague {benv : Benv} {idx : Nat} {acc : List Bytes}
    {bal : BalBuilder} {stW stC : State} {outW outC : MsgCallOutput}
    (hbal : benv.stat.rules.bal = none)
    (hW : processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
      .ok (stW, outW))
    (hC : processCheckedSystemTransaction (benv.withState stW)
      consolidationRequestPredeployAddress [] = .ok (stC, outC)) :
    runRequestContracts idx pragueRequests benv acc bal =
      .ok (stC, acc ++ optionalRequestEntry 1 outW.returnData ++
        optionalRequestEntry 2 outC.returnData, bal) := by
  rw [pragueRequests_eq]
  have hbal' : (benv.withState stW).stat.rules.bal = none := hbal
  simp only [runRequestContracts, hW, bind, Except.bind, hbal, hC, hbal',
    append_optionalRequestEntry]
  rfl

/-- Jaune's block output after the empty withdrawal stage and the request
pass, under rules without a block-level access list. -/
def requestsOutput (bout : BlockOutput) (withdrawalData consolidationData : Bytes) :
    BlockOutput :=
  { bout with
    requests := bout.requests ++ optionalRequestEntry 1 withdrawalData ++
      optionalRequestEntry 2 consolidationData
    blockAccessList := [] }

theorem processGeneralPurposeRequests_forward {benv : Benv} {bout : BlockOutput}
    {stW stC : State} {outW outC : MsgCallOutput}
    (hfork : CoveredFork benv.stat.fork)
    (hdeposit : parseDepositRequests bout = .ok [])
    (hW : processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
      .ok (stW, outW))
    (hC : processCheckedSystemTransaction (benv.withState stW)
      consolidationRequestPredeployAddress [] = .ok (stC, outC)) :
    processGeneralPurposeRequests benv bout =
      .ok (stC, { bout with requests := bout.requests ++ optionalRequestEntry 1 outW.returnData ++
        optionalRequestEntry 2 outC.returnData }) := by
  have hreq : benv.stat.rules.requests = pragueRequests := hfork.requests_eq
  unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt
  rw [hdeposit]
  simp only [bind, Except.bind, List.length_nil, gt_iff_lt, Nat.lt_irrefl, ite_false, hreq]
  rw [runRequestContracts_prague hfork.rules_bal_none hW hC]

/-! ## The body -/

/-- The forward block body: two unchecked system calls, a transaction fold from
`BlockOutput.init`, no withdrawals, and the two checked request calls. -/
theorem applyBody_forward {benv : Benv} {txs : List (Bytes ⊕ Tx)} {txList : List Tx}
    {stBeacon stHistory : State} {outBeacon outHistory : MsgCallOutput} {lastHash : B256}
    {benvTxs : Benv} {boutTxs : BlockOutput}
    {stW stC : State} {outW outC : MsgCallOutput}
    (hfork : CoveredFork benv.stat.fork)
    (hbeacon : processUncheckedSystemTransaction benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes = .ok (stBeacon, outBeacon))
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (hhistory : processUncheckedSystemTransaction (benv.withState stBeacon)
      historyStorageAddress lastHash.toBytes = .ok (stHistory, outHistory))
    (hdecode : txs.mapM decodeTx = .ok txList)
    (htxs : applyTransactions txList.putIndex ((benv.withState stBeacon).withState stHistory)
      BlockOutput.init = .ok (benvTxs, boutTxs))
    (hdeposit : parseDepositRequests boutTxs = .ok [])
    (hW : processCheckedSystemTransaction benvTxs withdrawalRequestPredeployAddress [] =
      .ok (stW, outW))
    (hC : processCheckedSystemTransaction (benvTxs.withState stW)
      consolidationRequestPredeployAddress [] = .ok (stC, outC)) :
    applyBody benv txs [] = .ok (stC, requestsOutput boutTxs outW.returnData outC.returnData) := by
  have hbal : benv.stat.rules.bal = none := hfork.rules_bal_none
  have hinit : ({} : BalBuilder).incorporateSystem benv.stat.rules 0 benv.state stBeacon
      (beaconRootsAddress :: outBeacon.accountReads.toList) outBeacon.storageReads.toList =
      ({} : BalBuilder) := by
    unfold BalBuilder.incorporateSystem
    rw [hbal]
  have hinit' : ({} : BalBuilder).incorporateSystem benv.stat.rules 0
      (benv.withState stBeacon).state stHistory
      (historyStorageAddress :: outHistory.accountReads.toList) outHistory.storageReads.toList =
      ({} : BalBuilder) := by
    unfold BalBuilder.incorporateSystem
    rw [hbal]
  have hlast' : (benv.withState stBeacon).stat.blockHashes.getLast? = some lastHash := hlast
  have hforkTxs : CoveredFork benvTxs.stat.fork := by
    obtain ⟨trace⟩ := exists_applyTransactionsTrace htxs hfork
    rw [trace.stat_eq]
    exact hfork
  have hrequests := processGeneralPurposeRequests_forward hforkTxs hdeposit hW hC
  have hwithdrawals : processWithdrawals benvTxs boutTxs [] = (benvTxs.state, boutTxs) := rfl
  have hself : benvTxs.withState benvTxs.state = benvTxs := by
    cases benvTxs
    rfl
  have hinitEq : ({ BlockOutput.init with bal := ({} : BalBuilder) } : BlockOutput) =
      BlockOutput.init := rfl
  cases boutTxs
  unfold applyBody
  rw [hbeacon]
  simp only [Except.mapError, bind, Except.bind]
  rw [hlast']
  simp only [Option.toExcept]
  rw [hhistory, hdecode]
  simp only [BalBuilder.incorporateSystem, hbal]
  rw [hinitEq, htxs]
  dsimp only
  rw [hwithdrawals]
  dsimp only
  rw [hself, hrequests]
  simp only [checkBlockAccessListGasLimit, hbal]
  rfl

/-! ## The header -/

/-- An unchanged gas limit of at least 1024 and below the absolute maximum
passes the adjustment window. -/
theorem checkGasLimit_self {gasLimit : Nat} (hmin : gasLimitMinimum ≤ gasLimit)
    (hwindow : gasLimitAdjustmentFactor ≤ gasLimit) (hmax : gasLimit < gasLimitMaximum) :
    checkGasLimit gasLimit gasLimit = .ok () := by
  have hmin' : 5000 ≤ gasLimit := hmin
  have hwindow' : 1024 ≤ gasLimit := hwindow
  have hdelta : 0 < gasLimit / 1024 := Nat.div_pos hwindow' (by decide)
  have h1 : ¬ gasLimit ≥ gasLimitMaximum := Nat.not_le.mpr hmax
  have h2 : ¬ gasLimit ≥ gasLimit + gasLimit / gasLimitAdjustmentFactor := by
    change ¬ gasLimit ≥ gasLimit + gasLimit / 1024
    omega
  have h3 : ¬ gasLimit ≤ gasLimit - gasLimit / gasLimitAdjustmentFactor := by
    change ¬ gasLimit ≤ gasLimit - gasLimit / 1024
    omega
  have h4 : ¬ gasLimit < gasLimitMinimum := Nat.not_lt.mpr hmin
  simp only [checkGasLimit, h1, h2, h3, h4, ite_false, bind, Except.bind]
  rfl

/-- A unit parent base fee stays a unit base fee whenever the parent used at
most its target, with an unchanged admissible gas limit. -/
theorem calculateBaseFeePerGas_unit {gasLimit parentGasUsed : Nat}
    (hmin : gasLimitMinimum ≤ gasLimit) (hwindow : gasLimitAdjustmentFactor ≤ gasLimit)
    (hmax : gasLimit < gasLimitMaximum)
    (htarget : parentGasUsed ≤ gasLimit / elasticityMultiplier) :
    calculateBaseFeePerGas gasLimit gasLimit parentGasUsed 1 = .ok 1 := by
  unfold calculateBaseFeePerGas
  rw [checkGasLimit_self hmin hwindow hmax]
  simp only [bind, Except.bind]
  by_cases heq : parentGasUsed = gasLimit / elasticityMultiplier
  · rw [ite_eq_left heq]
  · have hgt : ¬ parentGasUsed > gasLimit / elasticityMultiplier := Nat.not_lt.mpr htarget
    rw [ite_eq_right heq, ite_eq_right hgt]
    have hlt : gasLimit / elasticityMultiplier - parentGasUsed ≤ gasLimit / elasticityMultiplier :=
      Nat.sub_le _ _
    have hpos : 0 < gasLimit / elasticityMultiplier := Nat.div_pos (by
      change 5000 ≤ gasLimit at hmin
      change 2 ≤ gasLimit
      omega) (by decide)
    have hdiv : 1 * (gasLimit / elasticityMultiplier - parentGasUsed) /
        (gasLimit / elasticityMultiplier) ≤ 1 := by
      rw [Nat.one_mul]
      exact (Nat.div_le_iff_le_mul_add_pred hpos).mpr (by omega)
    have hzero : 1 * (gasLimit / elasticityMultiplier - parentGasUsed) /
        (gasLimit / elasticityMultiplier) / baseFeeMaxChangeDenominator = 0 := by
      apply Nat.div_eq_of_lt
      change _ < 8
      omega
    rw [hzero]

/-- A header validates against the chain it extends when its parent fields
and its own rule-dependent fields are exactly as `validateHeader` demands. -/
theorem validateHeader_ok_of_facts {rules : ForkRules} {chain : BlockChain}
    {header : Header} {parent : Block}
    (hlast : chain.blocks.getLast? = some parent)
    (hparentHash : header.parentHash = parent.header.hash)
    (hbase : calculateBaseFeePerGas header.gasLimit parent.header.gasLimit
      parent.header.gasUsed parent.header.baseFeePerGas = .ok header.baseFeePerGas)
    (hblob : header.excessBlobGas = calculateExcessBlobGas rules.blob parent.header)
    (hgas : header.gasUsed ≤ header.gasLimit)
    (htime : parent.header.timestamp < header.timestamp)
    (hnumber : header.number = parent.header.number + 1)
    (hextra : header.extraData.length ≤ 32)
    (hdifficulty : header.difficulty = 0) (hnonce : header.nonce = 0)
    (hommers : header.ommersHash = emptyOmmerHash)
    (hbal : header.blockAccessListHash.isSome = rules.header.blockAccessListHash)
    (hslot : header.slotNumber.isSome = rules.header.slotNumber) :
    validateHeader rules chain header = .ok () := by
  have hgt : ¬ header.gasUsed > header.gasLimit := Nat.not_lt.mpr hgas
  have hle : ¬ header.timestamp ≤ parent.header.timestamp := Nat.not_le.mpr htime
  have hextra' : ¬ header.extraData.length > 32 := Nat.not_lt.mpr hextra
  simp only [validateHeader, hlast, Option.toExcept, bind, Except.bind, hparentHash, Header.hash,
    hbase, Except.mapError, hblob, hgt, hle, hnumber, hextra', hdifficulty, hnonce, hommers, hbal,
    hslot, ne_eq, not_true_eq_false, ite_false]
  rfl

/-! ## The transition -/

/-- Every commitment check passes when the header commits to exactly the
body's results. -/
theorem stateTransitionChecks_ok_of_eq {bout : BlockOutput} {header : Header}
    {transactionsRoot blockStateRoot receiptRoot : B256} {blockLogsBloom : Bytes}
    {withdrawalsRoot requestsHash : B256}
    (hstateGas : bout.blockStateGasUsed = 0)
    (hgasUsed : header.gasUsed = bout.blockGasUsed)
    (htxsRoot : header.txsRoot = transactionsRoot)
    (hstateRoot : header.stateRoot = blockStateRoot)
    (hreceiptRoot : header.receiptRoot = receiptRoot)
    (hbloom : header.bloom = blockLogsBloom)
    (hwithdrawalsRoot : header.withdrawalsRoot = withdrawalsRoot)
    (hblobGasUsed : header.blobGasUsed = bout.blobGasUsed)
    (hrequestsHash : header.requestsHash = some requestsHash) :
    stateTransitionChecks bout header transactionsRoot blockStateRoot receiptRoot
      blockLogsBloom withdrawalsRoot requestsHash = .ok () := by
  have hmax : max bout.blockGasUsed bout.blockStateGasUsed = bout.blockGasUsed := by
    rw [hstateGas]
    exact Nat.max_eq_left (Nat.zero_le _)
  simp only [stateTransitionChecks, hmax, hgasUsed, htxsRoot, hstateRoot, hreceiptRoot, hbloom,
    hwithdrawalsRoot, hblobGasUsed, hrequestsHash, ne_eq, not_true_eq_false, ite_false, bind,
    Except.bind]
  rfl

/-- The configured transition of a block whose header validates, whose body
succeeds, and whose commitments are the body's results, on a covered fork. -/
theorem stateTransitionUsing_forward {cfg : ChainConfig} {pre : BlockChain} {block : Block}
    {fork : Fork} {st : State} {bout : BlockOutput}
    (hid : cfg.chainId = pre.chainId)
    (hforkAt : cfg.forkAt block.header.timestamp = .ok fork)
    (hcovered : CoveredFork fork)
    (hheader : validateHeader fork.ruleSet pre block.header = .ok ())
    (hommers : block.ommers = [])
    (hbody : applyBody (initBenv fork pre block.header) block.txs block.wds = .ok (st, bout))
    (hgasUsed : block.header.gasUsed = bout.blockGasUsed)
    (htxsRoot : block.header.txsRoot = getTransactionsRoot bout)
    (hstateRoot : block.header.stateRoot = st.root)
    (hreceiptRoot : block.header.receiptRoot = getReceiptRoot bout)
    (hbloom : block.header.bloom = logsBloom bout.blockLogs)
    (hwithdrawalsRoot : block.header.withdrawalsRoot = getWithdrawalsRoot bout)
    (hblobGasUsed : block.header.blobGasUsed = bout.blobGasUsed)
    (hrequestsHash : block.header.requestsHash = some (computeRequestsHash bout.requests)) :
    stateTransitionUsing cfg pre block = .ok ⟨appendBlock pre.blocks block, st, pre.chainId⟩ := by
  have hstateGas : bout.blockStateGasUsed = 0 :=
    (applyBody_legacyGasAccounting (benv := initBenv fork pre block.header)
      hcovered.stateGas_none hbody).2
  have hchecks := stateTransitionChecks_ok_of_eq (header := block.header) hstateGas hgasUsed
    htxsRoot hstateRoot hreceiptRoot hbloom hwithdrawalsRoot hblobGasUsed hrequestsHash
  have hbalNone : fork.ruleSet.bal = none := hcovered.bal_none
  have hommersCheck : stateTransitionOmmersCheck block.ommers = .ok () := by
    rw [hommers]
    rfl
  rw [stateTransitionUsing_eq_of_chainId_eq hid, hforkAt]
  simp only [Except.mapError, Except.bind]
  rw [stateTransitionAt_eq_ok_iff, stateTransitionE, hheader, hommersCheck]
  simp only [bind, Except.bind, Except.mapError]
  rw [hbody]
  simp only
  rw [hchecks]
  simp only [blockAccessListCheck, hbalNone]

/-- The retained configured block trace of a forward-constructed block
without withdrawals. -/
theorem configuredBlockTrace_forward {cfg : ChainConfig} {pre : BlockChain} {block : Block}
    {fork : Fork} {st : State}
    (hbound : sum pre.state.bal < 2 ^ 256) (hwds : block.wds = [])
    (hforkAt : cfg.forkAt block.header.timestamp = .ok fork)
    (hcovered : CoveredFork fork)
    (hstep : stateTransitionUsing cfg pre block = .ok ⟨appendBlock pre.blocks block, st, pre.chainId⟩) :
    Nonempty (ConfiguredBlockTrace cfg pre ⟨appendBlock pre.blocks block, st, pre.chainId⟩) := by
  have hbound' : sum pre.state.bal + wdsum block.wds < 2 ^ 256 := by
    have hnil : wdsum [] = 0 := rfl
    rw [hwds, hnil, Nat.add_zero]
    exact hbound
  refine exists_configuredBlockTrace_of_transition hbound' hstep ?_
  intro fork' hfork'
  rw [hforkAt] at hfork'
  cases hfork'
  exact hcovered

/-- A block without withdrawals never increases the total balance, so the
next block's bound follows from this one's. -/
theorem ConfiguredBlockTrace.sum_post_le {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) (hwds : trace.block.wds = []) :
    sum post.state.bal ≤ sum pre.state.bal := by
  have body := trace.bodyTrace
  rw [hwds] at body
  have := body.sum_le_of_empty_withdrawals trace.covered
  rw [trace.postState]
  exact this

end Blanc.BlockForward
