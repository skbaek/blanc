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
`BlockOutput.init`, no withdrawals, and the two checked request calls. A covered
fork pays no proof-of-work reward, so the ommer list is never read. -/
theorem applyBody_forward {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {txList : List Tx}
    {stBeacon stHistory : State} {outBeacon outHistory : MsgCallOutput} {lastHash : B256}
    {benvTxs : Benv} {boutTxs : BlockOutput}
    {stW stC : State} {outW outC : MsgCallOutput}
    (hfork : CoveredFork benv.stat.fork)
    (hbeacon : processUncheckedSystemTransaction benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes = .ok (stBeacon, outBeacon))
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (hhistory : processUncheckedSystemTransaction (benv.withState stBeacon)
      historyStorageAddress lastHash.toBytes = .ok (stHistory, outHistory))
    (hdecode : txs.mapM (decodeTx benv.stat.rules) = .ok txList)
    (htxs : applyTransactions txList.putIndex ((benv.withState stBeacon).withState stHistory)
      BlockOutput.init = .ok (benvTxs, boutTxs))
    (hdeposit : parseDepositRequests boutTxs = .ok [])
    (hW : processCheckedSystemTransaction benvTxs withdrawalRequestPredeployAddress [] =
      .ok (stW, outW))
    (hC : processCheckedSystemTransaction (benvTxs.withState stW)
      consolidationRequestPredeployAddress [] = .ok (stC, outC)) :
    applyBody benv txs ommers [] =
      .ok (stC, requestsOutput boutTxs outW.returnData outC.returnData) := by
  have hbal : benv.stat.rules.bal = none := hfork.rules_bal_none
  have hbeaconOn : benv.stat.rules.sys.beaconRoots = true :=
    hfork.cases (motive := fun f => (Fork.ruleSet f).sys.beaconRoots = true) rfl rfl rfl rfl
  have hhistoryOn : benv.stat.rules.sys.historyStorage = true :=
    hfork.cases (motive := fun f => (Fork.ruleSet f).sys.historyStorage = true) rfl rfl rfl rfl
  have hwdsOn : benv.stat.rules.header.withdrawalsRoot = true :=
    hfork.cases (motive := fun f => (Fork.ruleSet f).header.withdrawalsRoot = true)
      rfl rfl rfl rfl
  have hrequestsOn : benv.stat.rules.header.requestsHash = true :=
    hfork.cases (motive := fun f => (Fork.ruleSet f).header.requestsHash = true) rfl rfl rfl rfl
  have hpow : benv.stat.rules.pow = none :=
    hfork.cases (motive := fun f => (Fork.ruleSet f).pow = none) rfl rfl rfl rfl
  have hB : beaconRootsCall benv.stat.rules benv = .ok (stBeacon, ({} : BalBuilder)) := by
    unfold beaconRootsCall
    rw [if_pos hbeaconOn]
    simp only [Except.mapError, hbeacon, bind, Except.bind]
    unfold BalBuilder.incorporateSystem
    rw [hbal]
  have hlast' : (benv.withState stBeacon).stat.blockHashes.getLast? = some lastHash := hlast
  have hH : historyStorageCall benv.stat.rules (benv.withState stBeacon) ({} : BalBuilder) =
      .ok (stHistory, ({} : BalBuilder)) := by
    unfold historyStorageCall
    rw [if_pos hhistoryOn]
    simp only [hlast', Option.toExcept, Except.mapError, hhistory, bind, Except.bind]
    unfold BalBuilder.incorporateSystem
    rw [hbal]
  have hdecode' : txs.mapM (decodeTx ((benv.withState stBeacon).withState stHistory).stat.rules) =
      .ok txList := hdecode
  have hinitEq : ({ BlockOutput.init with bal := ({} : BalBuilder) } : BlockOutput) =
      BlockOutput.init := rfl
  have hforkTxs : CoveredFork benvTxs.stat.fork := by
    obtain ⟨trace⟩ := exists_applyTransactionsTrace htxs hfork
    rw [trace.stat_eq]
    exact hfork
  have hrequests := processGeneralPurposeRequests_forward hforkTxs hdeposit hW hC
  have hwds : withdrawalsPass benv.stat.rules benvTxs boutTxs [] = (benvTxs.state, boutTxs) := by
    unfold withdrawalsPass
    rw [if_pos hwdsOn]
    unfold BalBuilder.incorporateSystem
    rw [hbal]
    rfl
  have hself : benvTxs.withState benvTxs.state = benvTxs := by
    cases benvTxs
    rfl
  have hR : requestsPass benv.stat.rules (benvTxs.withState benvTxs.state) boutTxs =
      .ok (stC, { boutTxs with requests := (boutTxs.requests ++
        optionalRequestEntry 1 outW.returnData ++ optionalRequestEntry 2 outC.returnData) }) := by
    unfold requestsPass
    rw [if_pos hrequestsOn, hself, hrequests]
  unfold applyBody
  simp only [hB, hH, hdecode', bind, Except.bind]
  rw [hinitEq, htxs]
  dsimp only
  rw [hwds]
  dsimp only
  rw [hR]
  simp only [hpow, hbal, checkBlockAccessListGasLimit]
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

/-- A covered fork's header rules: every pre-Prague optional field is defined
and the consensus is proof of stake. -/
theorem coveredFork_header_rules {fork : Fork} (hcovered : CoveredFork fork) :
    fork.ruleSet.header.baseFee = true ∧ fork.ruleSet.header.withdrawalsRoot = true ∧
      fork.ruleSet.header.blobGas = true ∧ fork.ruleSet.header.parentBeaconBlockRoot = true ∧
        fork.ruleSet.pow = none :=
  hcovered.cases (motive := fun f => f.ruleSet.header.baseFee = true ∧
      f.ruleSet.header.withdrawalsRoot = true ∧ f.ruleSet.header.blobGas = true ∧
        f.ruleSet.header.parentBeaconBlockRoot = true ∧ f.ruleSet.pow = none)
    ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A header validates against the chain it extends when its parent fields
and its own rule-dependent fields are exactly as `validateHeader` demands, at a
covered fork whose parent already carries a base fee. -/
theorem validateHeader_ok_of_facts {fork : Fork} {chain : BlockChain}
    {header : Header} {parent : Block} {parentFee fee : Nat}
    (hcovered : CoveredFork fork)
    (hlast : chain.blocks.getLast? = some parent)
    (hparentHash : header.parentHash = parent.header.hash)
    (hparentFee : parent.header.baseFeePerGas = some parentFee)
    (hfee : header.baseFeePerGas = some fee)
    (hbase : calculateBaseFeePerGas header.gasLimit parent.header.gasLimit
      parent.header.gasUsed parentFee = .ok fee)
    (hwds : header.withdrawalsRoot.isSome = true)
    (hblobGasUsed : header.blobGasUsed.isSome = true)
    (hblob : header.excessBlobGas = some (calculateExcessBlobGas fork.ruleSet.blob parent.header))
    (hbeacon : header.parentBeaconBlockRoot.isSome = true)
    (hgas : header.gasUsed ≤ header.gasLimit)
    (htime : parent.header.timestamp < header.timestamp)
    (hnumber : header.number = parent.header.number + 1)
    (hextra : header.extraData.length ≤ 32)
    (hdifficulty : header.difficulty = 0) (hnonce : header.nonce = 0)
    (hommers : header.ommersHash = emptyOmmerHash)
    (hbal : header.blockAccessListHash.isSome = fork.ruleSet.header.blockAccessListHash)
    (hslot : header.slotNumber.isSome = fork.ruleSet.header.slotNumber) :
    validateHeader fork.ruleSet chain header = .ok () := by
  obtain ⟨hbaseFeeOn, hwdsOn, hblobOn, hbeaconOn, hpow⟩ := coveredFork_header_rules hcovered
  have hgt : ¬ header.gasUsed > header.gasLimit := Nat.not_lt.mpr hgas
  have hle : ¬ header.timestamp ≤ parent.header.timestamp := Nat.not_le.mpr htime
  have hextra' : ¬ header.extraData.length > 32 := Nat.not_lt.mpr hextra
  have hshape : checkHeaderShape fork.ruleSet header = .ok () := by
    simp only [checkHeaderShape, checkHeaderFieldPresence, hfee, hwds, hblobGasUsed, hblob,
      hbeacon, hbaseFeeOn, hwdsOn, hblobOn, hbeaconOn, Option.isSome_some, ne_eq,
      not_true_eq_false, ite_false, bind, Except.bind]
  have hfirst : checkFirstFeeGasLimit header parent.header = .ok () := by
    simp only [checkFirstFeeGasLimit, hfee, hparentFee, Option.isSome_some,
      Option.isNone_some, Bool.and_false, Bool.false_eq_true, ite_false]
  have hexpected : expectedBaseFee header parent.header = .ok (some fee) := by
    simp only [expectedBaseFee, hfee, hparentFee, hbase]
    rfl
  have hconsensus : checkConsensusFields fork.ruleSet header parent.header = .ok () := by
    simp only [checkConsensusFields, hpow, hdifficulty, hnonce, hommers, ne_eq,
      not_true_eq_false, ite_false, bind, Except.bind]
    rfl
  simp only [validateHeader, hshape, hlast, Option.toExcept, bind, Except.bind, hparentHash,
    Header.hash, Except.mapError, hfirst, hexpected, hblob, Option.any_some, bne_self_eq_false,
    Bool.false_eq_true, ite_false, hgt, hfee, hle, hnumber, hextra', hconsensus, hbal, hslot,
    ne_eq, not_true_eq_false]
  rfl

/-- A header template with the block-dependent fields committed to a body and
the parent.  The remaining consensus fields stay explicit template inputs. -/
def commitHeader (rules : ForkRules) (parent : Block) (template : Header)
    (st : State) (bout : BlockOutput) : Header :=
  { template with
    parentHash := parent.header.hash
    ommersHash := emptyOmmerHash
    stateRoot := st.root
    txsRoot := getTransactionsRoot bout
    receiptRoot := getReceiptRoot bout
    bloom := logsBloom bout.blockLogs
    difficulty := 0
    number := parent.header.number + 1
    gasUsed := bout.blockGasUsed
    timestamp := parent.header.timestamp + 1
    nonce := 0
    withdrawalsRoot := getWithdrawalsRoot bout
    blobGasUsed := bout.blobGasUsed
    excessBlobGas := calculateExcessBlobGas rules.blob parent.header
    requestsHash := some (computeRequestsHash bout.requests) }

/-- The committed header validates from its parent tip, base-fee equation,
extra-data bound, and rule-dependent optional-field facts, at a covered fork. -/
theorem commitHeader_ok {fork : Fork} {chain : BlockChain} {parent : Block}
    {template : Header} {st : State} {bout : BlockOutput} {parentFee fee : Nat}
    (hcovered : CoveredFork fork)
    (hlast : chain.blocks.getLast? = some parent)
    (hparentFee : parent.header.baseFeePerGas = some parentFee)
    (hfee : template.baseFeePerGas = some fee)
    (hbase : calculateBaseFeePerGas template.gasLimit parent.header.gasLimit
      parent.header.gasUsed parentFee = .ok fee)
    (hbeacon : template.parentBeaconBlockRoot.isSome = true)
    (hgas : bout.blockGasUsed ≤ template.gasLimit)
    (hextra : template.extraData.length ≤ 32)
    (hbal : template.blockAccessListHash.isSome = fork.ruleSet.header.blockAccessListHash)
    (hslot : template.slotNumber.isSome = fork.ruleSet.header.slotNumber) :
    validateHeader fork.ruleSet chain (commitHeader fork.ruleSet parent template st bout) =
      .ok () := by
  apply validateHeader_ok_of_facts (header := commitHeader fork.ruleSet parent template st bout)
    hcovered hlast rfl hparentFee hfee hbase rfl rfl rfl hbeacon
  · change bout.blockGasUsed ≤ template.gasLimit
    exact hgas
  · change parent.header.timestamp < parent.header.timestamp + 1
    omega
  · rfl
  · exact hextra
  · rfl
  · rfl
  · rfl
  · simpa only [commitHeader] using hbal
  · simpa only [commitHeader] using hslot

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
    hwithdrawalsRoot, hblobGasUsed, hrequestsHash, Option.any_some, bne_self_eq_false,
    Bool.false_eq_true, ne_eq, not_true_eq_false, ite_false, bind, Except.bind]
  rfl

/-- The configured transition of a block whose header validates, whose body
succeeds, and whose commitments are the body's results, on a covered fork. -/
theorem stateTransitionUsing_forward {cfg : ChainConfig} {pre : BlockChain} {block : Block}
    {fork : Fork} {st : State} {bout : BlockOutput}
    (hid : cfg.chainId = pre.chainId)
    (hforkAt : cfg.forkAt block.header.number block.header.timestamp = .ok fork)
    (hcovered : CoveredFork fork)
    (hheader : validateHeader fork.ruleSet pre block.header = .ok ())
    (hommers : block.ommers = [])
    (hbody : applyBody (initBenv fork pre block.header) block.txs block.ommers block.wds =
      .ok (st, bout))
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
  have hpow : fork.ruleSet.pow = none := (coveredFork_header_rules hcovered).2.2.2.2
  have hrequestsOn : fork.ruleSet.header.requestsHash = true :=
    hcovered.cases (motive := fun f => f.ruleSet.header.requestsHash = true) rfl rfl rfl rfl
  have hommersCheck : checkBlockOmmersScheduledE cfg fork.ruleSet pre block.header
      block.ommers = .ok () := by
    rw [hommers]
    simp only [checkBlockOmmersScheduledE, hpow]
    rfl
  have hcore : stateTransitionCoreE Sum.inr fork pre block
      (fun _ => checkBlockOmmersScheduledE cfg fork.ruleSet pre block.header block.ommers) =
      .ok ⟨appendBlock pre.blocks block, st, pre.chainId⟩ := by
    simp only [stateTransitionCoreE, hheader, hommersCheck, hbody, hrequestsOn, ↓reduceIte,
      Except.mapError, bind, Except.bind]
    rw [hchecks]
    simp only [blockAccessListCheck, hbalNone]
  rw [stateTransitionUsing_eq_of_chainId_eq hid, hforkAt]
  simp only [Except.mapError, Except.bind]
  rw [stateTransitionScheduledE_eq_ok_iff.mpr hcore]

/-- The retained configured block trace of a forward-constructed block
without withdrawals. -/
theorem configuredBlockTrace_forward {cfg : ChainConfig} {pre : BlockChain} {block : Block}
    {fork : Fork} {st : State}
    (hbound : sum pre.state.bal < 2 ^ 256) (hwds : block.wds = [])
    (hforkAt : cfg.forkAt block.header.number block.header.timestamp = .ok fork)
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

/-- A configured trace whose post-chain has the append shape identifies its
literal retained block. -/
theorem ConfiguredBlockTrace.block_eq
    {cfg : ChainConfig} {pre post : BlockChain} {block : Block} {st : State}
    (trace : ConfiguredBlockTrace cfg pre post)
    (hpost : post = ⟨appendBlock pre.blocks block, st, pre.chainId⟩) :
    trace.block = block := by
  cases hpost
  have htrace := congrArg (fun chain : BlockChain => chain.blocks.getLast?) trace.postEq
  have htrace' : some block = some trace.block := by
    simpa only [appendBlock_getLast?] using htrace
  exact (Option.some.inj htrace').symm

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

/-- A chain with a block has a last retained block hash. -/
theorem blockHashes_getLast_of_ne {chain : BlockChain} (h : chain.blocks ≠ []) :
    ∃ lastHash, (getLast256BlockHashes chain).getLast? = some lastHash := by
  unfold getLast256BlockHashes
  split
  · rename_i hnil
    exfalso
    rw [List.take_eq_nil_iff] at hnil
    rcases hnil with h0 | hrev
    · exact absurd h0 (by decide)
    · exact h (List.reverse_eq_nil_iff.mp hrev)
  · exact ⟨_, by rw [List.getLast?_reverse, List.head?_cons]⟩

end Blanc.BlockForward
