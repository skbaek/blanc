import Blanc.Weth10Stable
import Blanc.DeploymentMessage

/-!
Deployment-rooted stability for the compiled Blanc WETH10 program.

The public input records in this module are deliberately pre-execution: they
pin a strict canonical block, its encoded transaction bytes, the decoded
creation transaction, and independently checkable admission facts.  Execution
results live only in the proof-produced context and root records.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Canonical deployment inputs -/

/-- Compatibility aliases for the contract-neutral deployment plumbing. -/
def deploymentSystemProgram : Prog := Blanc.deploymentSystemProgram

def deploymentReceiptKey (index : Nat) : Bytes :=
  Blanc.deploymentReceiptKey index

def deploymentTxPreludeBout
    (bout : BlockOutput) (tx : Tx) (index : Nat) : BlockOutput :=
  Blanc.deploymentTxPreludeBout bout tx index

def deploymentIntrinsicGas (benv : Benv) (tx : Tx) (sender : Adr) : Nat :=
  Blanc.deploymentIntrinsicGas benv tx sender

def deploymentCalldataFloorGas (benv : Benv) (tx : Tx) (sender : Adr) : Nat :=
  Blanc.deploymentCalldataFloorGas benv tx sender

/-- The canonical transaction budget crosses both EIP-7623's calldata floor
and the constructor's independently proved execution/deposit accounting. -/
def deploymentTransactionGasBound (benv : Benv) (tx : Tx) (sender : Adr) : Nat :=
  max (deploymentCalldataFloorGas benv tx sender)
    (deploymentIntrinsicGas benv tx sender + weth10CreateMessageGasAccounting)

def deploymentEffectiveGasPrice (benv : Benv) (tx : Tx) : Nat :=
  Blanc.deploymentEffectiveGasPrice benv tx

def deploymentTenv
    (benv : Benv) (tx : Tx) (sender : Adr) (index : Nat) : Tenv :=
  Blanc.deploymentTenv benv tx sender index

def deploymentUsedGasFromMessage
    (benv : Benv) (tx : Tx) (sender : Adr) (out : MsgCallOutput) : Nat :=
  Blanc.deploymentUsedGasFromMessage benv tx sender out

def deploymentFinalState
    (benv : Benv) (tx : Tx) (sender : Adr)
    (messagePost : State) (usedGas : Nat) : State :=
  Blanc.deploymentFinalState benv tx sender messagePost usedGas

def deploymentFinalBout
    (bout : BlockOutput) (tx : Tx) (index : Nat)
    (out : MsgCallOutput) (usedGas : Nat) : BlockOutput :=
  Blanc.deploymentFinalBout bout tx index out usedGas

/-- Valid configured base state and collision-free target facts.  The four
system-address fields describe only pre-state code; no system-call result or
post-state is admitted here. -/
structure CanonicalDeploymentBase
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (sender ca : Adr) : Prop where
  configValid : cfg.Valid
  chainId_eq : cfg.chainId = base.chainId
  validContext : base.ValidContext
  sumNof : SumNof base.state.bal
  target_eq : ca = computeContractAddress sender (base.state.getNonce sender)
  target_ne_zero : ca ≠ 0
  target_not_precompile : ∀ {timestamp selected},
    cfg.rulesAt timestamp = .ok selected → ¬ selected.isPrecomp ca
  beacon_not_precompile : ¬ (Fork.ruleSet fork).isPrecomp beaconRootsAddress
  history_not_precompile : ¬ (Fork.ruleSet fork).isPrecomp historyStorageAddress
  withdrawalRequest_not_precompile :
    ¬ (Fork.ruleSet fork).isPrecomp withdrawalRequestPredeployAddress
  consolidationRequest_not_precompile :
    ¬ (Fork.ruleSet fork).isPrecomp consolidationRequestPredeployAddress
  sender_ne_target : sender ≠ ca
  withdrawalRequest_ne_target : withdrawalRequestPredeployAddress ≠ ca
  consolidationRequest_ne_target : consolidationRequestPredeployAddress ≠ ca
  target_noCodeOrNonce : accountHasCodeOrNonce base.state ca = false
  target_noStorage : accountHasStorage base.state ca = false
  lastBlockHash : ∃ lastHash,
    List.getLast? (getLast256BlockHashes base) = some lastHash
  beaconCode :
    some (base.state.getCode beaconRootsAddress).toList =
      Prog.compile deploymentSystemProgram
  historyCode :
    some (base.state.getCode historyStorageAddress).toList =
      Prog.compile deploymentSystemProgram
  withdrawalRequestCode :
    some (base.state.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (base.state.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram

/-- A strict configured block and type-2 creation transaction profile.  The
`CanonicalBlock` parameter itself retains the original bytes, strict
`rlpToBlock` equation, and exact re-encoding equation.  Every field below is
available before execution. -/
structure CanonicalWeth10DeploymentBlock
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx)
    (sender ca : Adr) : Prop where
  txs_eq : cb.block.txs = [.inl deploymentTxBytes]
  decode_eq : decodeTx (.inl deploymentTxBytes) = .ok deploymentTx
  ommers_eq : cb.block.ommers = []
  withdrawals_eq : cb.block.wds = []
  forkAt : cfg.forkAt cb.block.header.timestamp = .ok fork
  type_eq : ∃ maxPriorityFee maxFee,
    deploymentTx.type = .two cfg.chainId maxPriorityFee maxFee none []
  value_eq : deploymentTx.value = 0
  data_eq : deploymentTx.data = weth10InitCode
  nonce_eq : deploymentTx.nonce = base.state.getNonce sender
  nonce_not_max : deploymentTx.nonce ≠ UInt64.max
  recoveredSender : recoverSender cfg.chainId deploymentTx = .ok sender
  validated : validateTransaction (Fork.ruleSet fork) deploymentTx 0 =
    .ok (calculateIntrinsicCost (Fork.ruleSet fork) deploymentTx 0)
  checked :
    let benv := initBenv fork base cb.block.header
    checkTransaction benv.beginTransaction
      (deploymentTxPreludeBout .init deploymentTx 0) deploymentTx =
      .ok (sender, deploymentEffectiveGasPrice benv deploymentTx, [], 0)
  base_fee_le_effective :
    cb.block.header.baseFeePerGas ≤
      deploymentEffectiveGasPrice
        (initBenv fork base cb.block.header) deploymentTx
  upfront_funded :
    deploymentTx.gas *
        deploymentEffectiveGasPrice
          (initBenv fork base cb.block.header) deploymentTx ≤
      (base.state.bal sender).toNat
  gas_bound : deploymentTransactionGasBound
      (initBenv fork base cb.block.header) deploymentTx sender ≤ deploymentTx.gas
  runtime_code_fits : 6313 ≤ (Fork.ruleSet fork).code.maxCodeSize
  block_gas_room :
    deploymentTx.gas ≤ cb.block.header.gasLimit
  target_eq : ca = computeContractAddress sender deploymentTx.nonce

/-! ## Proof-produced pipeline contexts -/

/-- The mandatory beacon-roots and history-storage calls recovered from the
real block prefix. This structure is conclusion evidence, never input data. -/
structure DeploymentSystemPrefix
    (fork : Fork)
    (base : BlockChain) (block : Block) (txInput : Benv) : Type where
  stBeacon : State
  outBeacon : MsgCallOutput
  lastHash : B256
  stHistory : State
  outHistory : MsgCallOutput
  beaconRun :
    processUncheckedSystemTransaction
      (initBenv fork base block.header)
      beaconRootsAddress block.header.parentBeaconBlockRoot.toBytes =
      .ok (stBeacon, outBeacon)
  lastHashEq :
    List.getLast?
      ((initBenv fork base block.header).withState stBeacon).stat.blockHashes =
        some lastHash
  historyRun :
      processUncheckedSystemTransaction
      ((initBenv fork base block.header).withState stBeacon)
      historyStorageAddress lastHash.toBytes = .ok (stHistory, outHistory)
  txInput_eq :
    txInput =
      ((initBenv fork base block.header).withState stBeacon).withState
        stHistory
  environment_eq : txInput = initBenv fork base block.header
  state_eq : txInput.state = base.state
  createdAccounts_eq : txInput.createdAccounts = .emptyWithCapacity

/-- The transaction contexts are kept distinct: recovered prefix input,
`beginTransaction`, nonce/fee-updated state, and the actual prepared message.
Collision freedom is stated at exactly `msg.benv.state`. -/
structure PreparedDeploymentContext
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr) : Type where
  txInput : Benv
  begun : Benv
  debit : State
  tenv : Tenv
  msg : Msg
  systemPrefix : DeploymentSystemPrefix fork base cb.block txInput
  begun_eq : begun = txInput.beginTransaction
  debit_eq :
    (begun.state.incrNonce sender).subBal sender
      (deploymentTx.gas *
        deploymentEffectiveGasPrice txInput deploymentTx).toB256 = some debit
  tenv_eq : tenv = deploymentTenv txInput deploymentTx sender 0
  prepare_eq : prepareMessage {begun with state := debit} tenv deploymentTx =
    .ok msg
  msg_benv_eq : msg.benv = {begun with state := debit}
  msg_caller_eq : msg.caller = sender
  msg_target_eq : msg.target = none
  msg_gas_eq : msg.gas = deploymentTx.gas -
    deploymentIntrinsicGas txInput deploymentTx sender
  msg_value_eq : msg.value = 0
  msg_data_eq : msg.data = []
  msg_code_eq : msg.code.toList = weth10InitCode
  msg_codeAddress_eq : msg.codeAddress = none
  msg_shouldTransferValue_eq : msg.shouldTransferValue = true
  msg_auths_eq : msg.tenv.stat.auths = []
  msg_rules_eq : msg.benv.stat.rules = Fork.ruleSet fork
  msg_fork_eq : msg.benv.stat.fork = fork
  msg_chainId_eq : msg.benv.stat.chainId = cfg.chainId
  target_eq : msg.currentTarget = ca
  params_eq :
    freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget =
      freshDeployParams cfg.chainId.toB256 ca
  noCodeOrNonce : accountHasCodeOrNonce msg.benv.state ca = false
  noStorage : accountHasStorage msg.benv.state ca = false

/-! ## Exact protocol-system-call execution -/

/-- The canonical two-instruction system program executes exactly and leaves
the world state unchanged. This compatibility theorem delegates to the
contract-neutral deployment bridge. -/
theorem processUncheckedSystemTransaction_deploymentSystemProgram
    (benv : Benv) (target : Adr) (data : Bytes)
    (hcode : some (benv.state.getCode target).toList =
      Prog.compile deploymentSystemProgram)
    (hnp : ¬ benv.stat.rules.isPrecomp target)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ out,
      processUncheckedSystemTransaction benv target data =
        .ok (benv.state, out) ∧
      out.error = none ∧
      out.refundCounter = 0 ∧
      out.logs = [] ∧
      out.accountsToDelete = .emptyWithCapacity ∧
      out.returnData = [] := by
  exact Blanc.processUncheckedSystemTransaction_deploymentSystemProgram
    benv target data hcode hnp hfork

theorem processCheckedSystemTransaction_deploymentSystemProgram
    (benv : Benv) (target : Adr) (data : Bytes)
    (hcode : some (benv.state.getCode target).toList =
      Prog.compile deploymentSystemProgram)
    (hnp : ¬ benv.stat.rules.isPrecomp target)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ out,
      processCheckedSystemTransaction benv target data =
        .ok (benv.state, out) ∧
      out.error = none ∧
      out.refundCounter = 0 ∧
      out.logs = [] ∧
      out.accountsToDelete = .emptyWithCapacity ∧
      out.returnData = [] := by
  exact Blanc.processCheckedSystemTransaction_deploymentSystemProgram
    benv target data hcode hnp hfork

/-- Reconstruct the mandatory beacon-roots and history-storage prefix from the
canonical pre-state; neither call is smuggled into the input record. -/
theorem canonicalDeploymentSystemPrefix
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (hfork : CoveredFork fork) :
    Nonempty (Σ txInput, DeploymentSystemPrefix fork base cb.block txInput) := by
  let initial := initBenv fork base cb.block.header
  obtain ⟨outBeacon, hbeacon, _⟩ :=
    processUncheckedSystemTransaction_deploymentSystemProgram
      initial beaconRootsAddress cb.block.header.parentBeaconBlockRoot.toBytes
      (by simpa [initial, initBenv] using hbase.beaconCode)
      hbase.beacon_not_precompile
      (by simpa [initial, initBenv, initBenvStat] using hfork)
  obtain ⟨lastHash, hlast⟩ := hbase.lastBlockHash
  obtain ⟨outHistory, hhistory, _⟩ :=
    processUncheckedSystemTransaction_deploymentSystemProgram
      (initial.withState base.state) historyStorageAddress lastHash.toBytes
      (by simpa [initial, initBenv, Benv.withState] using hbase.historyCode)
      hbase.history_not_precompile
      (by simpa [initial, initBenv, initBenvStat, Benv.withState] using hfork)
  refine ⟨⟨initial, {
    stBeacon := base.state
    outBeacon := outBeacon
    lastHash := lastHash
    stHistory := base.state
    outHistory := outHistory
    beaconRun := hbeacon
    lastHashEq := ?_
    historyRun := ?_
    txInput_eq := by rfl
    environment_eq := by rfl
    state_eq := by rfl
    createdAccounts_eq := by rfl }⟩⟩
  · simpa [initial, initBenv, initBenvStat, Benv.withState] using hlast
  · simpa [initial, Benv.withState] using hhistory

/-- Produce the real transaction input, transaction-local origin boundary,
upfront nonce/fee debit, and the message returned by `prepareMessage`.
Collision freedom is derived at that message's own state. -/
theorem prepareCanonicalDeploymentContext
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (hfork : CoveredFork fork) :
    Nonempty
      (PreparedDeploymentContext cfg fork base cb deploymentTx sender ca) := by
  obtain ⟨⟨txInput, hprefix⟩⟩ :=
    canonicalDeploymentSystemPrefix cfg fork base cb sender ca hbase hfork
  let begun := txInput.beginTransaction
  let fee := deploymentTx.gas *
    deploymentEffectiveGasPrice txInput deploymentTx
  have hbegun_state : begun.state = base.state := by
    simpa [begun, Benv.beginTransaction] using hprefix.state_eq
  have hfee_le : fee ≤ (begun.state.bal sender).toNat := by
    rw [hbegun_state]
    have hprice : deploymentEffectiveGasPrice txInput deploymentTx =
        deploymentEffectiveGasPrice
          (initBenv fork base cb.block.header) deploymentTx := by
      rw [hprefix.txInput_eq]
      rfl
    simpa [fee, hprice] using henv.upfront_funded
  have hfee_lt : fee < 2 ^ 256 :=
    hfee_le.trans_lt (B256.toNat_lt _)
  have hfeeEncoded : fee.toB256.toNat = fee :=
    B256.toNat_toB256_of_lt hfee_lt
  have hnotlt : ¬ (begun.state.incrNonce sender).bal sender <
      fee.toB256 := by
    rw [B256.lt_iff_toNat_lt_toNat, hfeeEncoded]
    change ¬ ((begun.state.incrNonce sender).get sender).bal.toNat < fee
    rw [State.incrNonce_get_bal]
    exact not_lt_of_ge hfee_le
  let debit := (begun.state.incrNonce sender).setBal sender
    ((begun.state.incrNonce sender).bal sender - fee.toB256)
  have hdebit :
      (begun.state.incrNonce sender).subBal sender fee.toB256 =
        some debit := by
    unfold State.subBal
    rw [if_neg hnotlt]
  let tenv := deploymentTenv txInput deploymentTx sender 0
  let currentTarget :=
    computeContractAddress tenv.stat.origin
      (debit.getNonce tenv.stat.origin - 1)
  let msgBenv : Benv := {begun with state := debit}
  let msg : Msg :=
    { benv := msgBenv
      tenv := tenv
      caller := tenv.stat.origin
      target := deploymentTx.type.receiver?
      gas := tenv.stat.gas
      value := deploymentTx.value.toB256
      data := []
      code := .mk (.mk deploymentTx.data)
      depth := 1024
      currentTarget := currentTarget
      codeAddress := none
      shouldTransferValue := true
      isStatic := false
      accessedAddresses := tenv.stat.accessListAddresses.insertMany
        (msgBenv.stat.rules.precompiles ++ [tenv.stat.origin, currentTarget])
      accessedStorageKeys := tenv.stat.accessListStorageKeys
      disablePrecompiles := false }
  obtain ⟨maxPriorityFee, maxFee, htype⟩ := henv.type_eq
  have hreceiver : deploymentTx.type.receiver? = none := by
    rw [htype]
    rfl
  have hprepare : prepareMessage msgBenv tenv deploymentTx = .ok msg := by
    unfold prepareMessage
    rw [hreceiver]
    simp [msg, msgBenv, currentTarget, hreceiver]
    rfl
  have hdebit_nonce :
      debit.getNonce sender = base.state.getNonce sender + 1 := by
    dsimp only [debit]
    change (((begun.state.incrNonce sender).setBal sender _).get sender).nonce =
      base.state.getNonce sender + 1
    rw [State.setBal_get_self]
    change ((begun.state.incrNonce sender).get sender).nonce =
      base.state.getNonce sender + 1
    unfold State.incrNonce
    rw [State.get_set_self]
    change begun.state.getNonce sender + 1 = base.state.getNonce sender + 1
    rw [hbegun_state]
  have htarget : msg.currentTarget = ca := by
    dsimp only [msg, currentTarget]
    change computeContractAddress sender (debit.getNonce sender - 1) = ca
    rw [hdebit_nonce]
    simp
    exact hbase.target_eq.symm
  have htx_chain : txInput.stat.chainId = base.chainId := by
    rw [hprefix.txInput_eq]
    rfl
  have htx_rules : txInput.stat.rules = Fork.ruleSet fork := by
    rw [hprefix.txInput_eq]
    rfl
  have htx_fork : txInput.stat.fork = fork := by
    rw [hprefix.txInput_eq]
    rfl
  have hmsg_chain : msg.benv.stat.chainId = cfg.chainId := by
    dsimp only [msg, msgBenv, begun]
    simpa [Benv.beginTransaction] using
      htx_chain.trans hbase.chainId_eq.symm
  have hmsg_rules : msg.benv.stat.rules = Fork.ruleSet fork := by
    change begun.stat.rules = Fork.ruleSet fork
    change txInput.stat.rules = Fork.ruleSet fork
    exact htx_rules
  have hmsg_fork : msg.benv.stat.fork = fork := by
    change begun.stat.fork = fork
    change txInput.stat.fork = fork
    exact htx_fork
  have hdebit_ca : debit.get ca = base.state.get ca := by
    dsimp only [debit]
    rw [State.setBal_get_ne hbase.sender_ne_target]
    unfold State.incrNonce
    rw [State.get_set_ne _ hbase.sender_ne_target]
    rw [hbegun_state]
  have hnocode : accountHasCodeOrNonce msg.benv.state ca = false := by
    dsimp only [msg, msgBenv]
    have hpre := hbase.target_noCodeOrNonce
    unfold accountHasCodeOrNonce at hpre ⊢
    simpa [State.getNonce, State.getCode, hdebit_ca] using hpre
  have hnostor : accountHasStorage msg.benv.state ca = false := by
    dsimp only [msg, msgBenv]
    have hpre := hbase.target_noStorage
    unfold accountHasStorage at hpre ⊢
    simpa [State.getStor, hdebit_ca] using hpre
  exact ⟨{
    txInput := txInput
    begun := begun
    debit := debit
    tenv := tenv
    msg := msg
    systemPrefix := hprefix
    begun_eq := rfl
    debit_eq := by simpa [fee] using hdebit
    tenv_eq := rfl
    prepare_eq := hprepare
    msg_benv_eq := rfl
    msg_caller_eq := rfl
    msg_target_eq := by simpa [msg] using hreceiver
    msg_gas_eq := rfl
    msg_value_eq := by
      rw [show msg.value = deploymentTx.value.toB256 from rfl,
        henv.value_eq]
      decide
    msg_data_eq := rfl
    msg_code_eq := by
      rw [show msg.code = .mk (.mk deploymentTx.data) from rfl,
        henv.data_eq, ByteArray.toList_eq_toList_data]
    msg_codeAddress_eq := rfl
    msg_shouldTransferValue_eq := rfl
    msg_auths_eq := rfl
    msg_rules_eq := hmsg_rules
    msg_fork_eq := hmsg_fork
    msg_chainId_eq := hmsg_chain
    target_eq := htarget
    params_eq := by simp [hmsg_chain, htarget]
    noCodeOrNonce := hnocode
    noStorage := hnostor
  }⟩

structure CanonicalDeploymentMessageResult
    (cfg : ChainConfig) (fork : Fork) (ca : Adr)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (post : State) (out : MsgCallOutput) : Prop where
  run : processMessageCall ctx.msg = .ok (post, out)
  stable : Stable (freshDeployParams cfg.chainId.toB256 ca) ca post
  installed : some (post.getCode ca).toList =
    Prog.compile (weth10 (freshDeployParams cfg.chainId.toB256 ca))
  emptyStorage : post.getStor ca = Stor.empty
  storageInv : Stor.Weth10Inv (post.getStor ca) 0 0
  logs : out.logs = []
  returnData : out.returnData =
    weth10Code (freshDeployParams cfg.chainId.toB256 ca)
  gasLeft : out.gasLeft =
    ctx.msg.gas - weth10CreateMessageGasAccounting
  error : out.error = none
  refundCounter : out.refundCounter = 0
  accountsToDelete : out.accountsToDelete = .emptyWithCapacity
  withdrawalRequestCode :
    some (post.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (post.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram

/-- The prepared creation message takes the direct-create arm, passes the
collision checks at its own state, executes the real WETH10 constructor, and
packages the exact successful message-call output. -/
theorem canonicalDeploymentMessage_succeeds
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (hfork : CoveredFork fork) :
    ∃ post out, CanonicalDeploymentMessageResult cfg fork ca ctx post out := by
  have htotal : deploymentIntrinsicGas ctx.txInput deploymentTx sender +
      weth10CreateMessageGasAccounting ≤ deploymentTx.gas := by
    rw [ctx.systemPrefix.environment_eq]
    exact (le_max_right _ _).trans henv.gas_bound
  have hmsgFork : CoveredFork ctx.msg.benv.stat.fork := by
    rw [ctx.msg_fork_eq]
    exact hfork
  have hmsgStateGas : ctx.msg.benv.stat.rules.stateGas = none :=
    hmsgFork.rules_stateGas_none
  have hgas : weth10CreateMessageGasAccounting ≤ ctx.msg.gas := by
    rw [ctx.msg_gas_eq]
    omega
  have hmax : 6313 ≤ ctx.msg.benv.stat.rules.code.maxCodeSize := by
    rw [ctx.msg_rules_eq]
    exact henv.runtime_code_fits
  have hdebitSum := State.balSum_subBal ctx.debit_eq
  dsimp only [State.balSum] at hdebitSum
  rw [State.incrNonce_bal] at hdebitSum
  have hbegunBal : ctx.begun.state.bal = base.state.bal := by
    funext a
    rw [ctx.begun_eq]
    change ctx.txInput.state.bal a = base.state.bal a
    rw [ctx.systemPrefix.state_eq]
  have hsumDebit : sum ctx.debit.bal ≤ sum base.state.bal := by
    rw [hbegunBal] at hdebitSum
    omega
  have hsum : SumNof ctx.msg.benv.state.bal := by
    rw [ctx.msg_benv_eq]
    exact hsumDebit.trans_lt hbase.sumNof
  obtain ⟨post, hcreate, hinstalled, hempty, hinv, hlogs, houtput,
      hleft, herr, hrefund, hdelete⟩ :=
    processCreateMessage_weth10_success_full ctx.msg ctx.msg_value_eq
      ctx.msg_codeAddress_eq ctx.msg_code_eq hgas hmax hmsgFork
  obtain ⟨stablePost, hstableRun, hstable⟩ :=
    processCreateMessage_establishes_stable ctx.msg ctx.msg_value_eq
      ctx.msg_codeAddress_eq ctx.msg_code_eq hgas hmax hsum hmsgFork
  rw [hcreate] at hstableRun
  injection hstableRun with hstablePostEq
  subst stablePost
  have hstable' :
      Stable (freshDeployParams cfg.chainId.toB256 ca) ca post.state := by
    simpa [ctx.msg_chainId_eq, ctx.target_eq] using hstable
  rcases of_processCreateMessage ctx.msg (.ok post) hcreate with
    ⟨xl, hfilled, hcreateRel⟩
  have hcodeRel : Xlot.Rel Devm.CodePreserve xl :=
    Xlot.rel_of_filled codePreserve_refl_trans.1
      codePreserve_refl_trans.2 Ninst.codePreserve_effectRec
      Jinst.codePreserve_effect Linst.codePreserve_effect hfilled
  have hcreateCode := ProcessCreateMessage.codePreserve
    (Xlot.invGetCode_of_rel hcodeRel) hcreateRel
  have hinputCode (a : Adr) :
      ctx.msg.benv.state.getCode a = base.state.getCode a := by
    rw [ctx.msg_benv_eq]
    have hsub := State.subBal_getCode ctx.debit_eq (a := a)
    rw [hsub]
    unfold State.getCode
    rw [State.incrNonce_get_code]
    change ctx.begun.state.getCode a = base.state.getCode a
    rw [ctx.begun_eq]
    change ctx.txInput.state.getCode a = base.state.getCode a
    rw [ctx.systemPrefix.state_eq]
  have hpreservedCode (a : Adr) (hne : a ≠ ca)
      (hbaseCode : some (base.state.getCode a).toList =
        Prog.compile deploymentSystemProgram) :
      post.state.getCode a = base.state.getCode a := by
    have hnonempty : (ctx.msg.benv.state.getCode a).toList ≠ [] := by
      rw [hinputCode]
      intro hempty
      apply Prog.compile_ne_nil (p := deploymentSystemProgram)
      rw [← hbaseCode, hempty]
    have hne' : a ≠ ctx.msg.currentTarget := by
      simpa [ctx.target_eq] using hne
    have hc := hcreateCode a hne' hnonempty
    change post.state.getCode a = ctx.msg.benv.state.getCode a at hc
    rw [hinputCode] at hc
    exact hc
  have hwithdrawalCode :
      some (post.state.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    rw [hpreservedCode withdrawalRequestPredeployAddress
      hbase.withdrawalRequest_ne_target hbase.withdrawalRequestCode]
    exact hbase.withdrawalRequestCode
  have hconsolidationCode :
      some (post.state.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    rw [hpreservedCode consolidationRequestPredeployAddress
      hbase.consolidationRequest_ne_target hbase.consolidationRequestCode]
    exact hbase.consolidationRequestCode
  let out : MsgCallOutput :=
    { gasLeft := post.gasLeft
      refundCounter := 0
      logs := post.logs
      accountsToDelete := post.accountsToDelete
      error := post.error
      returnData := post.output }
  have hrun : processMessageCall ctx.msg = .ok (post.state, out) := by
    have htoNat : Int.toNat? post.refundCounter = some 0 := by
      rw [hrefund]
      rfl
    unfold processMessageCall
    rw [show ctx.msg.target.isNone = true by
      rw [ctx.msg_target_eq]
      rfl]
    unfold processMessageCall.create
    simp only [if_true]
    rw [ctx.target_eq]
    simp [ctx.noCodeOrNonce, ctx.noStorage, Except.bimap, hcreate, herr,
      htoNat, out]
    rw [hmsgStateGas]
    rfl
  refine ⟨post.state, out, hrun, hstable', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, hwithdrawalCode, hconsolidationCode⟩
  · simpa [ctx.target_eq, ctx.msg_chainId_eq] using hstable'.code
  · simpa [ctx.target_eq] using hempty
  · simpa [ctx.target_eq] using hinv
  · simpa [out] using hlogs
  · simpa [out, ctx.target_eq, ctx.msg_chainId_eq] using houtput
  · simpa [out] using hleft
  · simpa [out] using herr
  · rfl
  · simpa [out] using hdelete

structure CanonicalDeploymentTransactionResult
    (cfg : ChainConfig) (fork : Fork) (ca : Adr)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (post : State) (bout : BlockOutput) : Prop where
  run : processTransaction ctx.txInput .init deploymentTx 0 = .ok (post, bout)
  stable : Stable (freshDeployParams cfg.chainId.toB256 ca) ca post
  installed : some (post.getCode ca).toList =
    Prog.compile (weth10 (freshDeployParams cfg.chainId.toB256 ca))
  emptyStorage : post.getStor ca = Stor.empty
  blockLogs : bout.blockLogs = []
  requests : bout.requests = []
  blockAccessList : bout.blockAccessList = []
  depositRequests : parseDepositRequests bout = .ok []
  withdrawalRequestCode :
    some (post.getCode withdrawalRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  consolidationRequestCode :
    some (post.getCode consolidationRequestPredeployAddress).toList =
      Prog.compile deploymentSystemProgram
  receiptSucceeded :
    (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
      (fun entry => entry.2.succeeded) = some true

/-- The message theorem is threaded through the linearized real transaction
pipeline, including validation, checking, upfront debit, refund/tip settlement,
receipt insertion, and the final stable state. -/
theorem canonicalDeploymentTransaction_succeeds
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (hfork : CoveredFork fork) :
    ∃ post bout,
      CanonicalDeploymentTransactionResult cfg fork ca ctx post bout := by
  obtain ⟨messagePost, messageOut, hmessage⟩ :=
    canonicalDeploymentMessage_succeeds cfg fork base cb deploymentTx sender
      ca hbase henv ctx hfork
  let usedGas :=
    deploymentUsedGasFromMessage ctx.txInput deploymentTx sender messageOut
  let post := deploymentFinalState ctx.txInput deploymentTx sender
    messagePost usedGas
  let bout := deploymentFinalBout .init deploymentTx 0 messageOut usedGas
  have hrefund : Int.toNat? messageOut.refundCounter =
      some messageOut.refundCounter.toNat := by
    rw [hmessage.refundCounter]
    exact Int.mem_toNat?.mpr rfl
  have hdelete : messageOut.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList, hmessage.accountsToDelete]
    rfl
  obtain ⟨maxPriorityFee, maxFee, htype⟩ := henv.type_eq
  have hrules : ctx.txInput.beginTransaction.stat.rules = Fork.ruleSet fork := by
    rw [ctx.systemPrefix.environment_eq]
    rfl
  have htxRules : ctx.txInput.stat.rules = Fork.ruleSet fork := by
    rw [ctx.systemPrefix.environment_eq]
    rfl
  have hprice : deploymentEffectiveGasPrice
      (initBenv fork base cb.block.header) deploymentTx =
      deploymentEffectiveGasPrice ctx.txInput deploymentTx := by
    rw [ctx.systemPrefix.environment_eq]
  have hchecked :
      checkTransaction ctx.txInput.beginTransaction
          (deploymentTxPreludeBout .init deploymentTx 0) deploymentTx =
        .ok (sender, deploymentEffectiveGasPrice ctx.txInput deploymentTx,
          [], 0) := by
    simpa [ctx.systemPrefix.environment_eq, hprice] using henv.checked
  have hdebit := ctx.debit_eq
  rw [ctx.begun_eq] at hdebit
  simp only [Benv.beginTransaction] at hdebit
  have hvalidationStateGas :
      ctx.txInput.beginTransaction.stat.rules.stateGas = none := by
    change ctx.txInput.stat.rules.stateGas = none
    rw [ctx.systemPrefix.environment_eq]
    exact hfork.rules_stateGas_none
  have hforkStateGas : (Fork.ruleSet fork).stateGas = none :=
    hfork.stateGas_none
  have hintrinsic :
      calculateIntrinsicCost (Fork.ruleSet fork) deploymentTx 0 =
        calculateIntrinsicCost (Fork.ruleSet fork) deploymentTx sender := by
    simp [calculateIntrinsicCost, htype, hforkStateGas]
  have hprepare := ctx.prepare_eq
  rw [ctx.begun_eq, ctx.tenv_eq] at hprepare
  have hrun : processTransaction ctx.txInput .init deploymentTx 0 =
      .ok (post, bout) := by
    unfold processTransaction
    simp only [bind, Except.bind]
    change (do
      let validationSender ←
        ((match ctx.txInput.beginTransaction.stat.rules.stateGas with
          | none => Except.ok 0
          | some _ => do
            Except.mapError TransitionError.transaction
              (checkTransactionChainId ctx.txInput.beginTransaction deploymentTx)
            Except.mapError (fun e => TransitionError.senderRecovery e)
              (recoverSender ctx.txInput.beginTransaction.stat.chainId deploymentTx)) :
          Except TransitionError Adr)
      (fun _ => _) validationSender) = .ok (post, bout) <;>
      rw [hvalidationStateGas]
    simp only [bind, Except.bind]
    rw [hrules, henv.validated]
    simp only [Except.mapError]
    simp only [deploymentTxPreludeBout, Blanc.deploymentTxPreludeBout,
      ExecutionTrace.transactionPreludeBout] at hchecked
    rw [hchecked]
    simp only [Tx.isTypeThree, Tx.accessList, TxType.accessList, Tx.auths,
      htype, Bool.false_eq_true, if_false, Nat.add_zero,
      Benv.beginTransaction]
    rw [hdebit]
    simp only [Option.toExcept]
    simp only [deploymentTenv, Blanc.deploymentTenv,
      Blanc.deploymentIntrinsicGas, Benv.beginTransaction] at hprepare
    rw [htxRules] at hprepare
    simp only [List.map_nil, List.flatten_nil]
    rw [hintrinsic]
    simp only [allocateEvmGas, hforkStateGas]
    simp only [deploymentEffectiveGasPrice] at hprepare ⊢
    rw [hprepare]
    simp only [hmessage.run]
    rw [hrefund]
    simp only [hdelete, List.foldl_nil]
    simp only [settleSelfdestructs, hforkStateGas]
    have hforkBalNone : (Fork.ruleSet fork).bal = none := by
      rw [← htxRules]
      apply BenvStat.bal_none_of_stateGas_none
      rw [htxRules]
      exact hforkStateGas
    have hsettlement :
        settleTransactionGas (Fork.ruleSet fork) deploymentTx.gas
          (calculateIntrinsicCost (Fork.ruleSet fork) deploymentTx sender).2
          messageOut.gasLeft messageOut.stateGasLeft messageOut.refundCounter.toNat
          messageOut.stateGasUsed =
          ⟨usedGas, deploymentTx.gas - usedGas, usedGas, 0⟩ := by
      simp [settleTransactionGas, hforkStateGas, usedGas,
        deploymentUsedGasFromMessage, Blanc.deploymentUsedGasFromMessage,
        Blanc.deploymentCalldataFloorGas]
      rw [htxRules]
      simp
    rw [hsettlement]
    simp only [BlockOutput.withGasSettlement, hforkBalNone, List.foldl_nil,
      Nat.add_zero]
    simp only [post, bout, deploymentFinalState, Blanc.deploymentFinalState,
      deploymentFinalBout, Blanc.deploymentFinalBout,
      deploymentEffectiveGasPrice, Blanc.deploymentEffectiveGasPrice,
      Blanc.deploymentTxPreludeBout,
      ExecutionTrace.transactionPreludeBout, BlockOutput.init,
      deploymentReceiptKey, Blanc.deploymentReceiptKey]
  have hsum : SumNof post.bal := by
    have hle := processTransaction_sum_le hrun (by
      rw [htxRules]
      exact hforkStateGas)
    have hinput : ctx.txInput.state.bal = base.state.bal := by
      funext a
      rw [ctx.systemPrefix.state_eq]
    rw [hinput] at hle
    exact hle.trans_lt hbase.sumNof
  have hcode : some (post.getCode ca).toList =
      Prog.compile (weth10 (freshDeployParams cfg.chainId.toB256 ca)) := by
    dsimp only [post, deploymentFinalState, Blanc.deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessage.installed
  have hstor : post.getStor ca = Stor.empty := by
    dsimp only [post, deploymentFinalState, Blanc.deploymentFinalState]
    unfold State.addBal
    unfold State.getStor
    rw [State.setBal_get_stor, State.setBal_get_stor]
    exact hmessage.emptyStorage
  have hblockLogs : bout.blockLogs = [] := by
    dsimp only [bout, deploymentFinalBout, Blanc.deploymentFinalBout]
    simp [Blanc.deploymentTxPreludeBout,
      ExecutionTrace.transactionPreludeBout,
      hmessage.logs, BlockOutput.init]
  have hrequests : bout.requests = [] := by
    dsimp only [bout, deploymentFinalBout, Blanc.deploymentFinalBout]
    simp [Blanc.deploymentTxPreludeBout,
      ExecutionTrace.transactionPreludeBout,
      BlockOutput.init]
  have hblockAccessList : bout.blockAccessList = [] := by
    dsimp only [bout, deploymentFinalBout, Blanc.deploymentFinalBout]
    simp [Blanc.deploymentTxPreludeBout,
      ExecutionTrace.transactionPreludeBout,
      BlockOutput.init]
  have hwithdrawalCode :
      some (post.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    dsimp only [post, deploymentFinalState, Blanc.deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessage.withdrawalRequestCode
  have hconsolidationCode :
      some (post.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram := by
    dsimp only [post, deploymentFinalState, Blanc.deploymentFinalState]
    rw [State.addBal_getCode, State.addBal_getCode]
    exact hmessage.consolidationRequestCode
  have hstable : Stable (freshDeployParams cfg.chainId.toB256 ca) ca post := by
    refine ⟨hcode, hsum, ?_, ?_⟩
    · rw [hstor]
      apply (backedSpec weth10
        (freshDeployParams cfg.chainId.toB256 ca)).inv_mono
          Stor.Weth10Inv.of_empty
      exact Nat.zero_le _
    · rw [hstor]
      rfl
  have hentry :
      Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) =
        some (makeReceipt deploymentTx messageOut.error
          ((BlockOutput.init : BlockOutput).blockGasUsed + usedGas)
          messageOut.logs) := by
    dsimp only [bout, deploymentFinalBout, Blanc.deploymentFinalBout]
    simp only [Blanc.deploymentTxPreludeBout]
    change
      (((BlockOutput.init : BlockOutput).receiptsTrie.insert
        (deploymentReceiptKey 0)
        (makeReceipt deploymentTx messageOut.error
          ((BlockOutput.init : BlockOutput).blockGasUsed + usedGas)
          messageOut.logs))[deploymentReceiptKey 0]?) = _
    rw [Std.TreeMap.getElem?_insert_self]
  have hdeposit : parseDepositRequests bout = .ok [] := by
    unfold parseDepositRequests
    have hkeys : bout.receiptKeys = [deploymentReceiptKey 0] := by
      dsimp only [bout, deploymentFinalBout, Blanc.deploymentFinalBout]
      simp [Blanc.deploymentTxPreludeBout,
        ExecutionTrace.transactionPreludeBout, deploymentReceiptKey,
        BlockOutput.init]
    rw [hkeys]
    have hentry' := hentry
    change bout.receiptsTrie[deploymentReceiptKey 0]? = _ at hentry'
    simp
    rw [hentry']
    unfold makeReceipt
    rw [htype, hmessage.logs]
    rfl
  have hreceipt :
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
        (fun entry => entry.2.succeeded) = some true := by
    rw [hentry]
    simp [makeReceipt, hmessage.error]
  exact ⟨post, bout, hrun, hstable, hcode, hstor, hblockLogs, hrequests,
    hblockAccessList, hdeposit, hwithdrawalCode, hconsolidationCode, hreceipt⟩

/-! ## Exact post-transaction request suffix -/

/-- Conclusion evidence for the selected rules' two checked request-system calls.  Both
calls execute the installed nonempty system program, return no request bytes,
and leave the constructor post-state and block output unchanged. -/
structure CanonicalDeploymentSuffixResult
    (cfg : ChainConfig) (fork : Fork) (ca : Adr)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (post : State) (bout : BlockOutput) : Type where
  withdrawalOut : MsgCallOutput
  consolidationOut : MsgCallOutput
  withdrawalRun :
    processCheckedSystemTransaction (ctx.txInput.withState post)
      withdrawalRequestPredeployAddress [] = .ok (post, withdrawalOut)
  withdrawalReturnData : withdrawalOut.returnData = []
  consolidationRun :
    processCheckedSystemTransaction
      ((ctx.txInput.withState post).withState post)
      consolidationRequestPredeployAddress [] = .ok (post, consolidationOut)
  consolidationReturnData : consolidationOut.returnData = []
  run : processGeneralPurposeRequests (ctx.txInput.withState post) bout =
    .ok (post, bout)
  backedStateInv :
    (backedSpec weth10 (freshDeployParams cfg.chainId.toB256 ca)).StateInv ca post
  flashStateInv :
    (flashExactSpec (freshDeployParams cfg.chainId.toB256 ca) 0).StateInv ca post
  stable : Stable (freshDeployParams cfg.chainId.toB256 ca) ca post

/-- Execute the exact request suffix and apply the generic preservation rung
separately to WETH10's backing and exact-zero-flash specifications. -/
theorem canonicalDeploymentSuffix_succeeds
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : CanonicalDeploymentTransactionResult cfg fork ca ctx post bout)
    (hfork : CoveredFork fork) :
    Nonempty (CanonicalDeploymentSuffixResult cfg fork ca ctx post bout) := by
  have hpostFork : CoveredFork (ctx.txInput.withState post).stat.fork := by
    change CoveredFork ctx.txInput.stat.fork
    rw [ctx.systemPrefix.environment_eq]
    exact hfork
  have hpostPostFork :
      CoveredFork ((ctx.txInput.withState post).withState post).stat.fork := by
    simpa [Benv.withState] using hpostFork
  have hrequests : (ctx.txInput.withState post).stat.rules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)] := by
    change (Fork.ruleSet (ctx.txInput.withState post).stat.fork).requests = _
    exact hpostFork.requests_eq
  obtain ⟨withdrawalOut, hwithdrawal, _, _, _, _, hwithdrawalReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      (ctx.txInput.withState post) withdrawalRequestPredeployAddress []
      (by simpa [Benv.withState] using htx.withdrawalRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        exact hbase.withdrawalRequest_not_precompile)
      hpostFork
  obtain ⟨consolidationOut, hconsolidation, _, _, _, _,
      hconsolidationReturn⟩ :=
    processCheckedSystemTransaction_deploymentSystemProgram
      ((ctx.txInput.withState post).withState post)
      consolidationRequestPredeployAddress []
      (by simpa [Benv.withState] using htx.consolidationRequestCode)
      (by
        rw [ctx.systemPrefix.environment_eq]
        exact hbase.consolidationRequest_not_precompile)
      hpostPostFork
  have hwithdrawal' :
      processCheckedSystemTransaction (ctx.txInput.withState post)
        withdrawalRequestPredeployAddress [] = .ok (post, withdrawalOut) := by
    simpa [Benv.withState] using hwithdrawal
  have hbalNone : ctx.txInput.stat.rules.bal = none := by
    simpa [Benv.withState] using hpostFork.rules_bal_none
  have hrun : processGeneralPurposeRequests
      (ctx.txInput.withState post) bout = .ok (post, bout) := by
    unfold processGeneralPurposeRequests processGeneralPurposeRequestsAt
    rw [htx.depositRequests]
    rw [hrequests]
    simp [runRequestContracts, hwithdrawal', hconsolidation,
      hwithdrawalReturn, hconsolidationReturn, htx.requests,
      hbalNone]
    constructor
    · rfl
    · rw [← htx.requests]
  have hnotcreated :
      ca ∉ (ctx.txInput.withState post).createdAccounts := by
    rw [show (ctx.txInput.withState post).createdAccounts =
      ctx.txInput.createdAccounts by rfl,
      ctx.systemPrefix.createdAccounts_eq]
    simp
  have hbackedInput :
      (backedSpec weth10
        (freshDeployParams cfg.chainId.toB256 ca)).BenvInv ca
          (ctx.txInput.withState post) :=
    ⟨⟨htx.installed, htx.stable.sumNof, htx.stable.backed⟩, hnotcreated⟩
  have hflashInput :
      (flashExactSpec
        (freshDeployParams cfg.chainId.toB256 ca) 0).BenvInv ca
          (ctx.txInput.withState post) :=
    ⟨⟨htx.installed, trivial, htx.stable.flashZero⟩, hnotcreated⟩
  have hbacked :=
    ContractSpec.processGeneralPurposeRequests_preserves_inv_sum_le ca
      (backedSpec_preserves (freshDeployParams cfg.chainId.toB256 ca) ca)
      (ctx.txInput.withState post) bout post bout hrun hbackedInput hpostFork
  have hflash :=
    ContractSpec.processGeneralPurposeRequests_preserves_inv_sum_le ca
      (flashExactSpec_preserves (freshDeployParams cfg.chainId.toB256 ca) ca 0)
      (ctx.txInput.withState post) bout post bout hrun hflashInput hpostFork
  have hstable : Stable (freshDeployParams cfg.chainId.toB256 ca) ca post :=
    ⟨hbacked.1.code, hbacked.1.side, hbacked.1.inv, hflash.1.inv⟩
  exact ⟨⟨withdrawalOut, consolidationOut, hwithdrawal,
    hwithdrawalReturn, hconsolidation, hconsolidationReturn, hrun,
    hbacked.1, hflash.1, hstable⟩⟩

/-- Compose the recovered prefix, singleton decoded transaction, empty
withdrawal stage, and exact request suffix into Jaune's real block body. -/
theorem canonicalDeploymentApplyBody_succeeds
    (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (hfork : CoveredFork fork)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : CanonicalDeploymentTransactionResult cfg fork ca ctx post bout)
    (hsuffix : CanonicalDeploymentSuffixResult cfg fork ca ctx post bout) :
    applyBody (initBenv fork base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) := by
  have hputIndex : List.putIndex [deploymentTx] = [(0, deploymentTx)] := rfl
  have hbalNone : (initBenv fork base cb.block.header).stat.rules.bal = none := by
    apply BenvStat.bal_none_of_stateGas_none
    change (Fork.ruleSet fork).stateGas = none
    exact hfork.stateGas_none
  have hinitialBal :
      (({} : BalBuilder).incorporateSystem
          (initBenv fork base cb.block.header).stat.rules 0
          (initBenv fork base cb.block.header).state ctx.systemPrefix.stBeacon
          (beaconRootsAddress :: ctx.systemPrefix.outBeacon.accountReads.toList)
          ctx.systemPrefix.outBeacon.storageReads.toList).incorporateSystem
        (initBenv fork base cb.block.header).stat.rules 0
        ((initBenv fork base cb.block.header).withState ctx.systemPrefix.stBeacon).state
        ctx.systemPrefix.stHistory
        (historyStorageAddress :: ctx.systemPrefix.outHistory.accountReads.toList)
        ctx.systemPrefix.outHistory.storageReads.toList = (BlockOutput.init : BlockOutput).bal := by
    simp [BalBuilder.incorporateSystem, hbalNone]
    change ({} : BalBuilder) = ({} : BalBuilder)
    rfl
  unfold applyBody
  have hbeacon := ctx.systemPrefix.beaconRun
  change processUncheckedSystemTransaction
    (initBenv fork base cb.block.header)
    beaconRootsAddress
    (initBenv fork base cb.block.header).stat.parentBeaconBlockRoot.toBytes =
      .ok (ctx.systemPrefix.stBeacon, ctx.systemPrefix.outBeacon) at hbeacon
  rw [hbeacon]
  simp only [Except.mapError, bind, Except.bind]
  rw [ctx.systemPrefix.lastHashEq]
  simp only [Option.toExcept]
  rw [ctx.systemPrefix.historyRun]
  rw [henv.txs_eq]
  simp only [List.mapM_cons, List.mapM_nil, henv.decode_eq, bind,
    Except.bind]
  simp only [Except.pure, pure]
  rw [hputIndex]
  rw [hinitialBal]
  rw [← ctx.systemPrefix.txInput_eq]
  simp only [applyTransactions, htx.run, bind, Except.bind]
  rw [henv.withdrawals_eq]
  have hwdIndex : List.putIndex ([] : List Withdrawal) = [] := rfl
  have hwithdrawals :
      processWithdrawals (ctx.txInput.withState post) bout [] = (post, bout) := by
    simp only [processWithdrawals, processWithdrawalsTrie,
      processWithdrawalsState, hwdIndex, List.foldl_nil,
      BlockOutput.withWithdrawalsTrie]
    rfl
  rw [hwithdrawals]
  simp only [BalBuilder.incorporateSystem, hbalNone,
    checkBlockAccessListGasLimit]
  have hpostBenv :
      (ctx.txInput.withState post).withState post = ctx.txInput.withState post := by
    generalize hbenv : ctx.txInput = benv
    cases benv
    rfl
  rw [hpostBenv]
  cases bout
  rw [hsuffix.run]
  simp only
  have haccess := htx.blockAccessList
  congr
  exact haccess.symm

/-! ## Deployment-root adapter -/

structure DeploymentRoot
    (cfg : ChainConfig) (base deployed : BlockChain)
    (dp : DeployParams) (ca : Adr) : Prop where
  execution : ∃ (fork : Fork) (cb : CanonicalBlock)
      (deploymentTxBytes : Bytes)
      (deploymentTx : Tx) (sender : Adr)
      (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
      (post : State) (bout : BlockOutput),
    CanonicalDeploymentBase cfg fork base sender ca ∧
    CanonicalWeth10DeploymentBlock cfg fork base cb deploymentTxBytes
      deploymentTx sender ca ∧
    CoveredFork fork ∧
    CanonicalDeploymentTransactionResult cfg fork ca ctx post bout ∧
    Nonempty (CanonicalDeploymentSuffixResult cfg fork ca ctx post bout) ∧
    stateTransitionAt fork
        base cb.block = .ok deployed ∧
    applyBody (initBenv fork base cb.block.header)
        cb.block.txs cb.block.wds = .ok (post, bout) ∧
    post = deployed.state ∧
    (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
        (fun entry => entry.2.succeeded) = some true
  params_eq : dp = freshDeployParams cfg.chainId.toB256 ca
  configValid : cfg.Valid
  target_ne_zero : ca ≠ 0
  target_not_precompile : ∀ {timestamp rules},
    cfg.rulesAt timestamp = .ok rules → ¬ rules.isPrecomp ca
  emptyStorage : deployed.state.getStor ca = Stor.empty
  stable : Stable dp ca deployed.state
  deployed_validContext : deployed.ValidContext
  deployed_chainId : cfg.chainId = deployed.chainId

/-- A successful configured step over the strict canonical
envelope establishes the deployment root; all execution contexts and receipt
facts are constructed in this proof rather than admitted by the envelope. -/
theorem canonicalDeploymentStep_establishes_root
    (cfg : ChainConfig) (fork : Fork) (base deployed : BlockChain)
    (cb : CanonicalBlock) (deploymentTxBytes : Bytes)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (hfork : CoveredFork fork)
    (hstep : stateTransitionUsing cfg
      base cb.block = .ok deployed) :
    DeploymentRoot cfg base deployed
      (freshDeployParams cfg.chainId.toB256 ca) ca := by
  obtain ⟨ctx⟩ :=
    prepareCanonicalDeploymentContext cfg fork base cb deploymentTx sender ca
      hbase henv hfork
  obtain ⟨post, bout, htx⟩ :=
    canonicalDeploymentTransaction_succeeds cfg fork base cb deploymentTx
      sender ca hbase henv ctx hfork
  obtain ⟨suffix⟩ :=
    canonicalDeploymentSuffix_succeeds cfg fork base cb deploymentTx sender ca
      hbase ctx post bout htx hfork
  have happly : applyBody (initBenv fork base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) :=
    canonicalDeploymentApplyBody_succeeds cfg fork base cb deploymentTxBytes
      deploymentTx sender ca henv hfork ctx post bout htx suffix
  have hwith : stateTransitionAt fork base cb.block = .ok deployed := by
    have h := hstep
    rw [stateTransitionUsing_eq_of_chainId_eq
      (cfg := cfg) (ch := base) hbase.chainId_eq] at h
    rw [henv.forkAt] at h
    simpa [Except.mapError, Bind.bind, Except.bind] using h
  have hstate : post = deployed.state := by
    have hinvert := hwith
    rw [stateTransitionAt_eq_ok_iff, stateTransitionE] at hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    dsimp only at hinvert
    obtain ⟨⟨st, bout'⟩, hab, hinvert⟩ := Except.bind_eq_ok hinvert
    rw [happly] at hab
    obtain ⟨hst, hbout⟩ := Prod.mk.inj (Except.ok.inj hab)
    subst st
    subst bout'
    dsimp only at hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    obtain ⟨_, _, hinvert⟩ := Except.bind_eq_ok hinvert
    rw [← Except.ok.inj hinvert]
  let checkedBase := CheckedBlockChain.ofValidContext hbase.validContext
  have hwithChecked :
      stateTransitionAt fork checkedBase.val cb.block = .ok deployed := by
    change stateTransitionAt fork base cb.block = .ok deployed
    exact hwith
  have hcontext := BlockChain.validContext_of_transition
    (cc := checkedBase) (cb := cb) hwithChecked
  have hvalid : deployed.ValidContext := by
    let checkedDeployed := CheckedBlockChain.ofEvidence deployed cb.block
      hcontext.1 hcontext.2.1 hcontext.2.2.1 hcontext.2.2.2
    exact checkedDeployed.validContext
  have hchain : cfg.chainId = deployed.chainId :=
    hbase.chainId_eq.trans (stateTransitionAt_preserves_chainId hwith).symm
  refine ⟨?_, rfl, hbase.configValid, hbase.target_ne_zero,
    hbase.target_not_precompile,
    ?_, ?_, hvalid, hchain⟩
  · exact ⟨fork, cb, deploymentTxBytes, deploymentTx, sender, ctx, post, bout,
      hbase, henv, hfork, htx, ⟨suffix⟩, hwith, happly, hstate,
      htx.receiptSucceeded⟩
  · rw [← hstate]
    exact htx.emptyStorage
  · rw [← hstate]
    exact suffix.stable

theorem DeploymentRoot.reflReach
    (hroot : DeploymentRoot cfg base deployed dp ca) :
    BlockChain.ReachUsing cfg deployed deployed := by
  exact .refl deployed hroot.configValid hroot.deployed_validContext
    hroot.deployed_chainId

theorem DeploymentRoot.reachable_stable
    (hroot : DeploymentRoot cfg base deployed dp ca)
    (hreach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f) :
    Stable dp ca future.state :=
  chainUsing_preserves_stable dp ca _ deployed future hreach hroot.stable hcov

theorem DeploymentRoot.reachable_code
    (hroot : DeploymentRoot cfg base deployed dp ca)
    (hreach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f) :
    some (future.state.getCode ca).toList = Prog.compile (weth10 dp) :=
  (hroot.reachable_stable hreach hcov).code

theorem DeploymentRoot.reachable_flashZero
    (hroot : DeploymentRoot cfg base deployed dp ca)
    (hreach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f) :
    (future.state.getStor ca).get flashMintedSlot = 0 :=
  (hroot.reachable_stable hreach hcov).flashZero

theorem DeploymentRoot.reachable_solvent
    (hroot : DeploymentRoot cfg base deployed dp ca)
    (hreach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f) :
    balSum (future.state.getStor ca) ≤ (future.state.bal ca).toNat :=
  (hroot.reachable_stable hreach hcov).solvent

end Weth10

end Blanc
