import Blanc.Weth10Redeemable
import Blanc.Weth10DeploymentRoot
import Blanc.Weth10HolderFlowDeterminism
import Blanc.Weth10HolderFlowResult
import Blanc.Weth10HolderFlowWriteCompleteness

/-!
Lean-checked statement pins for the WETH10 flagship declarations.  Each
wrapper has the exact intended type and uses the named declaration as its
body, so a statement change breaks this file while a proof-only refactor does
not.  `Stor.Weth10Inv` is pinned separately by definitional unfolding.
-/

namespace Blanc

open Jaune

namespace Weth10

example (dp : DeployParams) :
    Prog.compile (weth10 dp) = some (weth10Code dp) :=
  weth10Code_compile dp

example (dp : DeployParams) (ca : Adr) (depth : Nat) :
    FlashExactDepth dp ca depth :=
  flashExactDepth dp ca depth

example (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).Sound ca :=
  backedSpec_sound dp ca

example (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).Preserves ca :=
  backedSpec_preserves dp ca

example (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : weth10CreateMessageGasAccounting ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      post.getCode msg.currentTarget =
        ⟨⟨weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget)⟩⟩ ∧
      post.state.getStor msg.currentTarget = Stor.empty ∧
      Stor.Weth10Inv (post.state.getStor msg.currentTarget) 0 0 ∧
      post.logs = [] ∧
      post.output =
        weth10Code (freshDeployParams
          msg.benv.stat.chainId.toB256 msg.currentTarget) ∧
      post.gasLeft = msg.gas - weth10CreateMessageGasAccounting :=
  processCreateMessage_weth10_success msg h_value h_codeAddress h_code h_gas h_max

example (chainId : B256) (contractAddress : Adr) :
    (freshDeployParams chainId contractAddress).deploymentChainId = chainId ∧
    (freshDeployParams chainId contractAddress).cachedDomainSeparator =
      deploymentDomainSeparator chainId contractAddress ∧
    Prog.compile (weth10 (freshDeployParams chainId contractAddress)) =
      some (weth10Code (freshDeployParams chainId contractAddress)) ∧
    weth10InitCode.drop weth10InitPrefix.length = weth10RuntimeTemplate ∧
    weth10InitCode.length = 6490 ∧
    weth10InitFunc.NoCalls ∧
    Stor.Weth10Inv Stor.empty 0 0 ∧
    (∀ msg : Msg, msg.currentTarget = contractAddress →
      Stor.Weth10Inv
        ((processCreateMessage.msg msg).benv.state.getStor contractAddress)
        0 0) ∧
    weth10CodeDepositGas = 1262600 ∧
    weth10Eip3860InitCodeGas = 406 ∧
    weth10CreateMessageGasAccounting = 1264071 ∧
    weth10TopLevelDeploymentGasAccounting ≤
      weth10TopLevelDeploymentGasBound ∧
    weth10TopLevelDeploymentGasBound = 1421317 :=
  freshDeployment_staticCertificate chainId contractAddress

example (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : Stable dp ca ch.state) :
    (ch'.state.getStor ca).get flashMintedSlot = 0 ∧
      balSum (ch'.state.getStor ca) ≤ (ch'.state.bal ca).toNat :=
  chain_reachable_backed_and_flash_zero dp ca ch ch' h_reach h_inv

example (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : weth10CreateMessageGasAccounting ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (h_sum : SumNof msg.benv.state.bal) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      Stable
        (freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget)
        msg.currentTarget post.state :=
  processCreateMessage_establishes_stable msg h_value h_codeAddress h_code
    h_gas h_max h_sum

example (s : Stor) (v b : B256) :
    Stor.Weth10Inv s v b ↔
      balSum s + v.toNat ≤ b.toNat + (s.get flashMintedSlot).toNat ∧
      (s.get flashMintedSlot).toNat ≤ maxFlashMinted := by
  rfl

example (w : State) (ca owner : Adr) :
    bookedBalanceNat w ca owner =
      (Stor.rest (w.getStor ca) owner).toNat :=
  rfl

example : Adr → Adr → Nat → Log :=
  redemptionBurnLog

example : DeployParams → Adr → Adr → Adr → Nat → State → Msg → Prop :=
  AdmissibleRedemptionMessage

example : DeployParams → Adr → Adr → Nat → State → Msg → Prop :=
  AdmissibleSelfRedemptionMessage

example : DeployParams → Adr → Adr → Adr → Nat →
    State → State → MsgCallOutput → Prop :=
  MessageRedemptionExactEffect

example : DeployParams → Adr → Adr → Adr → Nat → State → Msg → Prop :=
  MessageRedemptionEnabled

example : DeployParams → Adr → Adr → Adr → Nat →
    Benv → BlockOutput → Tx → Nat → Prop :=
  AdmissibleRedemptionTx

example : DeployParams → Adr → Adr → Adr → Nat →
    Benv → BlockOutput → Tx → Nat → State → BlockOutput → Prop :=
  TransactionEthAccounting

example : DeployParams → Adr → Adr → Adr → Nat →
    Benv → BlockOutput → Tx → Nat → State → BlockOutput → Prop :=
  TransactionRedemptionExactEffect

example : DeployParams → Adr → Adr → Adr → Nat →
    Benv → BlockOutput → Tx → Nat → Prop :=
  TransactionRedemptionEnabled

/-! Constructor pins make the frozen record obligations fail closed.  Merely
checking each record's outer function type would not detect a field-level
weakening or a hidden success premise. -/

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (state_eq : msg.benv.state = w)
    (rules_eq : msg.benv.stat.rules = pragueRules)
    (target_eq : msg.target = some ca)
    (currentTarget_eq : msg.currentTarget = ca)
    (codeAddress_eq : msg.codeAddress = some ca)
    (code_eq : some msg.code.toList = Prog.compile (weth10 dp))
    (installedCode_eq : msg.code = w.getCode ca)
    (caller_eq : msg.caller = owner)
    (value_eq : msg.value = 0)
    (depth_eq : msg.depth = 1024)
    (shouldTransferValue_eq : msg.shouldTransferValue = true)
    (isStatic_eq : msg.isStatic = false)
    (auths_eq : msg.tenv.stat.auths = [])
    (disablePrecompiles_eq : msg.disablePrecompiles = false)
    (target_not_precompile : pragueRules.isPrecomp ca = false)
    (recipient_ne_zero : recipient ≠ 0)
    (recipient_not_precompile : pragueRules.isPrecomp recipient = false)
    (recipient_code_free : (w.getCode recipient).toList = [])
    (original_storage_eq : msg.benv.stat.origState.getStor ca = w.getStor ca)
    (target_access : AddressAccessCase msg.accessedAddresses ca)
    (recipient_access : AddressAccessCase msg.accessedAddresses recipient)
    (owner_storage_access :
      StorageAccessCase msg.accessedStorageKeys ca owner.toB256)
    (recipient_account : RecipientAccountCase w recipient)
    (gas_bound : redemptionRuntimeCeiling q ≤ msg.gas) :
    AdmissibleRedemptionMessageCore dp ca owner recipient q w msg :=
  { state_eq := state_eq
    rules_eq := rules_eq
    target_eq := target_eq
    currentTarget_eq := currentTarget_eq
    codeAddress_eq := codeAddress_eq
    code_eq := code_eq
    installedCode_eq := installedCode_eq
    caller_eq := caller_eq
    value_eq := value_eq
    depth_eq := depth_eq
    shouldTransferValue_eq := shouldTransferValue_eq
    isStatic_eq := isStatic_eq
    auths_eq := auths_eq
    disablePrecompiles_eq := disablePrecompiles_eq
    target_not_precompile := target_not_precompile
    recipient_ne_zero := recipient_ne_zero
    recipient_not_precompile := recipient_not_precompile
    recipient_code_free := recipient_code_free
    original_storage_eq := original_storage_eq
    target_access := target_access
    recipient_access := recipient_access
    owner_storage_access := owner_storage_access
    recipient_account := recipient_account
    gas_bound := gas_bound }

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (core : AdmissibleRedemptionMessageCore
      dp ca owner recipient q w msg)
    (data_eq : msg.data = withdrawToCalldata recipient q)
    (selector_eq : Sevm.selector (initSevm msg) = withdrawToSelector) :
    AdmissibleRedemptionMessage dp ca owner recipient q w msg :=
  { toAdmissibleRedemptionMessageCore := core
    data_eq := data_eq
    selector_eq := selector_eq }

example {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (core : AdmissibleRedemptionMessageCore dp ca owner owner q w msg)
    (data_eq : msg.data = withdrawCalldata q)
    (selector_eq : Sevm.selector (initSevm msg) = withdrawSelector) :
    AdmissibleSelfRedemptionMessage dp ca owner q w msg :=
  { toAdmissibleRedemptionMessageCore := core
    data_eq := data_eq
    selector_eq := selector_eq }

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w post : State} {out : MsgCallOutput}
    (outError : out.error = none)
    (ownerDebit : bookedBalanceNat post ca owner + q =
      bookedBalanceNat w ca owner)
    (otherBookedUnchanged : ∀ a, a ≠ owner →
      bookedBalanceNat post ca a = bookedBalanceNat w ca a)
    (contractEthDebit : (post.bal ca).toNat + q = (w.bal ca).toNat)
    (recipientEthCredit :
      (post.bal recipient).toNat = (w.bal recipient).toNat + q)
    (otherEthUnchanged : ∀ a, a ≠ ca → a ≠ recipient →
      post.bal a = w.bal a)
    (sumPreserved : sum post.bal = sum w.bal)
    (burnLog : out.logs = [redemptionBurnLog ca owner q])
    (returnData : out.returnData = [])
    (codePreserved : ∀ a, post.getCode a = w.getCode a)
    (flashZero : (post.getStor ca).get flashMintedSlot = 0)
    (postStable : Stable dp ca post) :
    MessageRedemptionExactEffect dp ca owner recipient q w post out :=
  { outError := outError
    ownerDebit := ownerDebit
    otherBookedUnchanged := otherBookedUnchanged
    contractEthDebit := contractEthDebit
    recipientEthCredit := recipientEthCredit
    otherEthUnchanged := otherEthUnchanged
    sumPreserved := sumPreserved
    burnLog := burnLog
    returnData := returnData
    codePreserved := codePreserved
    flashZero := flashZero
    postStable := postStable }

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (rules_eq : benv.stat.rules = pragueRules)
    (type_eq : ∃ maxPriorityFee maxFee,
      tx.type = .two benv.stat.chainId maxPriorityFee maxFee (some ca) [])
    (data_eq : tx.data = withdrawToCalldata recipient q)
    (selector_eq : ∀ e : Sevm, e.data = tx.data →
      Sevm.selector e = withdrawToSelector)
    (value_eq : tx.value = 0)
    (nonce_eq : tx.nonce = benv.state.getNonce owner)
    (nonce_not_max : tx.nonce ≠ UInt64.max)
    (recoveredSender : recoverSender benv.stat.chainId tx = .ok owner)
    (owner_ne_zero : owner ≠ 0)
    (owner_code_free : (benv.state.getCode owner).toList = [])
    (validated :
      validateTransaction pragueRules tx = .ok (calculateIntrinsicCost tx))
    (checked :
      checkTransaction benv.beginTransaction
        (redemptionTxPreludeBout bout tx index) tx =
        .ok (owner, redemptionEffectiveGasPrice benv tx, [], 0))
    (base_fee_le_effective :
      benv.stat.baseFeePerGas ≤ redemptionEffectiveGasPrice benv tx)
    (upfront_funded : tx.gas * redemptionEffectiveGasPrice benv tx ≤
      (benv.state.bal owner).toNat)
    (gas_bound : redemptionTransactionGasBound q tx ≤ tx.gas)
    (block_gas_room : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (target_code :
      some (benv.state.getCode ca).toList = Prog.compile (weth10 dp))
    (target_not_precompile : pragueRules.isPrecomp ca = false)
    (target_not_created : ca ∉ benv.createdAccounts)
    (recipient_ne_zero : recipient ≠ 0)
    (recipient_not_precompile : pragueRules.isPrecomp recipient = false)
    (recipient_code_free : (benv.state.getCode recipient).toList = [])
    (recipient_account : RecipientAccountCase benv.state recipient) :
    AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index :=
  { rules_eq := rules_eq
    type_eq := type_eq
    data_eq := data_eq
    selector_eq := selector_eq
    value_eq := value_eq
    nonce_eq := nonce_eq
    nonce_not_max := nonce_not_max
    recoveredSender := recoveredSender
    owner_ne_zero := owner_ne_zero
    owner_code_free := owner_code_free
    validated := validated
    checked := checked
    base_fee_le_effective := base_fee_le_effective
    upfront_funded := upfront_funded
    gas_bound := gas_bound
    block_gas_room := block_gas_room
    target_code := target_code
    target_not_precompile := target_not_precompile
    target_not_created := target_not_created
    recipient_ne_zero := recipient_ne_zero
    recipient_not_precompile := recipient_not_precompile
    recipient_code_free := recipient_code_free
    recipient_account := recipient_account }

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {post : State} {bout' : BlockOutput}
    (perAddress : ∀ a,
      (post.bal a).toNat +
          (if a = owner then
            tx.gas * redemptionEffectiveGasPrice benv tx else 0) +
          (if a = ca then q else 0) =
        (benv.state.bal a).toNat +
          (if a = recipient then q else 0) +
          (if a = owner then redemptionGasRefund benv bout bout' tx else 0) +
          (if a = benv.stat.coinbase then
            redemptionPriorityFee benv bout bout' tx else 0))
    (totalAfterBaseFeeBurn :
      sum post.bal + redemptionBaseFeeBurn benv bout bout' =
        sum benv.state.bal) :
    TransactionEthAccounting
      dp ca owner recipient q benv bout tx index post bout' :=
  { perAddress := perAddress
    totalAfterBaseFeeBurn := totalAfterBaseFeeBurn }

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {post : State} {bout' : BlockOutput}
    (trace : TransactionRedemptionTrace
      dp ca owner recipient q benv bout tx index)
    (receiptAt : ∃ receipt,
      Std.TreeMap.get? bout'.receiptsTrie (redemptionReceiptKey index) =
        some ((2 : Fin 5), receipt))
    (receiptSucceeded :
      (Std.TreeMap.get? bout'.receiptsTrie (redemptionReceiptKey index)).map
        (fun entry => entry.2.succeeded) = some true)
    (receiptLogs :
      (Std.TreeMap.get? bout'.receiptsTrie (redemptionReceiptKey index)).map
        (fun entry => entry.2.logs) =
          some [redemptionBurnLog ca owner q])
    (ownerDebit : bookedBalanceNat post ca owner + q =
      bookedBalanceNat benv.state ca owner)
    (otherBookedUnchanged : ∀ a, a ≠ owner →
      bookedBalanceNat post ca a = bookedBalanceNat benv.state ca a)
    (codePreserved : ∀ a, post.getCode a = benv.state.getCode a)
    (flashZero : (post.getStor ca).get flashMintedSlot = 0)
    (postStable : Stable dp ca post)
    (ethAccounting : TransactionEthAccounting
      dp ca owner recipient q benv bout tx index post bout') :
    TransactionRedemptionExactEffect
      dp ca owner recipient q benv bout tx index post bout' :=
  { trace := trace
    receiptAt := receiptAt
    receiptSucceeded := receiptSucceeded
    receiptLogs := receiptLogs
    ownerDebit := ownerDebit
    otherBookedUnchanged := otherBookedUnchanged
    codePreserved := codePreserved
    flashZero := flashZero
    postStable := postStable
    ethAccounting := ethAccounting }

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleRedemptionMessage
      dp ca owner recipient q w msg) :
    MessageRedemptionEnabled dp ca owner recipient q w msg :=
  hstable.messageRedemption_enabled_of_le hq henv

example {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleSelfRedemptionMessage dp ca owner q w msg) :
    MessageRedemptionEnabled dp ca owner owner q w msg :=
  hstable.selfRedemption_enabled_of_le hq henv

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hstable : Stable dp ca benv.state)
    (hq : q ≤ bookedBalanceNat benv.state ca owner)
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index) :
    TransactionRedemptionEnabled
      dp ca owner recipient q benv bout tx index :=
  hstable.transactionRedemption_enabled_of_le hq henv

/-! Deployment constructor pins make the pre-execution/result boundary fail
closed on record-field additions, removals, or type changes. -/

example {chainId : UInt64} {base : BlockChain} {sender ca : Adr}
    (chainId_eq : chainId = base.chainId)
    (validContext : base.ValidContext)
    (sumNof : SumNof base.state.bal)
    (target_eq : ca = computeContractAddress sender (base.state.getNonce sender))
    (target_ne_zero : ca ≠ 0)
    (target_not_precompile : ¬ pragueRules.isPrecomp ca)
    (sender_ne_target : sender ≠ ca)
    (withdrawalRequest_ne_target : withdrawalRequestPredeployAddress ≠ ca)
    (consolidationRequest_ne_target : consolidationRequestPredeployAddress ≠ ca)
    (target_noCodeOrNonce : accountHasCodeOrNonce base.state ca = false)
    (target_noStorage : accountHasStorage base.state ca = false)
    (lastBlockHash : ∃ lastHash,
      List.getLast? (getLast256BlockHashes base) = some lastHash)
    (beaconCode : some (base.state.getCode beaconRootsAddress).toList =
      Prog.compile deploymentSystemProgram)
    (historyCode : some (base.state.getCode historyStorageAddress).toList =
      Prog.compile deploymentSystemProgram)
    (withdrawalRequestCode :
      some (base.state.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram)
    (consolidationRequestCode :
      some (base.state.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram) :
    CanonicalDeploymentBase chainId base sender ca :=
  { chainId_eq := chainId_eq
    validContext := validContext
    sumNof := sumNof
    target_eq := target_eq
    target_ne_zero := target_ne_zero
    target_not_precompile := target_not_precompile
    sender_ne_target := sender_ne_target
    withdrawalRequest_ne_target := withdrawalRequest_ne_target
    consolidationRequest_ne_target := consolidationRequest_ne_target
    target_noCodeOrNonce := target_noCodeOrNonce
    target_noStorage := target_noStorage
    lastBlockHash := lastBlockHash
    beaconCode := beaconCode
    historyCode := historyCode
    withdrawalRequestCode := withdrawalRequestCode
    consolidationRequestCode := consolidationRequestCode }

example {chainId : UInt64} {base : BlockChain} {cb : CanonicalBlock}
    {deploymentTxBytes : Bytes} {deploymentTx : Tx} {sender ca : Adr}
    (txs_eq : cb.block.txs = [.inl deploymentTxBytes])
    (decode_eq : decodeTx (.inl deploymentTxBytes) = .ok deploymentTx)
    (ommers_eq : cb.block.ommers = [])
    (withdrawals_eq : cb.block.wds = [])
    (type_eq : ∃ maxPriorityFee maxFee,
      deploymentTx.type = .two chainId maxPriorityFee maxFee none [])
    (value_eq : deploymentTx.value = 0)
    (data_eq : deploymentTx.data = weth10InitCode)
    (nonce_eq : deploymentTx.nonce = base.state.getNonce sender)
    (nonce_not_max : deploymentTx.nonce ≠ UInt64.max)
    (recoveredSender : recoverSender chainId deploymentTx = .ok sender)
    (validated : validateTransaction pragueRules deploymentTx =
      .ok (calculateIntrinsicCost deploymentTx))
    (checked :
      let benv := initBenv pragueRules base cb.block.header
      checkTransaction benv.beginTransaction
        (deploymentTxPreludeBout .init deploymentTx 0) deploymentTx =
        .ok (sender, deploymentEffectiveGasPrice benv deploymentTx, [], 0))
    (base_fee_le_effective : cb.block.header.baseFeePerGas ≤
      deploymentEffectiveGasPrice
        (initBenv pragueRules base cb.block.header) deploymentTx)
    (upfront_funded :
      deploymentTx.gas * deploymentEffectiveGasPrice
        (initBenv pragueRules base cb.block.header) deploymentTx ≤
      (base.state.bal sender).toNat)
    (gas_bound : deploymentTransactionGasBound deploymentTx ≤ deploymentTx.gas)
    (block_gas_room : deploymentTx.gas ≤ cb.block.header.gasLimit)
    (target_eq : ca = computeContractAddress sender deploymentTx.nonce) :
    CanonicalWeth10DeploymentBlock chainId base cb deploymentTxBytes
      deploymentTx sender ca :=
  { txs_eq := txs_eq
    decode_eq := decode_eq
    ommers_eq := ommers_eq
    withdrawals_eq := withdrawals_eq
    type_eq := type_eq
    value_eq := value_eq
    data_eq := data_eq
    nonce_eq := nonce_eq
    nonce_not_max := nonce_not_max
    recoveredSender := recoveredSender
    validated := validated
    checked := checked
    base_fee_le_effective := base_fee_le_effective
    upfront_funded := upfront_funded
    gas_bound := gas_bound
    block_gas_room := block_gas_room
    target_eq := target_eq }

example {chainId : UInt64} {base : BlockChain} {cb : CanonicalBlock}
    {deploymentTx : Tx} {sender ca : Adr}
    (txInput : Benv) (begun : Benv) (debit : State) (tenv : Tenv) (msg : Msg)
    (systemPrefix : DeploymentSystemPrefix base cb.block txInput)
    (begun_eq : begun = txInput.beginTransaction)
    (debit_eq :
      (begun.state.incrNonce sender).subBal sender
        (deploymentTx.gas *
          deploymentEffectiveGasPrice txInput deploymentTx).toB256 = some debit)
    (tenv_eq : tenv = deploymentTenv txInput deploymentTx sender 0)
    (prepare_eq : prepareMessage {begun with state := debit} tenv deploymentTx =
      .ok msg)
    (msg_benv_eq : msg.benv = {begun with state := debit})
    (msg_caller_eq : msg.caller = sender)
    (msg_target_eq : msg.target = none)
    (msg_gas_eq : msg.gas = deploymentTx.gas - deploymentIntrinsicGas deploymentTx)
    (msg_value_eq : msg.value = 0)
    (msg_data_eq : msg.data = [])
    (msg_code_eq : msg.code.toList = weth10InitCode)
    (msg_codeAddress_eq : msg.codeAddress = none)
    (msg_shouldTransferValue_eq : msg.shouldTransferValue = true)
    (msg_auths_eq : msg.tenv.stat.auths = [])
    (msg_rules_eq : msg.benv.stat.rules = pragueRules)
    (msg_chainId_eq : msg.benv.stat.chainId = chainId)
    (target_eq : msg.currentTarget = ca)
    (params_eq :
      freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget =
        freshDeployParams chainId.toB256 ca)
    (noCodeOrNonce : accountHasCodeOrNonce msg.benv.state ca = false)
    (noStorage : accountHasStorage msg.benv.state ca = false) :
    PreparedDeploymentContext chainId base cb deploymentTx sender ca :=
  { txInput := txInput
    begun := begun
    debit := debit
    tenv := tenv
    msg := msg
    systemPrefix := systemPrefix
    begun_eq := begun_eq
    debit_eq := debit_eq
    tenv_eq := tenv_eq
    prepare_eq := prepare_eq
    msg_benv_eq := msg_benv_eq
    msg_caller_eq := msg_caller_eq
    msg_target_eq := msg_target_eq
    msg_gas_eq := msg_gas_eq
    msg_value_eq := msg_value_eq
    msg_data_eq := msg_data_eq
    msg_code_eq := msg_code_eq
    msg_codeAddress_eq := msg_codeAddress_eq
    msg_shouldTransferValue_eq := msg_shouldTransferValue_eq
    msg_auths_eq := msg_auths_eq
    msg_rules_eq := msg_rules_eq
    msg_chainId_eq := msg_chainId_eq
    target_eq := target_eq
    params_eq := params_eq
    noCodeOrNonce := noCodeOrNonce
    noStorage := noStorage }

example {chainId : UInt64} {ca : Adr}
    {ctx : PreparedDeploymentContext chainId base cb deploymentTx sender ca}
    {post : State} {out : MsgCallOutput}
    (run : processMessageCall ctx.msg = .ok (post, out))
    (stable : Stable (freshDeployParams chainId.toB256 ca) ca post)
    (installed : some (post.getCode ca).toList =
      Prog.compile (weth10 (freshDeployParams chainId.toB256 ca)))
    (emptyStorage : post.getStor ca = Stor.empty)
    (storageInv : Stor.Weth10Inv (post.getStor ca) 0 0)
    (logs : out.logs = [])
    (returnData : out.returnData =
      weth10Code (freshDeployParams chainId.toB256 ca))
    (gasLeft : out.gasLeft = ctx.msg.gas - weth10CreateMessageGasAccounting)
    (error : out.error = none)
    (refundCounter : out.refundCounter = 0)
    (accountsToDelete : out.accountsToDelete = .emptyWithCapacity)
    (withdrawalRequestCode :
      some (post.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram)
    (consolidationRequestCode :
      some (post.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram) :
    CanonicalDeploymentMessageResult chainId ca ctx post out :=
  { run := run
    stable := stable
    installed := installed
    emptyStorage := emptyStorage
    storageInv := storageInv
    logs := logs
    returnData := returnData
    gasLeft := gasLeft
    error := error
    refundCounter := refundCounter
    accountsToDelete := accountsToDelete
    withdrawalRequestCode := withdrawalRequestCode
    consolidationRequestCode := consolidationRequestCode }

example {chainId : UInt64} {ca : Adr}
    {ctx : PreparedDeploymentContext chainId base cb deploymentTx sender ca}
    {post : State} {bout : BlockOutput}
    (run : processTransaction ctx.txInput .init deploymentTx 0 = .ok (post, bout))
    (stable : Stable (freshDeployParams chainId.toB256 ca) ca post)
    (installed : some (post.getCode ca).toList =
      Prog.compile (weth10 (freshDeployParams chainId.toB256 ca)))
    (emptyStorage : post.getStor ca = Stor.empty)
    (blockLogs : bout.blockLogs = [])
    (requests : bout.requests = [])
    (depositRequests : parseDepositRequests bout = .ok [])
    (withdrawalRequestCode :
      some (post.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram)
    (consolidationRequestCode :
      some (post.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram)
    (receiptSucceeded :
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
        (fun entry => entry.2.succeeded) = some true) :
    CanonicalDeploymentTransactionResult chainId ca ctx post bout :=
  { run := run
    stable := stable
    installed := installed
    emptyStorage := emptyStorage
    blockLogs := blockLogs
    requests := requests
    depositRequests := depositRequests
    withdrawalRequestCode := withdrawalRequestCode
    consolidationRequestCode := consolidationRequestCode
    receiptSucceeded := receiptSucceeded }

example {chainId : UInt64} {ca : Adr}
    {ctx : PreparedDeploymentContext chainId base cb deploymentTx sender ca}
    {post : State} {bout : BlockOutput}
    (withdrawalOut : MsgCallOutput) (consolidationOut : MsgCallOutput)
    (withdrawalRun :
      processCheckedSystemTransaction (ctx.txInput.withState post)
        withdrawalRequestPredeployAddress [] = .ok (post, withdrawalOut))
    (withdrawalReturnData : withdrawalOut.returnData = [])
    (consolidationRun :
      processCheckedSystemTransaction
        ((ctx.txInput.withState post).withState post)
        consolidationRequestPredeployAddress [] = .ok (post, consolidationOut))
    (consolidationReturnData : consolidationOut.returnData = [])
    (run : processGeneralPurposeRequests (ctx.txInput.withState post) bout =
      .ok (post, bout))
    (backedStateInv :
      (backedSpec weth10
        (freshDeployParams chainId.toB256 ca)).StateInv ca post)
    (flashStateInv :
      (flashExactSpec
        (freshDeployParams chainId.toB256 ca) 0).StateInv ca post)
    (stable : Stable (freshDeployParams chainId.toB256 ca) ca post) :
    CanonicalDeploymentSuffixResult chainId ca ctx post bout :=
  { withdrawalOut := withdrawalOut
    consolidationOut := consolidationOut
    withdrawalRun := withdrawalRun
    withdrawalReturnData := withdrawalReturnData
    consolidationRun := consolidationRun
    consolidationReturnData := consolidationReturnData
    run := run
    backedStateInv := backedStateInv
    flashStateInv := flashStateInv
    stable := stable }

example {chainId : UInt64} {base deployed : BlockChain}
    {dp : DeployParams} {ca : Adr}
    (execution : ∃ (cb : CanonicalBlock) (deploymentTxBytes : Bytes)
        (deploymentTx : Tx) (sender : Adr)
        (ctx : PreparedDeploymentContext chainId base cb deploymentTx sender ca)
        (post : State) (bout : BlockOutput),
      CanonicalDeploymentBase chainId base sender ca ∧
      CanonicalWeth10DeploymentBlock chainId base cb deploymentTxBytes
        deploymentTx sender ca ∧
      CanonicalDeploymentTransactionResult chainId ca ctx post bout ∧
      Nonempty (CanonicalDeploymentSuffixResult chainId ca ctx post bout) ∧
      stateTransitionUsing (ChainConfig.pragueOnly chainId)
          base cb.block = .ok deployed ∧
      applyBody (initBenv pragueRules base cb.block.header)
          cb.block.txs cb.block.wds = .ok (post, bout) ∧
      post = deployed.state ∧
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
          (fun entry => entry.2.succeeded) = some true)
    (params_eq : dp = freshDeployParams chainId.toB256 ca)
    (target_ne_zero : ca ≠ 0)
    (target_not_precompile : ¬ pragueRules.isPrecomp ca)
    (emptyStorage : deployed.state.getStor ca = Stor.empty)
    (stable : Stable dp ca deployed.state)
    (deployed_validContext : deployed.ValidContext)
    (deployed_chainId : chainId = deployed.chainId) :
    DeploymentRoot chainId base deployed dp ca :=
  { execution := execution
    params_eq := params_eq
    target_ne_zero := target_ne_zero
    target_not_precompile := target_not_precompile
    emptyStorage := emptyStorage
    stable := stable
    deployed_validContext := deployed_validContext
    deployed_chainId := deployed_chainId }

example (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase chainId base sender ca)
    (henv : CanonicalWeth10DeploymentBlock chainId base cb
      deploymentTxBytes deploymentTx sender ca) :
    Nonempty
      (PreparedDeploymentContext chainId base cb deploymentTx sender ca) :=
  prepareCanonicalDeploymentContext chainId base cb deploymentTx sender ca
    hbase henv

example (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase chainId base sender ca)
    (henv : CanonicalWeth10DeploymentBlock chainId base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext chainId base cb deploymentTx sender ca) :
    ∃ post out, CanonicalDeploymentMessageResult chainId ca ctx post out :=
  canonicalDeploymentMessage_succeeds chainId base cb deploymentTx sender ca
    hbase henv ctx

example (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase chainId base sender ca)
    (henv : CanonicalWeth10DeploymentBlock chainId base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext chainId base cb deploymentTx sender ca) :
    ∃ post bout,
      CanonicalDeploymentTransactionResult chainId ca ctx post bout :=
  canonicalDeploymentTransaction_succeeds chainId base cb deploymentTx
    sender ca hbase henv ctx

example (chainId : UInt64) (base deployed : BlockChain)
    (cb : CanonicalBlock) (deploymentTxBytes : Bytes)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase chainId base sender ca)
    (henv : CanonicalWeth10DeploymentBlock chainId base cb
      deploymentTxBytes deploymentTx sender ca)
    (hstep : stateTransitionUsing (ChainConfig.pragueOnly chainId)
      base cb.block = .ok deployed) :
    DeploymentRoot chainId base deployed
      (freshDeployParams chainId.toB256 ca) ca :=
  canonicalDeploymentStep_establishes_root chainId base deployed cb
    deploymentTxBytes deploymentTx sender ca hbase henv hstep

example (hroot : DeploymentRoot chainId base deployed dp ca) :
    BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed deployed :=
  hroot.reflReach

example (hroot : DeploymentRoot chainId base deployed dp ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    Stable dp ca future.state :=
  hroot.reachable_stable hreach

example (hroot : DeploymentRoot chainId base deployed dp ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    some (future.state.getCode ca).toList = Prog.compile (weth10 dp) :=
  hroot.reachable_code hreach

example (hroot : DeploymentRoot chainId base deployed dp ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    (future.state.getStor ca).get flashMintedSlot = 0 :=
  hroot.reachable_flashZero hreach

example (hroot : DeploymentRoot chainId base deployed dp ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    balSum (future.state.getStor ca) ≤ (future.state.bal ca).toNat :=
  hroot.reachable_solvent hreach

/-! The holder-flow history pins are intentionally proof-carrying and retain
the complete applied-block sequence.  These examples make weakening the
history to an endpoint-only summary, or dropping ordinary-reach coverage,
fail closed in the claims gate. -/

example {u : Adr}
    (ordinaryIn redeemed externalTransferredOut selfTransfer
      flashCredit flashRepayment : Nat) :
    HolderFlow u :=
  ⟨ordinaryIn, redeemed, externalTransferredOut, selfTransfer,
    flashCredit, flashRepayment⟩

example {u : Adr}
    (ordinaryIn redeemed externalTransferredOut selfTransfer
      flashCredit flashRepayment : Nat) :
    let flow : HolderFlow u :=
      ⟨ordinaryIn, redeemed, externalTransferredOut, selfTransfer,
        flashCredit, flashRepayment⟩
    flow.ordinaryIn = ordinaryIn ∧
      flow.redeemed = redeemed ∧
    flow.externalTransferredOut = externalTransferredOut ∧
      flow.selfTransfer = selfTransfer ∧
      flow.flashCredit = flashCredit ∧
      flow.flashRepayment = flashRepayment := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

example {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    SystemMessageTrace benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes
      trace.beaconState trace.beaconOut :=
  trace.beacon

example {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    SystemMessageTrace (benv.withState trace.beaconState)
      historyStorageAddress trace.lastHash.toBytes
      trace.historyState trace.historyOut :=
  trace.history

example {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    SystemMessageTrace
      (trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds))
      withdrawalRequestPredeployAddress []
      trace.requests.withdrawalState trace.requests.withdrawalOut :=
  trace.requests.withdrawal

example {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) :
    SystemMessageTrace
      ((trace.transactionBenv.withState
        (processWithdrawalsState trace.transactionBenv.state wds)).withState
          trace.requests.withdrawalState)
      consolidationRequestPredeployAddress []
      trace.requests.consolidationState trace.requests.consolidationOut :=
  trace.requests.consolidation

example : UInt64 → DeployParams → Adr → BlockChain → BlockChain → Type :=
  AccountedHistory

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory chainId dp ca checkpoint future → List Block :=
  AccountedHistory.appliedBlocks

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint : BlockChain}
    (hcfg : (ChainConfig.pragueOnly chainId).Valid)
    (hctx : checkpoint.ValidContext)
    (hid : chainId = checkpoint.chainId) :
    (AccountedHistory.refl (dp := dp) (ca := ca)
      hcfg hctx hid).appliedBlocks = [] := by
  rfl

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint current future : BlockChain}
    (prior : AccountedHistory chainId dp ca checkpoint current)
    (accounted : AccountedBlock chainId dp ca current future) :
    (AccountedHistory.step prior accounted).appliedBlocks =
      prior.appliedBlocks ++ [accounted.block] := by
  rfl

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory chainId dp ca checkpoint future → List FlowAction :=
  AccountedHistory.flowActions

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory chainId dp ca checkpoint future →
      (u : Adr) → HolderFlow u :=
  AccountedHistory.weth10Flow

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      checkpoint future :=
  history.toReachUsing

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      checkpoint future) :
    Nonempty (AccountedHistory chainId dp ca checkpoint future) :=
  exists_accountedHistory_of_reachUsing hstable hreach

example {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history₁ history₂ : AccountedHistory chainId dp ca checkpoint future)
    (hblocks : history₁.appliedBlocks = history₂.appliedBlocks) :
    history₁.weth10Flow u = history₂.weth10Flow u :=
  history₁.weth10Flow_eq_of_appliedBlocks_eq history₂ hblocks

/-! C1's taxonomy and provenance remain data, while executable authenticity
is supplied separately by the accepted-debit and emitter witnesses. -/

example : B256 → Adr → Nat → FlowAtom :=
  FlowAtom.ordinaryMint

example : B256 → B256 → Adr → Adr → Nat → FlowAtom :=
  FlowAtom.transfer

example : B256 → Adr → Adr → Nat → FlowAtom :=
  FlowAtom.redemption

example : B256 → Adr → Nat → FlowAtom :=
  FlowAtom.flashPair

example : AllowanceBranch :=
  AllowanceBranch.selfBypass

example : B256 → B256 → B256 → AllowanceBranch :=
  AllowanceBranch.finite

example : B256 → AllowanceBranch :=
  AllowanceBranch.maximum

example : DebitBranch :=
  DebitBranch.direct

example : AllowanceBranch → DebitBranch :=
  DebitBranch.delegated

example : AllowanceBranch → DebitBranch :=
  DebitBranch.flash

example (actualCaller : Adr) (rawSource : B256) (source : Adr)
    (branch : DebitBranch) : DebitProvenance :=
  { actualCaller := actualCaller
    rawSource := rawSource
    source := source
    branch := branch }

example : Adr → B256 → Adr → DebitBranch → DebitProvenance :=
  DebitProvenance.mk

example (atom : FlowAtom) (credit : Option CreditOccurrence)
    (debit : Option DebitProvenance) (actualCaller currentTarget : Adr)
    (codeAddress : Option Adr) (depth : Nat) : FlowAction :=
  { atom := atom
    credit := credit
    debit := debit
    actualCaller := actualCaller
    currentTarget := currentTarget
    codeAddress := codeAddress
    depth := depth }

example : FlowAtom → Option CreditOccurrence → Option DebitProvenance →
    Adr → Adr → Option Adr → Nat → FlowAction :=
  FlowAction.mk

example : Sevm → Devm → Devm → B256 → AllowanceBranch → Prop :=
  CallerAllowanceAccepted

example : Sevm → Devm → Devm → AllowanceBranch → Prop :=
  FlashAllowanceAccepted

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (authentic : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = some action)
    (accepted : action.AcceptedDebit dp frame.sevm frame.pre frame.post) :
    frame.HasAcceptedDebit dp ca action :=
  { authentic := authentic
    classified := classified
    accepted := accepted }

example {dp : DeployParams} {action : FlowAction}
    {e : Sevm} {pre post corePre : Devm}
    (rawSource : B256) (source : Adr) (branch : AllowanceBranch)
    (hdebit : action.debit = some
      { actualCaller := e.caller
        rawSource := rawSource
        source := source
        branch := .delegated branch })
    (accepted : CallerAllowanceAccepted e pre corePre 2 branch) :
    action.AcceptedDebit dp e pre post :=
  FlowAction.AcceptedDebit.delegated rawSource source corePre branch
    hdebit accepted

example {dp : DeployParams} {action : FlowAction}
    {e : Sevm} {pre post settle burn : Devm}
    (rawReceiver : B256) (receiver : Adr) (branch : AllowanceBranch)
    (hdebit : action.debit = some
      { actualCaller := e.caller
        rawSource := rawReceiver
        source := receiver
        branch := .flash branch })
    (accepted : FlashAllowanceAccepted e settle burn branch)
    (burnRun : Func.Run ((weth10 dp).main :: weth10Aux) e burn
      flashBurn post) :
    action.AcceptedDebit dp e pre post :=
  FlowAction.AcceptedDebit.flash rawReceiver receiver settle burn branch
    hdebit accepted burnRun

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasAcceptedDebit dp ca action :=
  frame.hasAcceptedDebit_of_flowAction?_eq_some context haction

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (authentic : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = some action)
    (effect : GenuineWethEmitterEffect dp frame.sevm frame.pre frame.post) :
    frame.HasGenuineWethEmitterEffect dp ca action :=
  { authentic := authentic
    classified := classified
    effect := effect }

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (haction : frame.flowAction? dp ca = some action) :
    frame.HasGenuineWethEmitterEffect dp ca action :=
  frame.hasGenuineWethEmitterEffect_of_flowAction?_eq_some context haction

/-! CREATE children are retained only through complete code-deposit
settlement, not merely because their raw interpreter result committed. -/

example : Jaune.Frame → Execution → Bool :=
  Blanc.Weth10.Frame.settlementCommits

example {dp : DeployParams} {ca : Adr} {f : Jaune.Frame}
    {raw : Execution} {settled : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    (child : Exec pc sevm pre raw)
    (rawCommits : Execution.commits raw = true)
    (hcreate : f.isCreate = true)
    (hsettled : processCreateMessage.settle f.outer
      (processMessage.settle f.inner (executeCode.handleError raw)) =
        .ok settled)
    (herror : settled.error.isSome = true) :
    (if Blanc.Weth10.Frame.settlementCommits f raw = true then
      Exec.flowActions dp ca child
     else []) = [] :=
  Exec.retainedChildActions_eq_nil_of_create_codeDepositRollback child
    rawCommits hcreate hsettled herror

/-! C2's local reverse theorem and classification record pin the same action
across the executed write, rich storage effect, WETH emitter, and accepted
debit evidence. -/

example (dp : DeployParams) (ca : Adr) :
    CompiledBalanceSstoreReverseComplete dp ca :=
  compiledBalanceSstoreReverseComplete dp ca

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr} {action : FlowAction}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (authentic : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = some action)
    (role : BalanceSstoreRole ca stepPre action.atom holder value)
    (rich : frame.HasRichLocalStorageEffect dp ca action)
    (emitter : frame.HasGenuineWethEmitterEffect dp ca action)
    (acceptedDebit : frame.HasAcceptedDebit dp ca action) :
    frame.BalanceSstoreClassification dp ca stepPre stepPost slot
      key value holder action :=
  { occurrence := occurrence
    authentic := authentic
    classified := classified
    role := role
    rich := rich
    emitter := emitter
    acceptedDebit := acceptedDebit }

example {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (rootPc : pc = 0) (rootMemory : pre.memory = Mem.empty)
    {frame : Exec.Frame}
    (retained : frame ∈ Exec.committedFrames run)
    (invocation : frame.exactInvocation dp ca)
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action :=
  Exec.weth10BalanceSstoreClassification_of_mem_committedFrames
    run installed rootPc rootMemory retained invocation occurrence

/-! C3-C6 public theorem pins.  The committed interpreter cores are concrete;
the frozen equations carry only the stable checkpoint and authentic retained
history premises. -/

example (dp : DeployParams) (ca : Adr) :
    CommittedExecStorageSound dp ca :=
  committedExecStorageSound dp ca

example (dp : DeployParams) (ca : Adr) :
    CommittedExecEthSound dp ca :=
  committedExecEthSound dp ca

example {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory chainId dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
      (history.weth10Flow u).flashRepayment :=
  history.flash_pair_totals_eq

example {chainId : UInt64} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    FlowActionsCreditNof history.flowActions :=
  history.noCommittedCreditWrap hstable

example {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    holderCreditLossOfActions history.flowActions u = 0 :=
  history.holderCreditLoss_eq_zero hstable

example {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn +
        (history.weth10Flow u).selfTransfer +
        (history.weth10Flow u).flashCredit =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut +
        (history.weth10Flow u).selfTransfer +
        (history.weth10Flow u).flashRepayment :=
  holderFlow_conserved hstable history

example {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
        (history.weth10Flow u).flashRepayment ∧
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut :=
  holderFlow_flash_cancelled hstable history

example {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u +
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) :=
  holderFlow_residual_floor hstable history

example {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) ≤
      bookedBalanceNat future.state ca u :=
  holderFlow_truncated_floor hstable history

example {chainId : UInt64} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory chainId dp ca checkpoint future)
    (noExternalTransfer :
      (history.weth10Flow u).externalTransferredOut = 0) :
    bookedBalanceNat checkpoint.state ca u ≤
      (history.weth10Flow u).redeemed +
        bookedBalanceNat future.state ca u :=
  holderFlow_withdrawal_floor hstable history noExternalTransfer

/-! Goal-specific boundary falsifiers and arithmetic deductions. -/

example {u : Adr} {initial final : Nat} (flow : HolderFlow u)
    (cancelled : initial + flow.ordinaryIn =
      final + flow.redeemed + flow.externalTransferredOut)
    (noRedemption : flow.redeemed = 0)
    (noExternalTransfer : flow.externalTransferredOut = 0) :
    initial ≤ final :=
  holderFlow_zero_outflow_floor_of_cancelled flow cancelled
    noRedemption noExternalTransfer

example {u : Adr} {initial final : Nat} (flow : HolderFlow u)
    (cancelled : initial + flow.ordinaryIn =
      final + flow.redeemed + flow.externalTransferredOut)
    (credited : 0 < flow.ordinaryIn)
    (noRedemption : flow.redeemed = 0)
    (noExternalTransfer : flow.externalTransferredOut = 0) :
    initial < final :=
  holderFlow_credited_strict_of_cancelled flow cancelled credited
    noRedemption noExternalTransfer

example {u : Adr} {initial : Nat} (flow : HolderFlow u)
    (covered : initial ≤
      flow.redeemed + flow.externalTransferredOut) :
    initial - (flow.redeemed + flow.externalTransferredOut) = 0 :=
  holderFlow_over_total_outflow_truncates flow covered

example (rawSource rawRecipient : B256) (u : Adr) (amount : Nat)
    (hsource : rawSource.toAdr = u)
    (hrecipient : rawRecipient.toAdr = u) :
    (FlowAtom.transfer rawSource rawRecipient rawSource.toAdr
        rawRecipient.toAdr amount).holderFlow u =
      { HolderFlow.zero u with selfTransfer := amount } :=
  holderFlow_dirty_alias_is_self_transfer rawSource rawRecipient u amount
    hsource hrecipient

example (rawSource rawRecipient : B256) (source recipient u : Adr) :
    (FlowAtom.transfer rawSource rawRecipient source recipient 0).holderFlow u =
      HolderFlow.zero u :=
  holderFlow_zero_transfer_eq_zero rawSource rawRecipient source recipient u

example (e : Sevm) (hsize : e.data.length.toB256 = 0) :
    primaryFlowAtom e =
      some (.ordinaryMint e.caller.toB256 e.caller e.value.toNat) :=
  primaryFlowAtom_wordZero_length_is_receive e hsize

example (e : Sevm)
    (hnonempty : e.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector e = transferSelector)
    (hraw : Sevm.argWord e 0 ≠ 0)
    (hnormalized : (Sevm.argWord e 0).toAdr = 0) :
    primaryFlowAtom e =
      some (.transfer e.caller.toB256 (Sevm.argWord e 0)
        e.caller 0 (Sevm.argWord e 1).toNat) :=
  primaryFlowAtom_dirty_zero_is_transfer e hnonempty hselector hraw
    hnormalized

example (e : Sevm)
    (hnonempty : e.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector e = transferAndCallSelector)
    (hraw : Sevm.argWord e 0 ≠ 0)
    (hnormalized : (Sevm.argWord e 0).toAdr = 0) :
    primaryFlowAtom e =
      some (.transfer e.caller.toB256 (Sevm.argWord e 0)
        e.caller 0 (Sevm.argWord e 1).toNat) :=
  primaryFlowAtom_dirty_zero_transferAndCall_is_transfer e hnonempty
    hselector hraw hnormalized

example (e : Sevm)
    (hnonempty : e.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector e = transferFromSelector)
    (hrawTo : Sevm.argWord e 1 ≠ 0)
    (hnormalized : (Sevm.argWord e 1).toAdr = 0) :
    primaryFlowAtom e =
      some (.transfer (Sevm.argWord e 0) (Sevm.argWord e 1)
        (Sevm.argWord e 0).toAdr 0 (Sevm.argWord e 2).toNat) :=
  primaryFlowAtom_dirty_zero_transferFrom_is_transfer e hnonempty
    hselector hrawTo hnormalized

example {dp : DeployParams} {ca : Adr} {e : Sevm}
    (hcodeAddress : e.codeAddress ≠ some ca) :
    ¬ exactInvocation dp ca e :=
  not_exactInvocation_of_codeAddress_ne hcodeAddress

example {dp : DeployParams} {ca : Adr} {e : Sevm}
    (htarget : e.currentTarget ≠ ca) :
    ¬ exactInvocation dp ca e :=
  not_exactInvocation_of_currentTarget_ne htarget

example {dp : DeployParams} {ca : Adr} {e : Sevm}
    (hcode : some e.code.toList ≠ Prog.compile (weth10 dp)) :
    ¬ exactInvocation dp ca e :=
  not_exactInvocation_of_code_ne hcode

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (htarget : frame.sevm.currentTarget ≠ ca) :
    frame.flowAction? dp ca = none :=
  frame.flowAction_eq_none_of_currentTarget_ne htarget

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcodeAddress : frame.sevm.codeAddress ≠ some ca) :
    frame.flowAction? dp ca = none :=
  frame.flowAction_eq_none_of_codeAddress_ne hcodeAddress

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcode : some frame.sevm.code.toList ≠ Prog.compile (weth10 dp)) :
    frame.flowAction? dp ca = none :=
  frame.flowAction_eq_none_of_code_ne hcode

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hpc : frame.pc ≠ 0) :
    frame.flowAction? dp ca = none :=
  frame.flowAction_eq_none_of_pc_ne hpc

/-! The executable numeric fixtures pin the category fold independently of
the proof-carrying history constructors. -/

example (u v : Adr) (hne : u ≠ v) :
    let observation := fun atom : FlowAtom =>
      ({ atom := atom
         actualCaller := 0
         currentTarget := 0
         codeAddress := some 0
         depth := 0 } : FlowObservation)
    let flow := holderFlowOfObservations
      [ observation (.ordinaryMint u.toB256 u 10)
      , observation (.transfer v.toB256 u.toB256 v u 3)
      , observation (.transfer u.toB256 u.toB256 u u 5)
      , observation (.flashPair u.toB256 u 7)
      , observation (.redemption u.toB256 u u 4)
      , observation (.transfer u.toB256 v.toB256 u v 2) ] u
    flow.ordinaryIn = 13 ∧
      flow.redeemed = 4 ∧
      flow.externalTransferredOut = 2 ∧
      flow.selfTransfer = 5 ∧
      flow.flashCredit = 7 ∧
      flow.flashRepayment = 7 :=
  holderFlow_multiStep_fixture_totals u v hne

example (u : Adr) :
    let observation := fun atom : FlowAtom =>
      ({ atom := atom
         actualCaller := 0
         currentTarget := 0
         codeAddress := some 0
         depth := 0 } : FlowObservation)
    let flow := holderFlowOfObservations
      [ observation (.flashPair u.toB256 u 2)
      , observation (.flashPair u.toB256 u 3) ] u
    flow.flashCredit = 5 ∧ flow.flashRepayment = 5 :=
  holderFlow_nestedFlash_fixture_totals u

example (u : Adr) :
    let observation :=
      ({ atom := FlowAtom.flashPair u.toB256 u maxFlashMinted
         actualCaller := 0
         currentTarget := 0
         codeAddress := some 0
         depth := 0 } : FlowObservation)
    let flow := holderFlowOfObservations [observation] u
    flow.flashCredit = maxFlashMinted ∧
      flow.flashRepayment = maxFlashMinted :=
  holderFlow_maximumFlash_fixture_totals u

example (ca u : Adr) :
    ({ atom := .ordinaryMint u.toB256 u 1
       credit := some
        { recipient := u, before := B256.max, amountWord := 1 }
       debit := none
       actualCaller := u
       currentTarget := ca
       codeAddress := some ca
       depth := 0 } : FlowAction).creditLossTotal = 2 ^ 256 :=
  maxOneMintCandidate_creditLoss ca u

example (ca source recipient : Adr) :
    ({ atom := .transfer source.toB256 recipient.toB256 source recipient 1
       credit := some
        { recipient := recipient, before := B256.max, amountWord := 1 }
       debit := some
        { actualCaller := source
          rawSource := source.toB256
          source := source
          branch := .direct }
       actualCaller := source
       currentTarget := ca
       codeAddress := some ca
       depth := 0 } : FlowAction).creditLossTotal = 2 ^ 256 :=
  maxOneTransferCandidate_creditLoss ca source recipient

end Weth10

end Blanc
