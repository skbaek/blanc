import Blanc.Weth10Redeemable

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

example {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hstable : Stable dp ca benv.state)
    (hq : q ≤ bookedBalanceNat benv.state ca owner)
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index) :
    TransactionRedemptionEnabled
      dp ca owner recipient q benv bout tx index :=
  hstable.transactionRedemption_enabled_of_le hq henv

end Weth10

end Blanc
