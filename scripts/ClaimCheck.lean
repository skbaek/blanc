import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.Capstone
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolFinal
import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteFrame
import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteInit
import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteExample
import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteRegistry
import Blanc.Lift.UniswapV2Pair.PairHistoryMinLiquidity
import Blanc.Lift.UniswapV2Pair.Properties
import Blanc.Lift.UniswapV2Pair.PropertiesMintBurn
import Blanc.Lift.UniswapV2Pair.PropertiesSwap
import Blanc.Lift.UniswapV2Pair.SqrtWalk
import Blanc.Lift.UniswapV2Pair.SwapCanonical
import Blanc.Lift.UniswapV2Pair.Creation.Facts
import Blanc.Lift.UniswapV2Pair.ModelControls
import Blanc.Lift.UniswapV2Pair.OracleControls
import Blanc.Lift.UniswapV2Pair.SwapControls
import Blanc.Lift.UniswapV2Pair.LedgerKeyControl
import Blanc.Lift.UniswapV2Pair.CalleeControls
import Blanc.Lift.UniswapV2Pair.CalleeControlsSwap
import Blanc.Lift.UniswapV2Pair.CalleeControlsReach
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary
import Blanc.Lift.UniswapV2Pair.PropertiesMinLiquidity
import Blanc.Lift.UniswapV2Pair.ModelMutants
import Blanc.Weth10Redeemable
import Blanc.Weth10MainnetCodeEq
import Blanc.Weth10DeploymentRoot
import Blanc.Weth10HolderFlowDeterminism
import Blanc.Weth10HolderFlowResult
import Blanc.Weth10HolderFlowWriteCompleteness
import Blanc.Weth10Attribution
import Blanc.Weth10AllowanceDispatch
import Blanc.Weth10Hardened
import Blanc.Weth10Dormant
import Blanc.Weth10FutureRedeemable
import Blanc.Weth10AnyOrder
import Blanc.Weth10Mainnet
import Blanc.Weth10PragueCompat
import Blanc.LidoCircuitBreakerDeploy
import Blanc.LidoCircuitBreakerRegistryModel
import Blanc.LidoCircuitBreakerRegistry
import Blanc.LidoCircuitBreakerEnumeration
import Blanc.LidoCircuitBreakerDeploymentRoot
import Blanc.ProxyPairOssifiableDeploymentFixture
import Blanc.ProxyPairOssifiableConstructorNonempty
import Blanc.ProxyPairOssifiableBothSlotFixture
import Blanc.ProxyPairOssifiableBothSlotDeployment
import Blanc.ProrataAttackTrace
import Blanc.BeaconDepositConstructorEffects
import Blanc.BeaconDepositBridgeCompiled
import Blanc.BeaconDepositSuccessSettlement
import Blanc.BeaconDepositSuccessChronology
import Blanc.BeaconDepositErrors
import Blanc.BeaconDepositRootPublic
import Blanc.BeaconDepositSelectorMiss
import Blanc.BeaconDepositCountEffects
import Blanc.BeaconDepositEffects
import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGateway
import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayControlRun
import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewaySentinelControlRun
import Blanc.BeaconDepositHistoryChain
import Blanc.DripFresh
import Blanc.DripRpow
import Blanc.DripTranscriptHistory
import Blanc.DripClockHistory
import Blanc.DripTraceRealizes
import Blanc.RevertCause
import Blanc.ProrataWethVaultMaxArithmetic
import Blanc.ProrataWethVaultShares
import Blanc.ProrataWethVaultViews
import Blanc.Composition.ProrataWethVaultConversions
import Blanc.Composition.ProrataWethVaultMessage
import Blanc.Composition.ProrataWethVaultEnvironment
import Blanc.Composition.ProrataWethVaultPairHistory
import Blanc.Composition.ProrataWethVaultAccountingHistory
import Blanc.Composition.ProrataWethVaultCoalitionHistory
import Blanc.Composition.ProrataWethVaultLedgerFaithful
import Blanc.Composition.ProrataWethVaultCoalitionInhabitant
import Blanc.Composition.ProrataWethVaultNonrevert
import Blanc.Composition.ProrataWethVaultCapacities
import Blanc.Lift.Weth9.FootHistory
import Blanc.Lift.Weth9.CommittedHistory
import Blanc.Lift.Weth9.LiveTx
import Blanc.Lift.Weth9.Creation.Deploy
import Blanc.Lift.Weth9.Creation.DeployInit
import Blanc.Lift.BeaconDeposit.BeaconEnv
import Blanc.Lift.BeaconDeposit.Creation.Deploy
import Blanc.Lift.Curve3Crv.CommittedHistory
import Blanc.Lift.Curve3Crv.Safe
import Blanc.Lift.Curve3Crv.Creation.Deploy
import Blanc.Lift.LidoCircuitBreakerDeployed.History
import Blanc.Lift.LidoCircuitBreakerDeployed.L2History
import Blanc.Lift.LidoCircuitBreakerDeployed.Creation.Deploy
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exclusion
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.Top
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.Top
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.ForkTop
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Envelope
import Blanc.Lift.WithdrawalRequest.WordFifo
import Blanc.Lift.WithdrawalRequest.WordDelivery
import Blanc.Composition.WithdrawalRequestDrainControl
import Blanc.Lift.WithdrawalRequest.SystemHistory
import Blanc.Lift.WithdrawalRequest.ExactFeeDomain
import Blanc.Composition.WithdrawalRequestFeeRefutation
import Blanc.Lift.WithdrawalRequest.NatLiveness
import Blanc.Lift.WithdrawalRequest.Creation.Deploy
import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.UniswapV2Pair.PairHistoryLive
import Blanc.Lift.UniswapV2Pair.PairHistoryLiveAdmin
import Blanc.Lift.UniswapV2Pair.PermitSource
import Blanc.Lift.UniswapV2Pair.BurnFeeTransfers
import Blanc.Lift.UniswapV2Pair.StaticViewClassify
import Blanc.Lift.UniswapV2Pair.Creation.DeployInit

/-!
Lean-checked statement pins for the WETH10 flagship declarations and the Lido
CircuitBreaker artifact, Registry, and exact direct-deployment/root carriers.
Each
wrapper has the exact intended type and uses the named declaration as its
body, so a statement change breaks this file while a proof-only refactor does
not.  `Stor.Weth10Inv` is pinned separately by definitional unfolding.
-/

namespace Blanc

open Jaune

example {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm)
    (hne : sevm.currentTarget ≠ f.inner.currentTarget)
    (hcode : devm.getCode f.inner.currentTarget ≠ .empty)
    (hnodel :
      getDelegatedCodeAddress (devm.getCode f.inner.currentTarget) = none) :
    f.inner.codeAddress = some f.inner.currentTarget :=
  Xinst.step_spawn_codeAddress_eq_currentTarget hs hne hcode hnodel

example {root target : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {source : Func} {instruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : some root.sevm.code.toList = program.compile)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    Exec.Deriv.SourceCursor.Toward cursor target instruction cursor :=
  cursor.toward compiled reached nonPush instructionAt

example {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor root program initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (chronology : Exec.Deriv.SourceCursor.Chronology initial cursor target)
    (distinct : cursor.node ≠ target) :
    Exec.Deriv.lt target cursor.node :=
  chronology.strictBefore distinct

namespace Weth10

example (dp : DeployParams) :
    Prog.compile (weth10 dp) = some (weth10Code dp) :=
  weth10Code_compile dp

example :
    weth10Code mainnetDeployParams = weth10MainnetCode :=
  weth10MainnetCode_eq

example (dp : DeployParams) (ca : Adr) (depth : Nat) :
    FlashExactDepth dp ca depth :=
  flashExactDepth dp ca depth

example (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).Sound ca :=
  backedSpec_sound dp ca

example (dp : DeployParams) (ca : Adr) :
    (backedSpec weth10 dp).Preserves ca :=
  backedSpec_preserves dp ca

/-!
The two pins above name `ContractSpec.Sound` and `ContractSpec.Preserves`,
which are `def`s: adding a premise to either changes what the flagship claims
while leaving those two examples typechecking.  The four pins below spell the
quantifier and premise list out instead, so the premise list itself is what is
pinned and a premise added anywhere in it breaks this file.

The flagship obligations are the `NoMem` ones: no WETH10 selector reads the
machine's memory, so neither the obligation nor the frame theorem is entitled
to a `Mem.Wf` premise.  The memory-carrying pair is pinned too, because the
message-, transaction- and block-level rungs consume it.

Since the 2026-09-23 coverage restriction each obligation, and the
deeper-frame hypothesis inside it, is stated only for frames whose fork is
`CoveredFork` (Prague, Osaka, BPO1, BPO2); Amsterdam frames are not covered.
-/

example (dp : DeployParams) (ca : Adr) :
    ∀ {sevm : Sevm} {pre post : Devm},
      CoveredFork sevm.benvStat.fork →
      Prog.Run sevm pre (backedSpec weth10 dp).prog post →
      sevm.currentTarget = ca →
      ( ∀ pc' sevm' pre' post',
          Exec pc' sevm' pre' (.ok post') →
          sevm'.depth < sevm.depth →
          Prog.At (backedSpec weth10 dp).prog ca pc' sevm' pre' →
          CoveredFork sevm'.benvStat.fork →
          (backedSpec weth10 dp).PreWf ca sevm' pre' →
          (backedSpec weth10 dp).Post ca sevm' post' ) →
      (backedSpec weth10 dp).Pre ca sevm pre →
      (backedSpec weth10 dp).Post ca sevm post :=
  backedSpec_soundNoMem dp ca

example (dp : DeployParams) (ca : Adr) :
    ∀ sevm pre post,
      CoveredFork sevm.benvStat.fork →
      Exec 0 sevm pre (.ok post) →
      (sevm.currentTarget = ca →
        some sevm.code.toList = Prog.compile (backedSpec weth10 dp).prog) →
      (backedSpec weth10 dp).Pre ca sevm pre →
      (backedSpec weth10 dp).Post ca sevm post :=
  backedSpec_preservesNoMem dp ca

example (dp : DeployParams) (ca : Adr) :
    ∀ {sevm : Sevm} {pre post : Devm},
      CoveredFork sevm.benvStat.fork →
      Prog.Run sevm pre (backedSpec weth10 dp).prog post →
      sevm.currentTarget = ca →
      ( ∀ pc' sevm' pre' post',
          Exec pc' sevm' pre' (.ok post') →
          sevm'.depth < sevm.depth →
          Prog.At (backedSpec weth10 dp).prog ca pc' sevm' pre' →
          CoveredFork sevm'.benvStat.fork →
          (backedSpec weth10 dp).PreWf ca sevm' pre' →
          (backedSpec weth10 dp).Post ca sevm' post' ) →
      Mem.Wf pre.memory →
      (backedSpec weth10 dp).Pre ca sevm pre →
      (backedSpec weth10 dp).Post ca sevm post :=
  backedSpec_sound dp ca

example (dp : DeployParams) (ca : Adr) :
    ∀ sevm pre post,
      CoveredFork sevm.benvStat.fork →
      Exec 0 sevm pre (.ok post) →
      (sevm.currentTarget = ca →
        some sevm.code.toList = Prog.compile (backedSpec weth10 dp).prog) →
      (sevm.currentTarget = ca → Mem.Wf pre.memory) →
      (backedSpec weth10 dp).Pre ca sevm pre →
      (backedSpec weth10 dp).Post ca sevm post :=
  backedSpec_preserves dp ca

example (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : weth10CreateMessageGasAccounting ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hfork : CoveredFork msg.benv.stat.fork) :
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
  processCreateMessage_weth10_success msg h_value h_codeAddress h_code h_gas h_max hfork

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

example (dp : DeployParams) (ca : Adr) (cfg : ChainConfig)
    (ch ch' : BlockChain)
    (h_reach : BlockChain.ReachUsing cfg ch ch')
    (h_inv : Stable dp ca ch.state)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f) :
    (ch'.state.getStor ca).get flashMintedSlot = 0 ∧
      balSum (ch'.state.getStor ca) ≤ (ch'.state.bal ca).toNat :=
  chain_reachable_backed_and_flash_zero dp ca cfg ch ch' h_reach h_inv hcov

example (msg : Msg)
    (h_value : msg.value = 0)
    (h_codeAddress : msg.codeAddress = .none)
    (h_code : msg.code.toList = weth10InitCode)
    (h_gas : weth10CreateMessageGasAccounting ≤ msg.gas)
    (h_max : 6313 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (h_sum : SumNof msg.benv.state.bal)
    (hfork : CoveredFork msg.benv.stat.fork) :
    ∃ post,
      processCreateMessage msg = .ok post ∧
      Stable
        (freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget)
        msg.currentTarget post.state :=
  processCreateMessage_establishes_stable msg h_value h_codeAddress h_code h_gas h_max h_sum hfork

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

example : ForkRules → DeployParams → Adr → Adr → Adr → Nat → State → Msg → Prop :=
  AdmissibleRedemptionMessage

example : ForkRules → DeployParams → Adr → Adr → Nat → State → Msg → Prop :=
  AdmissibleSelfRedemptionMessage

example : DeployParams → Adr → Adr → Adr → Nat →
    State → State → MsgCallOutput → Prop :=
  MessageRedemptionExactEffect

example : DeployParams → Adr → Adr → Adr → Nat → State → Msg → Prop :=
  MessageRedemptionEnabled

example : ForkRules → DeployParams → Adr → Adr → Adr → Nat →
    Benv → BlockOutput → Tx → Nat → Prop :=
  AdmissibleRedemptionTx

example : ForkRules → DeployParams → Adr → Adr → Nat →
    Benv → BlockOutput → Tx → Nat → Prop :=
  AdmissibleSelfRedemptionTx

example : ForkRules → DeployParams → Adr → Adr → Adr → Nat →
    Benv → BlockOutput → Tx → Nat → Nat → Nat → Prop :=
  NonSignatureRedemptionTxEnvelope

example (w : State) (owner : Adr) :
    TransactionSenderAdmissible w owner ↔
      (w.getCode owner).isEmpty ∨ isValidDelegation (w.getCode owner) := by
  rfl

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

example {rules : ForkRules} {dp : DeployParams}
    {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (state_eq : msg.benv.state = w)
    (rules_eq : msg.benv.stat.rules = rules)
    (fork_covered : CoveredFork msg.benv.stat.fork)
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
    (target_not_precompile : rules.isPrecomp ca = false)
    (recipient_ne_zero : recipient ≠ 0)
    (recipient_not_precompile : rules.isPrecomp recipient = false)
    (recipient_code_free : (w.getCode recipient).toList = [])
    (original_storage_eq : msg.benv.stat.origState.getStor ca = w.getStor ca)
    (target_access : AddressAccessCase msg.accessedAddresses ca)
    (recipient_access : AddressAccessCase msg.accessedAddresses recipient)
    (owner_storage_access :
      StorageAccessCase msg.accessedStorageKeys ca owner.toB256)
    (recipient_account : RecipientAccountCase w recipient)
    (gas_bound : redemptionRuntimeCeiling q ≤ msg.gas) :
    AdmissibleRedemptionMessageCore rules dp ca owner recipient q w msg :=
  { state_eq := state_eq
    rules_eq := rules_eq
    fork_covered := fork_covered
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

example {rules : ForkRules} {dp : DeployParams}
    {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (core : AdmissibleRedemptionMessageCore
      rules dp ca owner recipient q w msg)
    (data_eq : msg.data = withdrawToCalldata recipient q)
    (selector_eq : Sevm.selector (initSevm msg) = withdrawToSelector) :
    AdmissibleRedemptionMessage rules dp ca owner recipient q w msg :=
  { toAdmissibleRedemptionMessageCore := core
    data_eq := data_eq
    selector_eq := selector_eq }

example {rules : ForkRules} {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (core : AdmissibleRedemptionMessageCore rules dp ca owner owner q w msg)
    (data_eq : msg.data = withdrawCalldata q)
    (selector_eq : Sevm.selector (initSevm msg) = withdrawSelector) :
    AdmissibleSelfRedemptionMessage rules dp ca owner q w msg :=
  { toAdmissibleRedemptionMessageCore := core
    data_eq := data_eq
    selector_eq := selector_eq }

example {rules : ForkRules} {dp : DeployParams}
    {ca owner recipient : Adr} {q : Nat}
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
    (rules_eq : benv.stat.rules = rules)
    (fork_covered : CoveredFork benv.stat.fork)
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
    (owner_sender_admissible : TransactionSenderAdmissible benv.state owner)
    (validated :
      validateTransaction rules tx 0 = .ok (calculateIntrinsicCost rules tx 0))
    (checked :
      checkTransaction benv.beginTransaction
        (redemptionTxPreludeBout bout tx index) tx =
        .ok (owner, redemptionEffectiveGasPrice benv tx, [], 0))
    (base_fee_le_effective :
      benv.stat.baseFeePerGas ≤ redemptionEffectiveGasPrice benv tx)
    (upfront_funded : tx.gas * redemptionEffectiveGasPrice benv tx ≤
      (benv.state.bal owner).toNat)
    (gas_cap : checkTransactionGasCap rules.tx tx.gas = .ok ())
    (gas_bound : redemptionTransactionGasBound q benv tx owner ≤ tx.gas)
    (block_gas_room : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (target_code :
      some (benv.state.getCode ca).toList = Prog.compile (weth10 dp))
    (target_not_precompile : rules.isPrecomp ca = false)
    (target_not_created : ca ∉ benv.createdAccounts)
    (recipient_ne_zero : recipient ≠ 0)
    (recipient_not_precompile : rules.isPrecomp recipient = false)
    (recipient_code_free : (benv.state.getCode recipient).toList = [])
    (recipient_account : RecipientAccountCase benv.state recipient) :
    AdmissibleRedemptionTx
      rules dp ca owner recipient q benv bout tx index :=
  { rules_eq := rules_eq
    fork_covered := fork_covered
    type_eq := type_eq
    data_eq := data_eq
    selector_eq := selector_eq
    value_eq := value_eq
    nonce_eq := nonce_eq
    nonce_not_max := nonce_not_max
    recoveredSender := recoveredSender
    owner_ne_zero := owner_ne_zero
    owner_sender_admissible := owner_sender_admissible
    validated := validated
    checked := checked
    base_fee_le_effective := base_fee_le_effective
    upfront_funded := upfront_funded
    gas_cap := gas_cap
    gas_bound := gas_bound
    block_gas_room := block_gas_room
    target_code := target_code
    target_not_precompile := target_not_precompile
    target_not_created := target_not_created
    recipient_ne_zero := recipient_ne_zero
    recipient_not_precompile := recipient_not_precompile
    recipient_code_free := recipient_code_free
    recipient_account := recipient_account }

example {rules : ForkRules} {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (rules_eq : benv.stat.rules = rules)
    (fork_covered : CoveredFork benv.stat.fork)
    (type_eq : ∃ maxPriorityFee maxFee,
      tx.type = .two benv.stat.chainId maxPriorityFee maxFee (some ca) [])
    (data_eq : tx.data = withdrawCalldata q)
    (selector_eq : ∀ e : Sevm, e.data = tx.data →
      Sevm.selector e = withdrawSelector)
    (value_eq : tx.value = 0)
    (nonce_eq : tx.nonce = benv.state.getNonce owner)
    (nonce_not_max : tx.nonce ≠ UInt64.max)
    (recoveredSender : recoverSender benv.stat.chainId tx = .ok owner)
    (owner_ne_zero : owner ≠ 0)
    (owner_not_precompile : rules.isPrecomp owner = false)
    (owner_code_free : (benv.state.getCode owner).toList = [])
    (validated :
      validateTransaction rules tx 0 = .ok (calculateIntrinsicCost rules tx 0))
    (checked :
      checkTransaction benv.beginTransaction
        (redemptionTxPreludeBout bout tx index) tx =
        .ok (owner, redemptionEffectiveGasPrice benv tx, [], 0))
    (base_fee_le_effective :
      benv.stat.baseFeePerGas ≤ redemptionEffectiveGasPrice benv tx)
    (upfront_funded : tx.gas * redemptionEffectiveGasPrice benv tx ≤
      (benv.state.bal owner).toNat)
    (gas_cap : checkTransactionGasCap rules.tx tx.gas = .ok ())
    (gas_bound : redemptionTransactionGasBound q benv tx owner ≤ tx.gas)
    (block_gas_room : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (target_code :
      some (benv.state.getCode ca).toList = Prog.compile (weth10 dp))
    (target_not_precompile : rules.isPrecomp ca = false)
    (target_not_created : ca ∉ benv.createdAccounts)
    (owner_account : RecipientAccountCase benv.state owner) :
    AdmissibleSelfRedemptionTx rules dp ca owner q benv bout tx index :=
  { rules_eq := rules_eq
    fork_covered := fork_covered
    type_eq := type_eq
    data_eq := data_eq
    selector_eq := selector_eq
    value_eq := value_eq
    nonce_eq := nonce_eq
    nonce_not_max := nonce_not_max
    recoveredSender := recoveredSender
    owner_ne_zero := owner_ne_zero
    owner_not_precompile := owner_not_precompile
    owner_code_free := owner_code_free
    validated := validated
    checked := checked
    base_fee_le_effective := base_fee_le_effective
    upfront_funded := upfront_funded
    gas_cap := gas_cap
    gas_bound := gas_bound
    block_gas_room := block_gas_room
    target_code := target_code
    target_not_precompile := target_not_precompile
    target_not_created := target_not_created
    owner_account := owner_account }

example {rules : ForkRules} {dp : DeployParams}
    {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {maxPriorityFee maxFee : Nat}
    (rules_eq : benv.stat.rules = rules)
    (fork_covered : CoveredFork benv.stat.fork)
    (type_eq : tx.type =
      .two benv.stat.chainId maxPriorityFee maxFee (some ca) [])
    (data_eq : tx.data = withdrawToCalldata recipient q)
    (value_eq : tx.value = 0)
    (nonce_eq : tx.nonce = benv.state.getNonce owner)
    (nonce_not_max : tx.nonce ≠ UInt64.max)
    (owner_ne_zero : owner ≠ 0)
    (owner_sender_admissible : TransactionSenderAdmissible benv.state owner)
    (priority_fee_le_max : maxPriorityFee ≤ maxFee)
    (base_fee_le_max : benv.stat.baseFeePerGas ≤ maxFee)
    (max_fee_fits : tx.gas * maxFee ≤ B256.max.toNat)
    (max_fee_funded : tx.gas * maxFee ≤ (benv.state.bal owner).toNat)
    (gas_cap : checkTransactionGasCap rules.tx tx.gas = .ok ())
    (gas_bound : redemptionTransactionGasBound q benv tx owner ≤ tx.gas)
    (block_gas_room : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (target_code :
      some (benv.state.getCode ca).toList = Prog.compile (weth10 dp))
    (target_not_precompile : rules.isPrecomp ca = false)
    (target_not_created : ca ∉ benv.createdAccounts)
    (recipient_ne_zero : recipient ≠ 0)
    (recipient_not_precompile : rules.isPrecomp recipient = false)
    (recipient_code_free : (benv.state.getCode recipient).toList = [])
    (recipient_account : RecipientAccountCase benv.state recipient) :
    NonSignatureRedemptionTxEnvelope rules dp ca owner recipient q benv bout tx
      index maxPriorityFee maxFee :=
  { rules_eq := rules_eq
    fork_covered := fork_covered
    type_eq := type_eq
    data_eq := data_eq
    value_eq := value_eq
    nonce_eq := nonce_eq
    nonce_not_max := nonce_not_max
    owner_ne_zero := owner_ne_zero
    owner_sender_admissible := owner_sender_admissible
    priority_fee_le_max := priority_fee_le_max
    base_fee_le_max := base_fee_le_max
    max_fee_fits := max_fee_fits
    max_fee_funded := max_fee_funded
    gas_cap := gas_cap
    gas_bound := gas_bound
    block_gas_room := block_gas_room
    target_code := target_code
    target_not_precompile := target_not_precompile
    target_not_created := target_not_created
    recipient_ne_zero := recipient_ne_zero
    recipient_not_precompile := recipient_not_precompile
    recipient_code_free := recipient_code_free
    recipient_account := recipient_account }

example {rules : ForkRules} {dp : DeployParams}
    {ca owner recipient : Adr} {q : Nat}
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
      rules dp ca owner recipient q w msg) :
    MessageRedemptionEnabled dp ca owner recipient q w msg :=
  hstable.messageRedemption_enabled_of_le hq henv

example {rules : ForkRules} {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleSelfRedemptionMessage rules dp ca owner q w msg) :
    MessageRedemptionEnabled dp ca owner owner q w msg :=
  hstable.selfRedemption_enabled_of_le hq henv

example {rules : ForkRules} {dp : DeployParams}
    {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hstable : Stable dp ca benv.state)
    (hq : q ≤ bookedBalanceNat benv.state ca owner)
    (henv : AdmissibleRedemptionTx
      rules dp ca owner recipient q benv bout tx index) :
    TransactionRedemptionEnabled
      dp ca owner recipient q benv bout tx index :=
  hstable.transactionRedemption_enabled_of_le hq henv

example {rules : ForkRules} {dp : DeployParams}
    {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {maxPriorityFee maxFee : Nat}
    (henv : NonSignatureRedemptionTxEnvelope
      rules dp ca owner recipient q benv bout tx index maxPriorityFee maxFee)
    (hrecovered : recoverSender benv.stat.chainId tx = .ok owner) :
    AdmissibleRedemptionTx rules dp ca owner recipient q benv bout tx index :=
  henv.admissible_of_recoveredSender hrecovered

example {rules : ForkRules} {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hstable : Stable dp ca benv.state)
    (hq : q ≤ bookedBalanceNat benv.state ca owner)
    (henv : AdmissibleSelfRedemptionTx rules dp ca owner q benv bout tx index) :
    TransactionRedemptionEnabled dp ca owner owner q benv bout tx index :=
  hstable.selfTransactionRedemption_enabled_of_le hq henv

example {rules : ForkRules} {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (henv : AdmissibleSelfRedemptionTx rules dp ca owner q benv bout tx index)
    {debit : State} {msg : Msg} {entry messagePost : Devm}
    {messageOut : MsgCallOutput}
    (hdebit : TransactionDebitOutcome owner
      (tx.gas * redemptionEffectiveGasPrice benv tx) benv.state debit)
    (hprepare :
      prepareMessage {benv.beginTransaction with state := debit}
        (redemptionTenv benv tx owner index) tx = .ok msg)
    (hframe : MessageFrameRedemptionOutcome
      dp ca owner owner q debit msg entry messagePost messageOut) :
    let usedGas := redemptionUsedGasFromMessage benv tx owner messageOut
      messagePost.refundCounter.toNat
    processTransaction benv bout tx index = .ok
      (redemptionFinalState benv tx owner messagePost.state usedGas,
        redemptionFinalBout bout tx index messageOut usedGas) :=
  henv.processTransaction_eq_of_message hdebit hprepare hframe

/-! Deployment constructor pins make the pre-execution/result boundary fail
closed on record-field additions, removals, or type changes. -/

example {cfg : ChainConfig} {fork : Fork}
    {base : BlockChain} {sender ca : Adr}
    (configValid : cfg.Valid)
    (chainId_eq : cfg.chainId = base.chainId)
    (validContext : base.ValidContext)
    (sumNof : SumNof base.state.bal)
    (target_eq : ca = computeContractAddress sender (base.state.getNonce sender))
    (target_ne_zero : ca ≠ 0)
    (target_not_precompile : ∀ {timestamp selected},
      cfg.rulesAt timestamp = .ok selected → ¬ selected.isPrecomp ca)
    (beacon_not_precompile : ¬ (Fork.ruleSet fork).isPrecomp beaconRootsAddress)
    (history_not_precompile : ¬ (Fork.ruleSet fork).isPrecomp historyStorageAddress)
    (withdrawalRequest_not_precompile :
      ¬ (Fork.ruleSet fork).isPrecomp withdrawalRequestPredeployAddress)
    (consolidationRequest_not_precompile :
      ¬ (Fork.ruleSet fork).isPrecomp consolidationRequestPredeployAddress)
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
    CanonicalDeploymentBase cfg fork base sender ca :=
  { configValid := configValid
    chainId_eq := chainId_eq
    validContext := validContext
    sumNof := sumNof
    target_eq := target_eq
    target_ne_zero := target_ne_zero
    target_not_precompile := target_not_precompile
    beacon_not_precompile := beacon_not_precompile
    history_not_precompile := history_not_precompile
    withdrawalRequest_not_precompile := withdrawalRequest_not_precompile
    consolidationRequest_not_precompile := consolidationRequest_not_precompile
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

example {cfg : ChainConfig} {fork : Fork}
    {base : BlockChain} {cb : CanonicalBlock}
    {deploymentTxBytes : Bytes} {deploymentTx : Tx} {sender ca : Adr}
    (txs_eq : cb.block.txs = [.inl deploymentTxBytes])
    (decode_eq : decodeTx (.inl deploymentTxBytes) = .ok deploymentTx)
    (ommers_eq : cb.block.ommers = [])
    (withdrawals_eq : cb.block.wds = [])
    (forkAt : cfg.forkAt cb.block.header.timestamp = .ok fork)
    (type_eq : ∃ maxPriorityFee maxFee,
      deploymentTx.type = .two cfg.chainId maxPriorityFee maxFee none [])
    (value_eq : deploymentTx.value = 0)
    (data_eq : deploymentTx.data = weth10InitCode)
    (nonce_eq : deploymentTx.nonce = base.state.getNonce sender)
    (nonce_not_max : deploymentTx.nonce ≠ UInt64.max)
    (recoveredSender : recoverSender cfg.chainId deploymentTx = .ok sender)
    (validated : validateTransaction (Fork.ruleSet fork) deploymentTx 0 =
      .ok (calculateIntrinsicCost (Fork.ruleSet fork) deploymentTx 0))
    (checked :
      let benv := initBenv fork base cb.block.header
      checkTransaction benv.beginTransaction
        (deploymentTxPreludeBout .init deploymentTx 0) deploymentTx =
        .ok (sender, deploymentEffectiveGasPrice benv deploymentTx, [], 0))
    (base_fee_le_effective : cb.block.header.baseFeePerGas ≤
      deploymentEffectiveGasPrice
        (initBenv fork base cb.block.header) deploymentTx)
    (upfront_funded :
      deploymentTx.gas * deploymentEffectiveGasPrice
        (initBenv fork base cb.block.header) deploymentTx ≤
      (base.state.bal sender).toNat)
    (gas_bound : deploymentTransactionGasBound
      (initBenv fork base cb.block.header) deploymentTx sender ≤ deploymentTx.gas)
    (runtime_code_fits : 6313 ≤ (Fork.ruleSet fork).code.maxCodeSize)
    (block_gas_room : deploymentTx.gas ≤ cb.block.header.gasLimit)
    (target_eq : ca = computeContractAddress sender deploymentTx.nonce) :
    CanonicalWeth10DeploymentBlock cfg fork base cb deploymentTxBytes
      deploymentTx sender ca :=
  { txs_eq := txs_eq
    decode_eq := decode_eq
    ommers_eq := ommers_eq
    withdrawals_eq := withdrawals_eq
    forkAt := forkAt
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
    runtime_code_fits := runtime_code_fits
    block_gas_room := block_gas_room
    target_eq := target_eq }

example {cfg : ChainConfig} {fork : Fork}
    {base : BlockChain} {cb : CanonicalBlock}
    {deploymentTx : Tx} {sender ca : Adr}
    (txInput : Benv) (begun : Benv) (debit : State) (tenv : Tenv) (msg : Msg)
    (systemPrefix : DeploymentSystemPrefix fork base cb.block txInput)
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
    (msg_gas_eq : msg.gas = deploymentTx.gas -
      deploymentIntrinsicGas txInput deploymentTx sender)
    (msg_value_eq : msg.value = 0)
    (msg_data_eq : msg.data = [])
    (msg_code_eq : msg.code.toList = weth10InitCode)
    (msg_codeAddress_eq : msg.codeAddress = none)
    (msg_shouldTransferValue_eq : msg.shouldTransferValue = true)
    (msg_auths_eq : msg.tenv.stat.auths = [])
    (msg_rules_eq : msg.benv.stat.rules = Fork.ruleSet fork)
    (msg_fork_eq : msg.benv.stat.fork = fork)
    (msg_chainId_eq : msg.benv.stat.chainId = cfg.chainId)
    (target_eq : msg.currentTarget = ca)
    (params_eq :
      freshDeployParams msg.benv.stat.chainId.toB256 msg.currentTarget =
        freshDeployParams cfg.chainId.toB256 ca)
    (noCodeOrNonce : accountHasCodeOrNonce msg.benv.state ca = false)
    (noStorage : accountHasStorage msg.benv.state ca = false) :
    PreparedDeploymentContext cfg fork base cb deploymentTx sender ca :=
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
    msg_fork_eq := msg_fork_eq
    msg_chainId_eq := msg_chainId_eq
    target_eq := target_eq
    params_eq := params_eq
    noCodeOrNonce := noCodeOrNonce
    noStorage := noStorage }

example {cfg : ChainConfig} {fork : Fork} {ca : Adr}
    {ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca}
    {post : State} {out : MsgCallOutput}
    (run : processMessageCall ctx.msg = .ok (post, out))
    (stable : Stable (freshDeployParams cfg.chainId.toB256 ca) ca post)
    (installed : some (post.getCode ca).toList =
      Prog.compile (weth10 (freshDeployParams cfg.chainId.toB256 ca)))
    (emptyStorage : post.getStor ca = Stor.empty)
    (storageInv : Stor.Weth10Inv (post.getStor ca) 0 0)
    (logs : out.logs = [])
    (returnData : out.returnData =
      weth10Code (freshDeployParams cfg.chainId.toB256 ca))
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
    CanonicalDeploymentMessageResult cfg fork ca ctx post out :=
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

example {cfg : ChainConfig} {fork : Fork} {ca : Adr}
    {ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca}
    {post : State} {bout : BlockOutput}
    (run : processTransaction ctx.txInput .init deploymentTx 0 = .ok (post, bout))
    (stable : Stable (freshDeployParams cfg.chainId.toB256 ca) ca post)
    (installed : some (post.getCode ca).toList =
      Prog.compile (weth10 (freshDeployParams cfg.chainId.toB256 ca)))
    (emptyStorage : post.getStor ca = Stor.empty)
    (blockLogs : bout.blockLogs = [])
    (requests : bout.requests = [])
    (blockAccessList : bout.blockAccessList = [])
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
    CanonicalDeploymentTransactionResult cfg fork ca ctx post bout :=
  { run := run
    stable := stable
    installed := installed
    emptyStorage := emptyStorage
    blockLogs := blockLogs
    requests := requests
    blockAccessList := blockAccessList
    depositRequests := depositRequests
    withdrawalRequestCode := withdrawalRequestCode
    consolidationRequestCode := consolidationRequestCode
    receiptSucceeded := receiptSucceeded }

example {cfg : ChainConfig} {fork : Fork} {ca : Adr}
    {ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca}
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
        (freshDeployParams cfg.chainId.toB256 ca)).StateInv ca post)
    (flashStateInv :
      (flashExactSpec
        (freshDeployParams cfg.chainId.toB256 ca) 0).StateInv ca post)
    (stable : Stable (freshDeployParams cfg.chainId.toB256 ca) ca post) :
    CanonicalDeploymentSuffixResult cfg fork ca ctx post bout :=
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

example {cfg : ChainConfig} {base deployed : BlockChain}
    {dp : DeployParams} {ca : Adr}
    (execution : ∃ (fork : Fork) (cb : CanonicalBlock)
        (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender : Adr)
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
          (fun entry => entry.2.succeeded) = some true)
    (params_eq : dp = freshDeployParams cfg.chainId.toB256 ca)
    (configValid : cfg.Valid)
    (target_ne_zero : ca ≠ 0)
    (target_not_precompile : ∀ {timestamp rules},
      cfg.rulesAt timestamp = .ok rules → ¬ rules.isPrecomp ca)
    (emptyStorage : deployed.state.getStor ca = Stor.empty)
    (stable : Stable dp ca deployed.state)
    (deployed_validContext : deployed.ValidContext)
    (deployed_chainId : cfg.chainId = deployed.chainId) :
    DeploymentRoot cfg base deployed dp ca :=
  { execution := execution
    params_eq := params_eq
    configValid := configValid
    target_ne_zero := target_ne_zero
    target_not_precompile := target_not_precompile
    emptyStorage := emptyStorage
    stable := stable
    deployed_validContext := deployed_validContext
    deployed_chainId := deployed_chainId }

example (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (hfork : CoveredFork fork) :
    Nonempty
      (PreparedDeploymentContext cfg fork base cb deploymentTx sender ca) :=
  prepareCanonicalDeploymentContext cfg fork base cb deploymentTx sender ca
    hbase henv hfork

example (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (hfork : CoveredFork fork) :
    ∃ post out, CanonicalDeploymentMessageResult cfg fork ca ctx post out :=
  canonicalDeploymentMessage_succeeds cfg fork base cb deploymentTx sender ca
    hbase henv ctx hfork

example (cfg : ChainConfig) (fork : Fork)
    (base : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (ctx : PreparedDeploymentContext cfg fork base cb deploymentTx sender ca)
    (hfork : CoveredFork fork) :
    ∃ post bout,
      CanonicalDeploymentTransactionResult cfg fork ca ctx post bout :=
  canonicalDeploymentTransaction_succeeds cfg fork base cb deploymentTx
    sender ca hbase henv ctx hfork

example (cfg : ChainConfig) (fork : Fork)
    (base deployed : BlockChain)
    (cb : CanonicalBlock) (deploymentTxBytes : Bytes)
    (deploymentTx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase cfg fork base sender ca)
    (henv : CanonicalWeth10DeploymentBlock cfg fork base cb
      deploymentTxBytes deploymentTx sender ca)
    (hfork : CoveredFork fork)
    (hstep : stateTransitionUsing cfg
      base cb.block = .ok deployed) :
    DeploymentRoot cfg base deployed
      (freshDeployParams cfg.chainId.toB256 ca) ca :=
  canonicalDeploymentStep_establishes_root cfg fork base deployed cb
    deploymentTxBytes deploymentTx sender ca hbase henv hfork hstep

example (hroot : DeploymentRoot cfg base deployed dp ca) :
    BlockChain.ReachUsing cfg
      deployed deployed :=
  hroot.reflReach

example (hroot : DeploymentRoot cfg base deployed dp ca)
    (hreach : BlockChain.ReachUsing cfg
      deployed future)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f) :
    Stable dp ca future.state :=
  hroot.reachable_stable hreach hcov

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

example : ChainConfig → DeployParams → Adr → BlockChain → BlockChain → Type :=
  AccountedHistory

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory cfg dp ca checkpoint future → List Block :=
  AccountedHistory.appliedBlocks

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint : BlockChain}
    (hcfg : cfg.Valid)
    (hctx : checkpoint.ValidContext)
    (hid : cfg.chainId = checkpoint.chainId) :
    (AccountedHistory.refl (dp := dp) (ca := ca)
      hcfg hctx hid).appliedBlocks = [] := by
  rfl

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint current future : BlockChain}
    (prior : AccountedHistory cfg dp ca checkpoint current)
    (accounted : AccountedBlock cfg dp ca current future) :
    (AccountedHistory.step prior accounted).appliedBlocks =
      prior.appliedBlocks ++ [accounted.block] := by
  rfl

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory cfg dp ca checkpoint future → List FlowAction :=
  AccountedHistory.flowActions

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} :
    AccountedHistory cfg dp ca checkpoint future →
      (u : Adr) → HolderFlow u :=
  AccountedHistory.weth10Flow

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    BlockChain.ReachUsing cfg
      checkpoint future :=
  history.toReachUsing

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (hreach : BlockChain.ReachUsing cfg
      checkpoint future)
    (hcovered : ∀ {pre post block}, stateTransitionUsing cfg pre block = .ok post → ∀ {fork},
      cfg.forkAt block.header.timestamp = .ok fork → CoveredFork fork) :
    Nonempty (AccountedHistory cfg dp ca checkpoint future) :=
  exists_accountedHistory_of_reachUsing hstable hreach hcovered

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history₁ history₂ : AccountedHistory cfg dp ca checkpoint future)
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
    (authentic : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (classified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action)
    (accepted : action.AcceptedDebit dp frame.sevm frame.pre frame.post) :
    Blanc.Weth10.Exec.Frame.HasAcceptedDebit dp ca frame action :=
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
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasAcceptedDebit dp ca frame action :=
  Blanc.Weth10.Exec.Frame.hasAcceptedDebit_of_flowAction?_eq_some context haction

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (authentic : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (classified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action)
    (effect : GenuineWethEmitterEffect dp frame.sevm frame.pre frame.post) :
    Blanc.Weth10.Exec.Frame.HasGenuineWethEmitterEffect dp ca frame action :=
  { authentic := authentic
    classified := classified
    effect := effect }

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (haction : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action) :
    Blanc.Weth10.Exec.Frame.HasGenuineWethEmitterEffect dp ca frame action :=
  Blanc.Weth10.Exec.Frame.hasGenuineWethEmitterEffect_of_flowAction?_eq_some context haction

/-! CREATE children are retained only through complete code-deposit
settlement, not merely because their raw interpreter result committed. -/

example : Jaune.Frame → Execution → Bool :=
  Blanc.Frame.settlementCommits

example {dp : DeployParams} {ca : Adr} {f : Jaune.Frame}
    {raw : Execution} {settled : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    (child : Exec pc sevm pre raw)
    (rawCommits : Execution.commits raw = true)
    (hcreate : f.isCreate = true)
    (hsettled : processCreateMessage.settle f.outer
      (processMessage.settle f.inner
        (executeCode.handleErrorWith f.inner.benv.stat.rules.stateGas raw)) =
        .ok settled)
    (herror : settled.error.isSome = true) :
    (if Blanc.Frame.settlementCommits f raw = true then
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
    (occurrence : Blanc.Weth10.Exec.Frame.BalanceSstoreOccurrence dp ca frame stepPre stepPost slot
      key value holder)
    (authentic : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (classified : Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = some action)
    (role : BalanceSstoreRole ca stepPre action.atom holder value)
    (rich : Blanc.Weth10.Exec.Frame.HasRichLocalStorageEffect dp ca frame action)
    (emitter : Blanc.Weth10.Exec.Frame.HasGenuineWethEmitterEffect dp ca frame action)
    (acceptedDebit : Blanc.Weth10.Exec.Frame.HasAcceptedDebit dp ca frame action) :
    Blanc.Weth10.Exec.Frame.BalanceSstoreClassification dp ca frame stepPre stepPost slot
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
    (rootFork : CoveredFork sevm.benvStat.fork)
    {frame : Exec.Frame}
    (retained : frame ∈ Exec.committedFrames run)
    (invocation : Blanc.Weth10.Exec.Frame.exactInvocation dp ca frame)
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (occurrence : Blanc.Weth10.Exec.Frame.BalanceSstoreOccurrence dp ca frame stepPre stepPost slot
      key value holder) :
    ∃ action : FlowAction,
      Blanc.Weth10.Exec.Frame.BalanceSstoreClassification dp ca frame stepPre stepPost slot
        key value holder action :=
  Exec.weth10BalanceSstoreClassification_of_mem_committedFrames run installed rootPc rootMemory
    rootFork retained invocation occurrence

/-! C3-C6 public theorem pins.  The committed interpreter cores are concrete;
the frozen equations carry only the stable checkpoint and authentic retained
history premises. -/

example (dp : DeployParams) (ca : Adr) :
    CommittedExecStorageSound dp ca :=
  committedExecStorageSound dp ca

example (dp : DeployParams) (ca : Adr) :
    CommittedExecEthSound dp ca :=
  committedExecEthSound dp ca

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
      (history.weth10Flow u).flashRepayment :=
  history.flash_pair_totals_eq

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future) :
    FlowActionsCreditNof history.flowActions :=
  history.noCommittedCreditWrap hstable

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future) :
    holderCreditLossOfActions history.flowActions u = 0 :=
  history.holderCreditLoss_eq_zero hstable

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future) :
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

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future) :
    (history.weth10Flow u).flashCredit =
        (history.weth10Flow u).flashRepayment ∧
    bookedBalanceNat checkpoint.state ca u +
        (history.weth10Flow u).ordinaryIn =
      bookedBalanceNat future.state ca u +
        (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut :=
  holderFlow_flash_cancelled hstable history

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u +
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) :=
  holderFlow_residual_floor hstable history

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future) :
    bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) ≤
      bookedBalanceNat future.state ca u :=
  holderFlow_truncated_floor hstable history

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future)
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
    Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = none :=
  Blanc.Weth10.Exec.Frame.flowAction_eq_none_of_currentTarget_ne htarget

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcodeAddress : frame.sevm.codeAddress ≠ some ca) :
    Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = none :=
  Blanc.Weth10.Exec.Frame.flowAction_eq_none_of_codeAddress_ne hcodeAddress

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hcode : some frame.sevm.code.toList ≠ Prog.compile (weth10 dp)) :
    Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = none :=
  Blanc.Weth10.Exec.Frame.flowAction_eq_none_of_code_ne hcode

example {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (hpc : frame.pc ≠ 0) :
    Blanc.Weth10.Exec.Frame.flowAction? dp ca frame = none :=
  Blanc.Weth10.Exec.Frame.flowAction_eq_none_of_pc_ne hpc

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

/-! ## `weth10-redeem-future-v2`

The attribution definitions below are pinned twice over. A type pin alone
would not notice a *strengthening* of `NoAllowanceKeyCollision` or
`AllowanceQuiescent` — replacing either with `False` or `True` respectively
leaves its type untouched while making `hardenedDescription`,
`deploymentRoot_allowanceQuiescent` and the full-window corollary vacuous —
so each carries a definitional `Iff.rfl` pin as well. Decidability of the two
history-local predicates is frozen surface (they are properties of an explicit
history's finitely many entries, never global assumptions) and is pinned by
`inferInstance`.

The mirror image of that risk is a *weakening of a conclusion term*, and it
hollows out the identical set of claims. `hardenedOutflow` redefined as the
plain ledger outflow leaves every pinned type intact while
`hardenedOutflow_le_permanentOutflow` degenerates into `n ≤ n`,
`permanentOutflow_eq_hardenedOutflow_of_noCollision` and the flagship's
`hardenedDescription` field become content-free with `hnc` unused, and
`holderFlow_hardened_floor` restates the residual floor it was meant to
strengthen. No axiom moves under that rewrite, because the vacuous route
carries the same axioms. The computation is therefore pinned as well as the
type: the chronological fold, the per-frame contribution it sums, and the
per-debit witness that contribution tests. `touchedAllowancePairs` is pinned
the same way for the same reason in the opposite direction — it is the last
unpinned term inside `NoAllowanceKeyCollision`, and *adding* pairs to it
strengthens the hypothesis until every claim carrying it is vacuous.

`projectedAllowanceKey` is the term both pinned hypothesis predicates are
stated through, so its derivation and the two identities that make it the key
the compiled runtime computes are pinned first. Were those to drift together
the predicates would go on type-checking while describing a slot the runtime
never visits. -/

example (owner spender : B256) :
    projectedAllowanceKey owner spender =
      allowanceTagWord |||
        (allowancePayloadMask &&&
          Bytes.keccak (owner.toBytes ++ spender.toBytes)) :=
  rfl

example (e : Sevm) :
    callerAllowanceRuntimeKey e =
      projectedAllowanceKey (Sevm.argWord e 0) e.caller.toB256 :=
  callerAllowanceRuntimeKey_eq_projected e

example (e : Sevm) :
    flashAllowanceRuntimeKey e =
      projectedAllowanceKey (normalizedAddressArg e 0)
        e.currentTarget.toB256 :=
  flashAllowanceRuntimeKey_eq_projected e

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    List (B256 × B256) :=
  touchedAllowancePairs history

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    touchedAllowancePairs history =
      history.attributionLedger.filterMap fun frame =>
        frame.allowance.map fun event => (event.owner, event.spender) :=
  rfl

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) : Prop :=
  NoAllowanceKeyCollision history

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    NoAllowanceKeyCollision history ↔
      (touchedAllowancePairs history).Pairwise fun p q =>
        p ≠ q →
          projectedAllowanceKey p.1 p.2 ≠ projectedAllowanceKey q.1 q.2 :=
  Iff.rfl

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    Decidable (NoAllowanceKeyCollision history) :=
  inferInstance

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) (u : Adr) :
    Nat :=
  hardenedOutflow history u

/-! The hardened outflow's computation, not merely its type: the chronological
fold over the attribution ledger, the per-frame contribution the fold sums, and
the per-debit witness that contribution tests. The fold itself is private to
its own module, so it is named here through `open private`; a pin that stops
resolving because the fold was renamed or exposed fails closed, exactly as a
rewritten body does. -/

open private hardenedOutflowGo from Blanc.Weth10Attribution in
example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) (u : Adr) :
    hardenedOutflow history u =
      hardenedOutflowGo u [] history.attributionLedger :=
  rfl

example (frame : CountedFrame) (recent : List CountedFrame) (u : Adr) :
    frame.hardenedContribution recent u =
      match frame.action with
      | some action =>
          match action.debit with
          | some debit =>
              if debit.hardenedFor recent u then frame.permanentOutflow u else 0
          | none => 0
      | none => 0 :=
  rfl

example (debit : DebitProvenance) (recent : List CountedFrame) (u : Adr) :
    debit.hardenedFor recent u =
      match debit.branch with
      | .direct => debit.actualCaller = u
      | .delegated .selfBypass => debit.actualCaller = u
      | .delegated (.finite key _ _) =>
          (attributionRootAt recent key).attributedTo u
      | .delegated (.maximum key) =>
          (attributionRootAt recent key).attributedTo u
      | .flash .selfBypass => false
      | .flash (.finite key _ _) =>
          (attributionRootAt recent key).attributedTo u
      | .flash (.maximum key) =>
          (attributionRootAt recent key).attributedTo u :=
  rfl

example : Adr → Adr → State → Prop :=
  AllowanceQuiescent

example (ca u : Adr) (w : State) :
    AllowanceQuiescent ca u w ↔
      ∀ owner spender : B256, owner.toAdr = u →
        (w.getStor ca).get (projectedAllowanceKey owner spender) = 0 :=
  Iff.rfl

example (frame : CountedFrame) (u : Adr) :
    frame.authorizes u =
      ((match frame.action with
        | some action =>
            match action.debit with
            | some debit => debit.actualCaller = u
            | none => false
        | none => false) ||
      match frame.allowance with
      | some event =>
          match event.visit with
          | .approveStore _ => event.caller = u
          | .permitStore _ => event.owner.toAdr = u
          | _ => false
      | none => false) :=
  rfl

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} (u : Adr)
    (history : AccountedHistory cfg dp ca checkpoint future) : Prop :=
  NoAuthorizingActBy u history

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} (u : Adr)
    (history : AccountedHistory cfg dp ca checkpoint future) :
    NoAuthorizingActBy u history ↔
      ∀ frame ∈ history.attributionLedger, frame.authorizes u = false :=
  Iff.rfl

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain} (u : Adr)
    (history : AccountedHistory cfg dp ca checkpoint future) :
    Decidable (NoAuthorizingActBy u history) :=
  inferInstance

/-! The allowance-dispatch transport endpoints the attribution layer runs on:
the compiled program's committed allowance obligation, and the history-level
statement that every tagged allowance key holds exactly the ledger's last
committed write. -/

example (dp : DeployParams) (ca : Adr) :
    CommittedExecAllowanceSound dp ca :=
  committedExecAllowanceSound dp ca

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransported ca checkpoint.state future.state
      history.attributionLedger :=
  history.allowanceTransported_of_compiled hstable

/-! ## The read-sound strengthening

The two pins above are deliberately left exactly as they were. The transport
they state was *not* strengthened in place; instead a `Sound` sibling was
proved beside each, adding entry-read soundness of the same ledger against the
same entry storage. The carriers are pinned by definitional unfolding, so the
added conjunct cannot quietly become vacuous, and the downgrade witnesses at
the end of this section recover both original endpoints from their siblings —
the strengthening therefore cannot have been bought by weakening the published
statements. -/

example : Stor → List CountedFrame → Prop :=
  AllowanceEntryReadSound

example (pre : Stor) (ledger : List CountedFrame) :
    AllowanceEntryReadSound pre ledger ↔
      ∀ earlier record later, ledger = earlier ++ record :: later →
        ∀ event, record.allowance = some event →
          ∀ v, event.visit.read? = some v →
            v = applyAllowanceLedger pre earlier event.key :=
  Iff.rfl

example : Adr → State → State → List CountedFrame → Prop :=
  AllowanceTransportedSound

example (ca : Adr) (pre post : State) (ledger : List CountedFrame) :
    AllowanceTransportedSound ca pre post ledger ↔
      (AllowanceTransported ca pre post ledger ∧
        AllowanceEntryReadSound (pre.getStor ca) ledger) :=
  Iff.rfl

example : DeployParams → Adr → Prop :=
  CommittedExecAllowanceReadSound

example (dp : DeployParams) (ca : Adr) :
    CommittedExecAllowanceReadSound dp ca ↔
      ∀ {msg : Msg} {benv : Benv} {pc : Nat} {sevm : Sevm}
        {pre : Devm} {out : Execution}
        (run : Exec pc sevm pre out)
        (_htransfer : msg.benvAfterTransfer = .ok benv)
        (_hinit : (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv benv))
        (hcommit : Execution.commits out = true),
        MessageRunReady dp ca msg →
        CoveredFork msg.benv.stat.fork →
        AllowanceTransportedSound ca msg.benv.state
          (Execution.committedPost out hcommit).state
          (Exec.attributionStream dp ca run) :=
  Iff.rfl

/-! The flash-loan record carries no exemption from the entry-read clause. It
is the one record whose read is reconstructed from the committed post state
rather than observed at frame entry, and the pin below is what makes that
honest: the record is measured at the **post-callback settlement entry**,
which is where the runtime performed the read, and `Exec.frameContribution`
places the record after its subtree precisely so that the prefix the clause
measures it against replays to that state. Weakening this back to an
exemption is a semantic change, so it is pinned in full. -/

example {dp : DeployParams} {ca : Adr} {e : Sevm}
    {pre settlePre burnPre post : Devm}
    (htarget : e.currentTarget = ca)
    (hne0 : e.data.length.toB256 ≠ 0)
    (hsel : Sevm.selector e = flashLoanSelector)
    (houtcome : FlashAllowanceOutcome e settlePre burnPre)
    (hburn : Func.Run ((weth10 dp).main :: weth10Aux) e burnPre
      flashBurn post)
    {record : CountedFrame}
    (hrecord : record.allowance = frameAllowanceEvent e pre post) :
    AllowanceEntryReadSound (Devm.getStor settlePre ca) [record] :=
  flashSettlement_allowanceEntryRead htarget hne0 hsel houtcome hburn hrecord

/-! The read-sound endpoints themselves: the compiled program's read-sound
committed obligation, and the history-level read-sound transport that the
dormant-holder theorem consumes. -/

example (dp : DeployParams) (ca : Adr) :
    CommittedExecAllowanceReadSound dp ca :=
  committedExecAllowanceReadSound dp ca

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransportedSound ca checkpoint.state future.state
      history.attributionLedger :=
  history.allowanceTransportedSound_of_compiled hstable

/-! The downgrade witnesses. Each pinned original is recovered from its `Sound`
sibling by the generic downgrade, so the sibling asserts everything the pinned
statement asserts. -/

example (dp : DeployParams) (ca : Adr) :
    CommittedExecAllowanceSound dp ca :=
  CommittedExecAllowanceReadSound.committedExecAllowanceSound
    (committedExecAllowanceReadSound dp ca)

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hstable : Stable dp ca checkpoint.state) :
    AllowanceTransported ca checkpoint.state future.state
      history.attributionLedger :=
  (history.allowanceTransportedSound_of_compiled hstable).toAllowanceTransported

/-! The hardened outflow is a sub-sum of the permanent outflow unconditionally,
and equals it under trace-local collision-freedom. The collision hypothesis
appears on the equality and nowhere else. -/

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (history : AccountedHistory cfg dp ca checkpoint future) :
    hardenedOutflow history u ≤
      (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut :=
  hardenedOutflow_le_permanentOutflow history

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history) :
    (history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut =
      hardenedOutflow history u :=
  permanentOutflow_eq_hardenedOutflow_of_noCollision hstable history hnc

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u + hardenedOutflow history u :=
  holderFlow_hardened_floor hstable history hnc

/-! The dormant-holder theorem, the family's most human-legible claim: a holder
who performed no authorizing act and held no allowance at the checkpoint cannot
have lost a wei. Its five hypotheses are the whole content of "did nothing" —
`hquiet` is the checkpoint-side allowance quiescence and `hdormant` the
ledger-side absence of any authorizing act by `u`, and the conclusion is a bare
inequality on booked balances with no outflow term at all. Adding a hypothesis,
or weakening the conclusion to mention an outflow, breaks this pin. -/

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    (hstable : Weth10.Stable dp ca checkpoint.state)
    (history : AccountedHistory cfg dp ca checkpoint future)
    (hnc : NoAllowanceKeyCollision history)
    (hquiet : AllowanceQuiescent ca u checkpoint.state)
    (hdormant : NoAuthorizingActBy u history) :
    bookedBalanceNat checkpoint.state ca u ≤
      bookedBalanceNat future.state ca u :=
  dormant_holder_balance_monotone hstable history hnc hquiet hdormant

/-! The two enabledness capstones state their residual bound at the checkpoint
and discharge redemption at the future snapshot. Neither takes a collision
hypothesis; a holder's ability to redeem never rests on an assumption about
hash keys. -/

example {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future} {msg : Msg}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  deployment_reachable_residual_messageRedemption_enabled hroot hcov hcheckpoint hq henv

example {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleRedemptionTx
      rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_residual_transactionRedemption_enabled hroot hcov hcheckpoint hq hentry henv

example {cfg : ChainConfig} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future} {msg : Msg}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleSelfRedemptionMessage rules dp ca u q future.state msg) :
    MessageRedemptionEnabled dp ca u u q future.state msg :=
  deployment_reachable_residual_selfMessageRedemption_enabled hroot hcov hcheckpoint hq henv

example {cfg : ChainConfig} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index :=
  deployment_reachable_residual_selfTransactionRedemption_enabled hroot hcov hcheckpoint hq hentry
    henv

/-! The rebased pair states its bound against the *full booked balance at the
future snapshot itself*: rebasing the window at the future collapses the
outflow terms, so no residual subtraction appears in either statement. -/

example {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain} {msg : Msg}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionMessage rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  deployment_reachable_booked_messageRedemption_enabled hroot hcov hfuture hq henv

example {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionTx rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_booked_transactionRedemption_enabled hroot hcov hfuture hentry hq henv

example {cfg : ChainConfig} {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index :=
  deployment_reachable_booked_selfTransactionRedemption_enabled hroot hcov hfuture hentry hq henv

example {cfg : ChainConfig} {rules : ForkRules}
    {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {maxPriorityFee maxFee : Nat}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : NonSignatureRedemptionTxEnvelope
      rules dp ca u recipient q benv bout tx index maxPriorityFee maxFee)
    (hrecovered : recoverSender benv.stat.chainId tx = .ok u) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender hroot hcov hfuture
    hentry hq henv hrecovered

/-! The flagship record, pinned field by field. This is the pin that protects
the goal's central invariant: `hardenedDescription` carries
`NoAllowanceKeyCollision` as its OWN hypothesis, while `messageEnabled` and
`transactionEnabled` carry no collision hypothesis at all. Field assignment is
checked up to definitional equality, so moving the collision hypothesis onto
an enabledness field — or off `hardenedDescription` — breaks this example. -/

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future}
    (futureStable : Weth10.Stable dp ca future.state)
    (reachable : BlockChain.ReachUsing cfg checkpoint future)
    (conserved :
      bookedBalanceNat checkpoint.state ca u +
          (history.weth10Flow u).ordinaryIn =
        bookedBalanceNat future.state ca u +
          (history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut)
    (residualFloor :
      bookedBalanceNat checkpoint.state ca u ≤
        bookedBalanceNat future.state ca u +
          (history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut)
    (hardenedDescription :
      NoAllowanceKeyCollision history →
        (history.weth10Flow u).redeemed +
            (history.weth10Flow u).externalTransferredOut =
          hardenedOutflow history u)
    (messageEnabled : ∀ (rules : ForkRules) (q : Nat) (recipient : Adr) (msg : Msg),
      q ≤ bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) →
      AdmissibleRedemptionMessage rules dp ca u recipient q future.state msg →
      MessageRedemptionEnabled dp ca u recipient q future.state msg)
    (transactionEnabled : ∀ (rules : ForkRules) (q : Nat) (recipient : Adr)
        (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat),
      benv.state = future.state →
      q ≤ bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) →
      AdmissibleRedemptionTx rules dp ca u recipient q benv bout tx index →
      TransactionRedemptionEnabled dp ca u recipient q benv bout tx index) :
    FutureRedemptionGuarantee cfg dp ca u checkpoint future history :=
  { futureStable := futureStable
    reachable := reachable
    conserved := conserved
    residualFloor := residualFloor
    hardenedDescription := hardenedDescription
    messageEnabled := messageEnabled
    transactionEnabled := transactionEnabled }

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {checkpoint future : BlockChain}
    {history : AccountedHistory cfg dp ca checkpoint future}
    (base : FutureRedemptionGuarantee
      cfg dp ca u checkpoint future history)
    (selfMessageEnabled : ∀ (rules : ForkRules) (q : Nat) (msg : Msg),
      q ≤ bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) →
      AdmissibleSelfRedemptionMessage rules dp ca u q future.state msg →
      MessageRedemptionEnabled dp ca u u q future.state msg)
    (selfTransactionEnabled : ∀ (rules : ForkRules) (q : Nat) (benv : Benv)
        (bout : BlockOutput) (tx : Tx) (index : Nat),
      benv.state = future.state →
      q ≤ bookedBalanceNat checkpoint.state ca u -
        ((history.weth10Flow u).redeemed +
          (history.weth10Flow u).externalTransferredOut) →
      AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index →
      TransactionRedemptionEnabled dp ca u u q benv bout tx index) :
    FutureDualSelectorRedemptionGuarantee
      cfg dp ca u checkpoint future history :=
  { toFutureRedemptionGuarantee := base
    selfMessageEnabled := selfMessageEnabled
    selfTransactionEnabled := selfTransactionEnabled }

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hfuture : BlockChain.ReachUsing cfg checkpoint future) :
    ∃ history, FutureRedemptionGuarantee
      cfg dp ca u checkpoint future history :=
  deployment_reachable_future_redeemable hroot hcov hcheckpoint hfuture

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hfuture : BlockChain.ReachUsing cfg checkpoint future) :
    ∃ history, FutureDualSelectorRedemptionGuarantee
      cfg dp ca u checkpoint future history :=
  deployment_reachable_future_dualSelector_redeemable hroot hcov hcheckpoint hfuture

example {cfg : ChainConfig} {dp : DeployParams} {ca : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hcheckpoint : BlockChain.ReachUsing cfg deployed checkpoint)
    (hfuture : BlockChain.ReachUsing cfg checkpoint future) :
    ∃ history, ∀ u : Adr, FutureRedemptionGuarantee
      cfg dp ca u checkpoint future history :=
  deployment_reachable_future_redeemable_allHolders hroot hcov hcheckpoint hfuture

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca) :
    AllowanceQuiescent ca u deployed.state :=
  deploymentRoot_allowanceQuiescent hroot

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hfuture : BlockChain.ReachUsing cfg deployed future) :
    AllowanceQuiescent ca u deployed.state ∧
      ∃ history, FutureRedemptionGuarantee
        cfg dp ca u deployed future history :=
  deployment_fullWindow_future_redeemable hroot hcov hfuture

example : CountedFrame → List CountedFrame → Adr → Prop :=
  PermanentOutflowAuthorization

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (history : AccountedHistory cfg dp ca deployed future)
    {earlier later : List CountedFrame} {record : CountedFrame}
    {action : FlowAction} {debit : DebitProvenance}
    {event : AllowanceEvent}
    (hsplit : history.attributionLedger = earlier ++ record :: later)
    (hout : record.permanentOutflow u ≠ 0)
    (haction : record.action = some action)
    (hdebit : action.debit = some debit)
    (hevent : record.allowance = some event)
    (hkey : delegatedKey? debit.branch = some event.key) :
    attributionRootAt earlier.reverse event.key ≠ .checkpoint :=
  deployment_fullWindow_attributionRootAt_ne_checkpoint
    hroot history hsplit hout haction hdebit hevent hkey

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (history : AccountedHistory cfg dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history)
    {earlier later : List CountedFrame} {record : CountedFrame}
    (hsplit : history.attributionLedger = earlier ++ record :: later)
    (hout : record.permanentOutflow u ≠ 0) :
    PermanentOutflowAuthorization record earlier.reverse u :=
  deployment_fullWindow_permanentOutflowAuthorization
    hroot history hnc hsplit hout

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (history : AccountedHistory cfg dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history) :
    ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut =
      hardenedOutflow history u) ∧
      ∀ earlier record later,
        history.attributionLedger = earlier ++ record :: later →
        record.permanentOutflow u ≠ 0 →
        PermanentOutflowAuthorization record earlier.reverse u :=
  deployment_fullWindow_hardenedOutflow_only_authorizingRoots
    hroot history hnc

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (history : AccountedHistory cfg dp ca deployed future)
    (hnc : NoAllowanceKeyCollision history)
    (hdormant : NoAuthorizingActBy u history) :
    bookedBalanceNat deployed.state ca u ≤
      bookedBalanceNat future.state ca u :=
  deployment_fullWindow_dormant_holder_balance_monotone
    hroot history hnc hdormant

example {cfg : ChainConfig} {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hfuture : BlockChain.ReachUsing cfg deployed future) :
    ∃ history : AccountedHistory cfg dp ca deployed future,
      NoAllowanceKeyCollision history →
      NoAuthorizingActBy u history →
      bookedBalanceNat deployed.state ca u ≤
        bookedBalanceNat future.state ca u :=
  deployment_reachable_dormant_holder_balance_monotone hroot hcov hfuture

/-! The any-order records are constructor-pinned for the same reason. A
`budget` field weakened from the per-owner **aggregate** to a per-claim bound
would silently permit overbooking by splitting one owner's claim in two, and a
`remaining` field weakened to anything less than "every extension admissible
before is admissible after" would gut the any-order induction. -/

example {rules : ForkRules} {ca : Adr} {w : State} {cs : List RedemptionClaim}
    (recipients : ∀ c ∈ cs, ClaimAdmissible rules ca w c)
    (budget : ∀ u : Adr, ownerClaimTotal cs u ≤ bookedBalanceNat w ca u) :
    ClaimsAdmissible rules ca w cs :=
  { recipients := recipients
    budget := budget }

example {rules : ForkRules} {dp : DeployParams} {ca : Adr}
    {c : RedemptionClaim} {cs : List RedemptionClaim}
    {w mid post : State} {msg : Msg} {out : MsgCallOutput}
    (henv : AdmissibleRedemptionMessage
      rules dp ca c.owner c.recipient c.amount w msg)
    (message_eq : msg = canonicalRedemptionMessage rules ca c w)
    (hrun : processMessageCall msg = .ok (mid, out))
    (heffect : MessageRedemptionExactEffect
      dp ca c.owner c.recipient c.amount w mid out)
    (htail : RedemptionRun rules dp ca cs mid post) :
    RedemptionRun rules dp ca (c :: cs) w post :=
  .cons henv message_eq hrun heffect htail

example (ca : Adr) (w : State) (holders : List Adr)
    (recipient : Adr → Adr) :
    fullBalanceClaims ca w holders recipient =
      holders.map fun u =>
        ⟨u, bookedBalanceNat w ca u, recipient u⟩ :=
  rfl

example {rules : ForkRules} {dp : DeployParams} {ca : Adr}
    {cs : List RedemptionClaim}
    {w post : State}
    (run : RedemptionRun rules dp ca cs w post)
    (stable : Stable dp ca post)
    (booked : ∀ v : Adr,
      bookedBalanceNat post ca v + ownerClaimTotal cs v =
        bookedBalanceNat w ca v)
    (contractEth : (post.bal ca).toNat + claimTotal cs = (w.bal ca).toNat)
    (otherEth : ∀ a : Adr, a ≠ ca →
      (post.bal a).toNat = (w.bal a).toNat + recipientClaimTotal cs a)
    (sumPreserved : sum post.bal = sum w.bal)
    (codePreserved : ∀ a : Adr, post.getCode a = w.getCode a)
    (remaining : ∀ es : List RedemptionClaim,
      ClaimsAdmissible rules ca w (cs ++ es) →
        ClaimsAdmissible rules ca post es) :
    RedemptionOutcome rules dp ca cs w post :=
  { run := run
    stable := stable
    booked := booked
    contractEth := contractEth
    otherEth := otherEth
    sumPreserved := sumPreserved
    codePreserved := codePreserved
    remaining := remaining }

example {rules : ForkRules} {dp : DeployParams} {ca : Adr} {w : State}
    {cs ds : List RedemptionClaim}
    (hca : ¬ rules.isPrecomp ca)
    (hsel : ∃ f, CoveredFork f ∧ Fork.ruleSet f = rules)
    (hstable : Stable dp ca w)
    (hadm : ClaimsAdmissible rules ca w cs)
    (hperm : cs.Perm ds) :
    ∃ post, RedemptionOutcome rules dp ca ds w post :=
  redeemClaims_anyOrder hca hsel hstable hadm hperm

example {rules : ForkRules} {dp : DeployParams} {ca : Adr} {w : State}
    {holders : List Adr} {recipient : Adr → Adr}
    {claims : List RedemptionClaim}
    (hca : ¬ rules.isPrecomp ca)
    (hsel : ∃ f, CoveredFork f ∧ Fork.ruleSet f = rules)
    (hstable : Stable dp ca w)
    (hnodup : holders.Nodup)
    (hrecipients : ∀ u ∈ holders,
      ClaimAdmissible rules ca w
        ⟨u, bookedBalanceNat w ca u, recipient u⟩)
    (hperm : (fullBalanceClaims ca w holders recipient).Perm claims) :
    ∃ post, RedemptionOutcome rules dp ca claims w post :=
  redeemEveryoneList_anyOrder hca hsel hstable hnodup hrecipients hperm

example {cfg : ChainConfig} {rules : ForkRules} {timestamp : Nat}
    {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {cs ds : List RedemptionClaim}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hrules : cfg.rulesAt timestamp = .ok rules)
    (hadm : ClaimsAdmissible rules ca future.state cs)
    (hperm : cs.Perm ds) :
    ∃ post, RedemptionOutcome rules dp ca ds future.state post :=
  deployment_reachable_redeemClaims_anyOrder hroot hfuture hcov hrules hadm hperm

example {cfg : ChainConfig} {rules : ForkRules} {timestamp : Nat}
    {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {holders : List Adr}
    {recipient : Adr → Adr} {claims : List RedemptionClaim}
    (hroot : Weth10.DeploymentRoot cfg base deployed dp ca)
    (hfuture : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ t f, cfg.forkAt t = .ok f → CoveredFork f)
    (hrules : cfg.rulesAt timestamp = .ok rules)
    (hnodup : holders.Nodup)
    (hrecipients : ∀ u ∈ holders,
      ClaimAdmissible rules ca future.state
        ⟨u, bookedBalanceNat future.state ca u, recipient u⟩)
    (hperm :
      (fullBalanceClaims ca future.state holders recipient).Perm claims) :
    ∃ post, RedemptionOutcome rules dp ca claims future.state post :=
  deployment_reachable_redeemEveryoneList_anyOrder hroot hfuture hcov hrules hnodup hrecipients
    hperm


/-! ## Current-mainnet and Prague specialization pins -/

example
    {timestamp : Nat} {rules : ForkRules}
    (h : mainnetChainConfig.rulesAt timestamp = .ok rules) :
    rules = pragueRules ∨ rules = osakaRules ∨
      rules = bpo1Rules ∨ rules = bpo2Rules :=
  by
    exact mainnet_rulesAt_eq_named
      (timestamp := timestamp) (rules := rules) (h := h)

example
    {timestamp : Nat} (h : mainnetBpo2Timestamp ≤ timestamp) :
    mainnetChainConfig.rulesAt timestamp = .ok bpo2Rules :=
  by
    exact mainnet_rulesAt_eq_bpo2_of_ge
      (timestamp := timestamp) (h := h)

example (q : Nat) :
    checkTransactionGasCap pragueRules.tx (redemptionRuntimeCeiling q) =
      .ok () :=
  by
    exact pragueRules_redemptionRuntimeCeiling_gasCap
      (q := q)

example (q : Nat) :
    checkTransactionGasCap osakaRules.tx (redemptionRuntimeCeiling q) =
      .ok () :=
  by
    exact osakaRules_redemptionRuntimeCeiling_gasCap
      (q := q)

example (q : Nat) :
    checkTransactionGasCap bpo1Rules.tx (redemptionRuntimeCeiling q) =
      .ok () :=
  by
    exact bpo1Rules_redemptionRuntimeCeiling_gasCap
      (q := q)

example (q : Nat) :
    checkTransactionGasCap bpo2Rules.tx (redemptionRuntimeCeiling q) =
      .ok () :=
  by
    exact bpo2Rules_redemptionRuntimeCeiling_gasCap
      (q := q)

example {timestamp gas : Nat} {rules : ForkRules}
    (hrules : mainnetChainConfig.rulesAt timestamp = .ok rules)
    (hgas : gas ≤ 2 ^ 24) :
    checkTransactionGasCap rules.tx gas = .ok () :=
  by
    exact mainnet_checkTransactionGasCap_of_le
      (hrules := hrules) (hgas := hgas)

example :
    mainnetChainConfig.rulesAt 1_767_747_683 = .ok bpo2Rules :=
  by
    exact weth10CurrentMainnetCreation_rulesAt

example
    (base deployed : BlockChain) (cb : CanonicalBlock)
    (deploymentTxBytes : Bytes) (deploymentTx : Tx) (sender ca : Adr)
    (htimestamp : mainnetBpo2Timestamp ≤ cb.block.header.timestamp)
    (hbase : CanonicalDeploymentBase mainnetChainConfig .bpo2
      base sender ca)
    (henv : CanonicalWeth10DeploymentBlock mainnetChainConfig .bpo2
      base cb deploymentTxBytes deploymentTx sender ca)
    (hstep : stateTransitionUsing mainnetChainConfig
      base cb.block = .ok deployed) :
    MainnetDeploymentRoot base deployed
      (freshDeployParams mainnetChainConfig.chainId.toB256 ca) ca :=
  by
    exact canonicalMainnetBpo2DeploymentStep_establishes_root
      (base := base) (deployed := deployed) (cb := cb) (deploymentTxBytes := deploymentTxBytes) (deploymentTx := deploymentTx) (sender := sender) (ca := ca) (htimestamp := htimestamp) (hbase := hbase) (henv := henv) (hstep := hstep)

example
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (hreach : BlockChain.ReachUsing mainnetChainConfig ch ch')
    (hstable : Stable dp ca ch.state) :
    Stable dp ca ch'.state :=
  by
    exact chainUsing_preserves_stable_mainnet
      (dp := dp) (ca := ca) (ch := ch) (ch' := ch') (hreach := hreach) (hstable := hstable)

example
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (hreach : BlockChain.ReachUsing mainnetChainConfig ch ch')
    (hstable : Stable dp ca ch.state) :
    (ch'.state.getStor ca).get flashMintedSlot = 0 ∧
      balSum (ch'.state.getStor ca) ≤ (ch'.state.bal ca).toNat :=
  by
    exact chain_reachable_backed_and_flash_zero_mainnet
      (dp := dp) (ca := ca) (ch := ch) (ch' := ch') (hreach := hreach) (hstable := hstable)

example
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory mainnetChainConfig dp ca checkpoint future}
    {msg : Msg}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  by
    exact deployment_reachable_residual_messageRedemption_enabled_mainnet
      (rules := rules) (dp := dp) (ca := ca) (u := u) (recipient := recipient) (q := q) (base := base) (deployed := deployed) (checkpoint := checkpoint) (future := future) (history := history) (msg := msg) (hroot := hroot) (hcheckpoint := hcheckpoint) (hq := hq) (henv := henv)

example
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory mainnetChainConfig dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleRedemptionTx
      rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  by
    exact deployment_reachable_residual_transactionRedemption_enabled_mainnet
      (rules := rules) (dp := dp) (ca := ca) (u := u) (recipient := recipient) (q := q) (base := base) (deployed := deployed) (checkpoint := checkpoint) (future := future) (history := history) (benv := benv) (bout := bout) (tx := tx) (index := index) (hroot := hroot) (hcheckpoint := hcheckpoint) (hq := hq) (hentry := hentry) (henv := henv)

example
    {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory mainnetChainConfig dp ca checkpoint future}
    {msg : Msg}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (henv : AdmissibleSelfRedemptionMessage rules dp ca u q future.state msg) :
    MessageRedemptionEnabled dp ca u u q future.state msg :=
  by
    exact deployment_reachable_residual_selfMessageRedemption_enabled_mainnet
      (rules := rules) (dp := dp) (ca := ca) (u := u) (q := q) (base := base) (deployed := deployed) (checkpoint := checkpoint) (future := future) (history := history) (msg := msg) (hroot := hroot) (hcheckpoint := hcheckpoint) (hq := hq) (henv := henv)

example
    {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed checkpoint future : BlockChain}
    {history : AccountedHistory mainnetChainConfig dp ca checkpoint future}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hq : q ≤ bookedBalanceNat checkpoint.state ca u -
      ((history.weth10Flow u).redeemed +
        (history.weth10Flow u).externalTransferredOut))
    (hentry : benv.state = future.state)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index :=
  by
    exact deployment_reachable_residual_selfTransactionRedemption_enabled_mainnet
      (rules := rules) (dp := dp) (ca := ca) (u := u) (q := q) (base := base) (deployed := deployed) (checkpoint := checkpoint) (future := future) (history := history) (benv := benv) (bout := bout) (tx := tx) (index := index) (hroot := hroot) (hcheckpoint := hcheckpoint) (hq := hq) (hentry := hentry) (henv := henv)

example
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain} {msg : Msg}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionMessage
      rules dp ca u recipient q future.state msg) :
    MessageRedemptionEnabled dp ca u recipient q future.state msg :=
  by
    exact deployment_reachable_booked_messageRedemption_enabled_mainnet
      (rules := rules) (dp := dp) (ca := ca) (u := u) (recipient := recipient) (q := q) (base := base) (deployed := deployed) (future := future) (msg := msg) (hroot := hroot) (hfuture := hfuture) (hq := hq) (henv := henv)

example
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleRedemptionTx
      rules dp ca u recipient q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  by
    exact deployment_reachable_booked_transactionRedemption_enabled_mainnet
      (rules := rules) (dp := dp) (ca := ca) (u := u) (recipient := recipient) (q := q) (base := base) (deployed := deployed) (future := future) (benv := benv) (bout := bout) (tx := tx) (index := index) (hroot := hroot) (hfuture := hfuture) (hentry := hentry) (hq := hq) (henv := henv)

example
    {rules : ForkRules} {dp : DeployParams} {ca u : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : AdmissibleSelfRedemptionTx rules dp ca u q benv bout tx index) :
    TransactionRedemptionEnabled dp ca u u q benv bout tx index :=
  by
    exact deployment_reachable_booked_selfTransactionRedemption_enabled_mainnet
      (rules := rules) (dp := dp) (ca := ca) (u := u) (q := q) (base := base) (deployed := deployed) (future := future) (benv := benv) (bout := bout) (tx := tx) (index := index) (hroot := hroot) (hfuture := hfuture) (hentry := hentry) (hq := hq) (henv := henv)

example
    {rules : ForkRules} {dp : DeployParams} {ca u recipient : Adr}
    {q : Nat} {base deployed future : BlockChain}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {maxPriorityFee maxFee : Nat}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hentry : benv.state = future.state)
    (hq : q ≤ bookedBalanceNat future.state ca u)
    (henv : NonSignatureRedemptionTxEnvelope
      rules dp ca u recipient q benv bout tx index maxPriorityFee maxFee)
    (hrecovered : recoverSender benv.stat.chainId tx = .ok u) :
    TransactionRedemptionEnabled dp ca u recipient q benv bout tx index :=
  by
    exact deployment_reachable_booked_transactionRedemption_enabled_of_recoveredSender_mainnet
      (rules := rules) (dp := dp) (ca := ca) (u := u) (recipient := recipient) (q := q) (base := base) (deployed := deployed) (future := future) (benv := benv) (bout := bout) (tx := tx) (index := index) (maxPriorityFee := maxPriorityFee) (maxFee := maxFee) (hroot := hroot) (hfuture := hfuture) (hentry := hentry) (hq := hq) (henv := henv) (hrecovered := hrecovered)

example
    {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, FutureRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  by
    exact deployment_reachable_future_redeemable_mainnet
      (dp := dp) (ca := ca) (u := u) (base := base) (deployed := deployed) (checkpoint := checkpoint) (future := future) (hroot := hroot) (hcheckpoint := hcheckpoint) (hfuture := hfuture)

example
    {dp : DeployParams} {ca u : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, FutureDualSelectorRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  by
    exact deployment_reachable_future_dualSelector_redeemable_mainnet
      (dp := dp) (ca := ca) (u := u) (base := base) (deployed := deployed) (checkpoint := checkpoint) (future := future) (hroot := hroot) (hcheckpoint := hcheckpoint) (hfuture := hfuture)

example
    {dp : DeployParams} {ca : Adr}
    {base deployed checkpoint future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hcheckpoint : BlockChain.ReachUsing mainnetChainConfig deployed checkpoint)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig checkpoint future) :
    ∃ history, ∀ u : Adr, FutureRedemptionGuarantee
      mainnetChainConfig dp ca u checkpoint future history :=
  by
    exact deployment_reachable_future_redeemable_allHolders_mainnet
      (dp := dp) (ca := ca) (base := base) (deployed := deployed) (checkpoint := checkpoint) (future := future) (hroot := hroot) (hcheckpoint := hcheckpoint) (hfuture := hfuture)

example
    {dp : DeployParams} {ca u : Adr}
    {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    AllowanceQuiescent ca u deployed.state ∧
      ∃ history, FutureRedemptionGuarantee
        mainnetChainConfig dp ca u deployed future history :=
  by
    exact deployment_fullWindow_future_redeemable_mainnet
      (dp := dp) (ca := ca) (u := u) (base := base) (deployed := deployed) (future := future) (hroot := hroot) (hfuture := hfuture)

example
    {dp : DeployParams} {ca u : Adr} {base deployed future : BlockChain}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future) :
    ∃ history : AccountedHistory mainnetChainConfig dp ca deployed future,
      NoAllowanceKeyCollision history →
      NoAuthorizingActBy u history →
      bookedBalanceNat deployed.state ca u ≤
        bookedBalanceNat future.state ca u :=
  by
    exact deployment_reachable_dormant_holder_balance_monotone_mainnet
      (dp := dp) (ca := ca) (u := u) (base := base) (deployed := deployed) (future := future) (hroot := hroot) (hfuture := hfuture)

example
    {rules : ForkRules} {timestamp : Nat} {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {cs ds : List RedemptionClaim}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hrules : mainnetChainConfig.rulesAt timestamp = .ok rules)
    (hadm : ClaimsAdmissible rules ca future.state cs)
    (hperm : cs.Perm ds) :
    ∃ post, RedemptionOutcome rules dp ca ds future.state post :=
  by
    exact deployment_reachable_redeemClaims_anyOrder_mainnet
      (rules := rules) (timestamp := timestamp) (dp := dp) (ca := ca) (base := base) (deployed := deployed) (future := future) (cs := cs) (ds := ds) (hroot := hroot) (hfuture := hfuture) (hrules := hrules) (hadm := hadm) (hperm := hperm)

example
    {rules : ForkRules} {timestamp : Nat} {dp : DeployParams} {ca : Adr}
    {base deployed future : BlockChain} {holders : List Adr}
    {recipient : Adr → Adr} {claims : List RedemptionClaim}
    (hroot : MainnetDeploymentRoot base deployed dp ca)
    (hfuture : BlockChain.ReachUsing mainnetChainConfig deployed future)
    (hrules : mainnetChainConfig.rulesAt timestamp = .ok rules)
    (hnodup : holders.Nodup)
    (hrecipients : ∀ u ∈ holders,
      ClaimAdmissible rules ca future.state
        ⟨u, bookedBalanceNat future.state ca u, recipient u⟩)
    (hperm :
      (fullBalanceClaims ca future.state holders recipient).Perm claims) :
    ∃ post, RedemptionOutcome rules dp ca claims future.state post :=
  by
    exact deployment_reachable_redeemEveryoneList_anyOrder_mainnet
      (rules := rules) (timestamp := timestamp) (dp := dp) (ca := ca) (base := base) (deployed := deployed) (future := future) (holders := holders) (recipient := recipient) (claims := claims) (hroot := hroot) (hfuture := hfuture) (hrules := hrules) (hnodup := hnodup) (hrecipients := hrecipients) (hperm := hperm)

end Weth10

namespace LidoCircuitBreaker

example (storage : LogicalStorage) (entries : List Entry)
    (targetsNodup : (entries.map Prod.fst).Nodup)
    (targetsValid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.1)
    (pausersValid : ∀ entry ∈ entries, nonzeroCanonicalAddress entry.2)
    (lengthWord : storage.read arrayLengthSlot = Nat.toB256 entries.length)
    (arrayWords : ∀ index, index < entries.length →
      storage.read (arrayEntrySlot (Nat.toB256 (index + 1))) = targetAt entries index)
    (assignments : ∀ target, canonicalAddress target →
      storage.read (assignmentSlot target) = assignmentAt entries target)
    (indices : ∀ target, canonicalAddress target →
      storage.read (indexSlot target) = Nat.toB256 (oneBasedIndexAt entries target))
    (counts : ∀ pauser, canonicalAddress pauser →
      storage.read (countSlot pauser) = Nat.toB256 (assignmentCount entries pauser))
    (zeroCount : storage.read (countSlot 0) = 0) :
    RegistryWitness storage entries :=
  { targetsNodup := targetsNodup
    targetsValid := targetsValid
    pausersValid := pausersValid
    lengthWord := lengthWord
    arrayWords := arrayWords
    assignments := assignments
    indices := indices
    counts := counts
    zeroCount := zeroCount }

example (pauseDuration heartbeatInterval : B256) (registry : LogicalStorage)
    (heartbeatExpiry : B256 → B256) : LogicalState :=
  { pauseDuration := pauseDuration
    heartbeatInterval := heartbeatInterval
    registry := registry
    heartbeatExpiry := heartbeatExpiry }

example : RegistryWitness emptyStorage [] :=
  emptyWitness

example (dp : DeployParams) :
    Prog.compile (runtime dp) = some (lidoCircuitBreakerCode dp) :=
  lidoCircuitBreakerCode_compile dp

example (dp : DeployParams) :
    (funcs dp).map Prod.fst = runtimeEndpoints.map AbiEndpoint.selector :=
  funcs_selectors_eq_runtimeEndpoints dp

example :
    programSiteCount sourceSstoreSiteCount (runtime officialParams) = 20 :=
  runtime_source_sstore_site_count

example :
    programSiteCount sourceTstoreSiteCount (runtime officialParams) = 3 :=
  runtime_source_tstore_site_count

example :
    programSiteCount sourceExternalCallSiteCount (runtime officialParams) = 2 :=
  runtime_source_external_call_site_count

example :
    persistentWriteInventory.length =
        programSiteCount sourceSstoreSiteCount (runtime officialParams) ∧
      transientWriteInventory.length =
        programSiteCount sourceTstoreSiteCount (runtime officialParams) ∧
      externalCallInventory.length =
        programSiteCount sourceExternalCallSiteCount (runtime officialParams) :=
  sourceInventory_cardinalities

example :
    (runtime officialParams).entrySstoreFree
      getPausables enumerationComponent = true :=
  enumeration_entry_sstore_free

example :
    (enumerationWritingMutant officialParams).entrySstoreFree
      getPausables enumerationComponent = false :=
  enumeration_writing_mutant_rejected

example (args : ConstructorArgs) :
    (abiEncodeConstructorArgs args).length = constructorArgumentBytes :=
  abiEncodeConstructorArgs_length args

example :
    constructorPersistentWriteInventory.length = 2 ∧
      constructorTransientWriteInventory.length = 0 ∧
      constructorExternalCallInventory.length = 0 :=
  constructor_inventory_cardinalities

example : constructorProgramSiteCounts =
    (programSiteCount sourceSstoreSiteCount lidoCircuitBreakerConstructorProgram,
     programSiteCount sourceTstoreSiteCount lidoCircuitBreakerConstructorProgram,
     programSiteCount sourceExternalCallSiteCount lidoCircuitBreakerConstructorProgram) :=
  rfl

example :
    lidoCircuitBreakerCreationTemplate.drop lidoCircuitBreakerInitPrefix.length =
      runtimeTemplateCode :=
  creation_template_runtime_suffix

example (args : ConstructorArgs) :
    (lidoCircuitBreakerFullCreateInput args).length =
      lidoCircuitBreakerCreationTemplate.length + constructorArgumentBytes :=
  full_create_input_length args

example {region : Nat} {payload : B256}
    (hregion : region < 16) (hpayload : payload.toNat < 2 ^ 252) :
    (slot region payload).toNat =
      region * 2 ^ 252 + payload.toNat :=
  slot_toNat_of_region_payload_lt hregion hpayload

example {region : Nat} {left right : B256}
    (hregion : region < 16)
    (hleft : left.toNat < 2 ^ 252)
    (hright : right.toNat < 2 ^ 252)
    (hslot : slot region left = slot region right) :
    left = right :=
  slot_injective_payload hregion hleft hright hslot

example {leftRegion rightRegion : Nat} {left right : B256}
    (hlr : leftRegion < 16) (hrr : rightRegion < 16)
    (hleft : left.toNat < 2 ^ 252)
    (hright : right.toNat < 2 ^ 252)
    (hne : leftRegion ≠ rightRegion) :
    slot leftRegion left ≠ slot rightRegion right :=
  slot_ne_of_region_ne hlr hrr hleft hright hne

example {storage : LogicalStorage} {entries : List Entry}
    (h : RegistryWitness storage entries) :
    entries.length ≤ 2 ^ 160 - 1 :=
  h.entries_length_le

example {entries : List Entry} {target newPauser : B256}
    (htarget0 : target ≠ 0) {trace : SetPauserSourceTrace}
    (htrace : setPauserSourceTrace entries target newPauser = some trace) :
    setPauser entries target newPauser = some trace.postEntries ∧
      setPauserSourceWrites entries target newPauser = some trace.writes :=
  setPauser_sourceTrace_refines_model htarget0 htrace

example {s : Stor} {entries : List Entry}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    {target newPauser : B256}
    (htarget : canonicalAddress target)
    (hnew : canonicalAddress newPauser)
    {trace : SetPauserSourceTrace}
    (htrace : setPauserSourceTrace entries target newPauser = some trace) :
    RegistryWitness
      (logicalStorageOfStor (applyRegistryWrites s trace.writes))
      trace.postEntries :=
  hw.applySetPauserSourceTrace htarget hnew htrace

example (dp : DeployParams) {ca : Adr} {sevm : Sevm} {pre : Devm}
    {loc : Nat} {img : Bytes} {stack : List B256}
    {target : B256} {G : Nat}
    (howner : sevm.currentTarget = ca)
    (hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hstack : pre.stack = stack)
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (htargetCanonical : canonicalAddress target)
    (htargetZero : target = 0)
    (halign : pre.memory.size % 32 = 0)
    (hgas : pre.gasLeft = G +
      (gVerylow +
        (gVerylow + pre.extCost [⟨(targetWord * 32).toNat, 32⟩]) +
        gVerylow + (gVerylow + gHigh + gJumpdest) +
        (gVerylow + gMid + gJumpdest) +
        revertSelectorCost (pre.setMach ⟨pre.stack,
          (pre.memory.read (targetWord * 32).toNat 32).2, 0, pre.stateGas⟩)))
    (hroom : pre.stack.length < 1023) :
    let fs := (runtime dp).main :: (runtime dp).aux
    let data := customErrorData "PausableZero"
    let post := (pre.setMach ⟨stack,
      (pre.memory.read (targetWord * 32).toNat 32).2.write 0
        data.toB256.toBytes, G, pre.stateGas⟩).withOutput data
    Func.RunCompiledTo fs sevm pre setPauserKernel
        (.error (.revert, post)) ∧
      ∃ execution : Exec (loc + 1) sevm pre (.error (.revert, post)),
        ∀ occurrence : Exec.NinstOccurrence
            (⟨loc + 1, sevm, pre, .error (.revert, post), execution⟩ :
              Exec.Deriv),
          occurrence.instruction ≠ .reg .sstore :=
  setPauser_zero_runCompiledTo_pausableZero_noRegistryWrite dp howner
    hcodeAddress hbytes htable hstack hwf hr htargetRead htargetCanonical
    htargetZero halign hgas hroom

example {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {img : Bytes} {entries : List Entry}
    {target newPauser continuation : B256} {ca : Adr}
    {trace : SetPauserSourceTrace}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (howner : sevm.currentTarget = ca)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htargetCanonical : canonicalAddress target)
    (hnewCanonical : canonicalAddress newPauser)
    (herrorLookup : fs[pausableZeroErrorSlot]? = some pausableZeroError)
    (happendLookup : fs[appendTargetSlot]? = some appendTarget)
    (hafterLookup : fs[afterOldPauserSlot]? = some afterOldPauser)
    (hremoveLookup : fs[removeTargetSlot]? = some removeTarget)
    (hfinishLookup : fs[finishSetPauserSlot]? = some finishSetPauser)
    (hrun : Func.Run fs sevm pre setPauserKernel final)
    (htrace : setPauserSourceTrace entries target newPauser = some trace) :
    ∃ postRegistry postImg,
      Mem.Wf postRegistry.memory ∧
      Mem.Reads postRegistry.memory postImg ∧
      Bytes.toB256
        (postImg.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Bytes.toB256
        (postImg.sliceD (newPauserWord * 32).toNat 32 0) = newPauser ∧
      Bytes.toB256
        (postImg.sliceD (previousPauserWord * 32).toNat 32 0) =
          assignmentAt entries target ∧
      Bytes.toB256
        (postImg.sliceD (continuationWord * 32).toNat 32 0) =
          continuation ∧
      Devm.getStor postRegistry ca =
        applyRegistryWrites (Devm.getStor pre ca) trace.writes ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor postRegistry ca))
        trace.postEntries ∧
      Devm.getCode pre = Devm.getCode postRegistry ∧
      Func.Run fs sevm postRegistry finishSetPauser final :=
  setPauser_run_extracts_sourceTrace hwf hr htargetRead hnewRead
    hcontinuationRead howner hw htargetCanonical hnewCanonical herrorLookup
    happendLookup hafterLookup hremoveLookup hfinishLookup hrun htrace

example (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat}
    (howner : sevm.currentTarget = ca)
    (hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    Func.Run ((runtime dp).main :: (runtime dp).aux)
      sevm pre setPauserKernel final :=
  setPauserKernel_run_of_exec dp howner hcodeAddress hbytes htable hexec

example (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target newPauser : B256}
    {continuation : B256}
    (howner : sevm.currentTarget = ca)
    (hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htarget : canonicalAddress target)
    (hnew : canonicalAddress newPauser)
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    ∃ trace postRegistry postImg,
      setPauserSourceTrace entries target newPauser = some trace ∧
      Mem.Wf postRegistry.memory ∧
      Mem.Reads postRegistry.memory postImg ∧
      Bytes.toB256
        (postImg.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Bytes.toB256
        (postImg.sliceD (newPauserWord * 32).toNat 32 0) = newPauser ∧
      Bytes.toB256
        (postImg.sliceD (previousPauserWord * 32).toNat 32 0) =
          assignmentAt entries target ∧
      Bytes.toB256
        (postImg.sliceD (continuationWord * 32).toNat 32 0) =
          continuation ∧
      Devm.getStor postRegistry ca =
        applyRegistryWrites (Devm.getStor pre ca) trace.writes ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor postRegistry ca))
        trace.postEntries ∧
      Func.Run ((runtime dp).main :: (runtime dp).aux)
        sevm postRegistry finishSetPauser final :=
  setPauserKernel_exec_extracts_sourceTrace dp howner hcodeAddress hbytes
    htable hwf hr htargetRead hnewRead hcontinuationRead hw htarget hnew
    hexec

example (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target newPauser : B256}
    (howner : sevm.currentTarget = ca)
    (hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htarget : canonicalAddress target)
    (hnew : canonicalAddress newPauser)
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    ∃ trace,
      setPauserSourceTrace entries target newPauser = some trace ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor final ca)) trace.postEntries :=
  registerPauser_kernel_exec_preserves_registry dp howner hcodeAddress
    hbytes htable hwf hr htargetRead hnewRead hcontinuationRead hw htarget
    hnew hexec

example (dp : DeployParams) {ca : Adr} {sevm : Sevm}
    {pre final : Devm} {loc : Nat} {img : Bytes}
    {entries : List Entry} {target continuation : B256}
    (howner : sevm.currentTarget = ca)
    (hcodeAddress : sevm.codeAddress = some ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (htable : (table 0
      ((runtime dp).main :: (runtime dp).aux))[setPauserSlot]? =
        some (loc, setPauserKernel))
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (htargetRead : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = 0)
    (hcontinuationRead : Bytes.toB256
      (img.sliceD (continuationWord * 32).toNat 32 0) = continuation)
    (hcontinuation : continuation ≠ 0)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (htarget : canonicalAddress target)
    (hexec : Exec (loc + 1) sevm pre (.ok final)) :
    ∃ trace pausePre pauseImg,
      setPauserSourceTrace entries target 0 = some trace ∧
      Mem.Wf pausePre.memory ∧
      Mem.Reads pausePre.memory pauseImg ∧
      Bytes.toB256
        (pauseImg.sliceD (targetWord * 32).toNat 32 0) = target ∧
      Devm.getStor pausePre ca =
        applyRegistryWrites (Devm.getStor pre ca) trace.writes ∧
      RegistryWitness
        (logicalStorageOfStor (Devm.getStor pausePre ca))
        trace.postEntries ∧
      setPauser entries target 0 = some trace.postEntries ∧
      target ∉ trace.postEntries.map Prod.fst ∧
      (Devm.getStor pausePre ca).get (assignmentSlot target) = 0 ∧
      (Devm.getStor pausePre ca).get (indexSlot target) = 0 ∧
      Func.Run ((runtime dp).main :: (runtime dp).aux)
        sevm pausePre pauseAfterSet final :=
  pause_kernel_exec_reaches_pauseAfterSet dp howner hcodeAddress hbytes
    htable hwf hr htargetRead hnewRead hcontinuationRead hcontinuation hw
    htarget hexec

example (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr} {entries : List Entry} {target newPauser : B256}
    (htarget : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = registerPauserCalldata target newPauser)
    (htargetCanonical : canonicalAddress target)
    (hnewCanonical : canonicalAddress newPauser)
    (hentry : RegistryWitness
      (logicalStorageOfStor (msg.benv.state.getStor ca)) entries)
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome) :
    RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries :=
  registerPauser_settled_error_restores_registry dp htarget howner
    hcodeAddress hcode hvalue hdata htargetCanonical hnewCanonical hentry
    hprocess herror

example (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr} {entries : List Entry} {target : B256}
    (htarget : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = pauseCalldata target)
    (htargetCanonical : canonicalAddress target)
    (hentry : RegistryWitness
      (logicalStorageOfStor (msg.benv.state.getStor ca)) entries)
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome) :
    RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries :=
  pause_settled_error_restores_registry dp htarget howner hcodeAddress
    hcode hvalue hdata htargetCanonical hentry hprocess herror

example {post : Devm} {ca : Adr} {entries : List Entry}
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries)
    {target : B256} (htarget : canonicalAddress target) :
    ((Devm.getStor post ca).get (assignmentSlot target) ≠ 0 ↔
      target ∈ entries.map Prod.fst) ∧
    ((Devm.getStor post ca).get (indexSlot target) ≠ 0 ↔
      target ∈ entries.map Prod.fst) ∧
    ∀ index pauser, findEntry entries target = some (index, pauser) →
      (Devm.getStor post ca).get (assignmentSlot target) = pauser ∧
      (Devm.getStor post ca).get (indexSlot target) =
        Nat.toB256 (index + 1) ∧
      targetAt entries index = target ∧
      ∀ otherIndex, otherIndex < entries.length →
        targetAt entries otherIndex = target → otherIndex = index :=
  membershipEquivalence_registerPauser hw htarget

example {s : Stor} {entries : List Entry} {target : B256}
    (hw : RegistryWitness (logicalStorageOfStor s) entries)
    (htarget : nonzeroCanonicalAddress target)
    {trace : SetPauserSourceTrace}
    (htrace : setPauserSourceTrace entries target 0 = some trace) :
    let post := applyRegistryWrites s trace.writes
    (post.get (assignmentSlot target) = 0 ∧
     post.get (indexSlot target) = 0 ∧
     target ∉ trace.postEntries.map Prod.fst) ∧
    (match findEntry entries target with
     | none =>
         post.get
           (arrayEntrySlot (Nat.toB256 (entries.length + 1))) = 0
     | some (index, _oldPauser) =>
         post.get (arrayEntrySlot (Nat.toB256 entries.length)) = 0 ∧
         let moved := sourceLastTarget entries
         (moved = target ∨
           post.get (indexSlot moved) = Nat.toB256 (index + 1))) :=
  cleanStateAfterRemoval_registerPauser hw htarget htrace

open scoped BigOperators

example {post : Devm} {ca : Adr} {entries : List Entry}
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor post ca)) entries) :
    (∀ pauser, canonicalAddress pauser →
      (Devm.getStor post ca).get (countSlot pauser) =
        Nat.toB256 (assignmentCount entries pauser)) ∧
    (Devm.getStor post ca).get (countSlot 0) = 0 ∧
    (∑ pauser ∈ (entries.map Prod.snd).toFinset,
      ((Devm.getStor post ca).get (countSlot pauser)).toNat) =
        entries.length :=
  globalCountConservation_registerPauser hw

example {fs : List Func} {sevm : Sevm} {pre : Devm}
    {out : Execution} {img : Bytes} {entries : List Entry}
    {previousPauser newPauser : B256} {ca : Adr} {panicData : Bytes}
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hpreviousRead : Bytes.toB256
      (img.sliceD (previousPauserWord * 32).toNat 32 0) =
        previousPauser)
    (hnewRead : Bytes.toB256
      (img.sliceD (newPauserWord * 32).toNat 32 0) = newPauser)
    (howner : sevm.currentTarget = ca)
    (hprevious : canonicalAddress previousPauser)
    (hnew : canonicalAddress newPauser)
    (hw : RegistryWitness
      (logicalStorageOfStor (Devm.getStor pre ca)) entries)
    (hpanicLookup : fs[arithmeticPanicSlot]? =
      some (Func.revertData panicData))
    (hrun : Func.RunCompiledTo fs sevm pre registerAfterSet out) :
    Execution.Rel
      (fun _ post => RegistryWitness
        (logicalStorageOfStor (Devm.getStor post ca)) entries)
      pre out :=
  registerAfterSet_runCompiledTo_preserves_registry hwf hr hpreviousRead
    hnewRead howner hprevious hnew hw hpanicLookup hrun

example (dp : DeployParams)
    {msg : Msg} {sevm : Sevm} {pre : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {ca : Adr} {entries : List Entry}
    {img : Bytes} {stack : List B256}
    {selectorWord pauser expiry duration previousPauser countValue
      decrementedCount target arrayLength decrementedLength removedIndex
      lastTarget : B256}
    {G : Nat}
    (hmsgTarget : msg.target = some ca)
    (hmsgOwner : msg.currentTarget = ca)
    (hmsgCodeAddress : msg.codeAddress = some ca)
    (hmsgCode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hmsgValue : msg.value = 0)
    (hmsgData : msg.data = pauseCalldata target)
    (howner : sevm.currentTarget = ca)
    (hbytes : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hframeEntry :
      (Frame.ofCall msg).enter = .run ⟨0, sevm, pre⟩)
    (hentry : RegistryWitness
      (logicalStorageOfStor (msg.benv.state.getStor ca)) entries)
    (hstack : pre.stack = stack)
    (hvalue : sevm.value = 0)
    (hselectorData : Sevm.dataWord sevm 0 = selectorWord)
    (hselectorShift : selectorWord >>> 224 = selector "pause" [.address])
    (hwf : Mem.Wf pre.memory)
    (hr : Mem.Reads pre.memory img)
    (hdataLength : sevm.data.length = 36)
    (hmask : addressMask &&& target = 0)
    (hlock : pre.getTransVal sevm.currentTarget lockKey = 0)
    (hdataTarget : Sevm.dataWord sevm 4 = target)
    (hcaller : sevm.caller.toB256 = pauser)
    (hpauserNonzero : pauser ≠ 0)
    (hpauserCanonical : canonicalAddress pauser)
    (hauthorizationStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) = pauser)
    (hexpiryStorage :
      pre.getStorVal sevm.currentTarget (expirySlot pauser) = expiry)
    (hlive : sevm.benvStat.time < expiry)
    (hdurationStorage :
      pre.getStorVal sevm.currentTarget pauseDurationSlot = duration)
    (htargetNonzero : target ≠ 0)
    (htargetCanonical : canonicalAddress target)
    (hassignmentStorage :
      pre.getStorVal sevm.currentTarget (assignmentSlot target) =
        previousPauser)
    (hpreviousNonzero : previousPauser ≠ 0)
    (hpreviousCanonical : canonicalAddress previousPauser)
    (hcountStorage :
      pre.getStorVal sevm.currentTarget (countSlot previousPauser) =
        countValue)
    (hcountSub : countValue - 1 = decrementedCount)
    (harrayLengthBound : arrayLength.toNat < 2 ^ 252)
    (hindexStorage :
      pre.getStorVal sevm.currentTarget (indexSlot target) = removedIndex)
    (hlengthStorage :
      pre.getStorVal sevm.currentTarget arrayLengthSlot = arrayLength)
    (hdecrement : arrayLength - 1 = decrementedLength)
    (hlastStorage :
      pre.getStorVal sevm.currentTarget (arrayEntrySlot arrayLength) =
        lastTarget)
    (hlastCanonical : canonicalAddress lastTarget)
    (hcodeSize : (pre.getCode target.toAdr).size = 0)
    (haccess : target.toAdr ∈ pre.accessedAddresses ∨
      target.toAdr ∉ pre.accessedAddresses)
    (hwarmHole :
      (⟨sevm.currentTarget, arrayEntrySlot removedIndex⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hwarmMovedIndex :
      (⟨sevm.currentTarget, indexSlot lastTarget⟩ : Adr × B256) ∈
        pre.accessedStorageKeys)
    (hroom : stack.length < 1017)
    (hstatic : sevm.isStatic = false)
    (hemptyLookup :
      ((runtime dp).main :: (runtime dp).aux)[emptyRevertSlot]? =
        some Func.revert)
    (hpauseLookup :
      ((runtime dp).main :: (runtime dp).aux)[pauseAfterSetSlot]? =
        some pauseAfterSet)
    (hfinishLookup :
      ((runtime dp).main :: (runtime dp).aux)[finishSetPauserSlot]? =
        some finishSetPauser)
    (hremoveLookup :
      ((runtime dp).main :: (runtime dp).aux)[removeTargetSlot]? =
        some removeTarget)
    (hafterLookup :
      ((runtime dp).main :: (runtime dp).aux)[afterOldPauserSlot]? =
        some afterOldPauser)
    (hsetPauserLookup :
      ((runtime dp).main :: (runtime dp).aux)[setPauserSlot]? =
        some setPauserKernel)
    (hgas : pre.gasLeft = G + runtimePauseCost dp pre duration target
      previousPauser removedIndex arrayLength lastTarget)
    (hmsgFork : CoveredFork msg.benv.stat.fork) :
    ∃ raw,
      Prog.RunCompiledTo sevm pre (runtime dp) (.error (.revert, raw)) ∧
      ∃ rootExec : Exec 0 sevm pre (.error (.revert, raw)),
        raw.output = [] ∧
        ((∃ write : Exec.SuccessfulSstoreOccurrence
            (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
          write.storageOwner = ca ∧
          write.key = assignmentSlot target ∧
          write.value = 0 ∧
          ∃ zeroCode : Exec.NinstOccurrence
              (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            zeroCode.instruction = .reg .extcodesize ∧
            (∃ rest, zeroCode.node.devm.stack = target :: rest) ∧
            (zeroCode.node.devm.getCode target.toAdr).size = 0 ∧
            Exec.RawBefore
              (root :=
                ⟨0, sevm, pre, .error (.revert, raw), rootExec⟩)
              write.occurrence.node zeroCode.node) ∧
          ∀ occurrence : Exec.NinstOccurrence
              (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
            occurrence.instruction ≠ .exec .call ∧
            occurrence.instruction ≠ .exec .staticcall) ∧
        ∃ post,
          ProcessMessage msg
              (.some ⟨⟨0, sevm, pre⟩, .error (.revert, raw)⟩)
              (.ok post) ∧
          post.error.isSome ∧
          RegistryWitness
            (logicalStorageOfStor (Devm.getStor post ca)) entries :=
  pause_direct_postWrite_revert_settles_and_restores_registry dp hfork hmsgFork hmsgTarget hmsgOwner
    hmsgCodeAddress hmsgCode hmsgValue hmsgData howner hbytes hframeEntry hentry hstack hvalue
    hselectorData hselectorShift hwf hr hdataLength hmask hlock hdataTarget hcaller hpauserNonzero
    hpauserCanonical hauthorizationStorage hexpiryStorage hlive hdurationStorage htargetNonzero
    htargetCanonical hassignmentStorage hpreviousNonzero hpreviousCanonical hcountStorage hcountSub
    harrayLengthBound hindexStorage hlengthStorage hdecrement hlastStorage hlastCanonical hcodeSize
    haccess hwarmHole hwarmMovedIndex hroom hstatic hemptyLookup hpauseLookup hfinishLookup
    hremoveLookup hafterLookup hsetPauserLookup hgas

example :
    ∃ (msg : Msg) (sevm : Sevm) (pre : Devm) (raw : Devm),
      msg.target = some (Nat.toAdr 100) ∧
      msg.currentTarget = Nat.toAdr 100 ∧
      msg.codeAddress = some (Nat.toAdr 100) ∧
      msg.code.toList = lidoCircuitBreakerCode officialParams ∧
      msg.value = 0 ∧
      msg.data = pauseCalldata (7 : B256) ∧
      sevm = initSevm msg ∧
      pre = initDevm msg ∧
      (Frame.ofCall msg).enter = .run ⟨0, sevm, pre⟩ ∧
      RegistryWitness
        (logicalStorageOfStor (msg.benv.state.getStor (Nat.toAdr 100)))
        [((7 : B256), (9 : B256))] ∧
      sevm.caller.toB256 = (9 : B256) ∧
      pre.getStorVal (Nat.toAdr 100) (assignmentSlot (7 : B256)) = 9 ∧
      pre.getStorVal (Nat.toAdr 100) (expirySlot (9 : B256)) = 20 ∧
      sevm.benvStat.time < (20 : B256) ∧
      (7 : B256) ≠ 0 ∧
      canonicalAddress (7 : B256) ∧
      (pre.getCode (7 : B256).toAdr).size = 0 ∧
      Prog.RunCompiledTo sevm pre (runtime officialParams)
        (.error (.revert, raw)) ∧
      ∃ _rootExec : Exec 0 sevm pre (.error (.revert, raw)),
        raw.output = [] ∧
        ∃ post,
          ProcessMessage msg
              (.some ⟨⟨0, sevm, pre⟩, .error (.revert, raw)⟩)
              (.ok post) ∧
          post.error.isSome ∧
          RegistryWitness
            (logicalStorageOfStor (Devm.getStor post (Nat.toAdr 100)))
            [((7 : B256), (9 : B256))] := by
  rcases directPause_zeroCode_postWrite_error_control with
    ⟨msg, sevm, pre, raw, htarget, howner, hcodeAddress, hcode, hvalue,
      hdata, hsevm, hpre, hframe, hw, hcaller, hassignment, hexpiry,
      hlive, htarget0, hcanonical, hzeroCode, hrun, rootExec, houtput,
      _evidence, post, hprocess, herror, hrestored⟩
  exact ⟨msg, sevm, pre, raw, htarget, howner, hcodeAddress, hcode,
    hvalue, hdata, hsevm, hpre, hframe, hw, hcaller, hassignment, hexpiry,
    hlive, htarget0, hcanonical, hzeroCode, hrun, rootExec, houtput, post,
    hprocess, herror, hrestored⟩

/-! S3 Registry enumeration/observability public-role pins.  The dedicated
gate additionally hashes each normalized declaration header fail-closed. -/
#check getPausables_runCompiled
#check getPausables_noSstore_occurrence
#check registryViews_coherent
#check pauserSet_local_transition
#check pauserSet_target_zero_no_success
#check pauserSet_target_zero_error_logs_unchanged
#check pauserSet_register_success
#check pauserSet_register_success_committed
#check pauserSet_settled_error_not_observable
#check registryObservation_sound

/-! S9 carrier-field pins. The dedicated deployment gate hashes the complete
record bodies; these Lean wrappers independently pin each public field's type. -/

example {sevm : Sevm} {base post : Devm} {G : Nat}
    (h : OfficialValidationCheckpoints sevm base post G) :
    Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty, G + officialConstructorRequiredGas, base.stateGas⟩)
        lidoCircuitBreakerConstructorProgram post ∧
      Func.RunCompiled
        (lidoCircuitBreakerConstructorProgram.main ::
          lidoCircuitBreakerConstructorProgram.aux)
        sevm
        (base.setMach
          ⟨[(224 : B256), (616 : B256), (4282 : B256)],
            officialConstructorDecodedMemory, G + 49961, base.stateGas⟩)
        officialConstructorEffectBody post ∧
      sevm.code.size = 5122 ∧
      (∀ i : Fin 7,
        Bytes.toB256
            ((officialConstructorDecodedMemory.read (32 * i.val) 32).1) =
          officialConstructorArgumentWord i) ∧
      addressMask &&& officialParams.admin = 0 ∧
      officialParams.admin ≠ 0 ∧
      officialParams.minPauseDuration ≠ 0 ∧
      officialParams.minPauseDuration.toNat ≤
        officialParams.maxPauseDuration.toNat ∧
      officialParams.minHeartbeatInterval ≠ 0 ∧
      officialParams.minHeartbeatInterval.toNat ≤
        officialParams.maxHeartbeatInterval.toNat ∧
      officialParams.minPauseDuration.toNat ≤
        officialConstructorArgs.initialPauseDuration.toNat ∧
      officialConstructorArgs.initialPauseDuration.toNat ≤
        officialParams.maxPauseDuration.toNat ∧
      officialParams.minHeartbeatInterval.toNat ≤
        officialConstructorArgs.initialHeartbeatInterval.toNat ∧
      officialConstructorArgs.initialHeartbeatInterval.toNat ≤
        officialParams.maxHeartbeatInterval.toNat :=
  ⟨h.run, h.effectEntry, h.inputLength, h.decodedArguments,
    h.canonicalAdmin, h.adminNonzero, h.minPauseNonzero, h.pauseBounds,
    h.minHeartbeatNonzero, h.heartbeatBounds, h.initialPauseAboveMin,
    h.initialPauseBelowMax, h.initialHeartbeatAboveMin,
    h.initialHeartbeatBelowMax⟩

example {sevm : Sevm} {base post : Devm} {G : Nat}
    (h : OfficialConstructorEffectCheckpoints sevm base post G) :
    post = officialConstructorPost sevm base G ∧
      post.state =
        (base.state.setStorVal sevm.currentTarget pauseDurationSlot
          officialConstructorArgs.initialPauseDuration).setStorVal
            sevm.currentTarget heartbeatIntervalSlot
            officialConstructorArgs.initialHeartbeatInterval ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor base sevm.currentTarget).set pauseDurationSlot
          officialConstructorArgs.initialPauseDuration).set
            heartbeatIntervalSlot
            officialConstructorArgs.initialHeartbeatInterval ∧
      post.logs = base.logs ++ officialConstructorLogs sevm.currentTarget ∧
      post.stack = [] ∧
      post.memory = officialConstructorFinalMemory ∧
      post.gasLeft = G ∧
      post.output = lidoCircuitBreakerCode officialParams ∧
      post.refundCounter = base.refundCounter ∧
      post.returnData = base.returnData ∧
      post.error = base.error ∧
      post.accountsToDelete = base.accountsToDelete ∧
      post.createdAccounts = base.createdAccounts ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys =
        (base.accessedStorageKeys.insert
          (sevm.currentTarget, pauseDurationSlot)).insert
            (sevm.currentTarget, heartbeatIntervalSlot) ∧
      post.transientStorage = base.transientStorage ∧
      constructorProgramSiteCounts = (2, 0, 0) ∧
      constructorPersistentWriteInventory =
        [(⟨"constructor.pauseDuration", 0⟩, .configuration),
          (⟨"constructor.heartbeatInterval", 1⟩, .configuration)] ∧
      constructorTransientWriteInventory = [] ∧
      constructorExternalCallInventory = [] :=
  ⟨h.exactPost, h.state, h.storage, h.logs, h.stack, h.memory, h.gasLeft,
    h.output, h.refundCounter, h.returnData, h.error, h.accountsToDelete,
    h.createdAccounts, h.accessedAddresses, h.accessedStorageKeys,
    h.transientStorage, h.siteCounts, h.persistentInventory,
    h.transientInventory, h.externalCallInventory⟩

example (h : OfficialConstructorErrorArmLayout) :
    DeploymentProof.constructorBodyForProof 616 4898 4282 =
        officialConstructorValidationBody ∧
      lidoCircuitBreakerConstructorProgram.main =
        Ninst.callvalue ::: Ninst.iszero :::
          (officialConstructorValidationBody <?> (.call 1)) ∧
      lidoCircuitBreakerConstructorProgram.aux =
        [Func.revert,
          DeploymentProof.constructorErrorForProof "AdminZero",
          DeploymentProof.constructorErrorForProof "MinPauseDurationZero",
          DeploymentProof.constructorErrorForProof
            "MinPauseDurationExceedsMax",
          DeploymentProof.constructorErrorForProof
            "MinHeartbeatIntervalZero",
          DeploymentProof.constructorErrorForProof
            "MinHeartbeatIntervalExceedsMax",
          DeploymentProof.constructorErrorForProof "PauseDurationBelowMin",
          DeploymentProof.constructorErrorForProof "PauseDurationAboveMax",
          DeploymentProof.constructorErrorForProof
            "HeartbeatIntervalBelowMin",
          DeploymentProof.constructorErrorForProof
            "HeartbeatIntervalAboveMax"] ∧
      officialConstructorTableCallIndices =
        [1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :=
  ⟨h.body, h.main, h.aux, h.sites⟩

example {ca : Adr} {msg : Msg} {post : Devm}
    (h : OfficialCreateMessageExecution ca msg post) :
    ∃ (benv : Benv) (raw charged : Devm) (G : Nat),
      (processCreateMessage.msg msg).benvAfterTransfer = .ok benv ∧
      G = msg.gas - officialConstructorRequiredGas ∧
      processMessage (processCreateMessage.msg msg) = .ok raw ∧
      OfficialConstructorExecutionTrace ca
        (initSevm ((processCreateMessage.msg msg).withBenv benv))
        (initDevm ((processCreateMessage.msg msg).withBenv benv)) raw G ∧
      processCreateMessage.chargeCodeGas msg.benv.stat.rules raw = .ok charged ∧
      post = charged.setCode msg.currentTarget ⟨⟨charged.output⟩⟩ := by
  rcases h.pipeline with
    ⟨benv, raw, charged, G, htransfer, hgas, hprocess, htrace, hcharge,
      hpost⟩
  exact ⟨benv, raw, charged, G, htransfer, hgas, hprocess, htrace, hcharge,
    hpost⟩

example {ca : Adr} {sevm : Sevm} {base post : Devm} {G : Nat}
    (h : OfficialConstructorExecutionTrace ca sevm base post G) :
    sevm.currentTarget = ca ∧
      sevm.code.toList = officialFullCreateInput ∧
      Prog.compile lidoCircuitBreakerConstructorProgram =
        some lidoCircuitBreakerInitPrefix ∧
      OfficialValidationCheckpoints sevm base post G ∧
      OfficialConstructorErrorArmLayout ∧
      OfficialConstructorEffectCheckpoints sevm base post G ∧
      Jaune.exec ⟨0, sevm,
          base.setMach
            ⟨[], Mem.empty, G + officialConstructorRequiredGas, base.stateGas⟩⟩ =
        .ok post :=
  ⟨h.target_eq, h.fullInput, h.prefixCompile, h.validationCheckpoints,
    h.errorArmLayout, h.effectCheckpoints, h.exec⟩

example {chainId : UInt64} {base : BlockChain} {sender ca : Adr}
    (h : CanonicalDeploymentBase .prague chainId base sender ca) :
    base.ValidContext ∧
      chainId = base.chainId ∧
      SumNof base.state.bal ∧
      ca = computeContractAddress sender (base.state.getNonce sender) ∧
      ca ≠ 0 ∧
      (¬ pragueRules.isPrecomp ca) ∧
      sender ≠ ca ∧
      withdrawalRequestPredeployAddress ≠ ca ∧
      consolidationRequestPredeployAddress ≠ ca ∧
      accountHasCodeOrNonce base.state ca = false ∧
      accountHasStorage base.state ca = false ∧
      (∃ lastHash,
        List.getLast? (getLast256BlockHashes base) = some lastHash) ∧
      some (base.state.getCode beaconRootsAddress).toList =
        Prog.compile deploymentSystemProgram ∧
      some (base.state.getCode historyStorageAddress).toList =
        Prog.compile deploymentSystemProgram ∧
      some (base.state.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram ∧
      some (base.state.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram :=
  ⟨h.validContext, h.chainId_eq, h.sumNof, h.target_eq, h.target_ne_zero,
    h.target_not_precompile, h.sender_ne_target,
    h.withdrawalRequest_ne_target, h.consolidationRequest_ne_target,
    h.target_noCodeOrNonce, h.target_noStorage, h.lastBlockHash, h.beaconCode,
    h.historyCode, h.withdrawalRequestCode, h.consolidationRequestCode⟩

example {chainId : UInt64} {base : BlockChain} {cb : CanonicalBlock}
    {txBytes : Bytes} {tx : Tx} {sender ca : Adr}
    (h : CanonicalOfficialDeploymentBlock chainId base cb
      txBytes tx sender ca) :
    cb.block.txs = [.inl txBytes] ∧
      decodeTx (.inl txBytes) = .ok tx ∧
      cb.block.ommers = [] ∧
      cb.block.wds = [] ∧
      (∃ maxPriorityFee maxFee,
        tx.type = .two chainId maxPriorityFee maxFee none []) ∧
      tx.value = 0 ∧
      tx.data = officialFullCreateInput ∧
      tx.nonce = base.state.getNonce sender ∧
      tx.nonce ≠ UInt64.max ∧
      recoverSender chainId tx = .ok sender ∧
      validateTransaction pragueRules tx 0 =
        .ok (calculateIntrinsicCost pragueRules tx 0) ∧
      (let benv := initBenv .prague base cb.block.header
       checkTransaction benv.beginTransaction
          (deploymentTxPreludeBout .init tx 0) tx =
        .ok (sender, deploymentEffectiveGasPrice benv tx, [], 0)) ∧
      cb.block.header.baseFeePerGas ≤
        deploymentEffectiveGasPrice
          (initBenv .prague base cb.block.header) tx ∧
      tx.gas * deploymentEffectiveGasPrice
          (initBenv .prague base cb.block.header) tx ≤
        (base.state.bal sender).toNat ∧
      deploymentTransactionGasBound (initBenv .prague base cb.block.header) tx sender ≤
        tx.gas ∧
      tx.gas ≤ cb.block.header.gasLimit ∧
      ca = computeContractAddress sender tx.nonce :=
  ⟨h.txs_eq, h.decode_eq, h.ommers_eq, h.withdrawals_eq, h.type_eq,
    h.value_eq, h.data_eq, h.nonce_eq, h.nonce_not_max,
    h.recoveredSender, h.validated, h.checked, h.base_fee_le_effective,
    h.upfront_funded, h.gas_bound, h.block_gas_room, h.target_eq⟩

example {chainId : UInt64} {base : BlockChain} {cb : CanonicalBlock}
    {tx : Tx} {sender ca : Adr}
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca) :
    ctx.txInput =
        ((initBenv .prague base cb.block.header).withState
          ctx.systemPrefix.stBeacon).withState ctx.systemPrefix.stHistory ∧
      ctx.begun = ctx.txInput.beginTransaction ∧
      (ctx.begun.state.incrNonce sender).subBal sender
          (tx.gas * deploymentEffectiveGasPrice ctx.txInput tx).toB256 =
        some ctx.debit ∧
      ctx.tenv = deploymentTenv ctx.txInput tx sender 0 ∧
      prepareMessage {ctx.begun with state := ctx.debit} ctx.tenv tx =
        .ok ctx.msg ∧
      ctx.msg.benv = {ctx.begun with state := ctx.debit} ∧
      ctx.msg.caller = sender ∧
      ctx.msg.target = none ∧
      ctx.msg.gas = tx.gas - deploymentIntrinsicGas ctx.msg.benv tx sender ∧
      ctx.msg.value = 0 ∧
      ctx.msg.data = [] ∧
      ctx.msg.code.toList = officialFullCreateInput ∧
      ctx.msg.codeAddress = none ∧
      ctx.msg.shouldTransferValue = true ∧
      ctx.msg.tenv.stat.auths = [] ∧
      ctx.msg.benv.stat.rules = pragueRules ∧
      ctx.msg.benv.stat.chainId = chainId ∧
      ctx.msg.currentTarget = ca ∧
      accountHasCodeOrNonce ctx.msg.benv.state ca = false ∧
      accountHasStorage ctx.msg.benv.state ca = false ∧
      ctx.msg.benv.stat.origState = base.state ∧
      (ca, pauseDurationSlot) ∉ ctx.msg.accessedStorageKeys ∧
      (ca, heartbeatIntervalSlot) ∉ ctx.msg.accessedStorageKeys ∧
      (ctx.msg.benv.stat.origState.get ca).stor.get pauseDurationSlot = 0 ∧
      (ctx.msg.benv.stat.origState.get ca).stor.get
        heartbeatIntervalSlot = 0 ∧
      ctx.msg.isStatic = false :=
  ⟨ctx.systemPrefix.txInput_eq, ctx.begun_eq, ctx.debit_eq, ctx.tenv_eq,
    ctx.prepare_eq, ctx.msg_benv_eq, ctx.msg_caller_eq, ctx.msg_target_eq,
    ctx.msg_gas_eq, ctx.msg_value_eq, ctx.msg_data_eq, ctx.msg_code_eq,
    ctx.msg_codeAddress_eq, ctx.msg_shouldTransferValue_eq, ctx.msg_auths_eq,
    ctx.msg_rules_eq, ctx.msg_chainId_eq, ctx.target_eq, ctx.noCodeOrNonce,
    ctx.noStorage, ctx.originalState_eq, ctx.pauseCold, ctx.heartbeatCold,
    ctx.pauseOriginal, ctx.heartbeatOriginal, ctx.msg_static_eq⟩

example {ca : Adr} {msg : Msg} {post : Devm}
    (h : OfficialCreateMessageResult ca msg post) :
    msg.currentTarget = ca ∧
      processCreateMessage msg = .ok post ∧
      OfficialCreateMessageExecution ca msg post ∧
      some (post.getCode ca).toList =
        Prog.compile (runtime officialParams) ∧
      post.state.getStor ca =
        ((Stor.empty.set pauseDurationSlot
          officialConstructorArgs.initialPauseDuration).set
            heartbeatIntervalSlot
            officialConstructorArgs.initialHeartbeatInterval) ∧
      post.getStorVal ca pauseDurationSlot =
        officialConstructorArgs.initialPauseDuration ∧
      post.getStorVal ca heartbeatIntervalSlot =
        officialConstructorArgs.initialHeartbeatInterval ∧
      RegistryWitness (logicalStorageOfStor (post.state.getStor ca)) [] ∧
      RegistryCoherent (post.state.getStor ca) ∧
      post.logs = officialConstructorLogs ca ∧
      post.output = lidoCircuitBreakerCode officialParams ∧
      post.returnData = [] ∧
      post.gasLeft = msg.gas - officialCreateMessageGasAccounting ∧
      post.error = .none ∧
      post.refundCounter = 0 ∧
      post.accountsToDelete = .emptyWithCapacity ∧
      RegistryStable officialParams ca post.state :=
  ⟨h.target_eq, h.run, h.trace, h.installed, h.storage, h.pauseDuration,
    h.heartbeatInterval, h.emptyRegistry, h.coherent, h.logs, h.returnData,
    h.frameReturnData, h.gasLeft, h.error, h.refundCounter,
    h.accountsToDelete, h.stable⟩

example {ca : Adr} {msg : Msg} {post : State} {out : MsgCallOutput}
    (h : OfficialConstructorMessageResult ca msg post out) :
    msg.currentTarget = ca ∧
      msg.target = none ∧
      processMessageCall msg = .ok (post, out) ∧
      (∃ createPost,
        OfficialCreateMessageResult ca msg createPost ∧
        post = createPost.state ∧ out = officialMessageOutputOf createPost) ∧
      some (post.getCode ca).toList =
        Prog.compile (runtime officialParams) ∧
      (post.getStor ca).get pauseDurationSlot =
        officialConstructorArgs.initialPauseDuration ∧
      (post.getStor ca).get heartbeatIntervalSlot =
        officialConstructorArgs.initialHeartbeatInterval ∧
      RegistryWitness (logicalStorageOfStor (post.getStor ca)) [] ∧
      out.logs = officialConstructorLogs ca ∧
      out.returnData = lidoCircuitBreakerCode officialParams ∧
      out.gasLeft = msg.gas - officialCreateMessageGasAccounting ∧
      out.error = .none ∧
      out.accountsToDelete = .emptyWithCapacity ∧
      RegistryStable officialParams ca post :=
  ⟨h.target_eq, h.target_none, h.run, h.creation, h.installed,
    h.pauseDuration, h.heartbeatInterval, h.emptyRegistry, h.logs,
    h.returnData, h.gasLeft, h.error, h.accountsToDelete, h.stable⟩

example {chainId : UInt64} {base : BlockChain} {cb : CanonicalBlock}
    {tx : Tx} {sender ca : Adr}
    {ctx : PreparedDeploymentContext chainId base cb tx sender ca}
    {post : State} {bout : BlockOutput}
    (h : OfficialDeploymentTransactionResult chainId ca ctx post bout) :
    processTransaction ctx.txInput .init tx 0 = .ok (post, bout) ∧
      (∃ messagePost out,
        OfficialConstructorMessageResult ca ctx.msg messagePost out) ∧
      some (post.getCode ca).toList =
        Prog.compile (runtime officialParams) ∧
      (post.getStor ca).get pauseDurationSlot =
        officialConstructorArgs.initialPauseDuration ∧
      (post.getStor ca).get heartbeatIntervalSlot =
        officialConstructorArgs.initialHeartbeatInterval ∧
      RegistryWitness (logicalStorageOfStor (post.getStor ca)) [] ∧
      RegistryStable officialParams ca post ∧
      bout.blockLogs = officialConstructorLogs ca ∧
      bout.requests = [] ∧
      parseDepositRequests bout = .ok [] ∧
      bout.receiptKeys = [deploymentReceiptKey 0] ∧
      (∃ entry,
        Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0) =
            some entry ∧
        entry.2.logs = officialConstructorLogs ca ∧
        entry.2.succeeded = true) ∧
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
          (fun entry => entry.2.logs) =
        some (officialConstructorLogs ca) ∧
      (Std.TreeMap.get? bout.receiptsTrie (deploymentReceiptKey 0)).map
          (fun entry => entry.2.succeeded) = some true ∧
      some (post.getCode withdrawalRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram ∧
      some (post.getCode consolidationRequestPredeployAddress).toList =
        Prog.compile deploymentSystemProgram :=
  ⟨h.run, h.message, h.installed, h.pauseDuration, h.heartbeatInterval,
    h.emptyRegistry, h.stable, h.blockLogs, h.requests, h.depositRequests,
    h.receiptKeys, h.receiptEntry, h.receiptLogs, h.receiptSucceeded,
    h.withdrawalRequestCode, h.consolidationRequestCode⟩

example {chainId : UInt64} {base : BlockChain} {cb : CanonicalBlock}
    {tx : Tx} {sender ca : Adr}
    {ctx : PreparedDeploymentContext chainId base cb tx sender ca}
    {post : State} {bout : BlockOutput}
    (h : OfficialDeploymentSuffixResult chainId ca ctx post bout) :
    processCheckedSystemTransaction (ctx.txInput.withState post)
        withdrawalRequestPredeployAddress [] = .ok (post, h.withdrawalOut) ∧
      h.withdrawalOut.returnData = [] ∧
      processCheckedSystemTransaction
          ((ctx.txInput.withState post).withState post)
          consolidationRequestPredeployAddress [] =
        .ok (post, h.consolidationOut) ∧
      h.consolidationOut.returnData = [] ∧
      processGeneralPurposeRequests (ctx.txInput.withState post) bout =
        .ok (post, bout) ∧
      RegistryStable officialParams ca post :=
  ⟨h.withdrawalRun, h.withdrawalReturnData, h.consolidationRun,
    h.consolidationReturnData, h.run, h.stable⟩

/-! S9 constructor-to-block theorem pins. These wrappers freeze every public
premise, including the distinction between raw CREATE success, collision-
checked message settlement, receipt success, and the complete request suffix. -/

example (msg : Msg)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code.toList = officialFullCreateInput)
    (hgas : officialCreateMessageGasAccounting ≤ msg.gas)
    (hmax : 4282 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hpauseCold : (msg.currentTarget, pauseDurationSlot) ∉
      msg.accessedStorageKeys)
    (hpauseOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        pauseDurationSlot = 0)
    (hheartbeatCold : (msg.currentTarget, heartbeatIntervalSlot) ∉
      msg.accessedStorageKeys)
    (hheartbeatOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        heartbeatIntervalSlot = 0)
    (hstatic : msg.isStatic = false)
    (hfork : CoveredFork msg.benv.stat.fork) :
    ∃ post, OfficialCreateMessageResult msg.currentTarget msg post :=
  processCreateMessage_establishes_officialRegistryStable msg hvalue hcodeAddress hcode hgas hmax
    hpauseCold hpauseOriginal hheartbeatCold hheartbeatOriginal hstatic hfork

example (ca : Adr) (msg : Msg)
    (htarget : msg.currentTarget = ca)
    (htargetNone : msg.target = none)
    (hnoCodeOrNonce : accountHasCodeOrNonce msg.benv.state ca = false)
    (hnoStorage : accountHasStorage msg.benv.state ca = false)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code.toList = officialFullCreateInput)
    (hgas : officialCreateMessageGasAccounting ≤ msg.gas)
    (hmax : 4282 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hpauseCold : (msg.currentTarget, pauseDurationSlot) ∉
      msg.accessedStorageKeys)
    (hpauseOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        pauseDurationSlot = 0)
    (hheartbeatCold : (msg.currentTarget, heartbeatIntervalSlot) ∉
      msg.accessedStorageKeys)
    (hheartbeatOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        heartbeatIntervalSlot = 0)
    (hstatic : msg.isStatic = false)
    (hfork : CoveredFork msg.benv.stat.fork) :
    ∃ post out, OfficialConstructorMessageResult ca msg post out :=
  processMessageCall_establishes_officialRegistryStable ca msg htarget htargetNone hnoCodeOrNonce
    hnoStorage hvalue hcodeAddress hcode hgas hmax hpauseCold hpauseOriginal hheartbeatCold
    hheartbeatOriginal hstatic hfork

example (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase .prague chainId base sender ca)
    (henv : CanonicalOfficialDeploymentBlock chainId base cb
      txBytes tx sender ca)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca) :
    ∃ post bout,
      OfficialDeploymentTransactionResult chainId ca ctx post bout :=
  canonicalDeploymentTransaction_succeeds chainId base cb tx sender ca
    hbase henv ctx

example (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (tx : Tx) (sender ca : Adr)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : OfficialDeploymentTransactionResult chainId ca ctx post bout) :
    Nonempty (OfficialDeploymentSuffixResult chainId ca ctx post bout) :=
  canonicalDeploymentSuffix_succeeds chainId base cb tx sender ca ctx post
    bout htx

example (chainId : UInt64) (base : BlockChain) (cb : CanonicalBlock)
    (txBytes : Bytes) (tx : Tx) (sender ca : Adr)
    (henv : CanonicalOfficialDeploymentBlock chainId base cb
      txBytes tx sender ca)
    (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
    (post : State) (bout : BlockOutput)
    (htx : OfficialDeploymentTransactionResult chainId ca ctx post bout)
    (hsuffix : OfficialDeploymentSuffixResult chainId ca ctx post bout) :
    applyBody (initBenv .prague base cb.block.header)
      cb.block.txs cb.block.wds = .ok (post, bout) :=
  canonicalDeploymentApplyBody_succeeds chainId base cb txBytes tx sender ca
    henv ctx post bout htx hsuffix

/-! S9 direct-deployment root pins. The constructor pin freezes every public
field of the root package; the theorem and seven method pins freeze the exact
premise and consequence surfaces rather than merely checking that the names
still resolve. -/

example {chainId : UInt64} {base deployed : BlockChain} {ca : Adr}
    (execution : ∃ (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx)
        (sender : Adr)
        (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
        (post : State) (bout : BlockOutput),
      CanonicalDeploymentBase .prague chainId base sender ca ∧
      CanonicalOfficialDeploymentBlock chainId base cb txBytes tx sender ca ∧
      OfficialDeploymentTransactionResult chainId ca ctx post bout ∧
      Nonempty (OfficialDeploymentSuffixResult chainId ca ctx post bout) ∧
      stateTransitionUsing (ChainConfig.pragueOnly chainId)
        base cb.block = .ok deployed ∧
      applyBody (initBenv .prague base cb.block.header)
        cb.block.txs cb.block.wds = .ok (post, bout) ∧
      post = deployed.state)
    (target_ne_zero : ca ≠ 0)
    (target_not_precompile : ¬ pragueRules.isPrecomp ca)
    (installed : some (deployed.state.getCode ca).toList =
      Prog.compile (runtime officialParams))
    (pauseDuration : (deployed.state.getStor ca).get pauseDurationSlot =
      officialConstructorArgs.initialPauseDuration)
    (heartbeatInterval :
      (deployed.state.getStor ca).get heartbeatIntervalSlot =
        officialConstructorArgs.initialHeartbeatInterval)
    (emptyRegistry : RegistryWitness
      (logicalStorageOfStor (deployed.state.getStor ca)) [])
    (stable : RegistryStable officialParams ca deployed.state)
    (deployed_validContext : deployed.ValidContext)
    (deployed_chainId : chainId = deployed.chainId) :
    DeploymentRoot chainId base deployed ca :=
  { execution := execution
    target_ne_zero := target_ne_zero
    target_not_precompile := target_not_precompile
    installed := installed
    pauseDuration := pauseDuration
    heartbeatInterval := heartbeatInterval
    emptyRegistry := emptyRegistry
    stable := stable
    deployed_validContext := deployed_validContext
    deployed_chainId := deployed_chainId }

example (chainId : UInt64) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase .prague chainId base sender ca)
    (henv : CanonicalOfficialDeploymentBlock chainId base cb
      txBytes tx sender ca)
    (hstep : stateTransitionUsing (ChainConfig.pragueOnly chainId)
      base cb.block = .ok deployed) :
    DeploymentRoot chainId base deployed ca :=
  canonicalDeploymentStep_establishes_root chainId base deployed cb txBytes
    tx sender ca hbase henv hstep

example {chainId : UInt64} {base deployed : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot chainId base deployed ca) :
    BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed deployed :=
  DeploymentRoot.reflReach hroot

example {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    RegistryStable officialParams ca future.state :=
  DeploymentRoot.reachable_registryStable hroot hreach

example {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    some (future.state.getCode ca).toList =
      Prog.compile (runtime officialParams) :=
  DeploymentRoot.reachable_code hroot hreach

example {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    (future.state.getCode ca).toList =
      lidoCircuitBreakerCode officialParams :=
  DeploymentRoot.reachable_installedCode hroot hreach

example {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    ∃ entries,
      RegistryWitness
        (logicalStorageOfStor (future.state.getStor ca)) entries :=
  DeploymentRoot.reachable_witness hroot hreach

example {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future)
    {target : B256} (htarget : canonicalAddress target) :
    ∃ entries,
      RegistryWitness
        (logicalStorageOfStor (future.state.getStor ca)) entries ∧
      ((future.state.getStor ca).get (assignmentSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ((future.state.getStor ca).get (indexSlot target) ≠ 0 ↔
        target ∈ entries.map Prod.fst) ∧
      ∀ index pauser, findEntry entries target = some (index, pauser) →
        (future.state.getStor ca).get (assignmentSlot target) = pauser ∧
        (future.state.getStor ca).get (indexSlot target) =
          Nat.toB256 (index + 1) ∧
        targetAt entries index = target ∧
        ∀ otherIndex, otherIndex < entries.length →
          targetAt entries otherIndex = target → otherIndex = index :=
  DeploymentRoot.reachable_membership hroot hreach htarget

example {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot chainId base deployed ca)
    (hreach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future) :
    ∃ entries,
      RegistryWitness
        (logicalStorageOfStor (future.state.getStor ca)) entries ∧
      (∀ pauser, canonicalAddress pauser →
        (future.state.getStor ca).get (countSlot pauser) =
          Nat.toB256 (assignmentCount entries pauser)) ∧
      (future.state.getStor ca).get (countSlot 0) = 0 ∧
      (∑ pauser ∈ (entries.map Prod.snd).toFinset,
        ((future.state.getStor ca).get (countSlot pauser)).toNat) =
          entries.length :=
  DeploymentRoot.reachable_countConservation hroot hreach

end LidoCircuitBreaker

namespace ProxyPair

example {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {implementation requestedAdmin : Adr} {G : Nat}
    (hvalue : sevm.value = 0)
    (hinput : sevm.code.toList =
      ossifiableEmptyDataCreateInput implementation requestedAdmin)
    (himplementationNonzero : implementation ≠ 0)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold : (sevm.currentTarget, implementationSlotLit) ∉
      base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hgas : 200000 ≤ G) :
    ∃ post,
      Prog.RunCompiled sevm (base.setMach ⟨[], Mem.empty, G + 320, base.stateGas⟩)
        (ossifiableConstructorProgram 1249 3437 2188) post ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor base sevm.currentTarget).set implementationSlotLit
          implementation.toB256).set adminSlotLit requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [rawUpgradedLog sevm.currentTarget implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget 0
          requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = G - 49894 ∧
      post.error = base.error :=
  ossifiableConstructorProgram_canonicalEmptyInput_forward_exact
    hfork hvalue hinput himplementationNonzero hrequestedNonzero hcodeSizeNonzero
    haddressCold himplementationRaw himplementationOriginal
    himplementationCold hadminRaw hadminOriginal hadminCold hstatic hgas

example (msg : Msg) (implementation requestedAdmin : Adr)
    (hfork : CoveredFork msg.benv.stat.fork)
    (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code.toList =
      ossifiableEmptyDataCreateInput implementation requestedAdmin)
    (himplementationNonzero : implementation ≠ 0)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (himplementationCode :
      (msg.benv.state.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ msg.accessedAddresses)
    (himplementationOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get
        implementationSlotLit = 0)
    (himplementationCold :
      (msg.currentTarget, implementationSlotLit) ∉ msg.accessedStorageKeys)
    (hadminOriginal :
      (msg.benv.stat.origState.get msg.currentTarget).stor.get adminSlotLit = 0)
    (hadminCold :
      (msg.currentTarget, adminSlotLit) ∉ msg.accessedStorageKeys)
    (hstatic : msg.isStatic = false)
    (hgas : ossifiableCreateMessageGas ≤ msg.gas)
    (hmax : 2188 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post,
      OssifiableEmptySetupCreateResult msg implementation requestedAdmin post :=
  processCreateMessage_ossifiable_emptySetup_success msg implementation requestedAdmin hfork hvalue
    hcodeAddress hcode himplementationNonzero hrequestedNonzero himplementationCode haddressCold
    himplementationOriginal himplementationCold hadminOriginal hadminCold hstatic hgas hmax

example {runtimeOffset runtimeLength : Nat}
    {sevm : Sevm} {entry post : Devm} {tail : Stack}
    {image runtimeBytes setupData : Bytes}
    {implementation requestedAdmin : B256}
    (hp : tail <<+ entry.stack)
    (hwf : Mem.Wf entry.memory)
    (hreads : Mem.Reads entry.memory image)
    (hcoordinate : runtimeOffset + runtimeLength + 96 < 2 ^ 256)
    (hcodeSize : sevm.code.size < 2 ^ 256)
    (hspec :
      ossifiableConstructorDecodeSpec sevm.code.toList
        (runtimeOffset + runtimeLength) =
          .accepted implementation requestedAdmin setupData)
    (setupDataNonempty : setupData ≠ [])
    (hruntime :
      sevm.code.sliceD runtimeOffset runtimeLength
        (Linst.toUInt8 .stop) = runtimeBytes)
    (hruntimeLength : runtimeBytes.length = runtimeLength)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hoffsetBound : runtimeOffset < 2 ^ 256)
    (hlengthBound : runtimeLength < 2 ^ 256)
    (run : Prog.RunCompiledTo sevm entry
      (ossifiableConstructorProgram runtimeOffset
        (runtimeOffset + runtimeLength) runtimeLength) (.ok post)) :
    OssifiableConstructorNonemptySuccessResult runtimeOffset runtimeLength
      sevm entry post tail image runtimeBytes setupData implementation
      requestedAdmin :=
  ossifiableConstructorProgram_nonempty_success hp hwf hreads hcoordinate
    hcodeSize hspec setupDataNonempty hruntime hruntimeLength
    hruntimeNonempty hoffsetBound hlengthBound run

example {msg : Msg} {post : Devm}
    {implementation requestedAdmin : Adr} {setupData : Bytes}
    (hcode : msg.code.toList =
      ossifiableFullCreateInput implementation requestedAdmin setupData)
    (process : processCreateMessage msg = .ok post)
    (failed : post.error.isSome = true) :
    post.state = msg.benv.state ∧
      post.getStorVal msg.currentTarget implementationSlotLit =
        (msg.benv.state.getStor msg.currentTarget).get
          implementationSlotLit ∧
      post.getStorVal msg.currentTarget adminSlotLit =
        (msg.benv.state.getStor msg.currentTarget).get adminSlotLit ∧
      post.getCode msg.currentTarget =
        msg.benv.state.getCode msg.currentTarget :=
  processCreateMessage_ossifiable_failure_rollback hcode process failed

example :
    ∃ post, OssifiableEmptySetupCreateResult
      OssifiableCreateFixture.message OssifiableCreateFixture.implementation
      OssifiableCreateFixture.admin post :=
  OssifiableCreateFixture.message_success

example :
    ∃ post,
      processMessage OssifiableBothSlotFixture.message = .ok post ∧
      post.error = .none ∧
      post.output = [] ∧
      post.getStorVal OssifiableBothSlotFixture.target implementationSlotLit =
        OssifiableBothSlotFixture.postSetupImplementation.toB256 ∧
      post.getStorVal OssifiableBothSlotFixture.target adminSlotLit =
        OssifiableBothSlotFixture.postSetupAdmin.toB256 ∧
      post.logs = [] :=
  OssifiableBothSlotFixture.message_success

example {sevm : Sevm} {base : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hvalue : sevm.value = 0)
    (hinput : sevm.code.toList = ossifiableFullCreateInput
      OssifiableBothSlotFixture.implementation
      OssifiableBothSlotFixture.requestedAdmin
      OssifiableBothSlotFixture.setupData)
    (himplementationNonzero :
      OssifiableBothSlotFixture.implementation ≠ 0)
    (himplementationCode : base.getCode
      OssifiableBothSlotFixture.implementation =
        OssifiableBothSlotFixture.implementationCode)
    (hcodeSizeNonzero : (base.getCode
      OssifiableBothSlotFixture.implementation).size.toB256 ≠ 0)
    (haddressCold : OssifiableBothSlotFixture.implementation ∉
      base.accessedAddresses)
    (himplementationRaw : base.getStorVal sevm.currentTarget
      implementationSlotLit = 0)
    (himplementationOriginal : getOrigStorVal sevm sevm.currentTarget
      implementationSlotLit = 0)
    (himplementationCold : (sevm.currentTarget, implementationSlotLit) ∉
      base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal : getOrigStorVal sevm sevm.currentTarget
      adminSlotLit = 0)
    (hadminCold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hprecompile : sevm.benvStat.rules.isPrecomp
      OssifiableBothSlotFixture.implementation = false) :
    ∃ post,
      Prog.RunCompiled sevm (base.setMach ⟨[], Mem.empty, 526248, base.stateGas⟩)
        (ossifiableConstructorProgram 1249 3437 2188) post ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        OssifiableBothSlotFixture.postSetupImplementation.toB256 ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        OssifiableBothSlotFixture.requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorInitializationLog sevm
          OssifiableBothSlotFixture.implementation] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget
          OssifiableBothSlotFixture.postSetupAdmin.toB256
          OssifiableBothSlotFixture.requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = 475566 ∧
      post.error = base.error :=
  OssifiableBothSlotCreateFixture.program_success hfork hvalue hinput
    himplementationNonzero himplementationCode hcodeSizeNonzero
    haddressCold himplementationRaw himplementationOriginal
    himplementationCold hadminRaw hadminOriginal hadminCold hstatic hdepth
    hprecompile

example :
    ∃ post,
      processCreateMessage
          OssifiableBothSlotCreateFixture.creationMessage = .ok post ∧
      post.getCode OssifiableBothSlotFixture.target =
        ⟨⟨runtimeBaselineBytes⟩⟩ ∧
      post.getStorVal OssifiableBothSlotFixture.target
          implementationSlotLit =
        OssifiableBothSlotFixture.postSetupImplementation.toB256 ∧
      post.getStorVal OssifiableBothSlotFixture.target adminSlotLit =
        OssifiableBothSlotFixture.requestedAdmin.toB256 ∧
      post.logs =
        [rawUpgradedLog OssifiableBothSlotFixture.target
          OssifiableBothSlotFixture.implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog
          OssifiableBothSlotFixture.target
          OssifiableBothSlotFixture.postSetupAdmin.toB256
          OssifiableBothSlotFixture.requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft =
        OssifiableBothSlotCreateFixture.creationMessage.gas -
          OssifiableBothSlotCreateFixture.bothSlotCreateMessageGas ∧
      post.error = .none := by
  obtain ⟨post, result⟩ :=
    OssifiableBothSlotCreateFixture.creationMessage_success
  exact ⟨post, result.run, result.installed, result.implementationSlot,
    result.adminSlot, result.logs, result.output, result.gasLeft,
    result.error⟩

end ProxyPair

namespace Prorata

open scoped BigOperators

/-! ## PRORATA — the SF-frozen P3 and P4 headline statements.

The PRORATA etude's SF memo, §5, freezes these five P3 shapes and
three P4 shapes.  The pins below carry the frozen types and use the named
declarations as their bodies, so a statement change breaks this file while a
proof-only refactor does not. -/

-- P3: the genesis-anchored reachable invariant, in its public accounting
-- spelling — ledger sum equals supply, supply stays capped, and the share
-- price never falls below genesis.
example {cfg : ChainConfig} {deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    balSum (future.state.getStor ca) =
        supplyN (future.state.getStor ca) ∧
      supplyN (future.state.getStor ca) ≤ maxSupply.toNat ∧
      supplyN (future.state.getStor ca) ≤
        offset.toNat * (future.state.bal ca).toNat :=
  DeploymentRoot.reachable_accountingInvariant root reach hcov

-- P3: the pure finite-range cumulative-dust identity over a connected
-- accounting path.  Exact equality, no tolerance parameter.
example {o : Nat} (ho : o ≠ 0) (path : ProrataAccountingPath o) :
    let n := path.steps.length
    path.XAt n * (∏ j ∈ Finset.range n, path.DAt j) =
      path.XAt 0 * (∏ j ∈ Finset.Icc 1 n, path.DAt j) +
        ∑ i ∈ Finset.range n,
          (path.rhoAt i + path.kappaAt i) *
            (∏ j ∈ Finset.range i, path.DAt j) *
              (∏ j ∈ Finset.Icc (i + 2) n, path.DAt j) :=
  ProrataAccountingPath.prorata_dust_trace_exact ho path

-- P3: the realized endpoint (rung R11).  The same identity over every
-- realized finite trace of the deployed PRORATA, anchored at its own genesis,
-- where the root discharges `X₀ = 1` and `D₀ = O`.
example {cfg : ChainConfig} {deployed future : BlockChain} {ca : Adr}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (root : DeploymentRoot cfg deployed ca)
    (realizes : ProrataTraceRealizes root steps future) :
    ∃ path : ProrataAccountingPath offset.toNat,
      path.steps = steps ∧
      path.first = ⟨0, 0⟩ ∧
      path.last = AccountingSnapshot.ofWorldState ca future.state ∧
      path.XAt 0 = 1 ∧
      path.DAt 0 = offset.toNat ∧
      path.XAt steps.length * (∏ j ∈ Finset.range steps.length, path.DAt j) =
        (∏ j ∈ Finset.Icc 1 steps.length, path.DAt j) +
          ∑ i ∈ Finset.range steps.length,
            (path.rhoAt i + path.kappaAt i) *
              (∏ j ∈ Finset.range i, path.DAt j) *
                (∏ j ∈ Finset.Icc (i + 2) steps.length, path.DAt j) :=
  prorata_realized_dust_trace_exact root realizes

-- P3 non-vacuity, first direction: the realized carrier never admits a
-- continuation the configured chain relation does not.
example {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (realizes : ProrataTraceRealizes root steps future) :
    BlockChain.ReachUsing cfg deployed future :=
  ProrataTraceRealizes.toReachUsing realizes

-- P3 non-vacuity, second direction: every configured continuation of the
-- deployed PRORATA carries an exact accounting trace.  With the pin above
-- this fixes the carrier exactly onto chain reachability.
example {cfg : ChainConfig} {deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, ProrataTraceRealizes root steps future :=
  prorataTraceRealizes_exists_of_reachUsing root reach hcov

-- P4: the open-context bound.  The coalition's settled take is bounded by its
-- own settled input plus the outside subsidy it was handed.
example {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {coalition : Finset Adr} {victim : Adr}
    {charge : ProrataAccountingStep offset.toNat → AttackAttribution}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (trace : ProrataOpenAttackTrace root coalition victim charge steps future) :
    outA victim charge steps ≤
      inA victim charge steps + outsideSubsidy victim charge steps :=
  attacker_open_context trace

-- P4: no closed attack trace is profitable.  No honesty, cooperation or
-- no-donation premise appears anywhere in the carrier.
example {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {coalition : Finset Adr} {victim : Adr}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (trace : ProrataAttackTrace root coalition victim steps future) :
    outA victim coalitionCharge steps ≤ inA victim coalitionCharge steps :=
  attacker_no_profit trace

-- P4: the victim's shortfall across a deposit and a later successful exit of
-- the same unchanged shares is at most one virtual-asset quantum above the
-- genesis-anchored price ratio.
example {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {coalition : Finset Adr} {victim : Adr}
    {charge : ProrataAccountingStep offset.toNat → AttackAttribution}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (trace : ProrataOpenAttackTrace root coalition victim charge steps future)
    {deposit exit : ProrataAccountingStep offset.toNat} {v m p : Nat}
    (hmoves : victimMoves victim steps = [deposit, exit])
    (hdeposit : deposit.kind = .deposit v m)
    (hexit : exit.kind = .withdraw m p) :
    v - p ≤ Nat.div (deposit.pre.balance + 1) (deposit.pre.supply + offset.toNat) + 1 :=
  victim_loss_bound trace hmoves hdeposit hexit

end Prorata

/-! ## Reverting-walk vocabulary (vault-max-design-v1).

The visiting relation carries the meaning of every PRORATA WETH vault
nonrevert headline below, so its definition and every constructor type are
pinned, together with its anti-vacuity projection. -/

example (P : Sevm → Devm → Ninst → Devm → Prop) (sevm : Sevm) (devm : Devm)
    (p : Prog) (ex : Execution) :
    Prog.RunCompiledToVisiting P sevm devm p ex =
      ∃ mid, Devm.BurnBy gJumpdest devm mid ∧
        Func.RunCompiledToVisiting P (p.main :: p.aux) sevm mid p.main ex :=
  rfl

example {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm devm' : Devm} {i : Ninst} {f : Func} {ex : Execution}
    (step : Ninst.RunCompiled sevm devm i devm') (visited : P sevm devm i devm')
    (tail : Func.RunCompiledTo fs sevm devm' f ex) :
    Func.RunCompiledToVisiting P fs sevm devm (Func.next i f) ex :=
  Func.RunCompiledToVisiting.here step visited tail

example {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm devm' : Devm} {i : Ninst} {f : Func} {ex : Execution}
    (step : Ninst.RunCompiled sevm devm i devm')
    (tail : Func.RunCompiledToVisiting P fs sevm devm' f ex) :
    Func.RunCompiledToVisiting P fs sevm devm (Func.next i f) ex :=
  Func.RunCompiledToVisiting.next step tail

example {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm devm' : Devm} {f g : Func} {ex : Execution}
    (room : devm.stack.length < 1024)
    (pop : Devm.PopBurnBy [0] (gVerylow + gHigh) devm devm')
    (arm : Func.RunCompiledToVisiting P fs sevm devm' f ex) :
    Func.RunCompiledToVisiting P fs sevm devm (Func.branch f g) ex :=
  Func.RunCompiledToVisiting.zero room pop arm

example {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm devm' : Devm} {w : B256} {f g : Func} {ex : Execution}
    (nonzero : w ≠ 0) (room : devm.stack.length < 1024)
    (pop : Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm devm')
    (arm : Func.RunCompiledToVisiting P fs sevm devm' g ex) :
    Func.RunCompiledToVisiting P fs sevm devm (Func.branch f g) ex :=
  Func.RunCompiledToVisiting.succ nonzero room pop arm

example {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm devm' : Devm} {k : Nat} {f : Func} {ex : Execution}
    (lookup : fs[k]? = some f) (room : devm.stack.length < 1024)
    (burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) devm devm')
    (tail : Func.RunCompiledToVisiting P fs sevm devm' f ex) :
    Func.RunCompiledToVisiting P fs sevm devm (Func.call k) ex :=
  Func.RunCompiledToVisiting.call lookup room burn tail
example
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f : Func} {ex : Execution}
    (h : Func.RunCompiledToVisiting P fs sevm devm f ex) :
    ∃ (stepPre : Devm) (instruction : Ninst) (stepPost : Devm),
      Ninst.RunCompiled sevm stepPre instruction stepPost ∧
        P sevm stepPre instruction stepPost :=
  Func.RunCompiledToVisiting.exists_step h
example {sevm : Sevm} {pre d : Devm}
    {p : Prog}
    (h_pcf : Prog.pcFree p = true)
    (h_eq : some sevm.code.toList = p.compile)
    (h_exec : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledTo sevm pre p (.error (.revert, d)) :=
  Prog.runCompiledTo_of_exec_revert h_pcf h_eq h_exec

namespace ProrataWethVault

open Jaune.Ninst Ninst
open scoped LogOutputHinv

/-! ## PRORATA WETH vault — SF §9 P1 rounding statements, the exact capacity
arithmetic, the round-trip no-profit twin, the ERC-20 share surface and the
`maxRedeem` view (vault-max-design-v1). -/

example (amount assets supply : Nat) :
    assetFactorN assets * convertToSharesN amount assets supply ≤
      amount * denominatorN supply :=
  convertToSharesN_floor_le amount assets supply

example (amount assets supply : Nat) :
    amount * denominatorN supply <
      assetFactorN assets * (convertToSharesN amount assets supply + 1) :=
  convertToSharesN_lt_floor_add_one amount assets supply

example (shares assets supply : Nat) :
    denominatorN supply * convertToAssetsN shares assets supply ≤
      shares * assetFactorN assets :=
  convertToAssetsN_floor_le shares assets supply

example (shares assets supply : Nat) :
    shares * assetFactorN assets <
      denominatorN supply * (convertToAssetsN shares assets supply + 1) :=
  convertToAssetsN_lt_floor_add_one shares assets supply

example (shares assets supply : Nat) :
    shares * assetFactorN assets ≤
      previewMintN shares assets supply * denominatorN supply :=
  previewMintN_covers shares assets supply

example (shares assets supply : Nat) :
    previewMintN shares assets supply * denominatorN supply <
      shares * assetFactorN assets + denominatorN supply :=
  previewMintN_lt_add_denominator shares assets supply

example (amount assets supply : Nat) :
    amount * denominatorN supply ≤
      previewWithdrawN amount assets supply * assetFactorN assets :=
  previewWithdrawN_covers amount assets supply

example (amount assets supply : Nat) :
    previewWithdrawN amount assets supply * assetFactorN assets <
      amount * denominatorN supply + assetFactorN assets :=
  previewWithdrawN_lt_add_assetFactor amount assets supply

example (amount balance assets supply : Nat) :
    amount ≤ maxWithdrawN balance assets supply ↔
      previewWithdrawN amount assets supply ≤ balance :=
  le_maxWithdrawN_iff amount balance assets supply

example (amount assets supply : Nat) :
    convertToAssetsN (convertToSharesN amount assets supply)
        (assets + amount)
        (supply + convertToSharesN amount assets supply) ≤ amount :=
  roundtrip_no_profit amount assets supply

example
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "approve" [.address, .uint256]) :
    sevm.value = 0 ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      ¬ ValidAdr (allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0)) ∧
      allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0) ≠ supplySlot ∧
      AbiReturnsTrue post ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set
          (allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0))
          (Sevm.argWord sevm 1) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor post account = Devm.getStor pre account) ∧
      post.logs = pre.logs ++
        [approvalLogEntry sevm (Sevm.argWord sevm 0)
          (Sevm.argWord sevm 1)] :=
  approve_compiled_effect memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "transfer" [.address, .uint256]) :
    sevm.value = 0 ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      AbiReturnsTrue post ∧
      Devm.getStorVal post sevm.currentTarget supplySlot =
        Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      ∃ ownerBalance receiverBalance,
        ownerBalance =
          Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 ∧
        (Sevm.argWord sevm 1).toNat ≤ ownerBalance.toNat ∧
        receiverBalance =
          ((Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
            (ownerBalance - Sevm.argWord sevm 1)).get
              (Sevm.argWord sevm 0) ∧
        receiverBalance.toNat + (Sevm.argWord sevm 1).toNat < wordModulusN ∧
        Devm.getStor post sevm.currentTarget =
          ((Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
            (ownerBalance - Sevm.argWord sevm 1)).set (Sevm.argWord sevm 0)
              (receiverBalance + Sevm.argWord sevm 1) ∧
        (∀ account, sevm.currentTarget ≠ account →
          Devm.getStor post account = Devm.getStor pre account) ∧
        post.logs = pre.logs ++
          [transferLogEntry sevm sevm.caller.toB256 (Sevm.argWord sevm 0)
            (Sevm.argWord sevm 1)] :=
  transfer_compiled_effect memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    sevm.value = 0 ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      Sevm.argWord sevm 1 ≠ 0 ∧
      AbiReturnsTrue post ∧
      ¬ ValidAdr (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256) ∧
      allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256 ≠ supplySlot ∧
      Devm.getStorVal post sevm.currentTarget supplySlot =
        Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      ∃ allowance afterAllowance ownerBalance receiverBalance,
        allowance = Devm.getStorVal pre sevm.currentTarget
          (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256) ∧
        (Sevm.argWord sevm 2).toNat ≤ allowance.toNat ∧
        ((allowance = B256.max ∧
            afterAllowance = Devm.getStor pre sevm.currentTarget) ∨
          afterAllowance = (Devm.getStor pre sevm.currentTarget).set
            (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256)
            (allowance - Sevm.argWord sevm 2)) ∧
        ownerBalance = afterAllowance.get (Sevm.argWord sevm 0) ∧
        (Sevm.argWord sevm 2).toNat ≤ ownerBalance.toNat ∧
        receiverBalance =
          (afterAllowance.set (Sevm.argWord sevm 0)
            (ownerBalance - Sevm.argWord sevm 2)).get
              (Sevm.argWord sevm 1) ∧
        receiverBalance.toNat + (Sevm.argWord sevm 2).toNat < wordModulusN ∧
        Devm.getStor post sevm.currentTarget =
          ((afterAllowance.set (Sevm.argWord sevm 0)
            (ownerBalance - Sevm.argWord sevm 2)).set (Sevm.argWord sevm 1)
              (receiverBalance + Sevm.argWord sevm 2)) ∧
        (∀ account, sevm.currentTarget ≠ account →
          Devm.getStor post account = Devm.getStor pre account) ∧
        post.logs = pre.logs ++
          [transferLogEntry sevm (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
            (Sevm.argWord sevm 2)] :=
  transferFrom_compiled_effect memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (run : Prog.RunCompiled sevm pre vault post)
    (hselector :
      Sevm.selector sevm = selector "maxRedeem" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      WordViewEffect
        (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 0))
        pre post :=
  maxRedeem_compiled_effect run hselector

end ProrataWethVault

namespace Composition.ProrataWethVault

open Jaune.Ninst Ninst
open scoped LogOutputHinv BigOperators
open Source
open _root_.Blanc.ExecutionTrace

/-! ## PRORATA WETH vault — the claim map's compiled, capacity, nonrevert,
history and attack headlines (vault-max-design-v1).

Each pin carries the headline's exact type and uses the named declaration as
its body, so a statement change breaks this file while a proof-only refactor
does not.  The nonrevert pins are exec-level: they bind the frame's actual
execution through `Prog.runCompiledTo_of_exec_revert`. -/

example :
    WethChildRefused = fun (_sevm : Sevm) (callPre : Devm) (instruction : Ninst)
        (callPost : Devm) =>
      (instruction = Ninst.call ∨ instruction = Ninst.staticcall) ∧
        callPre.stack[1]? = some wethAccount.toB256 ∧
        callPost.stack.head? = some (0 : B256) :=
  rfl

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "deposit" [.uint256, .address]) :
    sevm.value = 0 ∧
      ∃ supply,
        supply = Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
        supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
        Blanc.ProrataWethVault.convertToSharesN (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
        sevm.caller.toB256 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 1) ∧
        Sevm.argWord sevm 1 ≠ 0 ∧
        (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤
          Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
        InboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 0)
          (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat))
          (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat))
          pre post :=
  deposit_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "mint" [.uint256, .address]) :
    sevm.value = 0 ∧
      ∃ supply,
        supply = Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
        supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
        Blanc.ProrataWethVault.previewMintN (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
        sevm.caller.toB256 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 1) ∧
        Sevm.argWord sevm 1 ≠ 0 ∧
        (Sevm.argWord sevm 0).toNat ≤
          Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
        InboundEffect sevm (Sevm.argWord sevm 1)
          (Nat.toB256 (Blanc.ProrataWethVault.previewMintN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat))
          (Sevm.argWord sevm 0)
          (Nat.toB256 (Blanc.ProrataWethVault.previewMintN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat))
          pre post :=
  mint_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]) :
    sevm.value = 0 ∧
      ∃ supply,
        supply = Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
        supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
        Blanc.ProrataWethVault.previewWithdrawN (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
        sevm.caller.toB256 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 1) ∧
        Sevm.argWord sevm 1 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 2) ∧
        Sevm.argWord sevm 2 ≠ 0 ∧
        (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 2)).toNat ∧
        (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤ supply.toNat ∧
        OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
          (Sevm.argWord sevm 0)
          (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
          (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
          pre post :=
  withdraw_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]) :
    sevm.value = 0 ∧
      ∃ supply,
        supply = Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
        supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
        Blanc.ProrataWethVault.previewRedeemN (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
        sevm.caller.toB256 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 1) ∧
        Sevm.argWord sevm 1 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 2) ∧
        Sevm.argWord sevm 2 ≠ 0 ∧
        (Sevm.argWord sevm 0).toNat ≤
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 2)).toNat ∧
        (Sevm.argWord sevm 0).toNat ≤ supply.toNat ∧
        OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
          (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
          (Sevm.argWord sevm 0)
          (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
          pre post :=
  redeem_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "convertToShares" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.convertToSharesN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  convertToShares_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "convertToAssets" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.convertToAssetsN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.convertToAssetsN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  convertToAssets_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "previewDeposit" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.previewDepositN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.previewDepositN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  previewDeposit_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "previewRedeem" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.previewRedeemN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  previewRedeem_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm = selector "previewMint" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.previewMintN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.previewMintN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  previewMint_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "previewWithdraw" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.previewWithdrawN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  previewWithdraw_compiled_effect config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (receiverNonzero : (Sevm.argWord sevm 0).toNat ≠ 0)
    (stable :
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxDeposit" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Blanc.ProrataWethVault.maxDepositN
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.maxDepositN
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  maxDeposit_compiled_effect_stable config hfork memoryWf receiverNonzero stable run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (receiverNonzero : (Sevm.argWord sevm 0).toNat ≠ 0)
    (stable :
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxMint" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Blanc.ProrataWethVault.maxMintN
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.maxMintN
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  maxMint_compiled_effect_stable config hfork memoryWf receiverNonzero stable run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (stable :
      (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN)
    (balanceLe :
      (Devm.getStorVal pre sevm.currentTarget
          (Sevm.argWord sevm 0)).toNat ≤
        (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxWithdraw" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Blanc.ProrataWethVault.maxWithdrawN
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 0)).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat <
        wordModulusN ∧
      Blanc.ProrataWethVault.WordViewEffect
        (Nat.toB256 (Blanc.ProrataWethVault.maxWithdrawN
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 0)).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget Blanc.ProrataWethVault.supplySlot).toNat))
        pre post :=
  maxWithdraw_compiled_effect_exact config hfork memoryWf stable balanceLe run selectorEq

example
    {sevm : Sevm} {pre d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq :
      Sevm.selector sevm = selector "deposit" [.uint256, .address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 2)) = 0)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr (Sevm.argWord sevm 1))
    (receiverNonzero : Sevm.argWord sevm 1 ≠ 0)
    (withinMax :
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.maxDepositViewN (Sevm.argWord sevm 1).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget
            Blanc.ProrataWethVault.supplySlot).toNat)
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) :=
  deposit_exec_revert_visits_refused_weth_child hfork stable memoryWf codeEq selectorEq valueZero
    argsPresent callerNonzero receiverValid receiverNonzero withinMax reverted

example
    {sevm : Sevm} {pre d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq :
      Sevm.selector sevm = selector "mint" [.uint256, .address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 2)) = 0)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr (Sevm.argWord sevm 1))
    (receiverNonzero : Sevm.argWord sevm 1 ≠ 0)
    (withinMax :
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.maxMintViewN (Sevm.argWord sevm 1).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget
            Blanc.ProrataWethVault.supplySlot).toNat)
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) :=
  mint_exec_revert_visits_refused_weth_child hfork stable memoryWf codeEq selectorEq valueZero
    argsPresent callerNonzero receiverValid receiverNonzero withinMax reverted

example
    {sevm : Sevm} {pre d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 3)) = 0)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr (Sevm.argWord sevm 1))
    (receiverNonzero : Sevm.argWord sevm 1 ≠ 0)
    (ownerValid : ValidAdr (Sevm.argWord sevm 2))
    (ownerNonzero : Sevm.argWord sevm 2 ≠ 0)
    (withinMax :
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.maxWithdrawViewN
          (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget
            Blanc.ProrataWethVault.supplySlot).toNat)
    (authorized :
      sevm.caller.toB256 = Sevm.argWord sevm 2 ∨
        (¬ ValidAdr (Blanc.ProrataWethVault.allowanceKey
            (Sevm.argWord sevm 2) sevm.caller.toB256) ∧
          Blanc.ProrataWethVault.allowanceKey (Sevm.argWord sevm 2)
              sevm.caller.toB256 ≠ Blanc.ProrataWethVault.supplySlot ∧
          Blanc.ProrataWethVault.previewWithdrawN (Sevm.argWord sevm 0).toNat
              ((pre.state.getStor wethAccount).get
                sevm.currentTarget.toB256).toNat
              (Devm.getStorVal pre sevm.currentTarget
                Blanc.ProrataWethVault.supplySlot).toNat ≤
            (Devm.getStorVal pre sevm.currentTarget
              (Blanc.ProrataWethVault.allowanceKey (Sevm.argWord sevm 2)
                sevm.caller.toB256)).toNat))
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) :=
  withdraw_exec_revert_visits_refused_weth_child hfork stable memoryWf codeEq selectorEq valueZero
    argsPresent callerNonzero receiverValid receiverNonzero ownerValid ownerNonzero withinMax
    authorized reverted

example
    {sevm : Sevm} {pre d : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 3)) = 0)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr (Sevm.argWord sevm 1))
    (receiverNonzero : Sevm.argWord sevm 1 ≠ 0)
    (ownerValid : ValidAdr (Sevm.argWord sevm 2))
    (ownerNonzero : Sevm.argWord sevm 2 ≠ 0)
    (withinMax :
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.maxRedeemN
          (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat)
    (authorized :
      sevm.caller.toB256 = Sevm.argWord sevm 2 ∨
        (¬ ValidAdr (Blanc.ProrataWethVault.allowanceKey
            (Sevm.argWord sevm 2) sevm.caller.toB256) ∧
          Blanc.ProrataWethVault.allowanceKey (Sevm.argWord sevm 2)
              sevm.caller.toB256 ≠ Blanc.ProrataWethVault.supplySlot ∧
          (Sevm.argWord sevm 0).toNat ≤
            (Devm.getStorVal pre sevm.currentTarget
              (Blanc.ProrataWethVault.allowanceKey (Sevm.argWord sevm 2)
                sevm.caller.toB256)).toNat))
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) :=
  redeem_exec_revert_visits_refused_weth_child hfork stable memoryWf codeEq selectorEq valueZero
    argsPresent callerNonzero receiverValid receiverNonzero ownerValid ownerNonzero withinMax
    authorized reverted

example
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm = selector "maxDeposit" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) :=
  maxDeposit_exec_revert_visits_refused_weth_child config hfork memoryWf codeEq selectorEq valueZero
    argsPresent argValid reverted

example
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm = selector "maxMint" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) :=
  maxMint_exec_revert_visits_refused_weth_child config hfork memoryWf codeEq selectorEq valueZero
    argsPresent argValid reverted

example
    {sevm : Sevm} {pre d : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm = selector "maxWithdraw" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (reverted : exec ⟨0, sevm, pre⟩ = .error (.revert, d)) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) :=
  maxWithdraw_exec_revert_visits_refused_weth_child config hfork memoryWf codeEq selectorEq
    valueZero argsPresent argValid reverted

example
    {sevm : Sevm} {pre : Devm}
    (codeEq : some sevm.code.toList = Prog.compile Blanc.ProrataWethVault.vault)
    (selectorEq : Sevm.selector sevm = selector "maxRedeem" [.address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 1)) = 0)
    (argValid : ValidAdr (Sevm.argWord sevm 0))
    (d : Devm) :
    exec ⟨0, sevm, pre⟩ ≠ .error (.revert, d) :=
  maxRedeem_exec_never_reverts codeEq selectorEq valueZero argsPresent argValid d

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "deposit" [.uint256, .address]) :
    (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.maxDepositViewN (Sevm.argWord sevm 1).toNat
        ((pre.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat :=
  deposit_success_within_maxDeposit config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "mint" [.uint256, .address]) :
    (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.maxMintViewN (Sevm.argWord sevm 1).toNat
        ((pre.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat :=
  mint_success_within_maxMint config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]) :
    (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.maxWithdrawViewN
        (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat
        ((pre.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat :=
  withdraw_success_within_maxWithdraw config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]) :
    (Sevm.argWord sevm 0).toNat ≤
      Blanc.ProrataWethVault.maxRedeemN
        (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat :=
  redeem_success_within_maxRedeem config hfork memoryWf run selectorEq

example
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (hfork : CoveredFork sevm.benvStat.fork)
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot (Devm.getStor post sevm.currentTarget) :=
  vault_message_preserves_conserved config hfork memoryWf run conserved

example {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (reach : BlockChain.ReachUsing cfg deployed future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, PairTraceRealizes root steps future ∧
      (PairBacked vault (future.state.getStor vault) (future.state.getStor wethAccount) ∨
        ∃ r ∈ steps, 0 < r.step.debitAmount) :=
  pair_reachable_backed_or_debit root reach hcov

example {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork)
    {timestamp : Nat} {rules : ForkRules} (rulesAt : cfg.rulesAt timestamp = .ok rules) :
    PairStable vault rules future.state :=
  pair_reachable_stable root realizes collision hcov rulesAt

example {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    {steps : List (PairStepRecord vault)} {future : BlockChain}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    PairBacked vault (future.state.getStor vault) (future.state.getStor wethAccount) ∧
      State.Inv wethAccount future.state :=
  pair_reachable_backed root realizes collision hcov

example {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    PairBacked vault (future.state.getStor vault) (future.state.getStor wethAccount) ∧
      State.Inv wethAccount future.state :=
  pair_history_backed root history collision hcov

example {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork)
    {timestamp : Nat} {rules : ForkRules} (rulesAt : cfg.rulesAt timestamp = .ok rules) :
    PairStable vault rules future.state :=
  pair_history_stable root history collision hcov rulesAt

example (vault : Adr) (frame : Exec.Frame)
    (weth : Blanc.Exec.Frame.exactInvocation Blanc.weth wethAccount wethAccount frame)
    (fresh : Exec.FreshEntry frame.sevm frame.pre)
    (callerNotVault : frame.sevm.caller ≠ vault) :
    (Stor.rest (Devm.getStor frame.post wethAccount) vault =
        Stor.rest (Devm.getStor frame.pre wethAccount) vault) ∨
      (∃ (source : Adr) (wad : B256), source ≠ vault ∧ 0 < wad.toNat ∧
        Transfer (Stor.rest (Devm.getStor frame.pre wethAccount)) source wad
          vault (Stor.rest (Devm.getStor frame.post wethAccount))) ∨
      (∃ call : WethAllowanceInvocation, call.approval = false ∧
        call.sevm = frame.sevm ∧ call.pre = frame.pre ∧
        call.post = frame.post ∧
        Sevm.argWord call.sevm 0 = vault.toB256 ∧
        call.pair? = some (vault.toB256, call.sevm.caller.toB256)) ∨
      (∃ callPre callPost : Devm,
        Stor.rest (Devm.getStor callPre wethAccount) vault =
            Stor.rest (Devm.getStor frame.pre wethAccount) vault ∧
          Ninst.Run frame.sevm callPre Ninst.call callPost ∧
          Devm.getStor frame.post = Devm.getStor callPost) :=
  wethFrame_vaultRow_classified vault frame weth fresh callerNotVault

example {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault) {steps : List (PairStepRecord vault)}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault) :
    ∃ path : FourQuote.RealizedPath vault,
      path.steps = PairStepRecord.fourQuoteSteps steps ∧
      path.snapshotAt 0 = ⟨0, 0⟩ ∧
      path.snapshotAt path.steps.length = FourQuote.stateSnapshot vault future.state ∧
      path.xAt 0 = 1 ∧
      path.dAt 0 = Blanc.ProrataWethVault.offsetN ∧
      path.xAt path.steps.length * (∏ j ∈ Finset.range path.steps.length, path.dAt j) =
        (∏ j ∈ Finset.Icc 1 path.steps.length, path.dAt j) +
          (∑ i ∈ Finset.range path.steps.length,
            path.roundingAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
          (∑ i ∈ Finset.range path.steps.length,
            path.retainedAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
          ∑ i ∈ Finset.range path.steps.length,
            path.creditAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j) :=
  pair_realized_dust_trace_exact root realizes collision

example {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, PairTraceRealizes root steps future ∧ PairLedgerFaithful vault history steps ∧
    ∃ path : FourQuote.RealizedPath vault,
      path.steps = PairStepRecord.fourQuoteSteps steps ∧
      path.snapshotAt 0 = ⟨0, 0⟩ ∧
      path.snapshotAt path.steps.length = FourQuote.stateSnapshot vault future.state ∧
      path.xAt 0 = 1 ∧
      path.dAt 0 = Blanc.ProrataWethVault.offsetN ∧
      path.xAt path.steps.length * (∏ j ∈ Finset.range path.steps.length, path.dAt j) =
        (∏ j ∈ Finset.Icc 1 path.steps.length, path.dAt j) +
          (∑ i ∈ Finset.range path.steps.length,
            path.roundingAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
          (∑ i ∈ Finset.range path.steps.length,
            path.retainedAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
          ∑ i ∈ Finset.range path.steps.length,
            path.creditAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j) :=
  pair_history_realized_dust_trace_exact root history collision hcov

example {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    {root : PairRoot cfg deployed vault} {coalition : Finset Adr} {victim : Adr}
    {charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution}
    {steps : List (PairStepRecord vault)}
    (trace : PairOpenAttackTrace root coalition victim charge steps future) :
    outA victim charge steps + sharesOut victim steps ≤
      inA victim charge steps + outsideSubsidy victim charge steps + sharesIn victim steps :=
  pair_attacker_open_context trace

example {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    {root : PairRoot cfg deployed vault} {coalition : Finset Adr} {victim : Adr}
    {steps : List (PairStepRecord vault)}
    (trace : PairAttackTrace root coalition victim steps future) :
    outA victim coalitionCharge steps + sharesOut victim steps ≤
      inA victim coalitionCharge steps + sharesIn victim steps :=
  pair_attacker_no_profit trace

example {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    {root : PairRoot cfg deployed vault} {victim : Adr}
    {steps : List (PairStepRecord vault)}
    (realizes : PairTraceRealizes root steps future)
    (collision : NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault)
    {deposit exit : PairStepRecord vault} {v m p : Nat}
    (hmoves : victimMoves victim steps = [deposit, exit])
    (hdeposit : deposit.flow = .inbound victim victim v m true)
    (hexit : exit.flow = .outbound victim victim m p true false) :
    v - p ≤ Nat.div (deposit.pre.balance + 1) (deposit.pre.supply + Blanc.ProrataWethVault.offsetN) + 1 :=
  pair_victim_loss_bound realizes collision hmoves hdeposit hexit

example {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, PairTraceRealizes root steps future ∧ PairLedgerFaithful vault history steps ∧
      ∀ (coalition : Finset Adr) (victim : Adr)
        (charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution),
        victim ∉ coalition →
        (∀ r ∈ steps, ∀ x : Adr, r.provenance.actor = some x → x ≠ victim → x ∈ coalition) →
        VictimSchedule victim steps →
        outA victim charge steps + sharesOut victim steps ≤
          inA victim charge steps + outsideSubsidy victim charge steps + sharesIn victim steps :=
  pair_history_attacker_open_context root history collision hcov

example {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, PairTraceRealizes root steps future ∧ PairLedgerFaithful vault history steps ∧
      ∀ (victim : Adr) (deposit exit : PairStepRecord vault) (v m p : Nat),
        victimMoves victim steps = [deposit, exit] →
        deposit.flow = .inbound victim victim v m true →
        exit.flow = .outbound victim victim m p true false →
        v - p ≤ Nat.div (deposit.pre.balance + 1) (deposit.pre.supply + Blanc.ProrataWethVault.offsetN) + 1 :=
  pair_history_victim_loss_bound root history collision hcov

example :
    ∃ state : PairAttackState Blanc.ProrataWethVault.offsetN,
      PairAttackPath Blanc.ProrataWethVault.offsetN state ∧
        state.inA = 1000001 ∧ state.outA = 500125 ∧ state.outsideSubsidy = 0 ∧
        state.sharesIn = 0 ∧ state.sharesOut = 0 :=
  pair_attack_carrier_inhabited

end Composition.ProrataWethVault

namespace BeaconDeposit

/-! ## Beacon deposit — compiled P1–P6 flagships.

These declaration pins keep the artifact, total behavior partition, public
views, complete retained chronology, and compiled/model bridge in the claims
inventory.  Their exact axiom sets are independently pinned by `check.sh`. -/

example : Prog.compile runtime = some code := code_compile

example : Prog.compile constructorProgram = some constructorInitPrefix :=
  constructorInitPrefix_compile
example {msg : Msg} {benv : Benv} {codeAddress : Adr}
    (sevm : Sevm) (base : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (s' : Acc) (ev : DepositEvent)
    (stor : Stor) (keys : KeySet) (countCost n G : Nat)
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hcodeAddress : msg.codeAddress = some codeAddress)
    (hnotPrecompile :
      decide (benv.stat.rules.isPrecomp codeAddress) = false)
    (hsevm : sevm = initSevm (msg.withBenv benv))
    (hbase : base = initDevm (msg.withBenv benv))
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hOk : deposit Bytes.sha256
      (accOfStor (Devm.getStor base sevm.currentTarget))
      pubkey withdrawalCredentials signature depositDataRoot
      sevm.value.toNat = .ok (s', ev))
    (hstor : Devm.getStor
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1))
      sevm.currentTarget = stor)
    (hkeys :
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor
            (Devm.getStor base sevm.currentTarget)).count + 1)).accessedStorageKeys =
        keys)
    (hcount : sstoreCost sevm
      (afterSload sevm base depositCountSlot) depositCountSlot
      (Nat.toB256
        (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) =
      countCost)
    (hheight : n < 32)
    (hfirst : FirstLive
      ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) n)
    (hselector : Sevm.selector sevm = depositSelector)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot)
    (hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys) < 2 ^ 256)
    (hcountSentry : gCallStipend <
      ((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 14 + countCost)
    (hreconstructBound :
      ((((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 38 + countCost) + 59) +
        1762 < 2 ^ 256)
    (hcode : sevm.code.toList = code)
    (hgasEntry : base.gasLeft =
      depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
        ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1)
        countCost G) :
    ∃ settled,
      processMessage msg = .ok settled ∧
        settled.stack = [] ∧
        settled.gasLeft = G ∧
        settled.logs = base.logs ++
          [depositEventLog sevm.currentTarget ev] ∧
        CanonicalDepositEventData ev
          (depositEventLog sevm.currentTarget ev).data ∧
        stor =
          (Devm.getStor base sevm.currentTarget).set depositCountSlot
            (Nat.toB256
              (accOfStor
                (Devm.getStor base sevm.currentTarget)).count + 1) ∧
        (∀ a, Devm.getStor settled a =
          if a = sevm.currentTarget then
            stor.set (branchSlot n)
              (accumulatedNode Bytes.sha256 (accOfStor stor).branch
                0 n depositDataRoot)
          else Devm.getStor base a) ∧
        (∀ a, settled.getCode a = base.getCode a) ∧
        settled.accessedAddresses = base.accessedAddresses ∧
        settled.output = base.output ∧
        settled.error = base.error ∧
        some sevm.code.toList = Prog.compile runtime :=
  deposit_success_settled_effects sevm base hfork pubkey withdrawalCredentials signature
    depositDataRoot s' ev stor keys countCost n G htransfer hcodeAddress hnotPrecompile hsevm hbase
    hdataBound hdec hOk hstor hkeys hcount hheight hfirst hselector hnodeleg hwarm hpre hdepth
    hstatic hbranchSentry hbound hcountSentry hreconstructBound hcode hgasEntry

example {sevm : Sevm} {base : Devm} {state : Acc}
    (hfork : CoveredFork sevm.benvStat.fork)
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {G : Nat} {reason : Reason}
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hcountBound : state.count < 2 ^ 256)
    (hselector : Sevm.selector sevm = depositSelector)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hcountValue : base.getStorVal sevm.currentTarget depositCountSlot =
      Nat.toB256 state.count)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hrootBound :
      (G + depositPostHashErrorGuardCost .depositDataRootMismatch + 18) +
        1762 < 2 ^ 256)
    (hcapBound :
      (G + depositPostHashErrorGuardCost .merkleTreeFull + 46) +
        1762 < 2 ^ 256)
    (herror : deposit Bytes.sha256 state pubkey withdrawalCredentials
      signature depositDataRoot sevm.value.toNat = .error reason)
    (hcode : sevm.code.toList = code) :
    ∃ runtimeCost post,
      ∃ execution : Exec 0 sevm
          (base.setMach ⟨[], Mem.empty, G + runtimeCost, base.stateGas⟩)
          (.error (.revert, post)),
        Prog.RunCompiledTo sevm
            (base.setMach ⟨[], Mem.empty, G + runtimeCost, base.stateGas⟩)
            runtime (.error (.revert, post)) ∧
          post.output = errorData (reasonString reason) ∧
          Exec.NoRawSstore execution ∧
          Exec.retainedStorageWrites execution = [] ∧
          Exec.retainedStorageEffectTriples execution = [] ∧
          some sevm.code.toList = Prog.compile runtime := by
  simpa only [DepositPublicErrorWitness] using
    deposit_error_runCompiledTo hfork hnonempty hdataBound hcountBound hselector hdec
      hcountValue hnodeleg hwarm hpre hdepth hstatic hrootBound hcapBound herror
      hcode

example (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hselector : Sevm.selector sevm = depositSelector)
    (hbad : ¬ DepositAbiStructureDecodable sevm.data)
    (hcode : sevm.code.toList = code) :
    ∃ failure : DepositAbiFailure,
      DepositAbiFailure.Holds sevm.data failure ∧
      ∃ execution : Exec 0 sevm
          (base.setMach
            ⟨[], Mem.empty, G + depositMalformedRuntimeGas failure, base.stateGas⟩)
          (.error (.revert,
            (base.setMach
              ⟨failure.finalStack sevm.data,
                failure.finalMemory sevm.data, G, base.stateGas⟩).withOutput [])),
        Prog.RunCompiledTo sevm
            (base.setMach
              ⟨[], Mem.empty, G + depositMalformedRuntimeGas failure, base.stateGas⟩)
            runtime
            (.error (.revert,
              (base.setMach
                ⟨failure.finalStack sevm.data,
                  failure.finalMemory sevm.data, G, base.stateGas⟩).withOutput [])) ∧
          Exec.NoRawSstore execution ∧
          Exec.retainedStorageWrites execution = [] ∧
          Exec.retainedStorageEffectTriples execution = [] ∧
          some sevm.code.toList = Prog.compile runtime :=
  deposit_malformed_noRawSstore sevm base G hnonempty hdataBound hselector
    hbad hcode
example (sevm : Sevm) (base : Devm) (G : Nat) (selector : B256)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hselector : Sevm.selector sevm = selector)
    (hmiss : selector ∉ beaconSelectors)
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach
          ⟨[], Mem.empty, G + unmatchedSelectorRuntimeGas selector, base.stateGas⟩)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩).withOutput [])),
      Prog.RunCompiledTo sevm
        (base.setMach
          ⟨[], Mem.empty, G + unmatchedSelectorRuntimeGas selector, base.stateGas⟩)
        runtime
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩).withOutput [])) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      Exec.retainedStorageEffectTriples execution = [] ∧
      some sevm.code.toList = Prog.compile runtime :=
  unmatched_selector_noRawSstore sevm base G selector hnonempty hselector
    hmiss hcode

example (sevm : Sevm) (base : Devm) (G : Nat)
    (hdataLength : 36 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = supportsInterfaceSelector)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      ∃ execution : Exec 0 sevm
          (base.setMach
            ⟨[], Mem.empty, G + supportsInterfaceRuntimeGas, base.stateGas⟩)
          (.ok post),
        Prog.RunCompiledTo sevm
            (base.setMach
              ⟨[], Mem.empty, G + supportsInterfaceRuntimeGas, base.stateGas⟩)
            runtime (.ok post) ∧
        post.gasLeft = G ∧
        Devm.output post = abiBoolReturn (supportsInterfaceArg sevm) ∧
        Devm.WorldEq base post ∧
        post.logs = base.logs ∧
        Exec.NoRawSstore execution ∧
        Exec.retainedStorageWrites execution = [] ∧
        Exec.retainedStorageEffectTriples execution = [] ∧
        some sevm.code.toList = Prog.compile runtime :=
  supportsInterface_runCompiled_noRawSstore sevm base G hdataLength
    hdataBound hvalue hselector hcode
example (sevm : Sevm) (base : Devm) (stor : Stor) (count G : Nat)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hstor : Devm.getStor base sevm.currentTarget = stor)
    (hcountValue :
      base.getStorVal sevm.currentTarget depositCountSlot =
        Nat.toB256 count)
    (hcount : count < 2 ^ 32)
    (hzero : ZeroHashesCorrect stor)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound :
      G + 416 +
          rootLoopGas sevm.currentTarget stor 32
            (rootInitialLoopState
              (afterSload sevm base depositCountSlot)
              (Nat.toB256 count)) <
        2 ^ 256)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      ∃ execution : Exec 0 sevm
          (base.setMach
            ⟨[], Mem.empty,
              G + getDepositRootRuntimeGas sevm base stor count, base.stateGas⟩)
          (.ok post),
        Prog.RunCompiledTo sevm
            (base.setMach
              ⟨[], Mem.empty,
                G + getDepositRootRuntimeGas sevm base stor count, base.stateGas⟩)
            runtime (.ok post) ∧
        post.stack = [] ∧
        post.gasLeft = G ∧
        post.output =
          (Acc.root Bytes.sha256 (accOfStor stor)).toBytes ∧
        Bytes.toB256 post.output =
          Acc.root Bytes.sha256 (accOfStor stor) ∧
        post.returnData =
          (Acc.root Bytes.sha256 (accOfStor stor)).toBytes ∧
        (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
        (∀ a, post.getCode a = base.getCode a) ∧
        post.accessedAddresses = base.accessedAddresses ∧
        post.accessedStorageKeys =
          (rootLoopIter sevm.currentTarget stor 32
            (rootInitialLoopState
              (afterSload sevm base depositCountSlot)
              (Nat.toB256 count))).keys ∧
        post.logs = base.logs ∧
        post.error = base.error ∧
        Exec.NoRawSstore execution ∧
        Exec.retainedStorageWrites execution = [] ∧
        Exec.retainedStorageEffectTriples execution = [] ∧
        some sevm.code.toList = Prog.compile runtime :=
  getDepositRoot_zero_runCompiled_noRawSstore sevm base stor count G hfork
    hdataLength hdataBound hvalue hselector hstor hcountValue hcount hzero
    hnodeleg hwarm hpre hdepth hbound hcode
example (sevm : Sevm) (base : Devm) (G : Nat)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hvalue : sevm.value ≠ 0)
    (hselector : Sevm.selector sevm = getDepositRootSelector)
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach
          ⟨[], Mem.empty, G + getDepositRootNonzeroValueRuntimeGas, base.stateGas⟩)
        (.error (.revert,
          (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩).withOutput [])),
      Prog.RunCompiledTo sevm
          (base.setMach
            ⟨[], Mem.empty, G + getDepositRootNonzeroValueRuntimeGas, base.stateGas⟩)
          runtime
          (.error (.revert,
            (base.setMach ⟨[], Mem.empty, G, base.stateGas⟩).withOutput [])) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      Exec.retainedStorageEffectTriples execution = [] ∧
      some sevm.code.toList = Prog.compile runtime :=
  getDepositRoot_nonzero_value_runCompiledTo_noRawSstore
    sevm base G hnonempty hvalue hselector hcode
example (sevm : Sevm) (base : Devm) (word : B256) (G : Nat)
    (hdataLength : 4 ≤ sevm.data.length)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = getDepositCountSelector)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hwarm :
      ⟨sevm.currentTarget, depositCountSlot⟩ ∈ base.accessedStorageKeys)
    (hstorage :
      base.getStorVal sevm.currentTarget depositCountSlot = word)
    (hcode : sevm.code.toList = code) :
    ∃ execution : Exec 0 sevm
        (base.setMach
          ⟨[], Mem.empty, G + getDepositCountWarmRuntimeGas, base.stateGas⟩)
        (.ok ((base.setMach
          ⟨[], getDepositCountResultMemory word, G, base.stateGas⟩).withOutput
            (abiDynamicBytesReturn (le64 word.toNat)))),
      Prog.RunCompiledTo sevm
          (base.setMach
            ⟨[], Mem.empty, G + getDepositCountWarmRuntimeGas, base.stateGas⟩)
          runtime
          (.ok ((base.setMach
            ⟨[], getDepositCountResultMemory word, G, base.stateGas⟩).withOutput
              (abiDynamicBytesReturn (le64 word.toNat)))) ∧
      Exec.NoRawSstore execution ∧
      Exec.retainedStorageWrites execution = [] ∧
      Exec.retainedStorageEffectTriples execution = [] ∧
      some sevm.code.toList = Prog.compile runtime :=
  getDepositCount_warm_runCompiled_noRawSstore sevm base word G hdataLength
    hdataBound hvalue hselector hfork hwarm hstorage hcode
example (sevm : Sevm) (base : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (s' : Acc) (ev : DepositEvent)
    (stor : Stor) (keys : KeySet) (countCost n G : Nat)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hOk : deposit Bytes.sha256
      (accOfStor (Devm.getStor base sevm.currentTarget))
      pubkey withdrawalCredentials signature depositDataRoot
      sevm.value.toNat = .ok (s', ev))
    (hstor : Devm.getStor
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1))
      sevm.currentTarget = stor)
    (hkeys :
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor
            (Devm.getStor base sevm.currentTarget)).count + 1)).accessedStorageKeys =
        keys)
    (hcount : sstoreCost sevm
      (afterSload sevm base depositCountSlot) depositCountSlot
      (Nat.toB256
        (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) =
      countCost)
    (hheight : n < 32)
    (hfirst : FirstLive
      ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) n)
    (hselector : Sevm.selector sevm = depositSelector)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbaseError : base.error = none)
    (hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot)
    (hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys) < 2 ^ 256)
    (hcountSentry : gCallStipend <
      ((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 14 + countCost)
    (hreconstructBound :
      ((((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 38 + countCost) + 59) +
        1762 < 2 ^ 256)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      ∃ execution : Exec 0 sevm
          (base.setMach
            ⟨[], Mem.empty,
              depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
                ((accOfStor
                  (Devm.getStor base sevm.currentTarget)).count + 1)
                countCost G, base.stateGas⟩)
          (.ok post),
        Prog.RunCompiledTo sevm
            (base.setMach
              ⟨[], Mem.empty,
                depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
                  ((accOfStor
                    (Devm.getStor base sevm.currentTarget)).count + 1)
                  countCost G, base.stateGas⟩)
            runtime (.ok post) ∧
          Exec.retainedStorageEffectTriples execution =
            [(sevm.currentTarget, depositCountSlot,
                Nat.toB256
                  (accOfStor
                    (Devm.getStor base sevm.currentTarget)).count + 1),
              (sevm.currentTarget, branchSlot n,
                accumulatedNode Bytes.sha256 (accOfStor stor).branch
                  0 n depositDataRoot)] ∧
          some sevm.code.toList = Prog.compile runtime :=
  deposit_success_retainedStorageEffectTriples sevm base hfork pubkey
    withdrawalCredentials signature depositDataRoot s' ev stor keys countCost
    n G hdataBound hdec hOk hstor hkeys hcount hheight hfirst hselector
    hnodeleg hwarm hpre hdepth hstatic hbaseError hbranchSentry hbound
    hcountSentry hreconstructBound hcode
example {sevm : Sevm} {base : Devm}
    (hvalue : sevm.value = 0)
    (hstorage : Devm.getStor base sevm.currentTarget = Stor.empty)
    (hshaCode : getDelegatedCodeAddress (base.getCode 2) = none)
    (hshaWarm : (2 : Adr) ∈ base.accessedAddresses)
    (herror : base.error = none)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hcode : sevm.code.toList = creationCode) :
    ∃ post,
    ∃ execution : Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, constructorProgramGas, base.stateGas⟩) (.ok post),
      post.output = code ∧
      post.error = none ∧
      Devm.getStor post sevm.currentTarget = constructorFinalStorage ∧
      ArtifactInv (Devm.getStor post sevm.currentTarget) [] ∧
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, constructorProgramGas, base.stateGas⟩)
        constructorProgram (.ok post) ∧
      Exec.retainedStorageEffectTriples execution =
        constructorStorageEffectTriples sevm.currentTarget :=
  constructor_success_retainedStorageEffectTriples hvalue hstorage hshaCode
    hshaWarm herror hstatic hdepth hpre hfork hcode
example (sevm : Sevm) (base : Devm)
    (hfork : CoveredFork sevm.benvStat.fork)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (s' : Acc) (ev : DepositEvent)
    (stor : Stor) (keys : KeySet) (countCost n G : Nat)
    (history : List B256)
    (hinvariant : ArtifactInv
      (Devm.getStor base sevm.currentTarget) history)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hOk : deposit Bytes.sha256
      (accOfStor (Devm.getStor base sevm.currentTarget))
      pubkey withdrawalCredentials signature depositDataRoot
      sevm.value.toNat = .ok (s', ev))
    (hstor : Devm.getStor
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1))
      sevm.currentTarget = stor)
    (hkeys :
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor
            (Devm.getStor base sevm.currentTarget)).count + 1)).accessedStorageKeys =
        keys)
    (hcount : sstoreCost sevm
      (afterSload sevm base depositCountSlot) depositCountSlot
      (Nat.toB256
        (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) =
      countCost)
    (hheight : n < 32)
    (hfirst : FirstLive
      ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) n)
    (hselector : Sevm.selector sevm = depositSelector)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot)
    (hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys) < 2 ^ 256)
    (hcountSentry : gCallStipend <
      ((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 14 + countCost)
    (hreconstructBound :
      ((((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 38 + countCost) + 59) +
        1762 < 2 ^ 256)
    (hcode : sevm.code.toList = code) :
    ∃ post,
      Prog.RunCompiled sevm
          (base.setMach
            ⟨[], Mem.empty,
              depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
                ((accOfStor
                  (Devm.getStor base sevm.currentTarget)).count + 1)
                countCost G, base.stateGas⟩)
          runtime post ∧
        ArtifactInv (Devm.getStor post sevm.currentTarget)
          (history ++ [depositDataNode Bytes.sha256 pubkey
            withdrawalCredentials signature
            (le64 (sevm.value.toNat / oneGwei))]) :=
  deposit_success_artifactInv sevm base hfork pubkey withdrawalCredentials signature
    depositDataRoot s' ev stor keys countCost n G history hinvariant hdataBound
    hdec hOk hstor hkeys hcount hheight hfirst hselector hnodeleg hwarm hpre
    hdepth hstatic hbranchSentry hbound hcountSentry hreconstructBound hcode

/-! ## Beacon deposit — P7/P8 deployment and open-history closure. -/

example
    (chainId : UInt64) (base deployed : BlockChain)
    (cb : CanonicalBlock) (txBytes : Bytes)
    (tx : Tx) (sender ca : Adr)
    (hbase : CanonicalDeploymentBase .prague chainId base sender ca)
    (henv : CanonicalBeaconDepositDeploymentBlock chainId base cb
      txBytes tx sender ca)
    (hstep : stateTransitionUsing (ChainConfig.pragueOnly chainId)
      base cb.block = .ok deployed) :
    DeploymentRoot chainId base deployed ca :=
  canonicalDeploymentStep_establishes_root chainId base deployed cb txBytes
    tx sender ca hbase henv hstep

example {chainId : UInt64} {base deployed : BlockChain} {ca : Adr}
    (hroot : DeploymentRoot chainId base deployed ca) :
    ∃ (cb : CanonicalBlock) (txBytes : Bytes) (tx : Tx) (sender : Adr)
      (ctx : PreparedDeploymentContext chainId base cb tx sender ca)
      (post : State) (bout : BlockOutput) (messagePost : State)
      (out : MsgCallOutput) (createPost : Devm),
      CanonicalBeaconDepositDeploymentBlock chainId base cb
        txBytes tx sender ca ∧
      stateTransitionUsing (ChainConfig.pragueOnly chainId)
        base cb.block = .ok deployed ∧
      DeploymentTransactionResult chainId ca ctx post bout ∧
      DirectConstructorMessageResult ca ctx.msg messagePost out ∧
      DirectCreateMessageResult ca ctx.msg createPost ∧
      DirectCreateMessageExecution ca ctx.msg createPost :=
  hroot.constructorOccurrence

example (baseline : List B256) (ca : Adr) :
    (historySpec baseline).SoundAdmitted ca HistoryEntry :=
  historySpec_sound baseline ca

example (baseline : List B256) (ca : Adr) :
    HistoryPreserves baseline ca :=
  historySpec_preserves baseline ca

example
    (chainId : UInt64) {baseline : List B256}
    {checkpoint future : BlockChain} {ca : Adr}
    (reach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      checkpoint future)
    (native : ReachNativeShaAdmitted reach ca)
    (installed :
      some (checkpoint.state.getCode ca).toList = Prog.compile runtime)
    (artifact : ArtifactInv (checkpoint.state.getStor ca) baseline) :
    ∃ suffix,
      ArtifactInv (future.state.getStor ca) (baseline ++ suffix) :=
  pragueOnly_history_extends chainId reach native installed artifact

example
    {chainId : UInt64} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot chainId base deployed ca)
    (reach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      deployed future)
    (native : ReachNativeShaAdmitted reach ca) :
    ∃ suffix,
      ArtifactInv (future.state.getStor ca) suffix ∧
      ((future.state.getStor ca).get depositCountSlot).toNat =
        suffix.length ∧
      (0 < ((future.state.getStor ca).get depositCountSlot).toNat ↔
        suffix ≠ []) ∧
      Acc.root Bytes.sha256 (accOfStor (future.state.getStor ca)) =
        mixedRootOf Bytes.sha256 suffix :=
  root.future_count_root reach native

end BeaconDeposit

namespace Composition.LidoCircuitBreakerTwg

open Blanc.LidoCircuitBreaker

/-! Entry 3: the pinned-target closure for the CircuitBreaker × gateway
composition.  These pins fix the exact public statements — the two ABI
agreements, the specialized bundle, the direct-installation adapter, and the
headline theorem — so a statement change breaks this file while a proof-only
refactor does not. -/

example (duration : B256) :
    LidoTriggerableWithdrawalsGateway.pauseForCalldata duration =
      LidoCircuitBreaker.pauseForCalldata duration :=
  Blanc.Composition.LidoCircuitBreakerTwg.pauseForCalldata_eq duration

example :
    LidoTriggerableWithdrawalsGateway.isPausedCalldata =
      LidoCircuitBreaker.isPausedCalldata :=
  Blanc.Composition.LidoCircuitBreakerTwg.isPausedCalldata_eq

example
    (dp : LidoTriggerableWithdrawalsGateway.DeployParams)
    (circuitBreaker pauser gateway : Adr)
    (different : gateway ≠ circuitBreaker) :
    LidoPinnedPauseTarget circuitBreaker pauser gateway
      (LidoTriggerableWithdrawalsGateway.runtime dp)
      LidoTriggerableWithdrawalsGateway.pausedUntil
      LidoTriggerableWithdrawalsGateway.protectedSurface :=
  Blanc.Composition.LidoCircuitBreakerTwg.gateway_lidoPinnedPauseTarget dp
    circuitBreaker pauser gateway different

example
    {fs : List Func} {sevm : Sevm} {entry final : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    {target : Adr} {duration : B256}
    {dp : LidoTriggerableWithdrawalsGateway.DeployParams}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (targetNe : target ≠ sevm.currentTarget)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target = false)
    (installed : entry.getCode target =
      Blanc.Composition.LidoCircuitBreakerTwg.gatewayCode dp)
    (targetWindow : MemWordAt entry (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt entry (durationWord * 32).toNat duration)
    (dynamic : sevm.isStatic = false)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet (.ok final)) :
    LidoPinnedBoundaryExecutions fs sevm entry target
      (LidoTriggerableWithdrawalsGateway.runtime dp) duration (.ok final) :=
  Blanc.Composition.LidoCircuitBreakerTwg.gatewayBoundaryExecutions_of_afterSet_ok hfork h_empty
    h_bubble targetNe nonprecompile installed targetWindow durationWindow dynamic run

example
    {sevm : Sevm} {pre final : Devm} {owner : Adr}
    (hfork : CoveredFork sevm.benvStat.fork)
    {target duration idx0 len0 last0 : B256} {img : Bytes}
    {dp : LidoTriggerableWithdrawalsGateway.DeployParams}
    {ex : Execution}
    (premises : PublicPauseEntryPremises sevm pre owner target duration
      idx0 len0 last0 img
      (Blanc.Composition.LidoCircuitBreakerTwg.gatewayCode dp))
    (targetNe : target.toAdr ≠ sevm.currentTarget)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (publicRun : Prog.RunCompiledTo sevm pre (runtime officialParams) ex)
    (success : ex = .ok final) :
    PublicPausePinnedTargetConclusion sevm pre target duration
      (Blanc.Composition.LidoCircuitBreakerTwg.gatewayCode dp)
      (LidoTriggerableWithdrawalsGateway.runtime dp)
      LidoTriggerableWithdrawalsGateway.pausedUntil ex final :=
  Blanc.Composition.LidoCircuitBreakerTwg.publicPause_gatewayPinnedTarget hfork premises targetNe
    nonprecompile publicRun success

/-! Reachability closure: the finite concrete world now supplies the production
run, exact after-set cut, boundary executions, noninterference and headline
conclusion rather than only the premise bundle above. -/

example :
    ∃ entry successPre final : Devm,
      Prog.RunCompiledTo gatewayPauseWorldSevm gatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm gatewayPauseWorldPre pauseWorldCallee.toB256
          pauseWorldDuration (gatewayCode controlDeployParams) (.ok final) entry ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      PauseSuccessNoninterference gatewayPauseWorldSevm entry successPre ∧
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          gatewayPauseWorldSevm entry pauseWorldCallee
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          pauseWorldDuration (.ok final) ∧
      PublicPauseCommittedOutcomes gatewayPauseWorldSevm gatewayPauseWorldPre
          pauseWorldCallee.toB256 pauseWorldDuration
          (gatewayCode controlDeployParams) (.ok final) ∧
      PublicPausePinnedTargetConclusion gatewayPauseWorldSevm
          gatewayPauseWorldPre pauseWorldCallee.toB256 pauseWorldDuration
          (gatewayCode controlDeployParams)
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          LidoTriggerableWithdrawalsGateway.pausedUntil (.ok final) final :=
  Blanc.Composition.LidoCircuitBreakerTwg.gatewayPauseWorld_closedPublicPause

end Composition.LidoCircuitBreakerTwg

namespace Composition.LidoCircuitBreakerTwgSentinel

open Blanc.LidoCircuitBreaker
open Blanc.Composition.LidoCircuitBreakerTwg

/-! The second exact pin holds the independently executed infinite-sentinel
world and the final storage projection that rules out modular addition. -/

example :
    ∃ entry successPre final : Devm,
      Prog.RunCompiledTo sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      PublicPauseAfterSetAt
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          pauseWorldCallee.toB256 pauseInfiniteSentinel
          (gatewayCode controlDeployParams) (.ok final) entry ∧
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm successPre pauseSuccess (.ok final) ∧
      PauseSuccessNoninterference
          sentinelGatewayPauseWorldSevm entry successPre ∧
      LidoPinnedBoundaryExecutions
          ((runtime officialParams).main :: (runtime officialParams).aux)
          sentinelGatewayPauseWorldSevm entry pauseWorldCallee
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          pauseInfiniteSentinel (.ok final) ∧
      PublicPauseCommittedOutcomes sentinelGatewayPauseWorldSevm
          sentinelGatewayPauseWorldPre pauseWorldCallee.toB256
          pauseInfiniteSentinel (gatewayCode controlDeployParams) (.ok final) ∧
      PublicPausePinnedTargetConclusion sentinelGatewayPauseWorldSevm
          sentinelGatewayPauseWorldPre pauseWorldCallee.toB256
          pauseInfiniteSentinel (gatewayCode controlDeployParams)
          (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
          LidoTriggerableWithdrawalsGateway.pausedUntil (.ok final) final :=
  Blanc.Composition.LidoCircuitBreakerTwgSentinel.sentinelGatewayPauseWorld_closedPublicPause

example :
    ∃ final : Devm,
      Prog.RunCompiledTo sentinelGatewayPauseWorldSevm sentinelGatewayPauseWorldPre
          (runtime officialParams) (.ok final) ∧
      final.getStorVal pauseWorldCallee
          LidoTriggerableWithdrawalsGateway.resumeSinceSlot =
            pauseInfiniteSentinel :=
  Blanc.Composition.LidoCircuitBreakerTwgSentinel.sentinelGatewayPauseWorld_storesInfiniteSentinel

end Composition.LidoCircuitBreakerTwgSentinel

namespace Drip

/-! ## DRIP — the R1–R4 headline statements.

The frozen DRIP completion design (its §4 row P2)
names one statement pin per R-headline.  Each pin below carries the headline's
exact type and uses the named declaration as its body, so a statement change
breaks this file while a proof-only refactor does not. -/

-- R1: one compiled `drip()` call rescales the index by the runtime's
-- fixed-point `rpow` factor over the elapsed time and stamps the clock.
example {e : Sevm} {entry s r : Devm} {image : Bytes}
    {tail : Stack}
    (frame : Frame image entry s) (hp : tail <<+ s.stack)
    (run : Func.Run (runtime.main :: runtime.aux) e s Drip.drip r) :
    ∃ postChi ret,
      Devm.getStor r e.currentTarget =
        ((Devm.getStor entry e.currentTarget).set chiSlot postChi).set rhoSlot
          e.benvStat.time ∧
      postChi.toNat =
        (Devm.getStorVal entry e.currentTarget chiSlot).toNat *
          Jaune.rpow scale.toNat half.toNat rate.toNat
            (e.benvStat.time -
              Devm.getStorVal entry e.currentTarget rhoSlot).toNat /
          scale.toNat ∧
      ReturnsWord ret r ∧ ret = postChi :=
  drip_compiled_drip frame hp run

-- R1: the certified two-sided error band of the deployed `rpow` tree.
example (k : Nat) :
    scale.toNat ^ (rpowTree half.toNat k).nodes * factorNat k ≤
        rate.toNat ^ k *
            scale.toNat ^ (rpowTree half.toNat k).scaleCount +
          (rpowTree half.toNat k).upperError scale.toNat rate.toNat 0 ∧
      rate.toNat ^ k *
            scale.toNat ^ (rpowTree half.toNat k).scaleCount ≤
        scale.toNat ^ (rpowTree half.toNat k).nodes * factorNat k +
          (rpowTree half.toNat k).lowerError scale.toNat rate.toNat 0 :=
  drip_rpow_certified_band k

-- R1: the exact rounding telescope behind that band.
example (k : Nat) :
    scale.toNat ^ (rpowTree half.toNat k).nodes * factorNat k +
        (rpowTree half.toNat k).exactUnder scale.toNat rate.toNat 0 =
      rate.toNat ^ k *
          scale.toNat ^ (rpowTree half.toNat k).scaleCount +
        (rpowTree half.toNat k).exactOver scale.toNat rate.toNat 0 :=
  drip_rpow_exact_telescope k

-- R2: every configured history of the deployed DRIP is realized by an
-- accounting trace whose call projection is the history's own DRIP calls.
example {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, DripTraceRealizes root coalition steps future ∧
      callKinds steps = history.dripCalls coalition ca :=
  dripTraceRealizes_transcript root coalition history hcov

-- R2: the executed-flow accounting identity, every term a function of the
-- actual history's DRIP calls.
example {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    coalitionUnits coalition ca future.state * chiN (future.state.getStor ca) +
        (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).joinResidue +
        scale.toNat * (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).paid +
        (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).exitResidue =
      (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).accrual +
        scale.toNat * (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).joined :=
  history_transcript_accounting_exact root coalition history hcov

-- R2: the executed-flow balance identity.
example {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) {coalition : Finset Adr}
    {steps : List RealizedStep}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (realizes : DripTraceRealizes root coalition steps future)
    (faithful : callKinds steps = history.dripCalls coalition ca) :
    (future.state.bal ca).toNat +
        (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).allPaid =
      (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).allJoined + Chain.giftSum steps :=
  history_transcript_balance_exact root history realizes faithful

-- R3: a successful `drip()` or `join()` leaves no stale index: the clock is
-- stamped to the block time and the index is the fresh value.
example {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (hsel : Sevm.selector sevm = dripSelector ∨
      Sevm.selector sevm = joinSelector) :
    Devm.getStorVal pre sevm.currentTarget rhoSlot ≤ sevm.benvStat.time ∧
      Devm.getStorVal post sevm.currentTarget rhoSlot = sevm.benvStat.time ∧
      (Devm.getStorVal post sevm.currentTarget chiSlot).toNat =
        freshNat (Devm.getStorVal pre sevm.currentTarget chiSlot).toNat
          (sevm.benvStat.time -
            Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat :=
  no_stale_index_success_callback_free exc hcode hnonempty hcanon hsel

-- R3: a successful `exit()` holds the same two equations at its settlement
-- boundary, with the accepted payout the only remaining distance.
example {sevm : Sevm} {pre post : Devm}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code.toList = code)
    (hsel : Sevm.selector sevm = exitSelector)
    (hnonempty : sevm.data.length.toB256 ≠ 0)
    (hcanon : pre.memory = Mem.empty)
    (hfork : CoveredFork sevm.benvStat.fork) :
    Devm.getStorVal pre sevm.currentTarget rhoSlot ≤ sevm.benvStat.time ∧
      ∃ callPre callPost guardPost returnPre,
        (Devm.getStor callPre sevm.currentTarget).get rhoSlot =
            sevm.benvStat.time ∧
          ((Devm.getStor callPre sevm.currentTarget).get chiSlot).toNat =
            freshNat (Devm.getStorVal pre sevm.currentTarget chiSlot).toNat
              (sevm.benvStat.time -
                Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat ∧
          AcceptedPayout sevm
            ((B256.rpow scale half rate
                  (sevm.benvStat.time -
                    Devm.getStorVal pre sevm.currentTarget rhoSlot).toNat *
                Devm.getStorVal pre sevm.currentTarget chiSlot / scale) *
              Sevm.dataWord sevm (32 * 0 + 4) / scale)
            callPre callPost guardPost returnPre ∧
          Devm.getStor post = Devm.getStor callPost :=
  no_stale_index_settlement_exit exc hcode hsel hnonempty hcanon hfork

-- R3: the executed-flow entitlement bound.
example {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    (transcriptTally scale.toNat freshNat scale.toNat 0
        (history.dripCalls coalition ca)).paid ≤
      (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).joined +
        (transcriptTally scale.toNat freshNat scale.toNat 0
          (history.dripCalls coalition ca)).accrual / scale.toNat :=
  history_transcript_entitlement root coalition history hcov

-- R3: two realized histories of pure `drip()` segments with the same total
-- elapsed time end with indices within the certified segment drift.
example {cfg : ChainConfig} {base deployed : BlockChain} {ca : Adr}
    {futureL futureR : BlockChain}
    (root : DeploymentRoot cfg base deployed ca) (coalition : Finset Adr)
    (historyL : ExecutionTrace.ConfiguredHistoryTrace cfg deployed futureL)
    (historyR : ExecutionTrace.ConfiguredHistoryTrace cfg deployed futureR)
    {left right : List Nat}
    (callsL : historyL.dripCalls coalition ca = left.map Kind.drip)
    (callsR : historyR.dripCalls coalition ca = right.map Kind.drip)
    (sameElapsed : left.sum = right.sum)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    natDistance (chiN (futureL.state.getStor ca)) (chiN (futureR.state.getStor ca)) ≤
      max (segmentDriftForward scale.toNat half.toNat rate.toNat scale.toNat left right)
          (segmentDriftForward scale.toNat half.toNat rate.toNat scale.toNat right left) :=
  realized_segment_certified root coalition historyL historyR callsL callsR sameElapsed hcov

-- R4: every configured history keeps the clock-paired invariant at its last
-- block's timestamp.
example {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg deployed future)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∀ t, future.blocks.getLast?.map (·.header.timestamp) = some t →
      ClockInv (chiN (deployed.state.getStor ca)) (rhoN (deployed.state.getStor ca))
        t (future.state.getStor ca) :=
  history_clockInv root history hcov

-- R4: the index and the clock never fall along a realized trace.
example {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    {coalition : Finset Adr} {steps : List RealizedStep}
    (realizes : DripTraceRealizes root coalition steps future) :
    chiN (deployed.state.getStor ca) ≤ chiN (future.state.getStor ca) ∧
      rhoN (deployed.state.getStor ca) ≤ rhoN (future.state.getStor ca) :=
  history_chi_rho_mono root realizes

end Drip

end Blanc

/-!
Deployed-bytecode claim map headlines: one exact statement pin per required headline of
`scripts/check-deployed-claim-map.py`, each written in the namespace and with the `open`s of the
module that states it, so every name resolves as it does there.  A change to any headline statement
breaks this file; a proof-only change does not.
-/

namespace Blanc.Lift.Weth9
open Jaune
open Blanc
open Blanc.Lift
open Blanc.ExecutionTrace

-- WETH9: weth9_history_footprint
example {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = weth9Sem.image ∧
      ∃ K : Key → Prop, (∀ k, K k → K₀ k ∨ k ∈ historyTouchedKeys ca trace) ∧
        FootInv K (future.state.getStor ca) (future.state.bal ca) :=
  weth9_history_footprint trace installed sumNof initial fresh

end Blanc.Lift.Weth9

namespace Blanc.Lift.Weth9
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- WETH9: weth9_history_committed
example {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = weth9Sem.image ∧ SumNof future.state.bal ∧
      FootInv (historyKeyUniverse ca trace K₀) (future.state.getStor ca) (future.state.bal ca) ∧
      (ledger K₀ (checkpoint.state.getStor ca)).run
          (replayCalls (committedInvocations ca trace)) =
        some (ledger (historyKeyUniverse ca trace K₀) (future.state.getStor ca)) ∧
      ∃ s : State,
        (State.mk (ledger K₀ (checkpoint.state.getStor ca)) (checkpoint.state.bal ca).toNat).run
            (replayCalls (committedInvocations ca trace)) = some s ∧
          s.ledger = ledger (historyKeyUniverse ca trace K₀) (future.state.getStor ca) ∧
          s.Backed :=
  weth9_history_committed trace installed sumNof initial fresh

end Blanc.Lift.Weth9

namespace Blanc.Lift.Weth9
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

-- WETH9: weth9_tx_withdraw
example
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E ca : Adr} {wad : B256}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat} {U : Key → Prop}
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some ca) [])
    (hvalue : tx.value = 0) (hdata : tx.data = withdrawCalldata wad)
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hgas : withdrawIntrinsicGas wad + withdrawFrameGas wad + 811 ≤ tx.gas)
    (hcap : tx.gas ≤ 16777216)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce) (hnonceMax : tx.nonce ≠ UInt64.max)
    (hnocode : (benv.state.getCode E).size = 0)
    (hfunds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat)
    (hprecE : benv.stat.rules.isPrecomp E = false) (hprecCa : benv.stat.rules.isPrecomp ca = false)
    (hcode : benv.state.getCode ca = code)
    (hinv : FootInv U (benv.state.getStor ca) (benv.state.bal ca)) (hholder : U (.bal E))
    (hbal : wad ≤ (benv.state.getStor ca).get (balSlot E))
    (hcbE : benv.stat.coinbase ≠ E) (hcbCa : benv.stat.coinbase ≠ ca) :
    ∃ (st : Jaune.State) (bout' : BlockOutput), processTransaction benv bout tx index = .ok (st, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad ∧
      st.getStor ca = (benv.state.getStor ca).set (balSlot E)
        ((benv.state.getStor ca).get (balSlot E) - wad) ∧
      (∀ a, a ≠ ca → st.getStor a = benv.state.getStor a) ∧
      (st.get E).nonce = tx.nonce + 1 ∧
      (st.get E).bal = benv.state.bal E -
          (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 + wad +
        ((tx.gas - withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad) *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 ∧
      (st.get ca).bal = benv.state.bal ca - wad ∧
      ((benv.state.bal E).toNat + wad.toNat < 2 ^ 256 →
        (st.get E).bal.toNat + withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) =
          (benv.state.bal E).toNat + wad.toNat) :=
  weth9_tx_withdraw hfork htype hvalue hdata hchain hprio hbase hgas hcap hroom hrecover hnonce hnonceMax hnocode hfunds hprecE hprecCa hcode hinv hholder hbal hcbE hcbCa

end Blanc.Lift.Weth9

namespace Blanc.Lift.Weth9.Creation
open Jaune Blanc.Lift Blanc.ForkUniform

-- WETH9: weth9_deploy_covered
example (f : Fork) (hf : CoveredFork f) :
    weth9Address = computeContractAddress deployer 446 ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode weth9Address).toList = Blanc.Lift.Weth9.code.toList ∧
      Devm.getStor post weth9Address = deployedStor :=
  weth9_deploy_covered f hf

end Blanc.Lift.Weth9.Creation

namespace Blanc.Lift.Weth9.Creation
open Jaune

-- WETH9: weth9_deploy_init_covered
example (f : Fork) (hf : CoveredFork f) :
    weth9Address = computeContractAddress deployer 446 ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode weth9Address).toList = Blanc.Lift.Weth9.code.toList ∧
      ∀ b : B256, FootInv (fun _ => False) (Devm.getStor post weth9Address) b :=
  weth9_deploy_init_covered f hf

end Blanc.Lift.Weth9.Creation

namespace Blanc.Lift.BeaconDeposit
open Jaune Blanc Blanc.ExecutionTrace

-- Beacon deposit: configuredHistory_solInv_sys
example {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodes ca trace) :=
  configuredHistory_solInv_sys trace systemInstalled systemNoAuthority systemNoFrame checkpointEmpty noAuthority noFrame installed invariant

end Blanc.Lift.BeaconDeposit

namespace Blanc.Lift.BeaconDeposit
open Jaune Blanc Blanc.ExecutionTrace

-- Beacon deposit: configuredHistory_root_sys
example {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (systemInstalled : SystemCodeInstalled checkpoint.state)
    (systemNoAuthority : ∀ p ∈ systemContracts, trace.NoAuthorityAt p.1)
    (systemNoFrame : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1)
    (checkpointEmpty : checkpoint.state.getCode 2 = ByteArray.empty)
    (noAuthority : trace.NoAuthorityAt 2)
    (noFrame : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ 2)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    BeaconDeposit.Acc.root Bytes.sha256 (solAcc (future.state.getStor ca)) =
      BeaconDeposit.mixedRootOf Bytes.sha256 (initialHistory ++ committedNodes ca trace) :=
  configuredHistory_root_sys trace systemInstalled systemNoAuthority systemNoFrame checkpointEmpty noAuthority noFrame installed invariant

end Blanc.Lift.BeaconDeposit

namespace Blanc.Lift.BeaconDeposit.Creation
open Jaune Blanc.BeaconDeposit Blanc.Lift.BeaconDeposit Blanc.ForkUniform

-- Beacon deposit: beacon_deploy_covered
example (f : Fork) (hf : CoveredFork f) :
    depositAddress = computeContractAddress deployer 0 ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode depositAddress).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (Devm.getStor post depositAddress) [] :=
  beacon_deploy_covered f hf

end Blanc.Lift.BeaconDeposit.Creation

namespace Blanc.Lift.Curve3Crv
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Curve 3Crv: c3crv_history_committed_derived
example {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initial : Blanc.Curve3Crv.State}
    {initialKeys : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = c3crvSem.image)
    (invariant : VyInv (checkpoint.state.getStor ca) initial initialKeys)
    (fresh : FreshKeys initialKeys (historyTouchedKeys ca trace)) :
    some (future.state.getCode ca).toList = c3crvSem.image ∧
      ∃ s, InvRun initial (committedInvocations ca trace) s ∧
        runInvocations initial (committedInvocations ca trace) = some s ∧
        VyInv (future.state.getStor ca) s
          (Key.extend initialKeys (invocationKeys (committedInvocations ca trace))) ∧
        Blanc.Curve3Crv.Conserved s :=
  c3crv_history_committed_derived trace installed invariant fresh

end Blanc.Lift.Curve3Crv

namespace Blanc.Lift.Curve3Crv
open Jaune
open Blanc.Curve3Crv (Call)

-- Curve 3Crv: c3crv_frame_refines
example {sevm : Sevm} {pre post : Devm} {s : Curve3Crv.State}
    {K : Key → Prop}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256) (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (houtput : pre.output = [])
    (hinv : VyInv (Devm.getStor pre sevm.currentTarget) s K)
    (hfresh : FreshKeys K (callKeys sevm.caller (decodeCall sevm)))
    (exc : Exec 0 sevm pre (.ok post)) :
    (IsWriter (decodeCall sevm) →
      ∃ ow : Option B256, (∀ w, ow = some w → OwnerAnswer sevm pre s.minter w) ∧
        ∃ o, Curve3Crv.step (c3ctx sevm ow) (decodeCall sevm) s = .ok o ∧
          VyInv (Devm.getStor post sevm.currentTarget) o.1
            (Key.extend K (callKeys sevm.caller (decodeCall sevm))) ∧
          (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
          post.logs = pre.logs ++ o.2.1.map (eventLog sevm.currentTarget) ∧
          RetOut post.output o.2.2) ∧
    (¬ IsWriter (decodeCall sevm) →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs ∧
        ∃ o, Curve3Crv.step (c3ctx sevm none) (decodeCall sevm) s = .ok o ∧
          RetOut post.output o.2.2) :=
  c3crv_frame_refines hcode hfork hcd hstack hmem houtput hinv hfresh exc

end Blanc.Lift.Curve3Crv

namespace Blanc.Lift.Curve3Crv.Creation
open Jaune Blanc.Lift Blanc.Lift.Curve3Crv Blanc.ForkUniform

-- Curve 3Crv: curve_deploy_covered
example (f : Fork) (hf : CoveredFork f) :
    tokenAddress = computeContractAddress deployer 42 ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      Devm.getStor post tokenAddress = deployedStor deployer.toB256 ∧
      VyInv (Devm.getStor post tokenAddress) (curveDeployedState deployer) (fun _ => False) :=
  curve_deploy_covered f hf

end Blanc.Lift.Curve3Crv.Creation

namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace
open scoped BigOperators

-- Lido CircuitBreaker: lido_history_l1_l3
example
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca (lidoEntry lidoA))
    (hcode : some (checkpoint.state.getCode ca).toList = lidoSpec.sem.image)
    (hzero : RegistryZeroRaw (checkpoint.state.getStor ca)) :
    ∃ entries,
      (∀ {t : B256}, canonicalAddress t →
        (addressSlotReadWord ((future.state.getStor ca).get (mapSlot t 3)) ≠ 0 ↔
          t ∈ entries.map Prod.fst) ∧
        ((future.state.getStor ca).get (mapSlot t 4) ≠ 0 ↔
          t ∈ entries.map Prod.fst) ∧
        ∀ index pauser, findEntry entries t = some (index, pauser) →
          addressSlotReadWord ((future.state.getStor ca).get (mapSlot t 3)) = pauser ∧
          (future.state.getStor ca).get (mapSlot t 4) = Nat.toB256 (index + 1) ∧
          addressSlotReadWord ((future.state.getStor ca).get (registryArraySlot index)) = t) ∧
      (∀ p, canonicalAddress p →
        (future.state.getStor ca).get (mapSlot p 6) = Nat.toB256 (assignmentCount entries p)) ∧
      (future.state.getStor ca).get (mapSlot 0 6) = 0 ∧
      (∑ p ∈ (entries.map Prod.snd).toFinset,
        ((future.state.getStor ca).get (mapSlot p 6)).toNat) = entries.length ∧
      (future.state.getStor ca).get 5 = Nat.toB256 entries.length :=
  lido_history_l1_l3 trace admitted hcode hzero

end Blanc.Lift.LidoCircuitBreakerDeployed

namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace

-- Lido CircuitBreaker: lido_history_l2_committed
example
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca (lidoEntry lidoA))
    (inv : lidoSpec.StateInv ca checkpoint.state)
    (frame : Exec.Frame) (member : frame ∈ trace.settledFrames)
    (target : frame.sevm.currentTarget = ca) (nonstatic : frame.sevm.isStatic = false)
    (hsig : Sevm.dataWord frame.sevm 0 >>> 224 = selector "registerPauser" [.address, .address])
    (hnp0 : Sevm.dataWord frame.sevm 36 = 0) :
    ∃ entries, RegistryWitness (solRegistryStorage (Devm.getStor frame.pre ca)) entries ∧
      L2Post entries (Sevm.dataWord frame.sevm 4) (Devm.getStor frame.post ca) :=
  lido_history_l2_committed trace admitted inv frame member target nonstatic hsig hnp0

end Blanc.Lift.LidoCircuitBreakerDeployed

namespace Blanc.Lift.LidoCircuitBreakerDeployed.Creation
open Jaune Blanc Blanc.Lift Blanc.LidoCircuitBreaker Blanc.ForkUniform

-- Lido CircuitBreaker: lido_deploy_covered
example (f : Fork) (hf : CoveredFork f) :
    breakerAddress = computeContractAddress deployer 0 ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode breakerAddress).toList = Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
      Devm.getStor post breakerAddress = deployedStor :=
  lido_deploy_covered f hf

end Blanc.Lift.LidoCircuitBreakerDeployed.Creation

namespace Blanc.Lift.LidoCircuitBreakerDeployed.Creation
open Jaune Blanc Blanc.Lift Blanc.LidoCircuitBreaker Blanc.ForkUniform

-- Lido CircuitBreaker: lido_deploy_init_covered
example (f : Fork) (hf : CoveredFork f)
    (hfa0 : ForeignApart 0 0) (hfa1 : ForeignApart 0 1) :
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode breakerAddress).toList = Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
      RegistryZeroRaw (Devm.getStor post breakerAddress) ∧
      lidoSpec.StateInv breakerAddress post.state :=
  lido_deploy_init_covered f hf hfa0 hfa1

end Blanc.Lift.LidoCircuitBreakerDeployed.Creation

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed
open Jaune Blanc.LockExclusion
open Jaune.Exec.Deriv (ParentPrefix)

-- Vyper V+: vplus_exclusion
example {sevm : Sevm} {pre : Devm} {out : Execution}
    (R : Exec 0 sevm pre out) (hfork : CoveredFork sevm.benvStat.fork) {P : Adr}
    (hP : pre.getCode P = forwarderCode curvePlainImpl847e ∨ pre.getCode P = code)
    (hI : pre.getCode curvePlainImpl847e = code)
    (hroot : sevm.currentTarget = P → sevm.code = pre.getCode P)
    (hash : lockL.HashAvoidIn P R)
    {F h c : Exec.Deriv} (hF : F ∈ Exec.rawFrameRoots R)
    (active : ActiveRel P F h) (spawn : Spawns h c)
    {G : Exec.Deriv} (hG : G ∈ Exec.rawFrameRoots c.exc) :
    ¬ lockL.Enters P G :=
  vplus_exclusion R hfork hP hI hroot hash hF active spawn hG

end Blanc.Lift.VyperNonreentrantDeployed.Fixed

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Jaune.Exec.Deriv (ParentPrefix ParentStep)

-- Vyper V+: vplus_witness_covered
example (g : Fork) (hg : CoveredFork g) :
    (msg0.withFork g).benv.stat.fork = g ∧ (f0.withFork g).enter = .run (e0.withFork g) ∧
    (e0.withFork g).pc = 0 ∧
    (∀ out, Exec 0 (e0.withFork g).sta (e0.withFork g).dyna out → out = .error (.revert, dF)) ∧
    ∃ (out : Execution) (R : Exec 0 (e0.withFork g).sta (e0.withFork g).dyna out)
      (h c G : Exec.Deriv),
      -- the antecedent of `vplus_exclusion`, for `F` the root of `R`
      (⟨0, (e0.withFork g).sta, (e0.withFork g).dyna, out, R⟩ : Exec.Deriv) ∈
        Exec.rawFrameRoots R ∧
      ActiveRel curvePlainImpl847e ⟨0, (e0.withFork g).sta, (e0.withFork g).dyna, out, R⟩ h ∧
      Spawns h c ∧
      -- the premises of `vplus_exclusion_impl`, for this `R`
      CoveredFork (e0.withFork g).sta.benvStat.fork ∧
      (e0.withFork g).dyna.getCode curvePlainImpl847e = code ∧
      ((e0.withFork g).sta.currentTarget = curvePlainImpl847e →
        (e0.withFork g).sta.code = (e0.withFork g).dyna.getCode curvePlainImpl847e) ∧
      lockL.HashAvoidIn curvePlainImpl847e R ∧
      -- the spawn: `remove_liquidity`'s `STATICCALL` of the coin `R`
      h.pc = 0x337a ∧ Ninst.At h.sevm.code h.pc (.exec .staticcall) ∧
      c.sevm.currentTarget = readerAddress ∧ c.sevm.code = Reader.code ∧
      -- the reentry into `get_virtual_price()`, refused
      G ∈ Exec.rawFrameRoots c.exc ∧ CPFrame curvePlainImpl847e code G ∧
      G.sevm.data = [0xbb, 0x7b, 0x8b, 0x80] ∧ G.exn = .error (.revert, dG) ∧
      (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      ¬ lockL.Enters curvePlainImpl847e G :=
  vplus_witness_covered g hg

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Jaune.Exec.Deriv (ParentPrefix ParentStep)

-- Vyper V+: vplus_witness2_covered
example (g : Fork) (hg : CoveredFork g) :
    (msgTop.withFork g).benv.stat.fork = g ∧
    (frameTop.withFork g).enter = .run (eTop.withFork g) ∧ (eTop.withFork g).pc = 0 ∧
    (∀ out, Exec 0 (eTop.withFork g).sta (eTop.withFork g).dyna out → out = .ok dTop) ∧
    ∃ (out : Execution) (R : Exec 0 (eTop.withFork g).sta (eTop.withFork g).dyna out)
      (F h c q G : Exec.Deriv),
      -- the premises of `vplus_exclusion_stethPool`, for this `R`
      CoveredFork (eTop.withFork g).sta.benvStat.fork ∧
      (eTop.withFork g).dyna.getCode curveStethPool847e = forwarderCode curvePlainImpl847e ∧
      (eTop.withFork g).dyna.getCode curvePlainImpl847e = code ∧
      ((eTop.withFork g).sta.currentTarget = curveStethPool847e →
        (eTop.withFork g).sta.code = (eTop.withFork g).dyna.getCode curveStethPool847e) ∧
      lockL.HashAvoidIn curveStethPool847e R ∧
      -- its antecedent: the pool body, active, spawns the receiver with the ETH payment
      F ∈ Exec.rawFrameRoots R ∧ ActiveRel curveStethPool847e F h ∧ Spawns h c ∧
      h.pc = 7427 ∧ Ninst.At h.sevm.code h.pc (.exec .call) ∧
      c.sevm.currentTarget = receiverAddress ∧ c.sevm.code = Receiver.code ∧
      c.sevm.value.toNat = 100 ∧
      -- the reentry through the forwarder, refused at the lock check
      q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = curveStethPool847e ∧
      q.sevm.code = forwarderCode curvePlainImpl847e ∧ G ∈ Exec.rawFrameRoots q.exc ∧
      G ∈ Exec.rawFrameRoots c.exc ∧ CPFrame curveStethPool847e code G ∧
      G.sevm.data = reentryCall ∧ G.exn = .error (.revert, dRe) ∧
      (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) ∧
      ¬ lockL.Enters curveStethPool847e G ∧
      -- the transaction commits
      out = .ok dTop ∧
      ((eTop.withFork g).dyna.getBal curveStethPool847e).toNat = 1000 ∧
      (dTop.getBal curveStethPool847e).toNat = 900 ∧
      ((eTop.withFork g).dyna.getBal receiverAddress).toNat = 0 ∧
      (dTop.getBal receiverAddress).toNat = 100 ∧
      lockAt curveStethPool847e 0 (eTop.withFork g).dyna = (3 : Nat).toB256 ∧
      lockAt curveStethPool847e 0 dTop = (3 : Nat).toB256 :=
  vplus_witness2_covered g hg

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.Witness.Boundary Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree
variable {g : Fork}

-- Vyper V−: vminus_witness_covered
example (g : Fork) (hg : CoveredFork g) :
    ∃ post0 post1 : Devm,
      -- the top-level message call, under `g`
      (msg0.withFork g).benv.stat.fork = g ∧ CoveredFork (msg0.withFork g).benv.stat.fork ∧
      (f0.withFork g).enter = .run (e0.withFork g) ∧
      Nonempty (Exec (e0.withFork g).pc (e0.withFork g).sta (e0.withFork g).dyna (.ok post0)) ∧
      processMessage (msg0.withFork g) = .ok post0 ∧ post0.error = none ∧
      post0.output = word 100 ++ word 100 ∧
      -- (a) frame 1: `P` running the implementation's `remove_liquidity`, spawned by the proxy
      stepN 11 (e0.withFork g) = some (e0_31.withFork g) ∧
      SpawnedBy (e0_31.withFork g).sta (e0_31.withFork g).dyna .delegatecall
        ⟨0, sevm1.withFork g, pre1⟩ ∧
      (sevm1.withFork g).currentTarget = proxyAddress ∧ (sevm1.withFork g).code = code ∧
      (sevm1.withFork g).data = removeCalldata ∧
      Nonempty (Exec 0 (sevm1.withFork g) pre1 (.ok post1)) ∧ post1.error = none ∧
      -- frame 1 takes slot 2 and calls `A` holding it
      storOf pre1.state proxyAddress (2 : Nat).toB256 = 0 ∧
      wrun fs1 (sevm1.withFork g) 339 c0 = .cont cfg339 ∧ Agree cfg339 ∧
      storOf cfg339.devm.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 ∧
      SpawnedBy (sevm1.withFork g) cfg339.devm .call (e2.withFork g) ∧
      (e2.withFork g).sta.currentTarget = attackerAddress ∧
      (e2.withFork g).sta.code = attackerCode ∧
      -- `A` calls `P`; the proxy delegates to the implementation: frame 4
      wrun fs2 (e2.withFork g).sta 24 cc2 = .cont aCall ∧
      SpawnedBy (e2.withFork g).sta aCall.devm .call (e3.withFork g) ∧
      (e3.withFork g).sta.currentTarget = proxyAddress ∧
      (e3.withFork g).sta.code = proxyCode ∧
      stepN 11 (e3.withFork g) = some (e31.withFork g) ∧
      SpawnedBy (e31.withFork g).sta (e31.withFork g).dyna .delegatecall (e4.withFork g) ∧
      (e4.withFork g).sta.currentTarget = proxyAddress ∧ (e4.withFork g).sta.code = code ∧
      (e4.withFork g).sta.data = addCalldata ∧
      -- frame 4 is entered while slot 2 = 1, its own lock (slot 0) free
      storOf e4.dyna.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 ∧
      storOf e4.dyna.state proxyAddress (0 : Nat).toB256 = 0 ∧
      Nonempty (Exec (e4.withFork g).pc (e4.withFork g).sta (e4.withFork g).dyna (.ok post4)) ∧
      -- frame 4 reaches `add_liquidity`'s body with slot 0 taken and slot 2 still held
      (∃ cB : Cfg, wrun fs1 (e4.withFork g).sta 2625 c4 = .cont cB ∧ Agree cB ∧
        cB.f = t_0370_c63 ∧
        storOf cB.devm.state proxyAddress (0 : Nat).toB256 = (1 : Nat).toB256 ∧
        storOf cB.devm.state proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256) ∧
      (storOf post4.state proxyAddress balanceOfASlot.toB256).toNat = 2106 ∧
      storOf post4.state proxyAddress (0 : Nat).toB256 = 0 ∧
      -- (b) the two guards in the deployed bytes: slot 2 and slot 0
      (code.getInst 6900 = some (.next (.push [0x02] (by decide))) ∧
        code.getInst 6902 = some (.next (.reg .sload)) ∧
        code.getInst 6911 = some (.next (.reg .sstore))) ∧
      (code.getInst 88 = some (.next (.push [0x00] (by decide))) ∧
        code.getInst 90 = some (.next (.reg .sload)) ∧
        code.getInst 99 = some (.next (.reg .sstore))) ∧
      (storOf post1.state proxyAddress (2 : Nat).toB256).toNat = 0 ∧
      -- (c) the harm
      (storOf post0.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf post0.state proxyAddress balanceOfASlot.toB256).toNat = 1906 ∧
      (storOf post0.state proxyAddress (26 : Nat).toB256).toNat <
        (storOf post0.state proxyAddress balanceOfASlot.toB256).toNat :=
  vminus_witness_covered g hg

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Witness Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
variable {g : Fork}

-- Vyper V−: vminus_txC_process
example (g : Fork) (hg : CoveredFork g) (bout : BlockOutput)
    (hroom : bout.blockGasUsed + txC.gas ≤ 60000000) :
    txC.gas < 2 ^ 24 ∧
    ∃ (st : State) (bout' : BlockOutput),
      processTransaction (benvPre.withFork g) bout txC 0 = .ok (st, bout') ∧
      (storOf st proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf st proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
      (storOf st proxyAddress (26 : Nat).toB256).toNat <
        (storOf st proxyAddress balanceOfA2Slot.toB256).toNat :=
  vminus_txC_process g hg bout hroom

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- EIP-7002: block_word_fifo
example
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap) :
    BlockWordFifo history block :=
  block_word_fifo history block installed senders authorities avoid systemEmpty init occurrences

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest.DrainControl
open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx FeeCounterexample

-- EIP-7002: systemEmpty_loadBearing_witness
example : SystemEmptyLoadBearing :=
  systemEmpty_loadBearing_witness

end Blanc.Lift.WithdrawalRequest.DrainControl

namespace Blanc.Lift.WithdrawalRequest
open Jaune Blanc.ExecutionTrace

-- EIP-7002: history_checked_system_totality
example {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    {benv : Benv} (state : benv.state = future.state) (fork : CoveredFork benv.stat.fork) :
    processCheckedSystemTransaction benv withdrawalRequestPredeployAddress [] =
      .ok ((systemProtocolPost benv).state, systemProtocolOutput benv) ∧
    (systemProtocolOutput benv).error = none ∧
    (systemProtocolOutput benv).gasLeft = systemTransactionGas - systemProtocolGas benv ∧
    systemProtocolGas benv ≤ 210000 ∧
    (systemProtocolOutput benv).returnData = (systemProtocolPost benv).output ∧
    (systemProtocolOutput benv).refundCounter = (systemProtocolPost benv).refundCounter :=
  history_checked_system_totality history code state fork

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune

-- EIP-7002: word_fee_eq_iff_natFeeDomain
example {excess : B256} {iterations : Nat}
    {output : B256}
    (run : WordFakeExponential.Run excess 17 1 17 0 iterations output)
    (model : Blanc.WithdrawalRequest.State) (excessEq : model.excess = excess.toNat) :
    (output / (17 : B256)).toNat = Blanc.WithdrawalRequest.fee model ↔
      NatFeeDomain excess iterations :=
  word_fee_eq_iff_natFeeDomain run model excessEq

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample
open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx FloodWalk

-- EIP-7002: nat_fee_guarantee_refuted
example : NatFeeGuaranteeRefuted :=
  nat_fee_guarantee_refuted

end Blanc.Lift.WithdrawalRequest.FeeCounterexample

namespace Blanc.Lift.WithdrawalRequest
open Jaune Blanc.ExecutionTrace

-- EIP-7002: history_submission_nat_live
example {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    let fresh := historySubmissionSevm future.state sevm data
    let base := b.withState future.state
    (base.getStorVal withdrawalRequestPredeployAddress 0 = B256.max →
      ∀ gas post, ¬ Nonempty (Exec 0 fresh (St base [] Mem.empty gas) (.ok post))) ∧
    (base.getStorVal withdrawalRequestPredeployAddress 0 ≠ B256.max →
      fakeExp 1 (base.getStorVal withdrawalRequestPredeployAddress 0).toNat 17 ≤
        sevm.value.toNat →
      ∃! result : Nat × B256,
        WordFakeExponential.Run (base.getStorVal withdrawalRequestPredeployAddress 0)
          17 1 17 0 result.1 result.2 ∧
        ∀ G, gCallStipend < G →
          Nonempty (Exec 0 fresh (St base [] Mem.empty
            (G + (1258 + 87 * result.1 + sloadScheduleCost fresh (userSubmissionReads fresh base) +
              submissionStoreGas fresh (afterSload fresh base 0) Mem.empty)))
            (.ok (submissionPost fresh (afterSload fresh base 0) Mem.empty G)))) :=
  history_submission_nat_live history code sevm b data fork user length

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest.Creation
open Jaune Blanc.Lift Blanc.WithdrawalRequest

-- EIP-7002: deploy_initial
example (fork : Fork) (hfork : CoveredFork fork) :
    (deployMsg fork).currentTarget = withdrawalRequestPredeployAddress ∧
    ∃ post, processCreateMessage (deployMsg fork) = .ok post ∧
      post.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      RepresentsStorage (post.getStor withdrawalRequestPredeployAddress).get initial ∧
      post.error = none :=
  deploy_initial fork hfork

end Blanc.Lift.WithdrawalRequest.Creation


/-! The project definitions those headline statements are stated through, where the definition
body is itself the claim, are pinned by unfolding (`Iff.rfl`), and record types by an exact
field-wise equivalence, so a weakened body or an added/removed field fails here. -/

namespace Blanc
open Jaune

-- WETH9 definition: SumNof
example (f : Adr → B256) :
    SumNof f ↔
      (sum f < 2 ^ 256) :=
  Iff.rfl

end Blanc

namespace Blanc.Lift.Weth9.State
open Jaune Blanc

-- WETH9 definition: Backed
example (s : State) :
    Backed s ↔
      (s.ledger.total ≤ s.eth) :=
  Iff.rfl

end Blanc.Lift.Weth9.State

namespace Blanc.Lift.Weth9
open Jaune
open Blanc
open Classical in

-- WETH9 definition: FootInv
example (K : Key → Prop) (s : Stor) (b : B256) :
    FootInv K s b ↔
      (Support K s) ∧
      (KeyInj K) ∧
      (KeyApart K) ∧
      (trackedSum K s ≤ b.toNat) :=
  ⟨fun h => ⟨h.support, h.inj, h.apart, h.backed⟩, fun ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, h2, h3⟩⟩

end Blanc.Lift.Weth9

namespace Blanc.Lift.BeaconDeposit
open Jaune
open Blanc.BeaconDeposit

-- Beacon deposit definition: SolInv
example (stor : Stor) (history : List B256) :
    SolInv stor history ↔
      (SolZeroHashesCorrect stor ∧ Inv Bytes.sha256 (solAcc stor) history) :=
  Iff.rfl

end Blanc.Lift.BeaconDeposit

namespace Blanc.Lift.Curve3Crv
open Jaune
open Blanc.Curve3Crv (Conserved)

-- Curve 3Crv definition: VyInv
example (stor : Stor) (s : Curve3Crv.State) (K : Key → Prop) :
    VyInv stor s K ↔
      (stor.get vyDecimalsSlot = s.decimals) ∧
      (stor.get vySupplySlot = s.totalSupply) ∧
      (stor.get vyMinterSlot = s.minter.toB256) ∧
      (VyStr stor vyNameBase 2 s.name) ∧
      (VyStr stor vySymbolBase 1 s.symbol) ∧
      (∀ k, K k → stor.get k.slot = k.val s) ∧
      (∀ k, ¬ K k → k.val s = 0) ∧
      (∀ x, stor.get x ≠ 0 → x ∈ vyFixedSlots ∨ ∃ k, K k ∧ k.slot = x) ∧
      (∀ k k', K k → K k' → k.slot = k'.slot → k = k') ∧
      (∀ k, K k → k.slot ∉ vyFixedSlots) ∧
      (Conserved s) :=
  ⟨fun h => ⟨h.decimals, h.supply, h.minter, h.name, h.symbol, h.known, h.unknown, h.support, h.inj, h.apart, h.conserved⟩, fun ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ => ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩⟩

end Blanc.Lift.Curve3Crv

namespace Blanc.Curve3Crv
open Jaune

-- Curve 3Crv definition: Conserved
example (s : State) :
    Conserved s ↔
      (s.totalSupply.toNat = sum s.balanceOf) :=
  Iff.rfl

end Blanc.Curve3Crv

namespace Blanc.Lift.Curve3Crv
open Jaune
open Blanc.Curve3Crv (Call Ctx Event Ret)

-- Curve 3Crv definition: OwnerAnswer
example (sevm : Sevm) (b : Devm) (m : Adr) (w : B256) :
    OwnerAnswer sevm b m w ↔
      (∃ out, StaticAnswered sevm b m ownerCalldata out ∧ 32 ≤ out.length ∧
    Bytes.toB256 (out.take 32) = w) :=
  Iff.rfl

end Blanc.Lift.Curve3Crv

namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

-- Lido CircuitBreaker definition: L2Post
example (entries : List Entry) (t : B256) (s : Stor) :
    L2Post entries t s ↔
      (nonzeroCanonicalAddress t ∧
  addressSlotReadWord (s.get (mapSlot t 3)) = 0 ∧
  s.get (mapSlot t 4) = 0 ∧
  (∃ entries', RegistryWitness (solRegistryStorage s) entries' ∧ t ∉ entries'.map Prod.fst) ∧
  match findEntry entries t with
  | some (index, _) =>
      addressSlotReadWord (s.get (registryArraySlot (entries.length - 1))) = 0 ∧
      s.get 5 = Nat.toB256 (entries.length - 1) ∧
      (index + 1 < entries.length →
        addressSlotReadWord (s.get (registryArraySlot index)) = sourceLastTarget entries ∧
        s.get (mapSlot (sourceLastTarget entries) 4) = Nat.toB256 (index + 1)) ∧
      (index + 1 = entries.length → sourceLastTarget entries = t)
  | none =>
      addressSlotReadWord (s.get (registryArraySlot entries.length)) = 0 ∧
      s.get 5 = Nat.toB256 entries.length) :=
  Iff.rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

-- Lido CircuitBreaker definition: RegistryZeroRaw
example (s : Stor) :
    RegistryZeroRaw s ↔
      (s.get 5 = 0 ∧
  ∀ p, canonicalAddress p →
    addressSlotReadWord (s.get (mapSlot p 3)) = 0 ∧
    s.get (mapSlot p 4) = 0 ∧
    s.get (mapSlot p 6) = 0) :=
  Iff.rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

namespace Blanc.LockExclusion
open Jaune
open Jaune.Exec.Deriv

-- Vyper V± definition: CPFrame
example (P : Adr) (code : ByteArray) (F : Exec.Deriv) :
    CPFrame P code F ↔
      (F.pc = 0 ∧ F.sevm.currentTarget = P ∧ F.sevm.code = code) :=
  Iff.rfl

end Blanc.LockExclusion

namespace Blanc.LockExclusion.LockSpec
open Jaune
open Jaune.Exec.Deriv

-- Vyper V± definition: Enters
example (L : LockSpec) (P : Adr) (G : Exec.Deriv) :
    Enters L P G ↔
      (CPFrame P L.code G ∧ ∃ x, ParentPrefix G x ∧ x.pc ∈ L.bodies) :=
  Iff.rfl

end Blanc.LockExclusion.LockSpec

namespace Blanc.LockExclusion.LockSpec
open Jaune
open Jaune.Exec.Deriv

-- Vyper V± definition: HashAvoidIn
example (L : LockSpec) (P : Adr)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    HashAvoidIn L P run ↔
      (∀ G ∈ Exec.rawFrameRoots run, CPFrame P L.code G → HashAvoid L.slot G) :=
  Iff.rfl

end Blanc.LockExclusion.LockSpec

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed
open Jaune Blanc.LockExclusion
open Jaune.Exec.Deriv (ParentPrefix)

-- Vyper V+ definition: ActiveRel
example (P : Adr) (F h : Exec.Deriv) :
    ActiveRel P F h ↔
      (CPFrame P code F ∧ ParentPrefix F h ∧
    ∃ b, ParentPrefix F b ∧ ParentPrefix b h ∧ b.pc ∈ lockMutBodies ∧
      ∀ x, ParentPrefix b x → ParentPrefix x h → x ≠ h → x.pc ∉ lockReleasePcs) :=
  Iff.rfl

end Blanc.Lift.VyperNonreentrantDeployed.Fixed

namespace Blanc.Lift.Witness
open Jaune Blanc.Lift

-- Vyper V− definition: SpawnedBy
example (sevm : Sevm) (devm : Devm) (x : Xinst) (child : Evm) :
    SpawnedBy sevm devm x child ↔
      (∃ f rsm, Xinst.step sevm devm x = .spawn f rsm ∧ f.enter = .run child) :=
  Iff.rfl

end Blanc.Lift.Witness

namespace Blanc.Lift.Witness
open Jaune Blanc.Lift

-- Vyper V− definition: Agree
example (c : Cfg) :
    Agree c ↔
      ((∀ x, x ∈ c.devm.accessedStorageKeys ↔ x ∈ c.keys) ∧
    (∀ a, a ∈ c.devm.accessedAddresses ↔ a ∈ c.adrs) ∧
    (∀ a k, storOf c.devm.state a k = lookupS c.stor a k) ∧
    AcctAgree c.devm.state c.acs) :=
  Iff.rfl

end Blanc.Lift.Witness

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- EIP-7002 definition: BlockWordFifo
example {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post) :
    BlockWordFifo history block ↔
      (∃ past transactionEvents : List WordReplayEvent, ∃ reset : WordReplayEvent,
    WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress)
      ((past ++ transactionEvents) ++ [reset])
      (post.state.getStor withdrawalRequestPredeployAddress) ∧
    past.map WordReplayEvent.frame = history.settledFrames.flatMap balanceFrameObservation ∧
    transactionEvents.map WordReplayEvent.frame =
      block.bodyTrace.transactions.settledFrames.flatMap balanceFrameObservation ∧
    reset.kind = .system ∧
    reset.frame.pre.state = block.bodyTrace.requestBenv.state ∧
    let model := (past ++ transactionEvents).foldl wordModelUpdate initial
    WordHistory initial model (wordModelSubmissions (past ++ transactionEvents))
      (wordModelOutputs initial past) ∧
    RepresentsStorage (block.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get model ∧
    block.bodyTrace.requests.withdrawalOut.returnData = systemOutput model ∧
    block.blockOutput.requests = block.bodyTrace.transactionBout.requests ++
      optionalRequestEntry 0 block.bodyTrace.requests.depositRequests ++
      optionalRequestEntry 1 (systemOutput model) ++
      optionalRequestEntry 2 block.bodyTrace.requests.consolidationOut.returnData ∧
    (optionalRequestEntry 1 block.bodyTrace.requests.withdrawalOut.returnData = [] ↔
      emitted model = []) ∧
    WordHistory initial (Blanc.WithdrawalRequest.system model)
      (wordModelSubmissions ((past ++ transactionEvents) ++ [reset]))
      (wordModelOutputs initial past ++ emitted model) ∧
    (wordModelSubmissions ((past ++ transactionEvents) ++ [reset])).map Submission.entry =
      (wordModelOutputs initial past ++ emitted model) ++
        (Blanc.WithdrawalRequest.system model).queue ∧
    let submissions := wordSubmissionFrames (past ++ transactionEvents)
    submissions.map Prod.fst =
      ((history.settledFrames ++ block.bodyTrace.transactions.settledFrames).flatMap
        submissionFramePayments).map Prod.fst ∧
    submissions.map Prod.fst =
      ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
        submissionFramePayments).map Prod.fst ∧
    (∀ pair ∈ submissions,
      pair.1.sevm.caller = pair.2.caller ∧ pair.1.sevm.data = submissionPayload pair.2) ∧
    submissions.map Prod.snd = (wordModelOutputs initial past ++ emitted model) ++
      (Blanc.WithdrawalRequest.system model).queue ∧
    RepresentsStorage (post.state.getStor withdrawalRequestPredeployAddress).get
      (Blanc.WithdrawalRequest.system model) ∧
    effectiveExcess model ≤ wordOccurrenceCap ∧ model.count ≤ wordOccurrenceCap ∧
    model.head ≤ model.tail ∧ model.tail ≤ wordOccurrenceCap ∧
    model.queue.length = model.tail - model.head ∧
    effectiveExcess model + model.count < 2 ^ 256 ∧ queueBase model.tail + 2 < 2 ^ 256 ∧
    effectiveExcess (Blanc.WithdrawalRequest.system model) ≤ wordOccurrenceCap ∧
    (Blanc.WithdrawalRequest.system model).tail ≤ wordOccurrenceCap ∧
    QueueSlotsSafe model ∧ QueueSlotsSafe (Blanc.WithdrawalRequest.system model)) :=
  Iff.rfl

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- EIP-7002 definition: SystemEmptyLoadBearing
example :
    SystemEmptyLoadBearing ↔
      (∃ (cfg : ChainConfig) (checkpoint pre post : BlockChain)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post),
    SystemCodeInstalled checkpoint.state ∧
    (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress ∧
    (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress ∧
    (∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress) ∧
    checkpoint.state.getCode systemAddress ≠ ByteArray.empty ∧
    RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial ∧
    ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap ∧
    ¬ BlockWordFifo history block) :=
  Iff.rfl

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune

-- EIP-7002 definition: NatFeeDomain
example (excess : B256) (iterations : Nat) :
    NatFeeDomain excess iterations ↔
      (∃ output, ∃ run : FakeExponential.Run excess.toNat
      Blanc.WithdrawalRequest.feeUpdateFraction 1 Blanc.WithdrawalRequest.feeUpdateFraction
      iterations output, FakeExponentialWordCorrespondence.NoWrap run 0) :=
  Iff.rfl

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample
open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx

-- EIP-7002 definition: NatFeeGuaranteeRefuted
example :
    NatFeeGuaranteeRefuted ↔
      (∃ (cfg : ChainConfig) (checkpoint future : BlockChain)
    (trace : ConfiguredHistoryTrace cfg checkpoint future),
    SystemCodeInstalled checkpoint.state ∧
    trace.NoSenderAt systemAddress ∧ trace.NoAuthorityAt systemAddress ∧
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress) ∧
    checkpoint.state.getCode systemAddress = ByteArray.empty ∧
    Blanc.WithdrawalRequest.RepresentsStorage
      (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      Blanc.WithdrawalRequest.initial ∧
    ∃ frame ∈ trace.settledFrames.flatMap balanceFrameObservation,
      ∃ (model : Blanc.WithdrawalRequest.State) (iterations : Nat) (output : B256),
        submissionPaymentFrame frame ∧
        model.excess = ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0).toNat ∧
        WordFakeExponential.Run ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0)
          17 1 17 0 iterations output ∧
        (output / 17).toNat ≤ frame.sevm.value.toNat ∧
        frame.sevm.value.toNat < Blanc.WithdrawalRequest.fee model) :=
  Iff.rfl

end Blanc.Lift.WithdrawalRequest.FeeCounterexample

namespace Blanc.WithdrawalRequest
open Jaune

-- EIP-7002 definition: RepresentsStorage
example (storage : B256 → B256) (state : State) :
    RepresentsStorage storage state ↔
      (Coherent state) ∧
      (StorageBounds state) ∧
      (storage 0 = state.excess.toB256) ∧
      (storage 1 = state.count.toB256) ∧
      (storage 2 = state.head.toB256) ∧
      (storage 3 = state.tail.toB256) ∧
      (∀ i (hi : i < state.queue.length),
    storage (queueSlot (state.head + i) 0) = callerWord state.queue[i] ∧
    storage (queueSlot (state.head + i) 1) = pubkeyWord state.queue[i] ∧
    storage (queueSlot (state.head + i) 2) = pubkeyAmountWord state.queue[i]) :=
  ⟨fun h => ⟨h.coherent, h.bounds, h.excess, h.count, h.head, h.tail, h.live⟩, fun ⟨h0, h1, h2, h3, h4, h5, h6⟩ => ⟨h0, h1, h2, h3, h4, h5, h6⟩⟩

end Blanc.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

-- EIP-7002: block_word_delivery
example
    {cfg : ChainConfig} {checkpoint preB postB preD postD : BlockChain}
    (historyB : ConfiguredHistoryTrace cfg checkpoint preB)
    (blockB : ConfiguredBlockTrace cfg preB postB)
    (historyD : ConfiguredHistoryTrace cfg checkpoint preD)
    (blockD : ConfiguredBlockTrace cfg preD postD) {depth : Nat}
    (extension : (ConfiguredHistoryTrace.step historyB blockB).ExtendsBy
      (ConfiguredHistoryTrace.step historyD blockD) depth)
    (installed : SystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step historyD blockD).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step historyD blockD).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step historyD blockD).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : RepresentsStorage (checkpoint.state.getStor withdrawalRequestPredeployAddress).get initial)
    (occurrences : ((ConfiguredHistoryTrace.step historyD blockD).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap)
    (modelB : Blanc.WithdrawalRequest.State)
    (repB : RepresentsStorage (blockB.bodyTrace.requestBenv.state.getStor
      withdrawalRequestPredeployAddress).get modelB)
    {q : Nat} {entry : Blanc.WithdrawalRequest.Entry} (queued : modelB.queue[q]? = some entry)
    (exactDepth : depth = q / 16) :
    ∃ modelD : Blanc.WithdrawalRequest.State,
      RepresentsStorage (blockD.bodyTrace.requestBenv.state.getStor
        withdrawalRequestPredeployAddress).get modelD ∧
      blockD.bodyTrace.requests.withdrawalOut.returnData = systemOutput modelD ∧
      (emitted modelD)[q % 16]? = some entry ∧
      (emitted modelD).take (q % 16 + 1) =
        (modelB.queue.drop (16 * depth)).take (q % 16 + 1) :=
  block_word_delivery historyB blockB historyD blockD extension installed senders authorities avoid systemEmpty init occurrences modelB repB queued exactDepth

end Blanc.Lift.WithdrawalRequest

namespace Blanc.Lift.WithdrawalRequest
open Jaune ExecutionAccountingReplay

-- EIP-7002: wordSystem_excess_wraps
example :
    let storage := (Stor.empty.set 0 (2 ^ 256 - 2 : Nat).toB256).set 1 10
    (∃ state, Blanc.WithdrawalRequest.RepresentsStorage storage.get state) ∧
    ((wordSystemStorage storage).get 0).toNat = 6 ∧
    ∀ state, Blanc.WithdrawalRequest.RepresentsStorage storage.get state →
      (Blanc.WithdrawalRequest.system state).excess = 2 ^ 256 + 6 ∧
      ¬ Blanc.WithdrawalRequest.RepresentsStorage (wordSystemStorage storage).get
        (Blanc.WithdrawalRequest.system state) :=
  wordSystem_excess_wraps

end Blanc.Lift.WithdrawalRequest

namespace Blanc.ExecutionTrace
open Jaune

-- EIP-7002 definition: the history-extension relation `block_word_delivery` is stated over
example {cfg : ChainConfig} {checkpoint current : BlockChain}
    (base : ConfiguredHistoryTrace cfg checkpoint current) :
    ConfiguredHistoryTrace.ExtendsBy base base 0 :=
  .refl

example {cfg : ChainConfig} {checkpoint current middle future : BlockChain}
    {base : ConfiguredHistoryTrace cfg checkpoint current}
    {trace : ConfiguredHistoryTrace cfg checkpoint middle} {n : Nat}
    (prior : ConfiguredHistoryTrace.ExtendsBy base trace n)
    (block : ConfiguredBlockTrace cfg middle future) :
    ConfiguredHistoryTrace.ExtendsBy base (.step trace block) (n + 1) :=
  .step prior block

end Blanc.ExecutionTrace

/-!
Uniswap V2 Pair claim-map headlines (section 5.8): one exact statement pin per required headline of
`scripts/check-deployed-claim-map.py`, each written in the namespace and with the `open`s of the
module that states it, so every name resolves as it does there.  A change to any headline statement
breaks this file; a proof-only change does not.
-/

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair: pair_history_committed
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        SourceReplay st₀ (steps.map PairStep.source) finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        (∀ k, K₀ k → K' k) ∧
        (∀ k, K' k → WriterExtend K₀ (pairHistoryTouchedKeys pair trace) k) ∧
        WriterRep K' (future.state.getStor pair) finish :=
  pair_history_committed trace installed initial fresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair: pair_history_initialized
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {factory token0 token1 : Adr} {domain : B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeys pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        SourceReplay (initializedState factory domain token0 token1)
          (steps.map PairStep.source) finish ∧
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        (∀ k, K' k → k ∈ pairHistoryTouchedKeys pair trace) ∧
        WriterRep K' (future.state.getStor pair) finish :=
  pair_history_initialized trace installed initial fresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair: pair_history_ledger
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {factory token0 token1 : Adr} {domain : B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeys pair trace)) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        runSourceInvocations (initializedState factory domain token0 token1) (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        finish.Ledger :=
  pair_history_ledger trace installed initial fresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair: pair_history_oracle
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        finish.price0CumulativeLast.toNat =
          (st₀.price0CumulativeLast.toNat +
            oracleSum0 (sourceReplayUpdates st₀ (steps.map PairStep.source))) % 2 ^ 256 ∧
        finish.price1CumulativeLast.toNat =
          (st₀.price1CumulativeLast.toNat +
            oracleSum1 (sourceReplayUpdates st₀ (steps.map PairStep.source))) % 2 ^ 256 ∧
        (∀ u ∈ sourceReplayUpdates st₀ (steps.map PairStep.source), u.update.Lawful) ∧
        OracleTimestampChain st₀.blockTimestampLast finish.blockTimestampLast
          (sourceReplayUpdates st₀ (steps.map PairStep.source)) ∧
        sourceReplayUpdates st₀ (steps.map PairStep.source) =
          (sourceReplayReceipts st₀ (steps.map PairStep.source)).flatMap Prod.snd ∧
        ∀ inv receipts, (inv, receipts) ∈ sourceReplayReceipts st₀ (steps.map PairStep.source) →
          ∃ s ∈ steps, inv = s.source ∧
            ∀ u ∈ receipts, u.update.timestamp = s.frame.sevm.benvStat.time :=
  pair_history_oracle trace installed initial fresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair: pair_history_feeOff_product
example {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayAnswers st₀ (steps.map PairStep.source) →
          ∀ before after, (before, after) ∈ sourceReplayEdges st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) :=
  pair_history_feeOff_product trace installed initial fresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair: pair_history_feeOn_product
example {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayNoShrink st₀ (steps.map PairStep.source) →
          ∀ before inv after, (before, inv, after) ∈ sourceReplaySteps st₀ (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
              after.reserve0.val * after.reserve1.val *
                (before.totalSupply.toNat + entryFeeAmount before inv.entry inv.transcript) ^ 2) :=
  pair_history_feeOn_product trace installed initial fresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair: permit_bytecode_refines_source
example {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (permitTouched (permitOwner sevm) (permitSpender sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf) (freshOutput : b.output = [])
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 228 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      sevm.benvStat.time ≤ permitDeadline sevm ∧
      ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (residual : Nat),
        PermitRawCall sevm b 0xd505accf gw callGas d out ∧
        ∀ codeExists, PermitSourceResult K current invocation sevm b post d out codeExists residual :=
  permit_bytecode_refines_source rep fresh representable codeEq fork selector freshOutput run

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair: burnRaw_source_authentic
example {U K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b publicPost : Devm} {G : Nat}
    (invocation : List Nat) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok publicPost))
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots run,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    BurnEntryAuthenticFinished U K current ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩
      b (.halted publicPost) invocation :=
  burnRaw_source_authentic invocation codeEq fork selector rep tracked run inj apart sub trace sem image installed good staticGood

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair: staticView_bytecode_inv
example {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      ∃ view : StaticView, Blanc.Sevm.selector sevm = view.selector :=
  staticView_bytecode_inv codeEq fork static run

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair: pair_history_writer_live
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (writer : LedgerWriter) {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (representable : sevm.data.length < 2 ^ 256)
    (length : writer.calldataSize ≤ sevm.data.length)
    (selector : Blanc.Sevm.selector sevm = writer.selector)
    (callFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀) (writer.keys sevm)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (G : Nat) (sourceFrame : Frame) (returndata : Bytes),
        startImmediate { state := finish, logs := [], updates := [] } (writerContext sevm [])
          (writer.entry sevm) = some (.finished sourceFrame returndata) →
        gCallStipend < G →
        Nonempty (Exec 0 sevm (St pre [] Mem.empty (G + writer.cost sevm pre))
          (.ok (writer.post sevm pre G))) ∧
        (writer.post sevm pre G).gasLeft = G ∧
        writer.Result K' { state := finish, logs := [], updates := [] } [] sevm pre
          (writer.post sevm pre G) G :=
  pair_history_writer_live trace installed initial fresh writer target state codeEq fork representable length selector callFresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair: pair_history_sync_live
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre d0 d1 : Devm} {callGas0 callGas1 G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) (static : sevm.isStatic = false)
    (sentry : gCallStipend <
      (callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm pre)
        (syncFirstToken sevm pre).toAdr) + sloadCost sevm (syncLockedWorld sevm pre) 6 + 119 +
      sstoreCost sevm (afterSload sevm pre 12) 12 0)
    (nonzero0 : ((syncFirstWorld sevm pre).getCode (syncFirstToken sevm pre).toAdr).size.toB256 ≠ 0)
    (call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (syncFirstWorld sevm pre) (syncFirstToken sevm pre).toAdr)
        (callGas0.toB256 :: (syncFirstToken sevm pre) :: 128 :: 36 :: 128 :: 32 :: 164 ::
          0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory getterInitMemory sevm.currentTarget) callGas0) (.exec .staticcall) d0)
    (success0 : d0.stack = 1 :: 164 :: 0x70a08231 :: (syncFirstToken sevm pre) :: 0x1fd4 :: 0x0257 ::
      [0xfff6cae9])
    (returnedGas0 : d0.gasLeft = callGas1 + 5 + 22 +
      temporalAccountAccessCost (afterSload sevm d0 7)
        (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr +
      sloadCost sevm d0 7 + 113 + 70)
    (long0 : 32 ≤ d0.returnData.length)
    (nonzero1 : ((afterSload sevm d0 7).getCode
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr).size.toB256 ≠ 0)
    (call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7)
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256.toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1)
    (success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
      Bytes.toB256 (d0.returnData.take 32) :: 0x1fd4 :: 0x0257 :: [0xfff6cae9])
    (returnedGas1 : d1.gasLeft = (syncUpdateUnlockClosedGas sevm d1
      (Bytes.toB256 (d0.returnData.take 32)) (Bytes.toB256 (d1.returnData.take 32)) 192 (G + 1)) + 70)
    (long1 : 32 ≤ d1.returnData.length) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      (finish.unlocked = 1 →
        (∃ result, finish.update (writerContext sevm []) (Bytes.toB256 (d0.returnData.take 32))
          (Bytes.toB256 (d1.returnData.take 32)) finish.reserve0.val finish.reserve1.val =
            .ok result) →
        let balance0 := (Bytes.toB256 (d0.returnData.take 32))
        let balance1 := (Bytes.toB256 (d1.returnData.take 32))
        let u := afterSload sevm d1 8
        let old0 := reserve0Read (d1.getStorVal sevm.currentTarget 8)
        let old1 := reserve1Read (d1.getStorVal sevm.currentTarget 8)
        let finalGas := (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 + 7
        let h := afterSload sevm u 8
        let delta := updateElapsedWord (u.getStorVal sevm.currentTarget 8) sevm.benvStat.time
        let w9 := updateAccumulatorPost sevm h 9 (updatePriceWord old0 old1) delta
        let v := updateOracleWorld sevm u old0 old1
        let store9 := sstoreCost sevm (afterSload sevm h 9) 9
          (updateAccumulatorWord (h.getStorVal sevm.currentTarget 9)
            (updatePriceWord old0 old1) delta)
        let load10 := sloadCost sevm w9 10
        let store10 := sstoreCost sevm (afterSload sevm w9 10) 10
          (updateAccumulatorWord (w9.getStorVal sevm.currentTarget 10)
            (updatePriceWord old1 old0) delta)
        let load8 := sloadCost sevm v 8
        let store8 := sstoreCost sevm (afterSload sevm v 8) 8
          (updateFinalPackedWord sevm u old0 old1 balance0 balance1)
        gCallStipend < finalGas + updateSyncGas 192 + store8 →
        (updateOracleActive sevm u old0 old1 →
          gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 + store10) →
        (updateOracleActive sevm u old0 old1 →
          gCallStipend < finalGas + updateSyncGas 192 + load8 + store8 + 110 +
            load10 + store10 + 42 + 149 + store9) →
        gCallStipend < (G + 1) + 8 + sstoreCost sevm (syncUpdatedWorld sevm d1 balance0 balance1) 12 1 →
        ∃ (post : Devm)
          (run : Exec 0 sevm (St pre [] Mem.empty (syncCalleePrefixGas sevm pre callGas0 + 15 + 229))
            (.ok post)),
          post.gasLeft = G ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (syncCalleePrefixGas sevm pre callGas0 + 15 + 229), .ok post, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (syncCalleePrefixGas sevm pre callGas0 + 15 + 229), .ok post, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (syncCalleePrefixGas sevm pre callGas0 + 15 + 229),
                .ok post, run⟩ post)) :=
  pair_history_sync_live trace installed initial fresh target state codeEq fork output representable value size selector static sentry nonzero0 call0 success0 returnedGas0 long0 nonzero1 call1 success1 returnedGas1 long1

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair: pair_history_mint_live
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (callee : MintPrefixCallee sevm pre [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        (runTyped finish (writerContext sevm []) (.mint (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ (liquidity : B256)
          (run : Exec 0 sevm (St pre [] Mem.empty (callee.gas + 228))
            (.ok (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G))),
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).gasLeft = G ∧
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).output =
            liquidity.toBytes ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) :=
  pair_history_mint_live trace installed initial fresh target state codeEq fork output representable value size guard selector callee rowsFresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair: pair_history_swap_live
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ {d0 d1 dC : Devm} {cg0 cg1 cgC g : Nat}
        (callee : SwapBackCalleeEnv sevm (swapFrontCutWorld sevm pre d0 d1 dC)
          (swapFrontCutMem sevm d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC).size
          (swapFrontPtr sevm d0 d1) (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1))
        (_front : SwapFrontForwardEnv sevm pre finish d0 d1 dC cg0 cg1 cgC
          callee.gas),
        SwapContextConditions (writerContext sevm []) →
        SwapModelConditions finish (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm)
          (swapBalanceWord callee.d0.returnData) (swapBalanceWord callee.d1.returnData) →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty
            (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
              swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166))
            (.ok (St callee.post [0x022c0d9f] callee.memory g)),
          (St callee.post [0x022c0d9f] callee.memory g).gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                  swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                    swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty
                (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
                  swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166), .ok _, run⟩
              (St callee.post [0x022c0d9f] callee.memory g)) :=
  pair_history_swap_live trace installed initial fresh target state codeEq fork output representable value size selector guards

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair: pair_history_burn_live
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (callee : BurnForwardEnv sevm pre g)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace K₀)
      (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final0 →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final1 →
        (runTyped finish (writerContext sevm []) (.burn (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) :=
  pair_history_burn_live trace installed initial fresh target state codeEq fork output representable value size guard selector callee rowsFresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair: pair_history_skim_live
example {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (callee : SkimForwardEnv sevm pre g)
    (firstFresh : callee.FirstCallFresh (pairHistoryUniverse pair trace K₀)) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 →
        transcript.ownTail.ownTail.firstWord = callee.balance1 →
        (runTyped finish (writerContext sevm []) (.skim (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) :=
  pair_history_skim_live trace installed initial fresh target state codeEq fork output representable value size abi selector callee firstFresh

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair: pair_history_permit_live
example {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre d : Devm} {G callGas : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (guard : (224 : B256) ≤ sevm.data.length.toB256 - 4)
    (sentry3 : gCallStipend < callGas + 641 + permitNonceStoreCharge sevm pre)
    (call : Ninst.RunCompiled sevm (St (permitNonceWorld sevm pre (permitOwner sevm))
      (callGas.toB256 :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm pre 0xd505accf)
      (permitPublicCallMemory sevm pre) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: permitPublicCallStack sevm pre 0xd505accf)
    (returnedGas : d.gasLeft = G + permitApproveCharge sevm d + 2165)
    (sentry : gCallStipend < G + permitApproveCharge sevm d + 1846) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstRecovered = (permitRecoveredWord d.returnData).toAdr →
        (runTyped finish (writerContext sevm []) (permitDecodedEntry sevm) transcript).status =
          .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty
            (callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre + 1137))
            (.ok (permitPublicPost sevm pre d d.returnData 0xd505accf G)),
          (permitPublicPost sevm pre d d.returnData 0xd505accf G).gasLeft = G ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                (callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre + 1137),
                .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre + 1137),
                  .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty
                (callGas + permitNonceStoreCharge sevm pre + permitNonceCharge sevm pre + 1137),
                .ok _, run⟩
              (permitPublicPost sevm pre d d.returnData 0xd505accf G)) :=
  pair_history_permit_live trace installed initial fresh target state codeEq fork output representable size selector guard sentry3 call success returnedGas sentry

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair: pair_history_initialize_live
example {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (guard : (64 : B256) ≤ sevm.data.length.toB256 - 4)
    (sentry0 : gCallStipend < G + initializeStore0Charge sevm pre + initializeLoad1Charge sevm pre +
      initializeStore1Charge sevm pre + 39)
    (sentry1 : gCallStipend < G + initializeStore1Charge sevm pre + 9) :
    ∃ (finish : State) (K' : WriterKey → Prop), PairHistoryReplayed pair trace K₀ st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        (runTyped finish (writerContext sevm [])
          (.initialize (initializeToken0 sevm) (initializeToken1 sevm)) transcript).status =
            .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty (G + initializeStorageCharge sevm pre + 377))
            (.ok (initializePublicPost sevm pre [0x485cc955] getterInitMemory G)),
          (initializePublicPost sevm pre [0x485cc955] getterInitMemory G).gasLeft = G ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (G + initializeStorageCharge sevm pre + 377),
                .ok _, run⟩) →
            PairStepOutcome PairFrameAuth
              (WriterExtend (pairHistoryUniverse pair trace K₀)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty
                  (G + initializeStorageCharge sevm pre + 377), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (G + initializeStorageCharge sevm pre + 377), .ok _, run⟩
              (initializePublicPost sevm pre [0x485cc955] getterInitMemory G)) :=
  pair_history_initialize_live trace installed initial fresh target state codeEq fork output representable size selector guard sentry0 sentry1

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

-- Uniswap V2 Pair: pair_create2_initialized
example {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {i sz salt : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hinit : create2InitCode M i sz = code.toList)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt code.toList))
        (create2NewAddress sevm.currentTarget salt code.toList))
    (hgas : 2400000 ≤ except64th G) (hroom : S.length < 1024) :
    ∃ post, Ninst.RunCompiled sevm (St b (0 :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) (.exec .create2) post ∧
      post.stack = (create2NewAddress sevm.currentTarget salt code.toList).toB256 :: S ∧
      (post.getCode (create2NewAddress sevm.currentTarget salt code.toList)).toList =
        Blanc.Lift.UniswapV2Pair.code.toList ∧
      ∀ {isevm : Sevm} {ib ipost : Devm} {iG : Nat},
        isevm.currentTarget = create2NewAddress sevm.currentTarget salt code.toList →
        Devm.getStor ib isevm.currentTarget =
          Devm.getStor post (create2NewAddress sevm.currentTarget salt code.toList) →
        isevm.caller = sevm.currentTarget →
        isevm.data.length < 2 ^ 256 → ib.output = [] →
        isevm.code = Blanc.Lift.UniswapV2Pair.code → CoveredFork isevm.benvStat.fork →
        Blanc.Sevm.selector isevm = 0x485cc955 →
        Exec 0 isevm (St ib [] Mem.empty iG) (.ok ipost) →
        InitializedCheckpoint (ipost.getStor isevm.currentTarget) sevm.currentTarget
          (domainSeparator sevm.benvStat.chainId.toB256
            (create2NewAddress sevm.currentTarget salt code.toList))
          (initializeToken0 isevm) (initializeToken1 isevm) :=
  pair_create2_initialized hfork hstatic hinit hnonce hdepth hfresh hgas hroom

end Blanc.Lift.UniswapV2Pair.Creation

namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

-- Uniswap V2 Pair: pair_create2_initialize_live
example {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {i sz salt : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hinit : create2InitCode M i sz = code.toList)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt code.toList))
        (create2NewAddress sevm.currentTarget salt code.toList))
    (hgas : 2400000 ≤ except64th G) (hroom : S.length < 1024) :
    ∃ post, Ninst.RunCompiled sevm (St b (0 :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) (.exec .create2) post ∧
      post.stack = (create2NewAddress sevm.currentTarget salt code.toList).toB256 :: S ∧
      (post.getCode (create2NewAddress sevm.currentTarget salt code.toList)).toList =
        Blanc.Lift.UniswapV2Pair.code.toList ∧
      ∀ {isevm : Sevm} {ib : Devm} {iG : Nat},
        isevm.currentTarget = create2NewAddress sevm.currentTarget salt code.toList →
        Devm.getStor ib isevm.currentTarget =
          Devm.getStor post (create2NewAddress sevm.currentTarget salt code.toList) →
        isevm.caller = sevm.currentTarget → isevm.value = 0 → isevm.isStatic = false →
        isevm.code = Blanc.Lift.UniswapV2Pair.code → CoveredFork isevm.benvStat.fork →
        Blanc.Sevm.selector isevm = 0x485cc955 →
        (4 : B256) ≤ isevm.data.length.toB256 → (64 : B256) ≤ isevm.data.length.toB256 - 4 →
        isevm.data.length < 2 ^ 256 → ib.output = [] →
        gCallStipend < iG + initializeStore0Charge isevm ib +
          initializeLoad1Charge isevm ib + initializeStore1Charge isevm ib + 39 →
        gCallStipend < iG + initializeStore1Charge isevm ib + 9 →
        ∃ ipost, Nonempty (Exec 0 isevm
            (St ib [] Mem.empty (iG + initializeStorageCharge isevm ib + 377)) (.ok ipost)) ∧
          InitializedCheckpoint (ipost.getStor isevm.currentTarget) sevm.currentTarget
            (domainSeparator sevm.benvStat.chainId.toB256
              (create2NewAddress sevm.currentTarget salt code.toList))
            (initializeToken0 isevm) (initializeToken1 isevm) :=
  pair_create2_initialize_live hfork hstatic hinit hnonce hdepth hfresh hgas hroom

end Blanc.Lift.UniswapV2Pair.Creation

namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

-- Uniswap V2 Pair: exhibit_create2
example {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {i sz : B256}
    (hfactory : sevm.currentTarget = factory)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hinit : create2InitCode M i sz = code.toList)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz pairAddress) pairAddress)
    (hgas : 2400000 ≤ except64th G) (hroom : S.length < 1024) :
    ∃ post, Ninst.RunCompiled sevm (St b (0 :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) (.exec .create2) post ∧
      post.stack = pairAddress.toB256 :: S ∧
      (post.getCode pairAddress).toList = Blanc.Lift.UniswapV2Pair.code.toList ∧
      Devm.getStor post pairAddress =
        ctorStor sevm.benvStat.chainId.toB256 pairAddress factory Stor.empty :=
  exhibit_create2 hfactory hfork hstatic hinit hnonce hdepth hfresh hgas hroom

end Blanc.Lift.UniswapV2Pair.Creation


/-! The Uniswap V2 Pair definitions those headline statements are stated through and the claim map
cites (the authentication and replay vocabulary, the answer premises, the oracle and ledger laws, the
storage representation, the gas expressions and the premise records), where the definition body is
itself the claim.  They are pinned by unfolding (`Iff.rfl`, `rfl`), recursive ones case by case, and
records by their exact constructor, so a weakened body or an added, removed or retyped field fails
here.  A premise record's own sub-records (for example the per-call environments a forward
environment is built from) are not unfolded here. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair definition: pairFrameObs
example (pair : Adr) (frame : Exec.Frame)  :
    pairFrameObs pair frame =
      (if frame.sevm.currentTarget = pair ∧ frame.sevm.isStatic = false then [frame] else []) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair definition: pairSubtreeFrames
example (pair : Adr) (f : Exec.Frame)  :
    pairSubtreeFrames pair f =
      ((Exec.committedFrames f.run).flatMap (pairFrameObs pair)) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair definition: pairHistoryTouchedKeys
example {cfg : ChainConfig} {checkpoint future : BlockChain}
    (pair : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future)  :
    pairHistoryTouchedKeys pair trace =
      (trace.rawFrames.flatMap fun D => if D.sevm.currentTarget = pair then pairDerivKeys D else []) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair definition: committedPairFrames
example {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future)  :
    committedPairFrames pair trace =
      (trace.settledFrames.flatMap (pairFrameObs pair)) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair record: PairStep
example 
    (frame : Exec.Frame)
    (entry : Entry)
    (transcript : Transcript) :
    PairStep  :=
  { frame := frame
    entry := entry
    transcript := transcript }

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair definition: PairStep.source
example (s : PairStep)  :
    PairStep.source s =
      ({ context := writerContext s.frame.sevm [], entry := s.entry, transcript := s.transcript }) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

-- Uniswap V2 Pair definition: PairStep.Authentic
example (pair : Adr)
    (s : PairStep)  :
    PairStep.Authentic pair s ↔
      (s.frame.pc = 0 ∧ Execution.commits s.frame.out = true ∧ s.frame.sevm.currentTarget = pair ∧
    s.frame.sevm.isStatic = false ∧
    PairFrameAuth (Blanc.Exec.Frame.rootDeriv s.frame) s.entry s.transcript) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: PairFrameAuth
example (D : Exec.Deriv) (entry : Entry) (T : Transcript)  :
    PairFrameAuth D entry T ↔
      (LockedAuth D entry T ∨ SwapAuth D entry T ∨ MintAuth D entry T ∨ SyncAuth D entry T ∨
    SkimAuth D entry T ∨ BurnAuth D entry T) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: LockedAuth
example (D : Exec.Deriv) (entry : Entry) (nested : Transcript)  :
    LockedAuth D entry nested ↔
      ((Blanc.Sevm.selector D.sevm = 0xa9059cbb ∧ entry = transferDecodedEntry D.sevm ∧
    nested = .done) ∨
  (Blanc.Sevm.selector D.sevm = 0x095ea7b3 ∧ entry = approveDecodedEntry D.sevm ∧
    nested = .done) ∨
  (Blanc.Sevm.selector D.sevm = 0x23b872dd ∧ entry = transferFromDecodedEntry D.sevm ∧
    nested = .done) ∨
  (Blanc.Sevm.selector D.sevm = 0x485cc955 ∧ entry = initializeDecodedEntry D.sevm ∧
    nested = .done) ∨
  (Blanc.Sevm.selector D.sevm = 0xd505accf ∧ entry = permitDecodedEntry D.sevm ∧
    ∃ (out : Bytes) (entered : Bool) (views : List StaticViewTurn),
      nested = .next (permitExternalResult out entered) (staticViewTranscript views .done) .done ∧
      PermitRecoveryAuth D out entered views) ∨
  (∃ view : StaticView, Blanc.Sevm.selector D.sevm = view.selector ∧
    entry = view.entry D.sevm ∧ nested = .done)) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: MintAuth
example (D : Exec.Deriv) (entry : Entry) (T : Transcript)  :
    MintAuth D entry T ↔
      (Blanc.Sevm.selector D.sevm = 0x6a627842 ∧ entry = .mint (Sevm.dataWord D.sevm 4).toAdr ∧
  ∃ (current : Checkpoint) (out0 out1 outF : Bytes) (views0 views1 viewsF : List StaticViewTurn),
    MintObservedSteps D current D.sevm out0 out1 outF ∧
    T = .next (feeObservedResult out0) (staticViewTranscript views0 .done)
      (.next (feeObservedResult out1) (staticViewTranscript views1 .done)
        (.next (feeObservedResult outF) (staticViewTranscript viewsF .done) .done)) ∧
    (∀ picked ∈ views0 ++ views1 ++ viewsF,
      Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
      picked.1.frame.sevm.currentTarget = D.sevm.currentTarget ∧
      picked.1.frame.sevm.isStatic = true) ∧
    MintViewProvenance D D.sevm.currentTarget current.state.token0 views0 ∧
    MintViewProvenance D D.sevm.currentTarget current.state.token1 views1 ∧
    MintViewProvenance D D.sevm.currentTarget current.state.factory viewsF) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SyncAuth
example (D : Exec.Deriv) (entry : Entry) (T : Transcript)  :
    SyncAuth D entry T ↔
      (Blanc.Sevm.selector D.sevm = 0xfff6cae9 ∧ entry = .sync ∧
  ∃ (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat) (b post : Devm)
    (result : SyncCanonicalResult K current invocation D b post),
    T = .next (syncExternalReply result.out0) (staticViewTranscript result.views0 .done)
      (.next (syncExternalReply result.out1) (staticViewTranscript result.views1 .done) .done)) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SkimAuth
example (D : Exec.Deriv) (entry : Entry) (T : Transcript)  :
    SkimAuth D entry T ↔
      (Blanc.Sevm.selector D.sevm = 0xbc25cf77 ∧ entry = .skim (skimRecipient D.sevm) ∧
  ∃ (b : Devm) (G : Nat), D.pc = 0 ∧ D.devm = St b [] Mem.empty G ∧
  ∃ (out0 : Bytes) (d : Devm), SkimFirstSteps D D.sevm b out0 d ∧
  ∃ (out1 : Bytes) (d2 : Devm) (views0 views1 : List StaticViewTurn)
    (turns1 turns3 : List MutableTurn),
    SkimSecondSteps D D.sevm d (skimToken1 D.sevm b) out1 d2 ∧
    T = .next (skimBalanceReply out0) (staticViewTranscript views0 .done)
      (.next (skimTransferReply d.returnData true) (mutableTranscript turns1 .done)
        (.next (skimBalanceReply out1) (staticViewTranscript views1 .done)
          (.next (skimTransferReply d2.returnData true) (mutableTranscript turns3 .done) .done))) ∧
    (∀ picked ∈ views0 ++ views1, Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
      picked.1.frame.sevm.currentTarget = D.sevm.currentTarget) ∧
    (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns1 ++ turns3 →
      LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
    (views0 = [] ∧ D.sevm.benvStat.rules.isPrecomp (skimToken0 D.sevm b).toAdr ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw),
        Execution.commits raw = true ∧
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        views0.map Prod.fst =
          (Exec.retainedTargetTurnsAt D.sevm.currentTarget [] childRun).filterMap Sum.getRight?) ∧
    (views1 = [] ∧ D.sevm.benvStat.rules.isPrecomp
        (skimToken1 D.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw),
        Execution.commits raw = true ∧
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        views1.map Prod.fst =
          (Exec.retainedTargetTurnsAt D.sevm.currentTarget [] childRun).filterMap Sum.getRight?) ∧
    ((turns1 = [] ∧ D.sevm.benvStat.rules.isPrecomp
        (skimToken0 D.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw)
        (committed : Execution.commits raw = true),
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        turns1.map MutableTurn.event =
          Exec.targetLogEventsFrom D.sevm.currentTarget [] 0 childRun committed) ∧
    ((turns3 = [] ∧ D.sevm.benvStat.rules.isPrecomp
        (skimToken1 D.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw)
        (committed : Execution.commits raw = true),
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        turns3.map MutableTurn.event =
          Exec.targetLogEventsFrom D.sevm.currentTarget [] 0 childRun committed)) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SwapAuth
example (D : Exec.Deriv) (entry : Entry) (T : Transcript)  :
    SwapAuth D entry T ↔
      (Blanc.Sevm.selector D.sevm = 0x022c0d9f ∧ entry = swapDecodedEntry D.sevm ∧
  ∃ (b : Devm) (G : Nat) (current : Checkpoint) (invocation : List Nat) (frame : Frame),
    D.pc = 0 ∧ D.devm = St b [] Mem.empty G ∧ frame.checkpoint = current ∧
    frame.context = writerContext D.sevm invocation ∧
  let sevm := D.sevm
  let locals := swapFrontLocals sevm current.state
  let w := swapCutWords sevm current.state
  let S := swapCutStack w 0x257 [0x022c0d9f]
  ∃ (T0 T1 TC : Transcript → Transcript) (turns0 turns1 turnsC : List MutableTurn)
    (b1 b2 d d0 d1 : Devm) (M1 M2 M : Mem) (p1 p : B256) (out0 out1 : Bytes)
    (views0 views1 : List StaticViewTurn),
    SwapTransferOpt D sevm (swapPrefixWorld sevm b) S getterInitMemory 128
      (swapAmount0Out sevm) (swapRecipientWord sevm) current.state.token0.toB256 0x8d0 b1 M1 p1 ∧
    SwapTransferOpt D sevm b1 S M1 p1
      (swapAmount1Out sevm) (swapRecipientWord sevm) current.state.token1.toB256 0x8e1 b2 M2 p ∧
    SwapCallbackOpt D sevm b2 S M2 p (swapRecipientWord sevm) (swapAmount0Out sevm)
      (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) d M ∧
    ((swapAmount0Out sevm = 0 ∧ T0 = id) ∨ (swapAmount0Out sevm ≠ 0 ∧
      T0 = (fun tail => .next (swapTransferReply b1.returnData) (mutableTranscript turns0 .done) tail) ∧
      SwapCallProvenance sevm.currentTarget D sevm (swapPrefixWorld sevm b) b1 turns0)) ∧
    ((swapAmount1Out sevm = 0 ∧ T1 = id) ∨ (swapAmount1Out sevm ≠ 0 ∧
      T1 = (fun tail => .next (swapTransferReply b2.returnData) (mutableTranscript turns1 .done) tail) ∧
      SwapCallProvenance sevm.currentTarget D sevm b1 b2 turns1)) ∧
    ((swapDataLength sevm = 0 ∧ TC = id) ∨ (swapDataLength sevm ≠ 0 ∧
      TC = (fun tail => .next (swapCallbackReply d.returnData) (mutableTranscript turnsC .done) tail) ∧
      SwapCallProvenance sevm.currentTarget D sevm b2 d turnsC)) ∧
    SwapBalanceCall D sevm d M p w.token0
      (w.token1 :: w.token0 :: 0 :: 0 :: w.reserve1 :: w.reserve0 :: w.dataLength ::
        w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: 0x257 :: [0x022c0d9f]) d0 out0 ∧
    SwapBalanceCall D sevm d0 (swapBalanceReply M p sevm.currentTarget out0) p w.token1
      (w.token1 :: w.token0 :: 0 :: swapBalanceWord out0 :: w.reserve1 :: w.reserve0 ::
        w.dataLength :: w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: 0x257 ::
        [0x022c0d9f]) d1 out1 ∧
    T = ((T0 ∘ T1) ∘ TC)
      (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
        (.next (feeObservedResult out1) (staticViewTranscript views1 .done) .done)) ∧
    (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns0 ++ turns1 ++ turnsC →
      LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
    PairViewProvenance D sevm frame (swapTokenWord w.token0) views0 ∧
    PairViewProvenance D sevm (frame.beginResume (swapRequest0 frame locals))
      (swapTokenWord w.token1) views1) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: BurnAuth
example (D : Exec.Deriv) (entry : Entry) (T : Transcript)  :
    BurnAuth D entry T ↔
      (Blanc.Sevm.selector D.sevm = 0x89afcb44 ∧
  entry = .burn ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord D.sevm 4).toAdr ∧
  BurnFrameAuth D T) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: PairStepOutcome
example (Auth : Exec.Deriv → Entry → Transcript → Prop) (U : WriterKey → Prop)
    (current : Checkpoint) (invocation : List Nat) (K : WriterKey → Prop) (D : Exec.Deriv)
    (post : Devm)  :
    PairStepOutcome Auth U current invocation K D post ↔
      (∃ (entry : Entry) (nested : Transcript) (child : RunResult) (bytes : Bytes)
    (K' : WriterKey → Prop),
    Auth D entry nested ∧
    ExactConsumes (startTyped current (writerContext D.sevm invocation) entry) nested child ∧
    child.status = .success bytes ∧ (∀ k, K k → K' k) ∧ (∀ k, K' k → U k) ∧
    WriterRep K' (post.getStor D.sevm.currentTarget) child.frame.current.state) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair definition: pairHistoryUniverse
example {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (K₀ : WriterKey → Prop)  :
    pairHistoryUniverse pair trace K₀ =
      (WriterExtend K₀ (pairHistoryTouchedKeys pair trace)) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace

-- Uniswap V2 Pair definition: PairHistoryReplayed
example {cfg : ChainConfig} {checkpoint future : BlockChain} (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (K₀ : WriterKey → Prop) (st₀ : State)
    (finish : State) (K' : WriterKey → Prop)  :
    PairHistoryReplayed pair trace K₀ st₀ finish K' ↔
      (∃ steps : List PairStep,
    steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
    (∀ s ∈ steps, s.Authentic pair) ∧
    runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
    (∀ k, K₀ k → K' k) ∧ (∀ k, K' k → pairHistoryUniverse pair trace K₀ k) ∧
    WriterRep K' (future.state.getStor pair) finish) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SourceInvocation.run
example (inv : SourceInvocation) (st : State)  :
    SourceInvocation.run inv st =
      (runTyped st inv.context inv.entry inv.transcript) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: OracleUpdate.Lawful
example (u : OracleUpdate)  :
    OracleUpdate.Lawful u ↔
      (u.elapsed = (u.timestamp.toNat % 2 ^ 32 + 2 ^ 32 - u.oldTimestamp.toNat) % 2 ^ 32 ∧
  u.increment0 =
    (if u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0 then
      (u.oldReserve1 * 2 ^ 112 / u.oldReserve0) * u.elapsed
    else 0) ∧
  u.increment1 =
    (if u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0 then
      (u.oldReserve0 * 2 ^ 112 / u.oldReserve1) * u.elapsed
    else 0)) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: State.Ledger
example (st : State)  :
    State.Ledger st ↔
      (Blanc.SumBacked st.balanceOf st.totalSupply) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: EntryNoShrink
example (st : State) (ctx : Context) (entry : Entry) (transcript : Transcript)  :
    EntryNoShrink st ctx entry transcript ↔
      (match entry with
  | .burn recipient => BurnEntryNoShrink st ctx.pair recipient transcript
  | .sync => SyncEntryNoShrink st transcript
  | _ => True) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SyncEntryNoShrink
example (st : State) (transcript : Transcript)  :
    SyncEntryNoShrink st transcript ↔
      (st.reserve0.val ≤ transcript.firstWord.toNat ∧
    st.reserve1.val ≤ transcript.ownTail.firstWord.toNat) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: BurnEntryNoShrink
example (st : State) (pair recipient : Adr) (transcript : Transcript)  :
    BurnEntryNoShrink st pair recipient transcript ↔
      (BurnFeeNoShrink st
    { locals := { recipient := recipient, reserves := st.cachedReserves, token0 := st.token0, token1 := st.token1 },
      balance0 := transcript.firstWord, balance1 := transcript.ownTail.firstWord,
      liquidity := st.balanceOf pair } transcript.ownTail.ownTail) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: EntryFeeOff
example (entry : Entry) (transcript : Transcript)  :
    EntryFeeOff entry transcript ↔
      (match entry with
  | .mint _ | .burn _ => transcript.ownTail.ownTail.firstWord.toAdr = 0
  | _ => True) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: entryFeeAmount
example (st : State) (entry : Entry) (transcript : Transcript)  :
    entryFeeAmount st entry transcript =
      (match entry with
  | .mint _ | .burn _ =>
    feeAmount st transcript.ownTail.ownTail.firstWord.toAdr st.reserve0.val st.reserve1.val
  | _ => 0) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: initializedState
example (factory : Adr) (domain : B256) (token0 token1 : Adr)  :
    initializedState factory domain token0 token1 =
      (initializeSourceState (State.empty factory domain) token0 token1) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: InitializedCheckpoint
example (s : Stor) (factory : Adr) (domain : B256) (token0 token1 : Adr)  :
    InitializedCheckpoint s factory domain token0 token1 ↔
      (WriterRep (fun _ => False) s (initializedState factory domain token0 token1)) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterKeysFinite
example (K : WriterKey → Prop)  :
    WriterKeysFinite K ↔
      (∃ keys : List WriterKey, ∀ k, K k ↔ k ∈ keys) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterSupport
example (K : WriterKey → Prop) (s : Stor)  :
    WriterSupport K s ↔
      (Blanc.SlotFootprint.Support WriterKey.slot writerFixedSlots K s) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterInj
example (K : WriterKey → Prop)  :
    WriterInj K ↔
      (Blanc.SlotFootprint.Inj WriterKey.slot K) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterApart
example (K : WriterKey → Prop)  :
    WriterApart K ↔
      (Blanc.SlotFootprint.Apart WriterKey.slot writerFixedSlots K) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterFreshKeys
example (K : WriterKey → Prop) (keys : List WriterKey)  :
    WriterFreshKeys K keys ↔
      (Blanc.SlotFootprint.FreshKeys WriterKey.slot writerFixedSlots K keys) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterExtend
example (K : WriterKey → Prop) (keys : List WriterKey)  :
    WriterExtend K keys =
      (Blanc.SlotFootprint.extendBy K keys) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterSelectedValues
example (K : WriterKey → Prop) (s : Stor) (st : State)  :
    WriterSelectedValues K s st ↔
      (∀ k, K k → s.get k.slot = k.value st) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterLogicalZero
example (K : WriterKey → Prop) (st : State)  :
    WriterLogicalZero K st ↔
      (∀ k, ¬ K k → k.value st = 0) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: WriterFixedMatches
example (s : Stor) (st : State)  :
    WriterFixedMatches s st ↔
      (s.get 0 = st.totalSupply ∧ s.get 3 = st.domainSeparator ∧
  (s.get 5).toAdr = st.factory ∧ (s.get 6).toAdr = st.token0 ∧
  (s.get 7).toAdr = st.token1 ∧
  reserve0Read (s.get 8) = Nat.toB256 st.reserve0.val ∧
  reserve1Read (s.get 8) = Nat.toB256 st.reserve1.val ∧
  reserveTimestampRead (s.get 8) = st.blockTimestampLast.toB256 ∧
  s.get 9 = st.price0CumulativeLast ∧ s.get 10 = st.price1CumulativeLast ∧
  s.get 11 = st.kLast ∧ s.get 12 = st.unlocked) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair record: WriterRep
example {K : WriterKey → Prop} {s : Stor} {st : State}
    (finite : WriterKeysFinite K)
    (fixed : WriterFixedMatches s st)
    (support : WriterSupport K s)
    (inj : WriterInj K)
    (apart : WriterApart K)
    (selected : WriterSelectedValues K s st)
    (logicalZero : WriterLogicalZero K st) :
    WriterRep K s st :=
  { finite := finite
    fixed := fixed
    support := support
    inj := inj
    apart := apart
    selected := selected
    logicalZero := logicalZero }

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SkimForwardEnv.FirstCallFresh
example {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g)
    (U : WriterKey → Prop) :
    env.FirstCallFresh U ↔
      ∃ R : Exec.Deriv, Blanc.Lift.StepIn R sevm
        (St env.qd0 (env.callGasT0.toB256 ::
          (skimToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          0 :: (128 + 164) :: 68 :: (128 + 164) :: 0 :: (68 + (128 + 164)) ::
          (skimToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          96 :: 0 :: (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b) ::
          skimToWord sevm :: skimToken0 sevm b :: 0x1a2b ::
          skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
          (safeTransfer_dynamicCallMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget env.qd0.returnData) 128
            (Bytes.toB256 (env.qd0.returnData.take 32) - skimReserve0 sevm b) (skimToWord sevm))
          env.callGasT0)
        (.exec .call) env.dt0 ∧
      WriterFreshKeys U ((Exec.rawFrameRoots R.exc).flatMap fun F =>
        if F.sevm.currentTarget = sevm.currentTarget
        then pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm else []) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair record: SkimForwardEnv
example {sevm : Sevm} {b : Devm} {g : Nat}
    (qd0 : Devm)
    (dt0 : Devm)
    (qd1 : Devm)
    (dt1 : Devm)
    (callGasQ0 : Nat)
    (callGasT0 : Nat)
    (callGasQ1 : Nat)
    (callGasT1 : Nat)
    (code0 : (((skimCachedWorld sevm b).getCode
      (skimToken0 sevm b).toAdr).size.toB256) ≠ 0)
    (sentry : gCallStipend < ((((callGasQ0 + 5) +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 186)) +
      sstoreCost sevm (afterSload sevm b 12) 12 0))
    (sentryU : gCallStipend < (g + 11) + sstoreCost sevm dt1 12 1)
    (qenv0 : SkimQueryEnv sevm
      (temporalAccountAccessBase (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr)
      (balanceRequestMemory getterInitMemory sevm.currentTarget) 128
      (skimToken0 sevm b)
      (164 :: 0x70a08231 :: skimToken0 sevm b :: skimReserve0 sevm b :: 0x1a26 ::
        skimToWord sevm :: skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      qd0 callGasQ0 (((callGasT0 +
        safeTransferPreCharge (balanceReplyMemory getterInitMemory sevm.currentTarget
          qd0.returnData).size 128 + 12)) + 80))
    (tenv0 : SwapTransferCallForward sevm qd0
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
      ((balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData).size)
      128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
      (skimToWord sevm) (skimToken0 sevm b) 0x1a2b callGasT0
      (((callGasQ1 + 5) +
        sloadCost sevm dt0 8 +
        swapStoreCost
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
            128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) dt0.returnData).size
          (swapMovedPointer 128 dt0.returnData).toNat +
        swapStoreCost
          (memExtSize
            (swapTransferMemory
              (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
              128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
              (skimToWord sevm) dt0.returnData).size
            (swapMovedPointer 128 dt0.returnData).toNat 32)
          ((swapMovedPointer 128 dt0.returnData) + 4).toNat +
        temporalAccountAccessCost (afterSload sevm dt0 8)
          ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
            skimToken1 sevm b)).toAdr + 171)) dt0)
    (code1 : ((((afterSload sevm dt0 8).getCode
      ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)).toAdr)).size.toB256) ≠ 0)
    (qenv1 : SkimQueryEnv sevm
      (temporalAccountAccessBase (afterSload sevm dt0 8)
        ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          skimToken1 sevm b)).toAdr)
      (skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget)
      (swapMovedPointer 128 dt0.returnData)
      (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
        skimToken1 sevm b)
      (((swapMovedPointer 128 dt0.returnData) + 36) :: 0x70a08231 ::
        (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&&
          skimToken1 sevm b) ::
        skimReserve1Word (dt0.getStorVal sevm.currentTarget 8) :: 0x1a26 ::
        skimToWord sevm :: skimToken1 sevm b :: 0x1aca :: skimToken1 sevm b ::
        skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      qd1 callGasQ1 (((callGasT1 +
        safeTransferPreCharge (((skimRequestMemory
          (swapTransferMemory
            (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
            128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
            (skimToWord sevm) dt0.returnData)
          (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
          [((swapMovedPointer 128 dt0.returnData).toNat, 36),
            ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
          (swapMovedPointer 128 dt0.returnData).toNat
          (qd1.returnData.take 32)).size
          (swapMovedPointer 128 dt0.returnData) + 12)) + 80))
    (tenv1 : SwapTransferCallForward sevm qd1
      (skimToken1 sevm b :: skimToken0 sevm b :: skimToWord sevm :: [0x0257, 0xbc25cf77])
      (((skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
        [((swapMovedPointer 128 dt0.returnData).toNat, 36),
          ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
        (swapMovedPointer 128 dt0.returnData).toNat (qd1.returnData.take 32))
      ((((skimRequestMemory
        (swapTransferMemory
          (balanceReplyMemory getterInitMemory sevm.currentTarget qd0.returnData)
          128 (Bytes.toB256 (qd0.returnData.take 32) - skimReserve0 sevm b)
          (skimToWord sevm) dt0.returnData)
        (swapMovedPointer 128 dt0.returnData) sevm.currentTarget).extends
        [((swapMovedPointer 128 dt0.returnData).toNat, 36),
          ((swapMovedPointer 128 dt0.returnData).toNat, 32)]).write
        (swapMovedPointer 128 dt0.returnData).toNat (qd1.returnData.take 32)).size)
      (swapMovedPointer 128 dt0.returnData)
      (Bytes.toB256 (qd1.returnData.take 32) -
        skimReserve1Word (dt0.getStorVal sevm.currentTarget 8))
      (skimToWord sevm) (skimToken1 sevm b) 0x1aca callGasT1 (g +
        sstoreCost sevm dt1 12 1 + 22) dt1) :
    SkimForwardEnv sevm b g :=
  { qd0 := qd0
    dt0 := dt0
    qd1 := qd1
    dt1 := dt1
    callGasQ0 := callGasQ0
    callGasT0 := callGasT0
    callGasQ1 := callGasQ1
    callGasT1 := callGasT1
    code0 := code0
    sentry := sentry
    sentryU := sentryU
    qenv0 := qenv0
    tenv0 := tenv0
    code1 := code1
    qenv1 := qenv1
    tenv1 := tenv1 }

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SkimForwardEnv.gas
example {sevm : Sevm} {b : Devm} {g : Nat} (env : SkimForwardEnv sevm b g)  :
    SkimForwardEnv.gas env =
      ((env.callGasQ0 + 5) +
      sstoreCost sevm (afterSload sevm b 12) 12 0 +
      sloadCost sevm (syncLockedWorld sevm b) 6 +
      sloadCost sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7 +
      sloadCost sevm (afterSload sevm (afterSload sevm (syncLockedWorld sevm b) 6) 7) 8 +
      swapStoreCost 96 128 + swapStoreCost 160 132 +
      temporalAccountAccessCost (skimCachedWorld sevm b) (skimToken0 sevm b).toAdr + 193 +
      sloadCost sevm b 12 + 23 + 63 + 123 + 63) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair record: MintPrefixCallee
example {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {toWord ρ : B256} {finalGas : Nat}
    (d0 : Devm)
    (d1 : Devm)
    (factoryPost : Devm)
    (callGas0 : Nat)
    (callGas1 : Nat)
    (factoryGas : Nat)
    (feeResidual : Nat)
    (sourceCost : Nat)
    (supplyCost : Nat)
    (recipientLoad : Nat)
    (creditCost : Nat)
    (lockLoad : Nat)
    (lockStore : Nat)
    (reserveLoad : Nat)
    (loadEq : lockLoad = sloadCost sevm b 12)
    (storeEq : lockStore = sstoreCost sevm (afterSload sevm b 12) 12 0)
    (reserveEq : reserveLoad = sloadCost sevm (mintLockedWorld sevm b) 8)
    (fee : MintFeePricingCallee sevm d1 factoryPost R
    (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
      sevm.currentTarget d1.returnData)
    feeResidual finalGas factoryGas sourceCost supplyCost recipientLoad creditCost
    (Bytes.toB256 (d1.returnData.take 32)) (Bytes.toB256 (d0.returnData.take 32))
    (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
    (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)) toWord ρ)
    (tokens : MintBalanceForward sevm (afterSload sevm (mintLockedWorld sevm b) 8) d0 d1 R M
    callGas0 callGas1
    (factoryGas + sloadCost sevm d1 5 +
      temporalAccountAccessCost (feeFactoryLoadWorld sevm d1) (feeFactoryWord sevm d1).toAdr + 360)
    (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
    (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)) toWord ρ)
    (sentry : gCallStipend < callGas0 + 5 +
    sloadCost sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6 +
    temporalAccountAccessCost (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6)
      ((afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr +
    166 + reserveLoad + 87 + lockStore) :
    MintPrefixCallee sevm b R M toWord ρ finalGas :=
  { d0 := d0
    d1 := d1
    factoryPost := factoryPost
    callGas0 := callGas0
    callGas1 := callGas1
    factoryGas := factoryGas
    feeResidual := feeResidual
    sourceCost := sourceCost
    supplyCost := supplyCost
    recipientLoad := recipientLoad
    creditCost := creditCost
    lockLoad := lockLoad
    lockStore := lockStore
    reserveLoad := reserveLoad
    loadEq := loadEq
    storeEq := storeEq
    reserveEq := reserveEq
    fee := fee
    tokens := tokens
    sentry := sentry }

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: MintPrefixCallee.gas
example {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {toWord ρ : B256} {finalGas : Nat} (c : MintPrefixCallee sevm b R M toWord ρ finalGas)  :
    MintPrefixCallee.gas c =
      (c.callGas0 + 5 + sloadCost sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6 +
    temporalAccountAccessCost (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6)
      ((afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr + 166 +
    c.reserveLoad + 100 + c.lockStore + c.lockLoad + 26) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair record: BurnForwardEnv
example {sevm : Sevm} {b : Devm} {g : Nat}
    (d0 : Devm)
    (d1 : Devm)
    (dF : Devm)
    (back : BurnBackForwardEnv sevm (burnBodyWorld sevm b d0 d1 dF)
    (burnBodyWorld sevm b d0 d1 dF).memory 128 (burnBodyWords sevm b d0 d1 dF) [0x89afcb44] (g + 64))
    (fee : BurnFeeCallee sevm d1 dF (burnMem2 sevm d0 d1) (burnB0 d0) (burnT1 sevm b) (burnT0 sevm b)
    (burnR1 sevm b) (burnR0 sevm b) (burnRecipientWord sevm) 0x053d [0x89afcb44] back.gas)
    (initial : BurnInitialCallee sevm b d0 d1 [0x89afcb44] fee.gas) :
    BurnForwardEnv sevm b g :=
  { d0 := d0
    d1 := d1
    dF := dF
    back := back
    fee := fee
    initial := initial }

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: BurnForwardEnv.gas
example {sevm : Sevm} {b : Devm} {g : Nat} (env : BurnForwardEnv sevm b g)  :
    BurnForwardEnv.gas env =
      (env.initial.gas + 249) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair record: SwapFrontForwardEnv
example {sevm : Sevm} {b : Devm} {st : State} {d0 d1 dC : Devm} {cg0 cg1 cgC Gc : Nat}
    (transfer0 : swapAmount0Out sevm ≠ 0 → SwapTransferCallForward sevm (swapPrefixWorld sevm b)
    (swapLocalsStack sevm st) getterInitMemory getterInitMemory.size 128 (swapAmount0Out sevm)
    (swapRecipientWord sevm) st.token0.toB256 0x8d0 cg0
    (swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
      (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) cg1
      (swapFrontCallbackGas sevm b d0 d1 cgC Gc)) d0)
    (transfer1 : swapAmount1Out sevm ≠ 0 → SwapTransferCallForward sevm
    (swapOptWorld (swapAmount0Out sevm) (swapPrefixWorld sevm b) d0) (swapLocalsStack sevm st)
    (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
    (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0).size
    (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) (swapRecipientWord sevm)
    st.token1.toB256 0x8e1 cg1 (swapFrontCallbackGas sevm b d0 d1 cgC Gc) d1)
    (callback : swapDataLength sevm ≠ 0 → SwapCallbackCallForward sevm
    (swapFrontTransferWorld sevm b d0 d1) (swapLocalsStack sevm st)
    (swapFrontTransferMem sevm d0 d1) (swapFrontPtr sevm d0 d1) (swapRecipientWord sevm)
    (swapAmount0Out sevm) (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) cgC Gc dC)
    (sentry : gCallStipend < swapFrontTransferGas sevm b d0 d1 cg0 cg1 cgC Gc +
    sstoreCost sevm (afterSload sevm b 12) 12 0) :
    SwapFrontForwardEnv sevm b st d0 d1 dC cg0 cg1 cgC Gc :=
  { transfer0 := transfer0
    transfer1 := transfer1
    callback := callback
    sentry := sentry }

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: swapFrontTransferGas
example (sevm : Sevm) (b d0 d1 : Devm)
    (cg0 cg1 cgC Gc : Nat)  :
    swapFrontTransferGas sevm b d0 d1 cg0 cg1 cgC Gc =
      (swapOptGas getterInitMemory 128 (swapAmount0Out sevm) cg0
    (swapOptGas (swapOptMem getterInitMemory 128 (swapAmount0Out sevm) (swapRecipientWord sevm) d0)
      (swapOptPtr 128 (swapAmount0Out sevm) d0) (swapAmount1Out sevm) cg1
      (swapFrontCallbackGas sevm b d0 d1 cgC Gc))) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair record: SwapBackCalleeEnv
example {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256} {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (d0 : Devm)
    (d1 : Devm)
    (callGas0 : Nat)
    (callGas1 : Nat)
    (first : SwapBalanceEnv sevm d M p w.token0 (w.token1 :: w.token0 :: 0 :: 0 :: swapCutTail w ρ R)
    d0 callGas0 (callGas1 + 5 + swapRequestCharge d0 (swapRequestSize n p) p w.token1 83 + 21))
    (second : SwapBalanceEnv sevm d0 (swapBalanceReply M p sevm.currentTarget d0.returnData) p
    w.token1 (w.token1 :: w.token0 :: 0 :: swapBalanceWord d0.returnData :: swapCutTail w ρ R) d1
    callGas1 (swapBackPostGas sevm d1 (swapRequestSize (swapRequestSize n p) p) p w
      (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData) G))
    (sentries : SwapUpdateSentries sevm d1 (swapRequestSize (swapRequestSize n p) p) p w.reserve0
    w.reserve1 (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapEventRunGas G (swapSyncSize (swapRequestSize (swapRequestSize n p) p) p) p
      (swapUnlockCost sevm d1 w.reserve0 w.reserve1 (swapBalanceWord d0.returnData)
        (swapBalanceWord d1.returnData)
        (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
        (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out)
        w.amount0Out w.amount1Out w.recipient)))
    (unlock : gCallStipend < G + 26 + swapUnlockCost sevm d1 w.reserve0 w.reserve1
    (swapBalanceWord d0.returnData) (swapBalanceWord d1.returnData)
    (swapInWord (swapBalanceWord d0.returnData) w.reserve0 w.amount0Out)
    (swapInWord (swapBalanceWord d1.returnData) w.reserve1 w.amount1Out)
    w.amount0Out w.amount1Out w.recipient) :
    SwapBackCalleeEnv sevm d M n p w ρ R G :=
  { d0 := d0
    d1 := d1
    callGas0 := callGas0
    callGas1 := callGas1
    first := first
    second := second
    sentries := sentries
    unlock := unlock }

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SwapBackCalleeEnv.gas
example {sevm : Sevm} {d : Devm} {M : Mem} {n : Nat} {p : B256}
    {w : SwapCutWords} {ρ : B256} {R : List B256} {G : Nat}
    (env : SwapBackCalleeEnv sevm d M n p w ρ R G)  :
    SwapBackCalleeEnv.gas env =
      (env.callGas0 + 5 + swapRequestCharge d n p w.token0 72 + 16) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: swapPrefixGas
example (sevm : Sevm) (b : Devm) (a0 : B256)  :
    swapPrefixGas sevm b a0 =
      (let locked := mintLockedWorld sevm b
  sloadCost sevm b 12 + sstoreCost sevm (afterSload sevm b 12) 12 0 + sloadCost sevm locked 8 +
    sloadCost sevm (afterSload sevm locked 8) 6 +
    sloadCost sevm (afterSload sevm (afterSload sevm locked 8) 6) 7 +
    (if a0 = 0 then 11 else 0) + 358) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: syncCalleePrefixGas
example (sevm : Sevm) (b : Devm) (callGas0 : Nat)  :
    syncCalleePrefixGas sevm b callGas0 =
      ((callGas0 + 5 + 22 + temporalAccountAccessCost (syncFirstWorld sevm b)
      (syncFirstToken sevm b).toAdr + sstoreCost sevm (afterSload sevm b 12) 12 0 +
      sloadCost sevm (syncLockedWorld sevm b) 6 + 126) + sloadCost sevm b 12 + 23) :=
  rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair record: SwapAbiGuards
example {sevm : Sevm}
    (args : (128 : B256).toNat ≤ (sevm.data.length.toB256 - 4).toNat)
    (offset : (swapDataOffset sevm).toNat ≤ (0x100000000 : B256).toNat)
    (head : (4 + swapDataOffset sevm + 32).toNat ≤ (4 + (sevm.data.length.toB256 - 4)).toNat)
    (length : (swapDataLength sevm).toNat ≤ (0x100000000 : B256).toNat)
    (tail : (swapDataStart sevm + swapDataLength sevm).toNat ≤
    (4 + (sevm.data.length.toB256 - 4)).toNat) :
    SwapAbiGuards sevm :=
  { args := args
    offset := offset
    head := head
    length := length
    tail := tail }

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SwapContextConditions
example (ctx : Context)  :
    SwapContextConditions ctx ↔
      (ctx.value = 0 ∧ ctx.isStatic = false) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: SwapModelConditions
example (st : State) (amount0Out amount1Out : B256)
    (recipient : Adr) (balance0 balance1 : B256)  :
    SwapModelConditions st amount0Out amount1Out recipient balance0 balance1 ↔
      (st.unlocked = 1 ∧
    (amount0Out > 0 ∨ amount1Out > 0) ∧
    amount0Out.toNat < st.reserve0.val ∧ amount1Out.toNat < st.reserve1.val ∧
    recipient ≠ st.token0 ∧ recipient ≠ st.token1 ∧
    balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧
    let inputs := swapInputs balance0 balance1 amount0Out amount1Out
      st.reserve0.val st.reserve1.val
    (inputs.1 > 0 ∨ inputs.2 > 0) ∧
      swapCheck balance0 balance1 inputs.1 inputs.2 st.reserve0.val st.reserve1.val = .ok ()) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: PermitRawCall
example (sevm : Sevm) (b : Devm) (sel : B256) (gw : B256) (callGas : Nat) (d : Devm)
    (out : Bytes)  :
    PermitRawCall sevm b sel gw callGas d out ↔
      (Ninst.Run sevm (St (permitNonceWorld sevm b (permitOwner sevm))
      (gw :: 1 :: 482 :: 128 :: 450 :: 32 :: permitPublicCallStack sevm b sel)
      (permitPublicCallMemory sevm b) callGas) (.exec .staticcall) d ∧
    StaticCallPost (permitNonceWorld sevm b (permitOwner sevm)) d
      (permitPublicCallStack sevm b sel) (permitPublicCallMemory sevm b) 482 128 450 32 1 out ∧
    out.length < 2 ^ 256 ∧
    StaticAnswered sevm (permitNonceWorld sevm b (permitOwner sevm)) (1 : B256).toAdr
      (ExternalOperation.encode
        (.recover (permitPublicDigest sevm b) (permitV sevm) (permitR sevm) (permitS sevm))) out ∧
    (permitRecoveredWord out).toAdr ≠ 0 ∧ (permitRecoveredWord out).toAdr = permitOwner sevm) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: PermitSourceResult
example (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat)
    (sevm : Sevm) (b post d : Devm) (out : Bytes) (codeExists : Bool) (residual : Nat)  :
    PermitSourceResult K current invocation sevm b post d out codeExists residual ↔
      (post = permitPublicPost sevm b d out 0xd505accf residual ∧
  WriterRep (WriterExtend K (permitTouched (permitOwner sevm) (permitSpender sevm)))
    (post.getStor sevm.currentTarget)
    (permitSourceState current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)) ∧
  startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm) =
    .suspended (permitSuspendedFrame current (writerContext sevm invocation) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm)
      (permitS sevm))
      (permitRequest current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
        (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm))
      (.permitRecovery (permitOwner sevm) (permitSpender sevm) (permitValue sevm)) ∧
  (permitRequest current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
    (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).calldata =
    ExternalOperation.encode
      (.recover (permitPublicDigest sevm b) (permitV sevm) (permitR sevm) (permitS sevm)) ∧
  (permitRequest current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
    (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).target = (1 : B256).toAdr ∧
  ExactConsumes (startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm))
    (.next (permitExternalResult out codeExists) .done .done)
    (permitSourceDone current (writerContext sevm invocation) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm)
      (permitS sevm)) ∧
  drive 3 (startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm))
    (.next (permitExternalResult out codeExists) .done .done) =
    permitSourceDone current (writerContext sevm invocation) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm)
      (permitS sevm) ∧
  (permitSourceFrame current (writerContext sevm invocation) (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).checkpoint =
    current ∧
  (permitSourceFrame current (writerContext sevm invocation) (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).current.logs =
    current.logs ++ [.owned (permitSourceOrigin (writerContext sevm invocation))
      (.approval (permitOwner sevm) (permitSpender sevm) (permitValue sevm))] ∧
  (permitSourceFrame current (writerContext sevm invocation) (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).current.updates =
    current.updates ∧
  post.output = [] ∧
  post.logs = b.logs ++
    [approvalRawLog sevm.currentTarget (permitOwner sevm) (permitSpender sevm) (permitValue sevm)] ∧
  post.getStor sevm.currentTarget =
    (((b.getStor sevm.currentTarget).set (permitNonceSlot (permitOwner sevm))
      (current.state.nonces (permitOwner sevm) + 1)).set
      (mapSlot (permitSpender sevm).toB256 (mapSlot (permitOwner sevm).toB256 2))
      (permitValue sevm)) ∧
  (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) ∧
  post.gasLeft = residual) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: BurnEntryAuthenticFinished
example (U K : WriterKey → Prop) (current : Checkpoint) (D : Exec.Deriv)
    (b : Devm) (o : Outcome) (invocation : List Nat)  :
    BurnEntryAuthenticFinished U K current D b o invocation ↔
      (let ctx := writerContext D.sevm invocation
  let recipient := ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord D.sevm 4).toAdr
  ∃ (a : BurnAnswers) (amount0 amount1 : B256),
    BurnCallProvenance D (b.getStor D.sevm.currentTarget) amount0 amount1 a ∧
    ∃ (K' : WriterKey → Prop) (final : Frame) (rets : List ChildReturn) (publicPost : Devm)
      (added : List PendingLog) (rawLogs : List Log),
      (∀ k, K' k → U k) ∧ (∀ k, K k → K' k) ∧
      ExactConsumes (startTyped current ctx (.burn recipient)) a.transcript
        { status := .success (encodeWords [amount0, amount1]), frame := final,
          remaining := .done, childReturns := rets } ∧
      o = .halted publicPost ∧ publicPost.output = encodeWords [amount0, amount1] ∧
      WriterRep K' (publicPost.getStor D.sevm.currentTarget) final.current.state ∧
      final.checkpoint = current ∧ final.context = ctx ∧ final.current.state.unlocked = 1 ∧
      final.current.logs = current.logs ++ added ∧ publicPost.logs = b.logs ++ rawLogs ∧
      added.map (PendingLog.rawWith (burnOwnedRaw D.sevm.currentTarget)) = rawLogs.map some) :=
  Iff.rfl

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair
open Jaune

-- Uniswap V2 Pair definition: runSourceInvocations
example (st : State) :
    runSourceInvocations st [] = some st :=
  rfl

example (st : State) (inv : SourceInvocation) (rest : List SourceInvocation) :
    runSourceInvocations st (inv :: rest) =
      (let out := inv.run st
      match out.status with
      | .success _ => runSourceInvocations out.frame.current.state rest
      | _ => none) :=
  rfl

-- Uniswap V2 Pair definition: SourceReplay
example (st : State) : SourceReplay st [] st :=
  SourceReplay.nil st

example {st finish : State} {inv : SourceInvocation} {rest : List SourceInvocation}
    {out : RunResult} {bytes : Bytes}
    (consumed : ExactConsumes
      (startTyped { state := st, logs := [], updates := [] } inv.context inv.entry)
      inv.transcript out)
    (successful : out.status = .success bytes)
    (tail : SourceReplay out.frame.current.state rest finish) :
    SourceReplay st (inv :: rest) finish :=
  SourceReplay.cons consumed successful tail

-- Uniswap V2 Pair definition: sourceReplayUpdates
example (st : State) : sourceReplayUpdates st [] = [] :=
  rfl

example (st : State) (inv : SourceInvocation) (rest : List SourceInvocation) :
    sourceReplayUpdates st (inv :: rest) =
      (inv.run st).frame.current.updates ++
        sourceReplayUpdates (inv.run st).frame.current.state rest :=
  rfl

-- Uniswap V2 Pair definition: sourceReplayAnswers
example (st : State) : sourceReplayAnswers st [] ↔ True :=
  Iff.rfl

example (st : State) (inv : SourceInvocation) (rest : List SourceInvocation) :
    sourceReplayAnswers st (inv :: rest) ↔
      (EntryFeeOff inv.entry inv.transcript ∧
        EntryNoShrink st inv.context inv.entry inv.transcript ∧
        sourceReplayAnswers (inv.run st).frame.current.state rest) :=
  Iff.rfl

-- Uniswap V2 Pair definition: sourceReplayNoShrink
example (st : State) : sourceReplayNoShrink st [] ↔ True :=
  Iff.rfl

example (st : State) (inv : SourceInvocation) (rest : List SourceInvocation) :
    sourceReplayNoShrink st (inv :: rest) ↔
      (EntryNoShrink st inv.context inv.entry inv.transcript ∧
        sourceReplayNoShrink (inv.run st).frame.current.state rest) :=
  Iff.rfl

-- Uniswap V2 Pair definition: sourceReplayEdges
example (st : State) : sourceReplayEdges st [] = [] :=
  rfl

example (st : State) (inv : SourceInvocation) (rest : List SourceInvocation) :
    sourceReplayEdges st (inv :: rest) =
      (st, (inv.run st).frame.current.state) ::
        sourceReplayEdges (inv.run st).frame.current.state rest :=
  rfl

-- Uniswap V2 Pair definition: sourceReplaySteps
example (st : State) : sourceReplaySteps st [] = [] :=
  rfl

example (st : State) (inv : SourceInvocation) (rest : List SourceInvocation) :
    sourceReplaySteps st (inv :: rest) =
      (st, inv, (inv.run st).frame.current.state) ::
        sourceReplaySteps (inv.run st).frame.current.state rest :=
  rfl

-- Uniswap V2 Pair definition: sourceReplayReceipts
example (st : State) : sourceReplayReceipts st [] = [] :=
  rfl

example (st : State) (inv : SourceInvocation) (rest : List SourceInvocation) :
    sourceReplayReceipts st (inv :: rest) =
      (inv, (inv.run st).frame.current.updates) ::
        sourceReplayReceipts (inv.run st).frame.current.state rest :=
  rfl

-- Uniswap V2 Pair definition: oracleSum0
example : oracleSum0 [] = 0 :=
  rfl

example (tagged : TaggedOracleUpdate) (updates : List TaggedOracleUpdate) :
    oracleSum0 (tagged :: updates) = tagged.update.increment0 + oracleSum0 updates :=
  rfl

-- Uniswap V2 Pair definition: oracleSum1
example : oracleSum1 [] = 0 :=
  rfl

example (tagged : TaggedOracleUpdate) (updates : List TaggedOracleUpdate) :
    oracleSum1 (tagged :: updates) = tagged.update.increment1 + oracleSum1 updates :=
  rfl

-- Uniswap V2 Pair definition: OracleTimestampChain
example (start finish : UInt32) : OracleTimestampChain start finish [] ↔ finish = start :=
  Iff.rfl

example (start finish : UInt32) (tagged : TaggedOracleUpdate)
    (updates : List TaggedOracleUpdate) :
    OracleTimestampChain start finish (tagged :: updates) ↔
      (tagged.update.oldTimestamp = start ∧
        OracleTimestampChain (UInt32.ofNat (tagged.update.timestamp.toNat % 2 ^ 32)) finish
          updates) :=
  Iff.rfl

-- Uniswap V2 Pair definition: LedgerWriter
example : LedgerWriter.approve.selector = 0x095ea7b3 := rfl
example : LedgerWriter.transfer.selector = 0xa9059cbb := rfl
example : LedgerWriter.transferFrom.selector = 0x23b872dd := rfl

example : LedgerWriter.approve.entry = approveDecodedEntry := rfl
example : LedgerWriter.transfer.entry = transferDecodedEntry := rfl
example : LedgerWriter.transferFrom.entry = transferFromDecodedEntry := rfl

example (sevm : Sevm) :
    LedgerWriter.approve.keys sevm = approveTouched sevm.caller (approveSpender sevm) :=
  rfl

example (sevm : Sevm) :
    LedgerWriter.transfer.keys sevm = transferTouched sevm.caller (transferRecipient sevm) :=
  rfl

example (sevm : Sevm) :
    LedgerWriter.transferFrom.keys sevm =
      transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm) :=
  rfl

example : LedgerWriter.approve.calldataSize = 68 := rfl
example : LedgerWriter.transfer.calldataSize = 68 := rfl
example : LedgerWriter.transferFrom.calldataSize = 100 := rfl

example (sevm : Sevm) (b : Devm) :
    LedgerWriter.approve.cost sevm b =
      sstoreCost sevm b (approveSlot sevm) (approveAmount sevm) + 2342 :=
  rfl

example (sevm : Sevm) (b : Devm) :
    LedgerWriter.transfer.cost sevm b =
      transferSourceCharge sevm b + transferDebitCharge sevm b +
        transferRecipientCharge sevm b + transferCreditCharge sevm b + 2740 :=
  rfl

example (sevm : Sevm) (b : Devm) :
    LedgerWriter.transferFrom.cost sevm b = transferFromPublicGas sevm b :=
  rfl

example (sevm : Sevm) (b : Devm) (G : Nat) :
    LedgerWriter.approve.post sevm b G =
      approvePublicPost sevm b [0x095ea7b3] getterInitMemory G :=
  rfl

example (sevm : Sevm) (b : Devm) (G : Nat) :
    LedgerWriter.transfer.post sevm b G =
      transferPublicPost sevm b [0xa9059cbb] getterInitMemory G :=
  rfl

example (sevm : Sevm) (b : Devm) (G : Nat) :
    LedgerWriter.transferFrom.post sevm b G =
      transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G :=
  rfl

example (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat) (sevm : Sevm)
    (b d : Devm) (G : Nat) :
    LedgerWriter.approve.Result K current invocation sevm b d G ↔
      ApproveSourceResult K current invocation sevm b d G :=
  Iff.rfl

example (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat) (sevm : Sevm)
    (b d : Devm) (G : Nat) :
    LedgerWriter.transfer.Result K current invocation sevm b d G ↔
      TransferSourceResult K current invocation sevm b d G :=
  Iff.rfl

example (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat) (sevm : Sevm)
    (b d : Devm) (G : Nat) :
    LedgerWriter.transferFrom.Result K current invocation sevm b d G ↔
      TransferFromSourceResult K current invocation sevm b d G :=
  Iff.rfl

-- Uniswap V2 Pair definition: StaticView.selector
example (s : ScalarGetter) : (StaticView.scalar s).selector = s.selector := rfl
example (s : StringGetter) : (StaticView.string s).selector = s.selector := rfl
example : StaticView.totalSupply.selector = 0x18160ddd := rfl
example : (StaticView.singleMapping .balanceOf).selector = 0x70a08231 := rfl
example : (StaticView.singleMapping .nonces).selector = 0x7ecebe00 := rfl
example : StaticView.allowance.selector = 0xdd62ed3e := rfl
example : StaticView.getReserves.selector = 0x0902f1ac := rfl

end Blanc.Lift.UniswapV2Pair

/-! ## Paper review 2 approved statement coverage -/

-- Paper review 2 statement: weth9_history_tx_withdraw
namespace Blanc.Lift.Weth9
open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

example : ∀ {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace))
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E : Adr} {wad : B256}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat}
    (hstate : benv.state = future.state)
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some ca) [])
    (hvalue : tx.value = 0) (hdata : tx.data = withdrawCalldata wad)
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hgas : withdrawIntrinsicGas wad + withdrawFrameGas wad + 811 ≤ tx.gas)
    (hcap : tx.gas ≤ 16777216)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce) (hnonceMax : tx.nonce ≠ UInt64.max)
    (hnocode : (benv.state.getCode E).size = 0)
    (hfunds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat)
    (hprecE : benv.stat.rules.isPrecomp E = false) (hprecCa : benv.stat.rules.isPrecomp ca = false)
    (hholder : historyKeyUniverse ca trace K₀ (.bal E))
    (hbal : wad ≤ (future.state.getStor ca).get (balSlot E))
    (hcbE : benv.stat.coinbase ≠ E) (hcbCa : benv.stat.coinbase ≠ ca),
    ∃ (st : Jaune.State) (bout' : BlockOutput), processTransaction benv bout tx index = .ok (st, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        withdrawGasUsed ((future.state.getStor ca).get (balSlot E)) wad ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        withdrawGasUsed ((future.state.getStor ca).get (balSlot E)) wad ∧
      st.getStor ca = (future.state.getStor ca).set (balSlot E)
        ((future.state.getStor ca).get (balSlot E) - wad) ∧
      (∀ a, a ≠ ca → st.getStor a = future.state.getStor a) ∧
      (st.get E).nonce = tx.nonce + 1 ∧
      (st.get E).bal = future.state.bal E -
          (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 + wad +
        ((tx.gas - withdrawGasUsed ((future.state.getStor ca).get (balSlot E)) wad) *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 ∧
      (st.get ca).bal = future.state.bal ca - wad ∧
      ((future.state.bal E).toNat + wad.toNat < 2 ^ 256 →
        (st.get E).bal.toNat + withdrawGasUsed ((future.state.getStor ca).get (balSlot E)) wad *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) =
          (future.state.bal E).toNat + wad.toNat) :=
  @weth9_history_tx_withdraw

end Blanc.Lift.Weth9

-- Paper review 2 statement: vplus_reachable_capstone
namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
open Jaune.Exec.Deriv (ParentPrefix)
open Blanc.Lift.VyperNonreentrantDeployed.Fixed (ActiveRel lockBodies lockL)

example : ∀ (fork : Fork) (hfork : CoveredFork fork),
    ∃ postI postP postInit postOracle postT postR postA postD postX : Devm,

      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
      processMessage (initMsg fork postP.state) = .ok postInit ∧ postInit.error = none ∧
      processMessage (oracleMsg fork postInit.state) = .ok postOracle ∧
      postOracle.error = none ∧ CleanPool postOracle.state ∧
      processCreateMessage (tokenCreateMsg fork postOracle.state) = .ok postT ∧
      postT.error = none ∧
      processCreateMessage (receiverCreateMsg fork postT.state) = .ok postR ∧
      postR.error = none ∧
      processMessage (approveMsg fork postR.state) = .ok postA ∧ postA.error = none ∧
      processMessage (addMsg fork postA.state) = .ok postD ∧ postD.error = none ∧

      Checkpoint postD.state ∧
      (storOf postD.state proxyAddr 0x16).toNat =
        Blanc.ledgerSumOn {creator} (fun holder => storOf postD.state proxyAddr (lpSlot holder)) ∧
      storOf postD.state proxyAddr 0x16 = 2000 ∧

      processMessage (removeMsg fork postD.state) = .ok postX ∧ postX.error = none ∧
      postX.gasLeft = 920078 ∧
      (Frame.ofCall (removeMsg fork postD.state)).enter = .run (eTop.re fork world8) ∧
      postD.state = world8 ∧ postX = dTop ∧
      ∃ (out : Execution) (R : Exec 0 (reS eTop.sta fork) eTop.dyna out)
        (F h c q G : Exec.Deriv),

        F ∈ Exec.rawFrameRoots R ∧ ActiveRel proxyAddr F h ∧ Spawns h c ∧ h.pc = 7427 ∧
        c.sevm.currentTarget = receiverAddr ∧ c.sevm.value.toNat = 100 ∧

        q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = proxyAddr ∧
        G ∈ Exec.rawFrameRoots q.exc ∧ CPFrame proxyAddr code G ∧ G.sevm.data = reentryData ∧
        G.exn = .error (.revert, dRe) ∧ (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
        (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) ∧

        lockL.HashAvoidIn proxyAddr R ∧
        (∀ G' ∈ Exec.rawFrameRoots c.exc, ¬ lockL.Enters proxyAddr G') ∧
        ¬ lockL.Enters proxyAddr G ∧

        out = .ok postX ∧
        (storOf postX.state proxyAddr 0x16).toNat =
          Blanc.ledgerSumOn {creator} (fun holder => storOf postX.state proxyAddr (lpSlot holder)) ∧
        storOf postX.state proxyAddr 0x16 = 1800 ∧
        (postX.state.get receiverAddr).bal = 100 ∧
        storOf postX.state tokenAddr receiverAddr.toB256 = 100 ∧
        (postX.state.get proxyAddr).bal = 900 ∧ storOf postX.state proxyAddr 0 = 3 :=
  @vplus_reachable_capstone

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit

-- Paper review 2 statement: vminus_reachable_capstone
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol


example : CapstoneStmt :=
  @vminus_reachable_capstone

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

-- Paper review 2 statement: vminus_reach_violation
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol


example : ViolationStmt :=
  @vminus_reach_violation

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

-- Paper review 2 statement: registerPauser_nonzero_finite
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc Blanc.Lift Blanc.LidoCircuitBreaker

example : ∀ {sevm : Sevm} {pre post : Devm}
    {entries : List LidoCircuitBreaker.Entry} {probes : List B256}
    {index : Nat} {oldPauser : B256}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hinstalled : Devm.getCode pre sevm.currentTarget = code)
    (hcode : sevm.code = Devm.getCode pre sevm.currentTarget)
    (hfresh : Exec.FreshEntry sevm pre)
    (hsig : Sevm.dataWord sevm 0 >>> 224 = selector "registerPauser" [.address, .address])
    (hpre : checkRegistryOn (solRegistryStorage (Devm.getStor pre sevm.currentTarget))
      entries probes = true)
    (hcover : checkLiveCovered entries probes = true)
    (hclosure : Sevm.dataWord sevm 4 ∈ probes ∧ oldPauser ∈ probes ∧
      Sevm.dataWord sevm 36 ∈ probes)
    (hnew : Sevm.dataWord sevm 36 ≠ 0)
    (hfind : findEntry entries (Sevm.dataWord sevm 4) = some (index, oldPauser))
    (hfaithful : SlotFootprint.checkFaithfulOn solKey (registryQueries probes entries.length)
      ((nonzeroWrites entries (Sevm.dataWord sevm 4) (Sevm.dataWord sevm 36) oldPauser).map
        Prod.fst) = true)
    (hapart : SlotFootprint.checkApartOn solKey (registryQueries probes entries.length)
      [mapSlot oldPauser 2, mapSlot (Sevm.dataWord sevm 36) 2] = true)
    (execution : Exec 0 sevm pre (.ok post)),
    checkRegistryOn (solRegistryStorage (Devm.getStor post sevm.currentTarget))
      (setEntryAt index (Sevm.dataWord sevm 4, Sevm.dataWord sevm 36) entries) probes = true ∧
    checkLiveCovered
      (setEntryAt index (Sevm.dataWord sevm 4, Sevm.dataWord sevm 36) entries) probes = true :=
  @registerPauser_nonzero_finite

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 statement: lido_create_finite_init
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc Blanc.Lift Blanc.LidoCircuitBreaker Blanc.ForkUniform

example : ∀ (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Creation.code)
    (hgas : 1000000 ≤ msg.gas) (hfork : CoveredFork msg.benv.stat.fork)
    (hstatic : msg.isStatic = false)
    (hmax : 4584 ≤ msg.benv.stat.rules.code.maxCodeSize)
    {probes : List B256} (hp : ∀ p ∈ probes, canonicalAddress p)
    (hapart : Blanc.SlotFootprint.checkApartOn solKey
      (registryQueries probes 0) [0, 1] = true),
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList =
        Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
      RegistryOn (solRegistryStorage (Devm.getStor post msg.currentTarget)) [] probes :=
  @lido_create_finite_init

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 statement: exampleApplicable
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc Blanc.LidoCircuitBreaker

example : checkRegistryOn (solRegistryStorage exampleStorage) exampleEntries exampleProbes = true ∧
    checkLiveCovered exampleEntries exampleProbes = true ∧
    findEntry exampleEntries 1 = some (0, 2) ∧
    ((1 : B256) ∈ exampleProbes ∧ (2 : B256) ∈ exampleProbes ∧ (3 : B256) ∈ exampleProbes) ∧
    (3 : B256) ≠ 0 ∧
    SlotFootprint.checkFaithfulOn solKey (registryQueries exampleProbes exampleEntries.length)
      ((nonzeroWrites exampleEntries 1 3 2).map Prod.fst) = true ∧
    SlotFootprint.checkApartOn solKey (registryQueries exampleProbes exampleEntries.length)
      [mapSlot 2 2, mapSlot 3 2] = true :=
  @exampleApplicable

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 statement: checkRegistryOn_eq_true
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc.LidoCircuitBreaker

example : ∀ {storage : LogicalStorage} {entries : List Entry}
    {probes : List B256},
    checkRegistryOn storage entries probes = true ↔ RegistryOn storage entries probes :=
  @checkRegistryOn_eq_true

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 statement: checkLiveCovered_eq_true
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc.LidoCircuitBreaker

example : ∀ {entries : List Entry} {probes : List B256},
    checkLiveCovered entries probes = true ↔ ∀ e ∈ entries, e.1 ∈ probes ∧ e.2 ∈ probes :=
  @checkLiveCovered_eq_true

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 statement: pair_history_minimum_liquidity
namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

example : ∀ {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {factory token0 token1 : Adr} {domain : B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeys pair trace))
    (nonzero : pair ≠ 0),
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        ((∀ s ∈ steps, s.source.CallersNonzero) →
          finish.SupplyFloor ∧
          ∀ before after, (before, after) ∈ sourceReplayEdges
              (initializedState factory domain token0 token1) (steps.map PairStep.source) →
            before.SupplyFloor ∧ after.SupplyFloor ∧
              (0 < before.totalSupply.toNat → 1000 ≤ after.totalSupply.toNat)) :=
  @pair_history_minimum_liquidity

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: pair_history_feeOff_ratio
namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

example : ∀ {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {factory token0 token1 : Adr} {domain : B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : InitializedCheckpoint (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeys pair trace))
    (nonzero : pair ≠ 0),
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        runSourceInvocations (initializedState factory domain token0 token1)
          (steps.map PairStep.source) = some finish ∧
        WriterRep K' (future.state.getStor pair) finish ∧
        (sourceReplayAnswers (initializedState factory domain token0 token1)
            (steps.map PairStep.source) →
          (∀ s ∈ steps, s.source.CallersNonzero) →
          ∀ before after, (before, after) ∈ sourceReplayEdges
              (initializedState factory domain token0 token1) (steps.map PairStep.source) →
            0 < before.totalSupply.toNat →
            1000 ≤ after.totalSupply.toNat ∧
              ((before.reserve0.val * before.reserve1.val : ℚ) / (before.totalSupply.toNat : ℚ) ^ 2 ≤
                (after.reserve0.val * after.reserve1.val : ℚ) / (after.totalSupply.toNat : ℚ) ^ 2)) :=
  @pair_history_feeOff_ratio

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: runTyped_mint_initial
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes} (zeroSupply : st.totalSupply = 0)
    (successful : (runTyped st ctx (.mint recipient) transcript).status = .success returndata),
    InitialMintResult st
      (mintObservation recipient st.cachedReserves transcript.firstWord transcript.ownTail.firstWord)
      (runTyped st ctx (.mint recipient) transcript).frame.current.state returndata :=
  @runTyped_mint_initial

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: runTyped_mint_later
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee { st with unlocked := 0 }
      transcript.ownTail.ownTail.firstWord.toAdr
      st.reserve0.val st.reserve1.val = .ok fee)
    (positiveSupply : fee.state.totalSupply ≠ 0)
    (successful : (runTyped st ctx (.mint recipient) transcript).status = .success returndata),
    LaterMintResult st
      (mintObservation recipient st.cachedReserves transcript.firstWord transcript.ownTail.firstWord)
      fee (runTyped st ctx (.mint recipient) transcript).frame.current.state returndata :=
  @runTyped_mint_later

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: runTyped_burn_payout
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    {fee : FeeResult}
    (feeAccepted : mintFee { st with unlocked := 0 }
      transcript.ownTail.ownTail.firstWord.toAdr
      st.reserve0.val st.reserve1.val = .ok fee)
    (successful : (runTyped st ctx (.burn recipient) transcript).status = .success returndata),
    BurnPayoutResult st ctx recipient
      (burnObservation recipient st ctx.pair transcript.firstWord transcript.ownTail.firstWord)
      fee returndata (runTypedRequests st ctx (.burn recipient) transcript) :=
  @runTyped_burn_payout

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: runTyped_swap_canonical_success
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {st : State} {ctx : Context}
    {amount0Out amount1Out : B256} {recipient : Adr} {data : Bytes}
    {balance0 balance1 : B256}
    (context : SwapContextConditions ctx)
    (conditions : SwapModelConditions st amount0Out amount1Out recipient balance0 balance1),
    (runTyped st ctx (.swap amount0Out amount1Out recipient data)
      (swapCanonicalTranscript amount0Out amount1Out balance0 balance1 data)).status = .success [] :=
  @runTyped_swap_canonical_success

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: swap_uint112_control
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : SwapContextConditions swapControlContext ∧
      swapControlState.unlocked = 1 ∧
      ((1 : B256) > 0 ∨ (0 : B256) > 0) ∧
        (1 : B256).toNat < 10 ∧ (0 : B256).toNat < 10 ∧
        (300 : Adr) ≠ 100 ∧ (300 : Adr) ≠ 200 ∧
        (10 : B256).toNat < 2 ^ 112 ∧
        (let inputs := swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10
         inputs.1 > 0 ∨ inputs.2 > 0) ∧
        swapCheck (Nat.toB256 (2 ^ 112)) 10
          (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).1
          (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).2 10 10 = .ok () ∧
        (Nat.toB256 (2 ^ 112)).toNat = 2 ^ 112 ∧
        ¬((Nat.toB256 (2 ^ 112)).toNat < 2 ^ 112) ∧
        ¬((runTyped swapControlState swapControlContext
          (.swap 1 0 300 [])
          (swapCanonicalTranscript 1 0 (Nat.toB256 (2 ^ 112)) 10 [])).status = .success []) :=
  @swap_uint112_control

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: sqrt_of_run
namespace Blanc.Lift.UniswapV2Pair
open Jaune
open Blanc.BabylonianSqrt

example : ∀ {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (Y :: R :: T) M G) t_2878_c69 o),
    ∃ G', o = .returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G') :=
  @sqrt_of_run

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: sqrt_exact
namespace Blanc.Lift.UniswapV2Pair
open Jaune
open Blanc.BabylonianSqrt

example : ∀ {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} (hroom : T.length ≤ 1014),
    SFunc.RunExact cert.prog sevm (St b (Y :: R :: T) M (G + sqrtCharge Y.toNat))
      t_2878_c69 (.returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G)) :=
  @sqrt_exact

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: swap_bytecode_exact_consumes
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))),
    SwapCanonicalBody (fun _ => True) K current invocation run :=
  @swap_bytecode_exact_consumes

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: pairAddress_eq
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example : pairAddress = create2NewAddress factory salt code.toList :=
  @pairAddress_eq

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 statement: pairAddress_wrong_salt
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example : create2AddressOfHash factory (saltWord ^^^ 1) initHash ≠ pairAddress :=
  @pairAddress_wrong_salt

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 statement: pairAddress_wrong_initHash
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example : create2AddressOfHash factory saltWord (initHash ^^^ 1) ≠ pairAddress :=
  @pairAddress_wrong_initHash

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 statement: noShrink_required
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example : (runTyped (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
      .done).status = .success [] ∧
    mintRun.status = .success (encodeWords [1]) ∧ donationRun.status = .success [] ∧
    0 < checkpoint.totalSupply.toNat ∧ shrinkingRun.status = .success [] ∧
    ¬ SyncEntryNoShrink checkpoint shrinkingTranscript ∧
    ¬ (checkpoint.reserve0.val * checkpoint.reserve1.val * shrunk.totalSupply.toNat ^ 2 ≤
      shrunk.reserve0.val * shrunk.reserve1.val * checkpoint.totalSupply.toNat ^ 2) :=
  @noShrink_required

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 statement: mintRoundUp_breaks_feeOff_product
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example : (runTypedWith mintRoundUp (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
      .done).status = .success [] ∧
    (runTypedWith mintRoundUp (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
      .done).frame.current.state = initialized ∧
    upMintRun.status = .success (encodeWords [1]) ∧
    upDonationRun.status = .success [] ∧ upDonationRun.frame.current.state = checkpoint ∧
    0 < checkpoint.totalSupply.toNat ∧ EntryFeeOff (.mint 20) laterTranscript ∧
    EntryNoShrink checkpoint context (.mint 20) laterTranscript ∧
    (runTyped checkpoint context (.mint 20) laterTranscript).status = .success (encodeWords [1]) ∧
    checkpoint.reserve0.val * checkpoint.reserve1.val *
        (runTyped checkpoint context (.mint 20) laterTranscript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped checkpoint context (.mint 20) laterTranscript).frame.current.state.reserve0.val *
        (runTyped checkpoint context (.mint 20) laterTranscript).frame.current.state.reserve1.val *
        checkpoint.totalSupply.toNat ^ 2 ∧
    upLaterRun.status = .success (encodeWords [2]) ∧
    ¬ (checkpoint.reserve0.val * checkpoint.reserve1.val *
        upLaterRun.frame.current.state.totalSupply.toNat ^ 2 ≤
      upLaterRun.frame.current.state.reserve0.val * upLaterRun.frame.current.state.reserve1.val *
        checkpoint.totalSupply.toNat ^ 2) :=
  @mintRoundUp_breaks_feeOff_product

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 statement: feeMutant_disagrees
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example : (runTyped checkpoint context (.swap 0 1001 20 []) feeSwapTranscript).status =
      .failed (.sourceGuard "UniswapV2: K") ∧
    feeMutantRun.status = .success [] ∧
    feeMutantRun.frame.current.state.reserve0.val = 1006015 ∧
    feeMutantRun.frame.current.state.reserve1.val = 1 :=
  @feeMutant_disagrees

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 statement: burnRoundUp_disagrees
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example : (runTyped checkpoint { context with sender := 20 } (.transfer 17 1) .done).status =
      .success (encodeWords [1]) ∧
    (runTyped burnReady context (.burn 20) burnTranscript).status =
      .success (encodeWords [1, 1]) ∧
    (runTypedWith burnRoundUp burnReady context (.burn 20) burnTranscript).status =
      .success (encodeWords [2, 2]) :=
  @burnRoundUp_disagrees

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 statement: oracle_law_requires_timestamp_wrap
namespace Blanc.Lift.UniswapV2Pair.OracleControls
open Jaune

example : wrapRun.status = .success [] ∧
    ∃ u ∈ wrapRun.frame.current.updates, u.update.Lawful ∧ ¬ u.update.LawfulNoWrap :=
  @oracle_law_requires_timestamp_wrap

end Blanc.Lift.UniswapV2Pair.OracleControls

-- Paper review 2 statement: swap_bytecode_uint112_control
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    (swapCheck (Nat.toB256 (2 ^ 112)) 10
        (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).1
        (swapInputs (Nat.toB256 (2 ^ 112)) 10 1 0 10 10).2 10 10 = .ok () ∧
      (Nat.toB256 (2 ^ 112)).toNat = 2 ^ 112 ∧
      ¬((runTyped swapControlState swapControlContext (.swap 1 0 300 [])
        (swapCanonicalTranscript 1 0 (Nat.toB256 (2 ^ 112)) 10 [])).status = .success [])) ∧
    ∃ (d d0 d1 : Devm) (M M0 : Mem) (p t0 t1 : B256) (S0 S1 : List B256) (out0 out1 : Bytes),
      t0 = (0xffffffffffffffffffffffffffffffffffffffff &&& b.getStorVal sevm.currentTarget 6) ∧
      t1 = (0xffffffffffffffffffffffffffffffffffffffff &&& b.getStorVal sevm.currentTarget 7) ∧
      SwapBalanceCall ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm d M p t0 S0 d0 out0 ∧
      SwapBalanceCall ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm d0 M0 p t1 S1 d1 out1 ∧
      ¬(2 ^ 112 ≤ (swapBalanceWord out0).toNat) ∧ ¬(2 ^ 112 ≤ (swapBalanceWord out1).toNat) :=
  @swap_bytecode_uint112_control

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: approve_storage_alias_breaks_ledger
namespace Blanc.Lift.UniswapV2Pair.LedgerKeyControl
open Jaune

example : ∀ {K : WriterKey → Prop} {sevm : Sevm}
    {b post : Devm} {G : Nat} {keys : List Adr} {a : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (tracked : K (.balance a)) (inj : WriterInj K) (apart : WriterApart K)
    (member : a ∈ keys)
    (aliasing : approveSlot sevm = (WriterKey.balance a).slot)
    (differs : approveAmount sevm ≠ rawBalance (b.getStor sevm.currentTarget) a)
    (ledger : RawLedgerOn keys (b.getStor sevm.currentTarget)),
    ¬ WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm)) ∧
    ¬ RawLedgerOn keys (post.getStor sevm.currentTarget) :=
  @approve_storage_alias_breaks_ledger

end Blanc.Lift.UniswapV2Pair.LedgerKeyControl

-- Paper review 2 statement: sync_no_success_of_reverting_token0
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    False :=
  @sync_no_success_of_reverting_token0

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: sync_no_success_of_reverting_token1
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    False :=
  @sync_no_success_of_reverting_token1

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: skim_no_success_of_reverting_token0
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    False :=
  @skim_no_success_of_reverting_token0

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: mint_no_success_of_reverting_token0
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    False :=
  @mint_no_success_of_reverting_token0

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: mint_no_success_of_reverting_token1
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    False :=
  @mint_no_success_of_reverting_token1

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: swap_no_success_of_reverting_token0
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (amount0 : swapAmount0Out sevm ≠ 0)
    (token0 : (b.getStorVal sevm.currentTarget 6).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    False :=
  @swap_no_success_of_reverting_token0

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: swap_no_success_of_reverting_token1
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat} {tok : Adr}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (amount1 : swapAmount1Out sevm ≠ 0)
    (token1 : (b.getStorVal sevm.currentTarget 7).toAdr = tok)
    (tokenCode : b.getCode tok = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp tok)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    False :=
  @swap_no_success_of_reverting_token1

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: swap_no_success_of_reverting_callback
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : ∀ {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (data : swapDataLength sevm ≠ 0)
    (recipientCode : b.getCode (swapRecipient sevm) = revertingCode)
    (notPrecompile : ¬ sevm.benvStat.rules.isPrecomp (swapRecipient sevm))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)),
    False :=
  @swap_no_success_of_reverting_callback

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 statement: sync_liveness_refuted
namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.Lift.UniswapV2Pair.Creation

example : ¬ ∀ w pair, ConfiguredWorld w pair → SyncLive w pair :=
  @sync_liveness_refuted

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: ViolationAt
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

example (g : Fork) (W : State) (post : Devm) :
    ViolationAt g W post = (
      processMessage (violMsg g W) = .ok post ∧ post.error = none ∧ post.gasLeft = gasV ∧
      storOf post.state proxyAddr 26 = 1800 ∧ storOf post.state proxyAddr lpSlotA = 1906 ∧
      (storOf post.state proxyAddr 26).toNat < (storOf post.state proxyAddr lpSlotA).toNat ∧
      storOf post.state proxyAddr 2 = 0 ∧
      ∃ (e0 e1 e1' e2 e3 e4 e4' e5 : Evm) (c0 cR c2 c339 c3 cA c5 cB : Cfg) (post2 post5 : Devm),

        (Frame.ofCall (violMsg g W)).enter = .run e0 ∧ Nonempty (Exec e0.pc e0.sta e0.dyna (.ok post)) ∧
        e0.sta.caller = creator ∧ e0.sta.currentTarget = attackerAddr ∧ e0.sta.code = AttackerR.code ∧
        c0.devm = e0.dyna ∧ c0.f = AttackerR.t_0000_c0 ∧ c0.K = [] ∧ Agree c0 ∧
        wrun fsA e0.sta 33 c0 = .cont cR ∧ Agree cR ∧ SpawnedBy e0.sta cR.devm .call e1 ∧
        e1.sta.currentTarget = proxyAddr ∧ e1.sta.code = fwdCode ∧
        stepN 11 e1 = some e1' ∧ SpawnedBy e1'.sta e1'.dyna .delegatecall e2 ∧

        e2.sta.currentTarget = proxyAddr ∧ e2.sta.code = Vulnerable.code ∧ e2.sta.data = removeCallR ∧
        Nonempty (Exec e2.pc e2.sta e2.dyna (.ok post2)) ∧ post2.error = none ∧
        storOf e2.dyna.state proxyAddr 2 = 0 ∧
        c2.devm = e2.dyna ∧ c2.f = Vulnerable.t_0000_c0 ∧ c2.K = [] ∧ Agree c2 ∧
        wrun fsI e2.sta 339 c2 = .cont c339 ∧ Agree c339 ∧
        storOf c339.devm.state proxyAddr 2 = 1 ∧ storOf c339.devm.state proxyAddr 26 = 2000 ∧
        SpawnedBy e2.sta c339.devm .call e3 ∧
        e3.sta.currentTarget = attackerAddr ∧ e3.sta.code = AttackerR.code ∧ e3.sta.value = 100 ∧

        c3.devm = e3.dyna ∧ c3.f = AttackerR.t_0000_c0 ∧ c3.K = [] ∧ Agree c3 ∧
        wrun fsA e3.sta 32 c3 = .cont cA ∧ Agree cA ∧ SpawnedBy e3.sta cA.devm .call e4 ∧
        e4.sta.currentTarget = proxyAddr ∧ e4.sta.code = fwdCode ∧ e4.sta.value = 100 ∧
        stepN 11 e4 = some e4' ∧ SpawnedBy e4'.sta e4'.dyna .delegatecall e5 ∧
        e5.sta.currentTarget = proxyAddr ∧ e5.sta.code = Vulnerable.code ∧ e5.sta.data = reAddCall ∧
        storOf e5.dyna.state proxyAddr 2 = 1 ∧ storOf e5.dyna.state proxyAddr 0 = 0 ∧
        Nonempty (Exec e5.pc e5.sta e5.dyna (.ok post5)) ∧ post5.error = none ∧
        c5.devm = e5.dyna ∧ c5.f = Vulnerable.t_0000_c0 ∧ c5.K = [] ∧ Agree c5 ∧
        wrun fsI e5.sta 2625 c5 = .cont cB ∧ Agree cB ∧ cB.f = Vulnerable.t_0370_c63 ∧
        storOf cB.devm.state proxyAddr 0 = 1 ∧ storOf cB.devm.state proxyAddr 2 = 1 ∧
        storOf post5.state proxyAddr 26 = 2106 ∧ storOf post5.state proxyAddr lpSlotA = 2106 ∧
        storOf post5.state proxyAddr 0 = 0 ∧ storOf post5.state proxyAddr 2 = 1 ∧

        (Vulnerable.code.getInst 6900 = some (.next (.push [0x02] (by decide))) ∧
          Vulnerable.code.getInst 6902 = some (.next (.reg .sload)) ∧
          Vulnerable.code.getInst 6911 = some (.next (.reg .sstore))) ∧
        (Vulnerable.code.getInst 88 = some (.next (.push [0x00] (by decide))) ∧
          Vulnerable.code.getInst 90 = some (.next (.reg .sload)) ∧
          Vulnerable.code.getInst 99 = some (.next (.reg .sstore))) ∧

        storOf post2.state proxyAddr 26 = 1800 ∧ storOf post2.state proxyAddr lpSlotA = 1906 ∧
        storOf post2.state proxyAddr 2 = 0
    ) := by
  unfold ViolationAt
  rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

-- Paper review 2 definition: ViolationStmt
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

example :
    ViolationStmt = (
      ∀ g : Fork, CoveredFork g → ∀ W : State, Checkpoint W → ∃ post : Devm, ViolationAt g W post
    ) := by
  unfold ViolationStmt
  rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

-- Paper review 2 definition: CapstoneStmt
namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)
open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

example :
    CapstoneStmt = (
      ∀ fork : Fork, CoveredFork fork →
        ∃ postI postP postC tokenPost attackerPost approvePost addPost post : Devm,
          processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧ postI.error = none ∧
          processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧ postP.error = none ∧
          processMessage (initMsg fork postP.state) = .ok postC ∧ postC.error = none ∧
          processCreateMessage (tokenCreateMsg fork postC.state) = .ok tokenPost ∧
          tokenPost.error = none ∧
          processCreateMessage (attackerCreateMsg fork tokenPost.state) = .ok attackerPost ∧
          attackerPost.error = none ∧
          processMessage (approveMsg fork attackerPost.state) = .ok approvePost ∧
          approvePost.error = none ∧
          processMessage (addMsg fork approvePost.state) = .ok addPost ∧ addPost.error = none ∧
          SoundCheckpoint addPost.state ∧ Checkpoint addPost.state ∧
          ViolationAt fork addPost.state post
    ) := by
  unfold CapstoneStmt
  rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

-- Paper review 2 definition: registryQueries
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc.LidoCircuitBreaker

example (probes : List B256) (length : Nat) :
    registryQueries probes length = (
      arrayLengthSlot ::
        ((List.range length).map fun i => arrayEntrySlot (Nat.toB256 (i + 1))) ++
        probes.flatMap (fun p => [assignmentSlot p, indexSlot p, countSlot p])
    ) := by
  unfold registryQueries
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 definition: checkRegistryOn
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc.LidoCircuitBreaker

example (storage : LogicalStorage) (entries : List Entry)
    (probes : List B256) :
    checkRegistryOn storage entries probes = (
      decide (entries.length < 2 ^ 252) &&
      decide ((entries.map Prod.fst).Nodup) &&
      entries.all (fun e => decide (e.1 ≠ 0 ∧ e.1.toNat < 2 ^ 160) &&
        decide (e.2 ≠ 0 ∧ e.2.toNat < 2 ^ 160)) &&
      probes.all (fun p => decide (p.toNat < 2 ^ 160)) &&
      decide (storage.read arrayLengthSlot = Nat.toB256 entries.length) &&
      (List.range entries.length).all (fun i =>
        decide (storage.read (arrayEntrySlot (Nat.toB256 (i + 1))) = targetAt entries i)) &&
      probes.all (fun p =>
        decide (storage.read (assignmentSlot p) = assignmentAt entries p) &&
        decide (storage.read (indexSlot p) = Nat.toB256 (oneBasedIndexAt entries p)) &&
        decide (storage.read (countSlot p) = Nat.toB256 (assignmentCount entries p)))
    ) := by
  unfold checkRegistryOn
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 definition: checkLiveCovered
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc.LidoCircuitBreaker

example (entries : List Entry) (probes : List B256) :
    checkLiveCovered entries probes = (
      entries.all fun e => decide (e.1 ∈ probes ∧ e.2 ∈ probes)
    ) := by
  unfold checkLiveCovered
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 definition: State.MinimumLocked
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (st : State) :
    State.MinimumLocked st = (
      1000 ≤ (st.balanceOf 0).toNat
    ) := by
  unfold State.MinimumLocked
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: State.ZeroAllowances
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (st : State) :
    State.ZeroAllowances st = (
      ∀ spender, st.allowance 0 spender = 0
    ) := by
  unfold State.ZeroAllowances
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: State.SupplyFloor
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (st : State) :
    State.SupplyFloor st = (
      (st.totalSupply.toNat = 0 ∨ st.MinimumLocked) ∧ st.ZeroAllowances
    ) := by
  unfold State.SupplyFloor
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: SourceInvocation.CallersNonzero
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (inv : SourceInvocation) :
    SourceInvocation.CallersNonzero inv = (
      inv.context.sender ≠ 0 ∧ inv.transcript.CallersNonzero
    ) := by
  unfold SourceInvocation.CallersNonzero
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: sqrtCharge
namespace Blanc.Lift.UniswapV2Pair
open Jaune
open Blanc.BabylonianSqrt

example (y : Nat) :
    sqrtCharge y = (
      if 3 < y then 108 + 109 * sourceCount y else if y = 0 then 66 else 71
    ) := by
  unfold sqrtCharge
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: factory
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example :
    factory = (
      0x5c69bee701ef814a2b6a3edd4b1652cb9cc5aa6f
    ) := by
  unfold factory
  rfl

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 definition: token0
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example :
    token0 = (
      0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48
    ) := by
  unfold token0
  rfl

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 definition: token1
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example :
    token1 = (
      0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2
    ) := by
  unfold token1
  rfl

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 definition: pairAddress
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example :
    pairAddress = (
      0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc
    ) := by
  unfold pairAddress
  rfl

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 definition: salt
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example :
    salt = (
      Bytes.keccak (token0.toBytes ++ token1.toBytes)
    ) := by
  unfold salt
  rfl

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 definition: saltWord
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example :
    saltWord = (
      0x85053f65cd1ece2bb37b70c13d66eadebf2779df5ddd68cf12f3ccfdc6bfe760
    ) := by
  unfold saltWord
  rfl

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 definition: initHash
namespace Blanc.Lift.UniswapV2Pair.Creation
open Jaune Blanc.Lift

example :
    initHash = (
      0x96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f
    ) := by
  unfold initHash
  rfl

end Blanc.Lift.UniswapV2Pair.Creation

-- Paper review 2 definition: initializedStor
namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.Lift.UniswapV2Pair.Creation

example (chainWord : B256) (self factory token0 token1 : Adr) :
    initializedStor chainWord self factory token0 token1 = (
      let s := ctorStor chainWord self factory Stor.empty
      (s.set 6 (addressSlotWriteWord (s.get 6) token0.toB256)).set 7
        (addressSlotWriteWord (s.get 7) token1.toB256)
    ) := by
  unfold initializedStor
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: ConfiguredWorld
namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.Lift.UniswapV2Pair.Creation

example (w : Devm) (pair : Adr) :
    ConfiguredWorld w pair = (
      w.getCode pair = code ∧
        ∃ chainWord factory token0 token1, w.getStor pair = initializedStor chainWord pair factory token0 token1
    ) := by
  unfold ConfiguredWorld
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: SyncLive
namespace Blanc.Lift.UniswapV2Pair
open Jaune Blanc.Lift.UniswapV2Pair.Creation

example (w : Devm) (pair : Adr) :
    SyncLive w pair = (
      ∃ (sevm : Sevm) (G : Nat) (post : Devm), sevm.currentTarget = pair ∧ sevm.code = code ∧
        CoveredFork sevm.benvStat.fork ∧ Blanc.Sevm.selector sevm = 0xfff6cae9 ∧
        Nonempty (Exec 0 sevm (St w [] Mem.empty G) (.ok post))
    ) := by
  unfold SyncLive
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: rawBalance
namespace Blanc.Lift.UniswapV2Pair.LedgerKeyControl
open Jaune

example (s : Stor) (a : Adr) :
    rawBalance s a = (
      s.get (WriterKey.balance a).slot
    ) := by
  unfold rawBalance
  rfl

end Blanc.Lift.UniswapV2Pair.LedgerKeyControl

-- Paper review 2 definition: RawLedgerOn
namespace Blanc.Lift.UniswapV2Pair.LedgerKeyControl
open Jaune

example (keys : List Adr) (s : Stor) :
    RawLedgerOn keys s = (
      Blanc.footprintSum keys (rawBalance s) = (s.get 0).toNat
    ) := by
  unfold RawLedgerOn
  rfl

end Blanc.Lift.UniswapV2Pair.LedgerKeyControl

-- Paper review 2 definition: _root_.Blanc.Lift.UniswapV2Pair.OracleUpdate.LawfulNoWrap
namespace Blanc.Lift.UniswapV2Pair.OracleControls
open Jaune

example (u : OracleUpdate) :
    _root_.Blanc.Lift.UniswapV2Pair.OracleUpdate.LawfulNoWrap u = (
      u.elapsed = u.timestamp.toNat - u.oldTimestamp.toNat ∧
      u.increment0 =
        (if u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0 then
          (u.oldReserve1 * 2 ^ 112 / u.oldReserve0) * u.elapsed
        else 0) ∧
      u.increment1 =
        (if u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0 then
          (u.oldReserve0 * 2 ^ 112 / u.oldReserve1) * u.elapsed
        else 0)
    ) := by
  unfold _root_.Blanc.Lift.UniswapV2Pair.OracleUpdate.LawfulNoWrap
  rfl

end Blanc.Lift.UniswapV2Pair.OracleControls

-- Paper review 2 definition: answer
namespace Blanc.Lift.UniswapV2Pair.OracleControls
open Jaune

example (value : B256) :
    answer value = (
      { success := true, returndata := encodeWords [value], codeExists := true,
        recoveryOutput := 0 }
    ) := by
  unfold answer
  rfl

end Blanc.Lift.UniswapV2Pair.OracleControls

-- Paper review 2 definition: initialized
namespace Blanc.Lift.UniswapV2Pair.OracleControls
open Jaune

example :
    initialized = (
      { State.empty 16 0 with token0 := 18, token1 := 19 }
    ) := by
  unfold initialized
  rfl

end Blanc.Lift.UniswapV2Pair.OracleControls

-- Paper review 2 definition: wrapContext
namespace Blanc.Lift.UniswapV2Pair.OracleControls
open Jaune

example :
    wrapContext = (
      { pair := 17, sender := 20, value := 0, timestamp := 4294967297,
        isStatic := false, invocation := [] }
    ) := by
  unfold wrapContext
  rfl

end Blanc.Lift.UniswapV2Pair.OracleControls

-- Paper review 2 definition: syncTranscript
namespace Blanc.Lift.UniswapV2Pair.OracleControls
open Jaune

example :
    syncTranscript = (
      .next (answer 1) .done (.next (answer 1) .done .done)
    ) := by
  unfold syncTranscript
  rfl

end Blanc.Lift.UniswapV2Pair.OracleControls

-- Paper review 2 definition: wrapRun
namespace Blanc.Lift.UniswapV2Pair.OracleControls
open Jaune

example :
    wrapRun = (
      runTyped initialized wrapContext .sync syncTranscript
    ) := by
  unfold wrapRun
  rfl

end Blanc.Lift.UniswapV2Pair.OracleControls

-- Paper review 2 definition: production
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example :
    production = (
      { mintAmount := mintAmount, burnAmounts := burnAmounts, swapCheck := swapCheck }
    ) := by
  unfold production
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: ceilDiv
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example (numerator denominator : Nat) :
    ceilDiv numerator denominator = (
      (numerator + denominator - 1) / denominator
    ) := by
  unfold ceilDiv
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: mintLiquidityUp
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example (amount0 amount1 supply reserve0 reserve1 : Nat) :
    mintLiquidityUp amount0 amount1 supply reserve0 reserve1 = (
      min (ceilDiv (amount0 * supply) reserve0) (ceilDiv (amount1 * supply) reserve1)
    ) := by
  unfold mintLiquidityUp
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: mintAmountUp
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example (amount0 amount1 supply : B256) (reserve0 reserve1 : Nat) :
    mintAmountUp amount0 amount1 supply reserve0 reserve1 = (
      match mintAmount amount0 amount1 supply reserve0 reserve1 with
      | .error failure => .error failure
      | .ok liquidity =>
        .ok (if supply = 0 then liquidity
          else mintLiquidityUp amount0.toNat amount1.toNat supply.toNat reserve0 reserve1)
    ) := by
  unfold mintAmountUp
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: burnAmountsUp
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example (liquidity balance0 balance1 supply : B256) :
    burnAmountsUp liquidity balance0 balance1 supply = (
      match burnAmounts liquidity balance0 balance1 supply with
      | .error failure => .error failure
      | .ok _ =>
        .ok (ceilDiv (liquidity.toNat * balance0.toNat) supply.toNat,
          ceilDiv (liquidity.toNat * balance1.toNat) supply.toNat)
    ) := by
  unfold burnAmountsUp
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: swapCheckFee
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example (fee : Nat) (balance0 balance1 : B256) (amount0In amount1In reserve0 reserve1 : Nat) :
    swapCheckFee fee balance0 balance1 amount0In amount1In reserve0 reserve1 = (
      if amount0In > 0 ∨ amount1In > 0 then
        if balance0.toNat * 1000 < 2 ^ 256 ∧ amount0In * fee < 2 ^ 256 then
          if amount0In * fee ≤ balance0.toNat * 1000 then
            if balance1.toNat * 1000 < 2 ^ 256 ∧ amount1In * fee < 2 ^ 256 then
              if amount1In * fee ≤ balance1.toNat * 1000 then
                let adjusted0 := balance0.toNat * 1000 - amount0In * fee
                let adjusted1 := balance1.toNat * 1000 - amount1In * fee
                if adjusted0 * adjusted1 < 2 ^ 256 then
                  if reserve0 * reserve1 * 1000 ^ 2 ≤ adjusted0 * adjusted1 then .ok ()
                  else .error (.sourceGuard "UniswapV2: K")
                else .error (.sourceGuard "ds-math-mul-overflow")
              else .error (.sourceGuard "ds-math-sub-underflow")
            else .error (.sourceGuard "ds-math-mul-overflow")
          else .error (.sourceGuard "ds-math-sub-underflow")
        else .error (.sourceGuard "ds-math-mul-overflow")
      else .error (.sourceGuard "UniswapV2: INSUFFICIENT_INPUT_AMOUNT")
    ) := by
  unfold swapCheckFee
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: mintRoundUp
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example :
    mintRoundUp = (
      { production with mintAmount := mintAmountUp }
    ) := by
  unfold mintRoundUp
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: burnRoundUp
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example :
    burnRoundUp = (
      { production with burnAmounts := burnAmountsUp }
    ) := by
  unfold burnRoundUp
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: feeMutant
namespace Blanc.Lift.UniswapV2Pair.ModelMutants
open Jaune

example (fee : Nat) :
    feeMutant fee = (
      { production with swapCheck := swapCheckFee fee }
    ) := by
  unfold feeMutant
  rfl

end Blanc.Lift.UniswapV2Pair.ModelMutants

-- Paper review 2 definition: context
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    context = (
      { pair := 17, sender := 20, value := 0, timestamp := 0,
        isStatic := false, invocation := [] }
    ) := by
  unfold context
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: answer
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example (value : B256) :
    answer value = (
      { success := true, returndata := encodeWords [value], codeExists := true,
        recoveryOutput := 0 }
    ) := by
  unfold answer
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: initialized
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    initialized = (
      (runTyped (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
        .done).frame.current.state
    ) := by
  unfold initialized
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: mintTranscript
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    mintTranscript = (
      .next (answer 1001) .done (.next (answer 1001) .done (.next (answer 0) .done .done))
    ) := by
  unfold mintTranscript
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: mintRun
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    mintRun = (
      runTyped initialized context (.mint 20) mintTranscript
    ) := by
  unfold mintRun
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: minted
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    minted = (
      mintRun.frame.current.state
    ) := by
  unfold minted
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: donationTranscript
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    donationTranscript = (
      .next (answer 1002) .done (.next (answer 1002) .done .done)
    ) := by
  unfold donationTranscript
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: donationRun
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    donationRun = (
      runTyped minted context .sync donationTranscript
    ) := by
  unfold donationRun
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: checkpoint
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    checkpoint = (
      donationRun.frame.current.state
    ) := by
  unfold checkpoint
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: mintExpected
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    mintExpected = (
      { State.empty 16 0 with
        token0 := 18, token1 := 19, totalSupply := 1001,
        balanceOf := Blanc.ledgerCredit (Blanc.ledgerCredit (fun _ => 0) 0 1000) 20 1,
        reserve0 := ⟨1001, by decide⟩, reserve1 := ⟨1001, by decide⟩ }
    ) := by
  unfold mintExpected
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: checkpointExpected
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    checkpointExpected = (
      { mintExpected with reserve0 := ⟨1002, by decide⟩, reserve1 := ⟨1002, by decide⟩ }
    ) := by
  unfold checkpointExpected
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: shrinkingTranscript
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    shrinkingTranscript = (
      .next (answer 0) .done (.next (answer 1002) .done .done)
    ) := by
  unfold shrinkingTranscript
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: shrinkingRun
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    shrinkingRun = (
      runTyped checkpoint context .sync shrinkingTranscript
    ) := by
  unfold shrinkingRun
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: shrunk
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    shrunk = (
      shrinkingRun.frame.current.state
    ) := by
  unfold shrunk
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: laterTranscript
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    laterTranscript = (
      .next (answer 1004) .done (.next (answer 1004) .done (.next (answer 0) .done .done))
    ) := by
  unfold laterTranscript
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: upMintRun
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    upMintRun = (
      runTypedWith mintRoundUp initialized context (.mint 20) mintTranscript
    ) := by
  unfold upMintRun
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: upDonationRun
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    upDonationRun = (
      runTypedWith mintRoundUp upMintRun.frame.current.state context .sync donationTranscript
    ) := by
  unfold upDonationRun
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: upLaterRun
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    upLaterRun = (
      runTypedWith mintRoundUp checkpoint context (.mint 20) laterTranscript
    ) := by
  unfold upLaterRun
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: transferOk
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    transferOk = (
      { success := true, returndata := [], codeExists := true, recoveryOutput := 0 }
    ) := by
  unfold transferOk
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: feeSwapTranscript
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    feeSwapTranscript = (
      .next transferOk .done (.next (answer 1006015) .done (.next (answer 1) .done .done))
    ) := by
  unfold feeSwapTranscript
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: feeMutantRun
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    feeMutantRun = (
      runTypedWith (feeMutant 2) checkpoint context (.swap 0 1001 20 []) feeSwapTranscript
    ) := by
  unfold feeMutantRun
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: burnReady
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    burnReady = (
      (runTyped checkpoint
        (have c := context;
          { pair := c.pair, sender := 20, value := c.value, timestamp := c.timestamp,
            isStatic := c.isStatic, invocation := c.invocation })
        (.transfer 17 1) .done).frame.current.state
    ) := rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 definition: burnTranscript
namespace Blanc.Lift.UniswapV2Pair.ModelControls
open Jaune
open ModelMutants

example :
    burnTranscript = (
      .next (answer 1002) .done (.next (answer 1002) .done (.next (answer 0) .done
        (.next transferOk .done (.next transferOk .done
          (.next (answer 1001) .done (.next (answer 1001) .done .done))))))
    ) := by
  unfold burnTranscript
  rfl

end Blanc.Lift.UniswapV2Pair.ModelControls

-- Paper review 2 constructor: RegistryOn.mk
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc.LidoCircuitBreaker

example : ∀ {storage : LogicalStorage} {entries : List Entry} {probes : List B256},
    entries.length < 2 ^ 252 →
    (entries.map Prod.fst).Nodup →
    (∀ e ∈ entries, nonzeroCanonicalAddress e.1) →
    (∀ e ∈ entries, nonzeroCanonicalAddress e.2) →
    (∀ p ∈ probes, canonicalAddress p) →
    storage.read arrayLengthSlot = Nat.toB256 entries.length →
    (∀ i ∈ List.range entries.length,
      storage.read (arrayEntrySlot (Nat.toB256 (i + 1))) = targetAt entries i) →
    (∀ p ∈ probes, storage.read (assignmentSlot p) = assignmentAt entries p) →
    (∀ p ∈ probes, storage.read (indexSlot p) = Nat.toB256 (oneBasedIndexAt entries p)) →
    (∀ p ∈ probes, storage.read (countSlot p) = Nat.toB256 (assignmentCount entries p)) →
    RegistryOn storage entries probes :=
  @RegistryOn.mk

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 definition: Transcript.CallersNonzero (every constructor)
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example : Transcript.done.CallersNonzero = True := rfl

example (result : ExternalResult) (turns tail : Transcript) :
    (Transcript.next result turns tail).CallersNonzero =
      (turns.CallersNonzero ∧ tail.CallersNonzero) := rfl

example (emitter : Adr) (topics : List B256) (data : Bytes) (tail : Transcript) :
    (Transcript.foreignLog emitter topics data tail).CallersNonzero = tail.CallersNonzero := rfl

example (sender : Adr) (value : B256) (isStatic : Bool) (entry : Entry)
    (transcript tail : Transcript) :
    (Transcript.invoke sender value isStatic entry transcript tail).CallersNonzero =
      (sender ≠ 0 ∧ transcript.CallersNonzero ∧ tail.CallersNonzero) := rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: InitialMintResult
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (prior : State) (observed : MintObserved) (post : State)
    (returndata : Bytes) :
    @InitialMintResult prior observed post returndata = (
      let root := Nat.sqrt (observed.amount0.toNat * observed.amount1.toNat)
      1000 < root ∧ observed.amount0.toNat * observed.amount1.toNat < 2 ^ 256 ∧
        post.totalSupply.toNat = root ∧
        post.balanceOf = Blanc.ledgerCredit (Blanc.ledgerCredit prior.balanceOf 0 1000)
          observed.recipient (Nat.toB256 (root - 1000)) ∧
        post.reserve0.val = observed.balance0.toNat ∧ post.reserve1.val = observed.balance1.toNat ∧
        returndata = encodeWords [Nat.toB256 (root - 1000)]
    ) := by
  unfold InitialMintResult
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: mintObservation
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (recipient : Adr) (reserves : CachedReserves)
    (balance0 balance1 : B256) :
    @mintObservation recipient reserves balance0 balance1 = (
      { recipient := recipient, reserves := reserves, balance0 := balance0, balance1 := balance1,
        amount0 := balance0 - Nat.toB256 reserves.reserve0.val,
        amount1 := balance1 - Nat.toB256 reserves.reserve1.val }
    ) := by
  unfold mintObservation
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: LaterMintResult
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (_prior : State) (observed : MintObserved) (fee : FeeResult) (post : State)
    (returndata : Bytes) :
    @LaterMintResult _prior observed fee post returndata = (
      let liquidity := AMMArithmetic.mintLiquidity observed.amount0.toNat observed.amount1.toNat
        fee.state.totalSupply.toNat observed.reserves.reserve0.val observed.reserves.reserve1.val
      liquidity > 0 ∧
        liquidity < 2 ^ 256 ∧
        post.totalSupply.toNat = fee.state.totalSupply.toNat + liquidity ∧
        post.balanceOf = Blanc.ledgerCredit fee.state.balanceOf observed.recipient (Nat.toB256 liquidity) ∧
        post.reserve0.val = observed.balance0.toNat ∧
        post.reserve1.val = observed.balance1.toNat ∧
        returndata = encodeWords [Nat.toB256 liquidity]
    ) := by
  unfold LaterMintResult
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: burnObservation
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (recipient : Adr) (st : State) (pair : Adr)
    (balance0 balance1 : B256) :
    @burnObservation recipient st pair balance0 balance1 = (
      { locals := { recipient := recipient, reserves := st.cachedReserves, token0 := st.token0, token1 := st.token1 },
        balance0 := balance0,
        balance1 := balance1,
        liquidity := st.balanceOf pair }
    ) := by
  unfold burnObservation
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: BurnPayoutResult
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (prior : State) (ctx : Context) (recipient : Adr) (observed : BurnObserved)
    (fee : FeeResult) (returndata : Bytes) (requests : List Request) :
    @BurnPayoutResult prior ctx recipient observed fee returndata requests = (
      let supply := fee.state.totalSupply
      let amount0 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance0.toNat supply.toNat
      let amount1 := AMMArithmetic.burnPayment observed.liquidity.toNat observed.balance1.toNat supply.toNat
      amount0 > 0 ∧ amount1 > 0 ∧
        amount0 < 2 ^ 256 ∧ amount1 < 2 ^ 256 ∧
        observed.liquidity = prior.balanceOf ctx.pair ∧
        requests.filter (fun r => r.site == .burnTransfer0) =
          [requestFor .burnTransfer0 prior.token0 (.transfer recipient (Nat.toB256 amount0))] ∧
        requests.filter (fun r => r.site == .burnTransfer1) =
          [requestFor .burnTransfer1 prior.token1 (.transfer recipient (Nat.toB256 amount1))] ∧
        returndata = encodeWords [Nat.toB256 amount0, Nat.toB256 amount1]
    ) := by
  unfold BurnPayoutResult
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: SwapCanonicalBody
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (Own : Devm → Prop) (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    @SwapCanonicalBody Own K current invocation sevm b post G run = (
      let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      let ctx := writerContext sevm invocation
      let locals := swapFrontLocals sevm current.state
      let w := swapCutWords sevm current.state
      let S := swapCutStack w 0x257 [0x022c0d9f]
      sevm.value = 0 ∧ sevm.isStatic = false ∧
      ∃ (frame : Frame) (T0 T1 TC : Transcript → Transcript) (turns0 turns1 turnsC : List MutableTurn)
        (b1 b2 d d0 d1 : Devm) (M1 M2 M : Mem) (p1 p : B256) (out0 out1 : Bytes)
        (views0 views1 : List StaticViewTurn) (final : Frame) (rets : List ChildReturn)
        (K' : WriterKey → Prop) (added : List PendingLog),
        SwapTransferOpt root sevm (swapPrefixWorld sevm b) S getterInitMemory 128
          (swapAmount0Out sevm) (swapRecipientWord sevm) current.state.token0.toB256 0x8d0 b1 M1 p1 ∧
        SwapTransferOpt root sevm b1 S M1 p1
          (swapAmount1Out sevm) (swapRecipientWord sevm) current.state.token1.toB256 0x8e1 b2 M2 p ∧
        SwapCallbackOpt root sevm b2 S M2 p (swapRecipientWord sevm) (swapAmount0Out sevm)
          (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) d M ∧
        ((swapAmount0Out sevm = 0 ∧ T0 = id) ∨ (swapAmount0Out sevm ≠ 0 ∧
          T0 = (fun tail => .next (swapTransferReply b1.returnData) (mutableTranscript turns0 .done) tail) ∧
          SwapCallProvenance sevm.currentTarget root sevm (swapPrefixWorld sevm b) b1 turns0)) ∧
        ((swapAmount1Out sevm = 0 ∧ T1 = id) ∨ (swapAmount1Out sevm ≠ 0 ∧
          T1 = (fun tail => .next (swapTransferReply b2.returnData) (mutableTranscript turns1 .done) tail) ∧
          SwapCallProvenance sevm.currentTarget root sevm b1 b2 turns1)) ∧
        ((swapDataLength sevm = 0 ∧ TC = id) ∨ (swapDataLength sevm ≠ 0 ∧
          TC = (fun tail => .next (swapCallbackReply d.returnData) (mutableTranscript turnsC .done) tail) ∧
          SwapCallProvenance sevm.currentTarget root sevm b2 d turnsC)) ∧
        SwapBalanceCall root sevm d M p w.token0
          (w.token1 :: w.token0 :: 0 :: 0 :: w.reserve1 :: w.reserve0 :: w.dataLength ::
            w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: 0x257 :: [0x022c0d9f]) d0 out0 ∧
        SwapBalanceCall root sevm d0 (swapBalanceReply M p sevm.currentTarget out0) p w.token1
          (w.token1 :: w.token0 :: 0 :: swapBalanceWord out0 :: w.reserve1 :: w.reserve0 ::
            w.dataLength :: w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: 0x257 ::
            [0x022c0d9f]) d1 out1 ∧
        ExactConsumes (startTyped current ctx (swapDecodedEntry sevm))
          (((T0 ∘ T1) ∘ TC)
            (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
              (.next (feeObservedResult out1) (staticViewTranscript views1 .done) .done)))
          { status := .success [], frame := final, remaining := .done, childReturns := rets } ∧
        frame.checkpoint = current ∧ frame.context = ctx ∧
        final.checkpoint = current ∧ final.context = ctx ∧ final.current.state.unlocked = 1 ∧
        (∀ k, K' k → WriterExtend K (swapTraceKeys root) k) ∧
        WriterRep K' (post.getStor sevm.currentTarget) final.current.state ∧
        (swapBalanceWord out0).toNat < 2 ^ 112 ∧ (swapBalanceWord out1).toNat < 2 ^ 112 ∧
        final.current.logs = current.logs ++ added ∧
        (∃ L : List Log, d.logs = b.logs ++ L ∧
          post.logs = b.logs ++ L ++
            [swapSyncLog sevm.currentTarget (swapBalanceWord out0) (swapBalanceWord out1),
             swapEventLog sevm
              (swapInWord (swapBalanceWord out0) w.reserve0 w.amount0Out)
              (swapInWord (swapBalanceWord out1) w.reserve1 w.amount1Out)
              w.amount0Out w.amount1Out w.recipient] ∧
          added.map (PendingLog.rawWith (swapOwnedRaw sevm.currentTarget)) =
            (L ++ [swapSyncLog sevm.currentTarget (swapBalanceWord out0) (swapBalanceWord out1),
             swapEventLog sevm
              (swapInWord (swapBalanceWord out0) w.reserve0 w.amount0Out)
              (swapInWord (swapBalanceWord out1) w.reserve1 w.amount1Out)
              w.amount0Out w.amount1Out w.recipient]).map some) ∧
        post.output = [] ∧
        (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns0 ++ turns1 ++ turnsC →
          LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
        PairViewProvenance root sevm frame (swapTokenWord w.token0) views0 ∧
        PairViewProvenance root sevm (frame.beginResume (swapRequest0 frame locals))
          (swapTokenWord w.token1) views1 ∧
        Own d
    ) := by
  unfold SwapCanonicalBody
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: swapTraceKeys
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (root : Exec.Deriv) :
    @swapTraceKeys root = (
      skimTraceKeys root
    ) := by
  unfold swapTraceKeys
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: swapCanonicalTranscript
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (amount0Out amount1Out : B256) (balance0 balance1 : B256)
    (data : Bytes) :
    @swapCanonicalTranscript amount0Out amount1Out balance0 balance1 data = (
      if amount0Out > 0 then
        .next swapOk .done (swapCanonicalTail amount1Out balance0 balance1 data)
      else if amount1Out > 0 then
        .next swapOk .done (swapCanonicalPostTransfers balance0 balance1 data)
      else swapCanonicalPostTransfers balance0 balance1 data
    ) := by
  unfold swapCanonicalTranscript
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: swapControlState
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example :
    @swapControlState = (
      { State.empty 0 0 with
        token0 := 100, token1 := 200, unlocked := 1,
        reserve0 := ⟨10, by decide⟩, reserve1 := ⟨10, by decide⟩ }
    ) := by
  unfold swapControlState
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: swapControlContext
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example :
    @swapControlContext = (
      { pair := 0, sender := 400, value := 0, timestamp := 0,
        isStatic := false, invocation := [] }
    ) := by
  unfold swapControlContext
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: swapOk
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example :
    @swapOk = (
      { success := true, returndata := [], codeExists := true, recoveryOutput := 0 }
    ) := by
  unfold swapOk
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: swapAnswer
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (balance : B256) :
    @swapAnswer balance = (
      { success := true, returndata := encodeWords [balance], codeExists := true, recoveryOutput := 0 }
    ) := by
  unfold swapAnswer
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: swapCanonicalPostTransfers
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (balance0 balance1 : B256) (data : Bytes) :
    @swapCanonicalPostTransfers balance0 balance1 data = (
      if data.length > 0 then
        .next swapOk .done
          (.next (swapAnswer balance0) .done (.next (swapAnswer balance1) .done .done))
      else
        .next (swapAnswer balance0) .done (.next (swapAnswer balance1) .done .done)
    ) := by
  unfold swapCanonicalPostTransfers
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: swapCanonicalTail
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (amount1Out : B256) (balance0 balance1 : B256) (data : Bytes) :
    @swapCanonicalTail amount1Out balance0 balance1 data = (
      if amount1Out > 0 then
        .next swapOk .done (swapCanonicalPostTransfers balance0 balance1 data)
      else swapCanonicalPostTransfers balance0 balance1 data
    ) := by
  unfold swapCanonicalTail
  rfl

end Blanc.Lift.UniswapV2Pair

-- Paper review 2 definition: mintLiquidity
namespace Blanc.Lift.AMMArithmetic


example (amount0 amount1 supply reserve0 reserve1 : Nat) :
    @mintLiquidity amount0 amount1 supply reserve0 reserve1 = (
      min (amount0 * supply / reserve0) (amount1 * supply / reserve1)
    ) := by
  unfold mintLiquidity
  rfl

end Blanc.Lift.AMMArithmetic

-- Paper review 2 definition: burnPayment
namespace Blanc.Lift.AMMArithmetic


example (liquidity balance supply : Nat) :
    @burnPayment liquidity balance supply = (
      liquidity * balance / supply
    ) := by
  unfold burnPayment
  rfl

end Blanc.Lift.AMMArithmetic

-- Paper review 2 definition: exampleEntries
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc Blanc.LidoCircuitBreaker

example :
    @exampleEntries = (
      [(1, 2)]
    ) := by
  unfold exampleEntries
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 definition: exampleProbes
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc Blanc.LidoCircuitBreaker

example :
    @exampleProbes = (
      [0, 1, 2, 3]
    ) := by
  unfold exampleProbes
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 definition: exampleInitialWrites
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc Blanc.LidoCircuitBreaker

example :
    @exampleInitialWrites = (
      [(assignmentSlot 1, 2), (arrayEntrySlot 1, 1), (indexSlot 1, 1),
        (arrayLengthSlot, 1), (countSlot 2, 1)]
    ) := by
  unfold exampleInitialWrites
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 definition: exampleStorage
namespace Blanc.Lift.LidoCircuitBreakerDeployed
open Jaune Blanc Blanc.LidoCircuitBreaker

example :
    @exampleStorage = (
      applyRegistryRawWrites Stor.empty exampleInitialWrites
    ) := by
  unfold exampleStorage
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed

-- Paper review 2 definition: swapOwnedRaw
namespace Blanc.Lift.UniswapV2Pair
open Jaune

example (pair : Adr) (event : Event) :
    swapOwnedRaw pair event = (match event with
      | .transfer source recipient value => some (transferRawLog pair source recipient value)
      | .approval owner spender value => some (approvalRawLog pair owner spender value)
      | .sync reserve0 reserve1 => some (swapSyncLog pair reserve0.toB256 reserve1.toB256)
      | .swap sender in0 in1 out0 out1 recipient =>
          some ⟨pair, [swapEventTopic, sender.toB256, recipient.toB256],
            in0.toBytes ++ in1.toBytes ++ out0.toBytes ++ out1.toBytes⟩
      | _ => none) := by
  cases event <;> rfl

end Blanc.Lift.UniswapV2Pair
