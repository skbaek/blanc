import Blanc.Lift.BeaconDeposit.Creation.HistoricalDeploy
import Blanc.Lift.BeaconDeposit.Creation.HistoricalTxRecover

/-! The actual recovered transaction, prepared over a real supplied pre-state.
This conditional producer establishes no historical state or block inclusion. -/

namespace Blanc.Lift.BeaconDeposit.Creation.HistoricalTx

open Jaune Blanc.BeaconDeposit ExecutionTrace

/-- Muir validates the actual CREATE record using the structural intrinsic cap. -/
theorem validated_muir :
    validateTransaction muirGlacierRules tx 0 =
      .ok ((calculateIntrinsicCost muirGlacierRules tx 0).1, 0) := by
  exact validateTransaction_ok_of_noInitcodeLimit
    (rules := muirGlacierRules) (tx := tx) (sender := 0) (f := 0)
    rfl rfl (muir_intrinsic_le 0).2
    (max_le (Nat.le_trans (muir_intrinsic_le 0).1 (by decide : 159128 ≤ 3141592))
      (Nat.zero_le _))
    (by decide) rfl

/-- Admission retains the carried block output and uses the kernel-recovered sender. -/
theorem checked_muir (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (hnonce : benv.state.getNonce deployer = 0)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 461814024000000000 ≤ (benv.state.bal deployer).toNat)
    (hroom : 3141592 ≤ benv.stat.blockGasLimit - bout.blockGasUsed) :
    checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (deployer, 147000000000, [], 0) := by
  have hrules : benv.beginTransaction.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hgas := checkTransactionGasLimits_ok_of_room
    (benv := benv.beginTransaction) (bout := transactionPreludeBout bout tx index) (tx := tx)
    (by rw [hrules]; rfl) hroom (by change 0 ≤ _; exact Nat.zero_le _)
  refine checkTransaction_ok_of_parts
    (benv := benv.beginTransaction) (bout := transactionPreludeBout bout tx index) (tx := tx)
    (sender := deployer) (blobGas := 0) (effectiveGasPrice := 147000000000)
    (maxFee := 461814024000000000) (maxFee' := 461814024000000000) (blobHashes := [])
    hgas ?_ ?_ ?_ rfl rfl rfl ?_
  · simp only [checkTransactionChainId, tx, Benv.beginTransaction, hchain]
    rfl
  · change recoverSender benv.stat.chainId tx = .ok deployer
    rw [hchain]
    exact recoveredSender
  · change checkTransactionLegacyGasFee benv.stat.baseFeePerGas 3141592 147000000000 = _
    rw [hbasefee]
    decide
  · apply checkTransactionSenderAccount_ok_of_noCode
    · exact hnonce
    · exact hfunds
    · exact hsenderCode


/-- Exact stage equations and the resulting constructor postcondition. The real
pre-state and carried transaction index/output are retained throughout. -/
structure PreparedCreation (benv : Benv) (bout : BlockOutput) (index : Nat)
    (intrinsic : Nat) (debit : State) (msg : Msg) (post : Devm) : Prop where
  intrinsicEq : (calculateIntrinsicCost muirGlacierRules tx 0).1 = intrinsic
  validated : validateTransaction benv.stat.rules tx 0 = .ok (intrinsic, 0)
  checked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
    .ok (deployer, 147000000000, [], 0)
  feeEq : tx.gas * 147000000000 = 461814024000000000
  feeFits : 461814024000000000 ≤ B256.max.toNat
  feeWord : (461814024000000000 : Nat).toB256.toNat = 461814024000000000
  debited : (benv.state.incrNonce deployer).subBal deployer
    (461814024000000000 : Nat).toB256 = some debit
  senderNonce : debit.getNonce deployer = 1
  prepared : prepareMessage { benv.beginTransaction with state := debit }
    (transactionTenv benv.beginTransaction tx index deployer 147000000000 intrinsic []) tx =
    .ok msg
  world : msg.benv = { benv.beginTransaction with state := debit }
  target : msg.currentTarget = depositAddress
  creation : msg.target = none
  collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false
  code : msg.code = Creation.code
  codeAddress : msg.codeAddress = none
  data : msg.data = []
  value : msg.value = 0
  rules : msg.benv.stat.rules = muirGlacierRules
  gas : msg.gas = tx.gas - intrinsic
  gasLower : Historical.need 0 + 45 ≤ msg.gas
  gasUpper : msg.gas < 2 ^ 64 + 45
  stateGas : msg.stateGasGrant = 0
  transfer : msg.shouldTransferValue = true
  precompiles : msg.disablePrecompiles = false
  nonstatic : msg.isStatic = false
  depth : msg.depth = 1024
  maxCode : 6358 ≤ msg.benv.stat.rules.code.maxCodeSize
  process : processCreateMessage msg = .ok post
  installed : (post.getCode depositAddress).toList = Blanc.Lift.BeaconDeposit.code.toList
  invariant : SolInv (Devm.getStor post depositAddress) []
  error : post.error = none
  refund : post.refundCounter = 0
  logs : post.logs = []
  deletions : post.accountsToDelete = .emptyWithCapacity

/-- Prepare the actual signed CREATE transaction and execute its certified Muir
constructor from honest pre-execution facts. No successful run or final invariant
is assumed. This is not a historical state witness or transaction settlement. -/
theorem prepare_muir_actual_creation
    (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (hnonce : benv.state.getNonce deployer = 0)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 461814024000000000 ≤ (benv.state.bal deployer).toNat)
    (hroom : 3141592 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hfresh : accountHasCodeOrNonce benv.state depositAddress = false) :
    ∃ intrinsic debit msg post, PreparedCreation benv bout index intrinsic debit msg post := by
  obtain ⟨intrinsic, hintrinsic⟩ :
      ∃ intrinsic, (calculateIntrinsicCost muirGlacierRules tx 0).1 = intrinsic := ⟨_, rfl⟩
  have hvalid := validated_muir
  rw [hintrinsic] at hvalid
  have hgasAllocation := muir_gas_sufficient 0
  rw [hintrinsic] at hgasAllocation
  have hrules : benv.beginTransaction.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hnonceMax : (benv.state.get deployer).nonce ≠ UInt64.max := by
    change benv.state.getNonce deployer ≠ UInt64.max
    rw [hnonce]
    decide
  have hfeeWord : (461814024000000000 : Nat).toB256.toNat = 461814024000000000 := by
    exact B256.toNat_toB256_of_lt (by decide)
  have hpay : (461814024000000000 : Nat).toB256 ≤ benv.state.bal deployer := by
    rw [B256.le_iff_toNat_le_toNat, hfeeWord]
    exact hfunds
  let debit := (benv.state.incrNonce deployer).setBal deployer
    (benv.state.bal deployer - (461814024000000000 : Nat).toB256)
  have hdebit : (benv.state.incrNonce deployer).subBal deployer
      (461814024000000000 : Nat).toB256 = some debit := subBal_incrNonce_of_le hpay
  have hnonceDebit : debit.getNonce deployer = 1 := by
    change (debit.get deployer).nonce = 1
    dsimp only [debit]
    rw [debit_get_self hnonceMax]
    change benv.state.getNonce deployer + 1 = 1
    rw [hnonce]
    rfl
  have htargetAccount : debit.get depositAddress = benv.state.get depositAddress :=
    debit_get_ne (by decide : deployer ≠ depositAddress)
  have hcollision : accountHasCodeOrNonce debit depositAddress = false := by
    unfold accountHasCodeOrNonce State.getNonce State.getCode
    rw [htargetAccount]
    exact hfresh
  let tenv := transactionTenv benv.beginTransaction tx index deployer 147000000000 intrinsic []
  let msg : Msg :=
    { benv := { benv.beginTransaction with state := debit }, tenv := tenv,
      caller := deployer, target := none, gas := tx.gas - intrinsic,
      value := 0, data := [], code := .mk (.mk tx.data), depth := 1024,
      currentTarget := depositAddress, codeAddress := none,
      shouldTransferValue := true, isStatic := false,
      accessedAddresses := tenv.stat.accessListAddresses.insertMany
        (benv.beginTransaction.stat.rules.precompiles ++ [deployer, depositAddress]),
      accessedStorageKeys := tenv.stat.accessListStorageKeys, disablePrecompiles := false }
  have htarget : computeContractAddress deployer (debit.getNonce deployer - 1) =
      depositAddress := by
    rw [hnonceDebit, UInt64.sub_self]
    exact depositAddress_eq.symm
  have hreceiver : tx.type.receiver? = none := rfl
  have horigin : tenv.stat.origin = deployer := rfl
  have hprepared : prepareMessage { benv.beginTransaction with state := debit } tenv tx =
      .ok msg := by
    simp only [prepareMessage, hreceiver, horigin, htarget]
    rfl
  have hcode : msg.code = Creation.code := by
    change ByteArray.mk (Array.mk tx.data) = Creation.code
    rw [tx_data, ByteArray.toList_eq_toList_data]
  have hgas := hgasAllocation
  change Historical.need 0 + 45 ≤ msg.gas ∧ msg.gas < 2 ^ 64 + 45 at hgas
  have hmsgRules : msg.benv.stat.rules = muirGlacierRules := hrules
  have hmax : 6358 ≤ msg.benv.stat.rules.code.maxCodeSize := by
    rw [hmsgRules]
    decide
  obtain ⟨post, hrun, hinstalled, hinv, herror, hrefund, hlogs, hdeletions⟩ := beacon_create_muir_meta msg rfl rfl hcode
    hgas.1 hgas.2 hmsgRules rfl (by change (1024 : Nat) ≠ 0; decide) hmax
  refine ⟨intrinsic, debit, msg, post,
    { intrinsicEq := hintrinsic, validated := ?_, checked := checked_muir benv bout index hfork hchain hbasefee hnonce
        hsenderCode hfunds hroom,
      feeEq := rfl, feeFits := by decide, feeWord := hfeeWord, debited := hdebit,
      senderNonce := hnonceDebit, prepared := hprepared,
      world := rfl, target := rfl, creation := rfl, collision := hcollision,
      code := hcode, codeAddress := rfl, data := rfl, value := rfl, rules := hmsgRules,
      gas := rfl, gasLower := hgas.1, gasUpper := hgas.2, stateGas := rfl,
      transfer := rfl, precompiles := rfl,
      nonstatic := rfl, depth := rfl, maxCode := hmax, process := hrun,
      installed := hinstalled, invariant := hinv, error := herror, refund := hrefund,
      logs := hlogs, deletions := hdeletions }⟩
  change validateTransaction (Fork.ruleSet benv.stat.fork) tx 0 = _
  rw [hfork]
  exact hvalid

end Blanc.Lift.BeaconDeposit.Creation.HistoricalTx
