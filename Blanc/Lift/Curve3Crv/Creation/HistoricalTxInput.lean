import Blanc.Lift.Curve3Crv.Creation.HistoricalDeploy
import Blanc.Lift.Curve3Crv.Creation.HistoricalTxRecover
import Blanc.TransactionForwardH

/-!
# The 3Crv creation transaction, prepared over a supplied pre-state

`validated_muir` and `checked_muir`: Muir Glacier validation (exact intrinsic 97,992) and
admission of the recorded transaction, with the kernel-recovered deployer as sender, from honest
pre-execution facts (nonce 42, no sender code, funds for `678343 · 120427120878` wei, block-gas
room). `prepare_muir_actual_creation` runs every stage up to and including the CREATE message
(`curve_create_muir_meta`) and records the stage equations in `PreparedCreation`. The pre-state,
carried block output and index are arbitrary; no block inclusion is claimed here.
-/

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx

open Jaune Blanc.Lift ExecutionTrace

/-- The maximum gas fee: `678343 · 120427120878` wei. -/
theorem fee_eq : tx.gas * 120427120878 = 81690894457745154 := rfl

/-- Muir validates the recorded CREATE with its exact intrinsic gas. -/
theorem validated_muir : validateTransaction muirGlacierRules tx 0 = .ok (97992, 0) := by
  have h := validateTransaction_ok_of_noInitcodeLimit
    (rules := muirGlacierRules) (tx := tx) (sender := 0) (f := 0)
    rfl rfl (by rw [muir_intrinsic]) (by rw [muir_intrinsic]; decide) (by decide) rfl
  rw [muir_intrinsic] at h
  exact h

/-- Admission uses the kernel-recovered sender; the pre-EIP-155 signature passes the chain-id
check at any chain id. -/
theorem checked_muir (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (hnonce : benv.state.getNonce deployer = 42)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 81690894457745154 ≤ (benv.state.bal deployer).toNat)
    (hroom : 678343 ≤ benv.stat.blockGasLimit - bout.blockGasUsed) :
    checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (deployer, 120427120878, [], 0) := by
  have hrules : benv.beginTransaction.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hgas := checkTransactionGasLimits_ok_of_room
    (benv := benv.beginTransaction) (bout := transactionPreludeBout bout tx index) (tx := tx)
    (by rw [hrules]; rfl) hroom (by change 0 ≤ _; exact Nat.zero_le _)
  refine checkTransaction_ok_of_parts
    (benv := benv.beginTransaction) (bout := transactionPreludeBout bout tx index) (tx := tx)
    (sender := deployer) (blobGas := 0) (effectiveGasPrice := 120427120878)
    (maxFee := 81690894457745154) (maxFee' := 81690894457745154) (blobHashes := [])
    hgas ?_ (recoveredSender _) ?_ rfl rfl rfl ?_
  · simp only [checkTransactionChainId, tx]
    rfl
  · change checkTransactionLegacyGasFee benv.stat.baseFeePerGas 678343 120427120878 = _
    rw [hbasefee]
    decide
  · apply checkTransactionSenderAccount_ok_of_noCode
    · exact hnonce
    · exact hfunds
    · exact hsenderCode

/-- Exact stage equations of the prepared creation and the constructor's postcondition. The
pre-state and carried transaction index and output are retained throughout. -/
structure PreparedCreation (benv : Benv) (bout : BlockOutput) (index : Nat)
    (debit : State) (msg : Msg) (post : Devm) : Prop where
  validated : validateTransaction benv.stat.rules tx 0 = .ok (97992, 0)
  checked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
    .ok (deployer, 120427120878, [], 0)
  debited : (benv.state.incrNonce deployer).subBal deployer
    (81690894457745154 : Nat).toB256 = some debit
  prepared : prepareMessage { benv.beginTransaction with state := debit }
    (transactionTenv benv.beginTransaction tx index deployer 120427120878 97992 []) tx =
    .ok msg
  target : msg.currentTarget = tokenAddress
  creation : msg.target = none
  collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false
  rules : msg.benv.stat.rules = muirGlacierRules
  gas : msg.gas = 580351
  process : processCreateMessage msg = .ok post
  installed : (post.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList
  storage : Devm.getStor post tokenAddress = deployedStor deployer.toB256
  error : post.error = none
  refund : post.refundCounter = 0
  logs : post.logs = [transferLog tokenAddress deployer.toB256]
  deletions : post.accountsToDelete = .emptyWithCapacity
  gasLeft : post.gasLeft = 0

/-- Prepare the recorded signed CREATE and execute its constructor under Muir Glacier from honest
pre-execution facts. No successful run, constructor result or gas observation is assumed. -/
theorem prepare_muir_actual_creation
    (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (hnonce : benv.state.getNonce deployer = 42)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 81690894457745154 ≤ (benv.state.bal deployer).toNat)
    (hroom : 678343 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hfresh : accountHasCodeOrNonce benv.state tokenAddress = false) :
    ∃ debit msg post, PreparedCreation benv bout index debit msg post := by
  have hrules : benv.beginTransaction.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hnonceMax : (benv.state.get deployer).nonce ≠ UInt64.max := by
    change benv.state.getNonce deployer ≠ UInt64.max
    rw [hnonce]
    decide
  have hfeeWord : (81690894457745154 : Nat).toB256.toNat = 81690894457745154 :=
    B256.toNat_toB256_of_lt (by decide)
  have hpay : (81690894457745154 : Nat).toB256 ≤ benv.state.bal deployer := by
    rw [B256.le_iff_toNat_le_toNat, hfeeWord]
    exact hfunds
  let debit := (benv.state.incrNonce deployer).setBal deployer
    (benv.state.bal deployer - (81690894457745154 : Nat).toB256)
  have hdebit : (benv.state.incrNonce deployer).subBal deployer
      (81690894457745154 : Nat).toB256 = some debit := subBal_incrNonce_of_le hpay
  have hnonceDebit : debit.getNonce deployer = 43 := by
    change (debit.get deployer).nonce = 43
    dsimp only [debit]
    rw [debit_get_self hnonceMax]
    change benv.state.getNonce deployer + 1 = 43
    rw [hnonce]
    rfl
  have htargetAccount : debit.get tokenAddress = benv.state.get tokenAddress :=
    debit_get_ne (by decide : deployer ≠ tokenAddress)
  have hcollision : accountHasCodeOrNonce debit tokenAddress = false := by
    unfold accountHasCodeOrNonce State.getNonce State.getCode
    rw [htargetAccount]
    exact hfresh
  let tenv := transactionTenv benv.beginTransaction tx index deployer 120427120878 97992 []
  let msg : Msg :=
    { benv := { benv.beginTransaction with state := debit }, tenv := tenv,
      caller := deployer, target := none, gas := tx.gas - 97992,
      value := 0, data := [], code := .mk (.mk tx.data), depth := 1024,
      currentTarget := tokenAddress, codeAddress := none,
      shouldTransferValue := true, isStatic := false,
      accessedAddresses := tenv.stat.accessListAddresses.insertMany
        (benv.beginTransaction.stat.rules.precompiles ++ [deployer, tokenAddress]),
      accessedStorageKeys := tenv.stat.accessListStorageKeys, disablePrecompiles := false }
  have htarget : computeContractAddress deployer (debit.getNonce deployer - 1) =
      tokenAddress := by
    rw [hnonceDebit, tokenAddress_eq]
    rfl
  have hreceiver : tx.type.receiver? = none := rfl
  have horigin : tenv.stat.origin = deployer := rfl
  have hprepared : prepareMessage { benv.beginTransaction with state := debit } tenv tx =
      .ok msg := by
    simp only [prepareMessage, hreceiver, horigin, htarget]
    rfl
  have hcode : msg.code = Creation.code := by
    change ByteArray.mk (Array.mk tx.data) = Creation.code
    rw [tx_data, ByteArray.toList_eq_toList_data]
  have hmsgRules : msg.benv.stat.rules = muirGlacierRules := hrules
  have hmsgGas : msg.gas = 580351 := rfl
  obtain ⟨post, hrun, hinstalled, hstor, herror, hrefund, hlogs, hdeletions, hleft⟩ :=
    curve_create_muir_meta msg rfl rfl hcode rfl rfl (Nat.le_of_eq hmsgGas.symm) hmsgRules rfl
  refine ⟨debit, msg, post,
    { validated := ?_,
      checked := checked_muir benv bout index hfork hbasefee hnonce hsenderCode hfunds hroom,
      debited := hdebit, prepared := hprepared, target := rfl, creation := rfl,
      collision := hcollision, rules := hmsgRules, gas := hmsgGas, process := hrun,
      installed := hinstalled, storage := hstor, error := herror, refund := hrefund,
      logs := hlogs, deletions := hdeletions, gasLeft := by rw [hleft, hmsgGas] }⟩
  change validateTransaction (Fork.ruleSet benv.stat.fork) tx 0 = _
  rw [hfork]
  exact validated_muir

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx
