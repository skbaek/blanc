import Blanc.Lift.Curve3Pool.Creation.HistoricalTx
import Blanc.TransactionHistoricalForward
import Blanc.TransactionAdmissionProjection
import Blanc.TransactionForwardH
import Blanc.ExecutionInCellProvenance
import Blanc.ExecutionHistoryMuirCut

/-!
# The 3pool creation transaction, prepared, settled and placed in its block

* `prepare_muir_actual_creation`, `settle_muir_actual_creation`: from honest pre-execution facts
  the recorded signed CREATE is admitted, executed and settled at its block's Muir rules; its gas
  used is exactly the signed limit 4,812,312, it logs nothing, and the settled state holds the
  certified runtime at `poolAddress` with storage `deployedStor deployTime`.
* `actual_prechecks`, `actual_debit`, `actual_message_target`, `actual_fresh_of_success`: on a
  retained trace, checked admission fixes the sender, nonce 43, funds and room, and message
  success excludes the collision arm.
* `actual_block_cut`: inside a retained configured mainnet block at the recorded coordinates, a
  cut holding the recorded transaction whose receipt reports success leaves the runtime and the
  deployed storage. Fork, base fee, clock, sender, funds, nonce, sender code, gas room and target
  freshness are all derived.
-/

namespace Blanc.Lift.Curve3Pool.Creation.HistoricalTx

open Jaune Blanc.Lift ExecutionTrace

/-- The maximum gas fee: `4812312 · 120202843721` wei. -/
theorem fee_eq : tx.gas * 120202843721 = 578453587272692952 := rfl

/-- Muir validates the recorded CREATE with its exact intrinsic gas. -/
theorem validated_muir : validateTransaction muirGlacierRules tx 0 = .ok (385884, 0) := by
  have h := validateTransaction_ok_of_noInitcodeLimit
    (rules := muirGlacierRules) (tx := tx) (sender := 0) (f := 0)
    rfl rfl (by rw [muir_intrinsic]) (by rw [muir_intrinsic]; decide) (by decide) rfl
  rw [muir_intrinsic] at h
  exact h

/-- Admission uses the kernel-recovered sender. -/
theorem checked_muir (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (hnonce : benv.state.getNonce deployer = 43)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 578453587272692952 ≤ (benv.state.bal deployer).toNat)
    (hroom : 4812312 ≤ benv.stat.blockGasLimit - bout.blockGasUsed) :
    checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (deployer, 120202843721, [], 0) := by
  have hrules : benv.beginTransaction.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hgas := checkTransactionGasLimits_ok_of_room
    (benv := benv.beginTransaction) (bout := transactionPreludeBout bout tx index) (tx := tx)
    (by rw [hrules]; rfl) hroom (by change 0 ≤ _; exact Nat.zero_le _)
  refine checkTransaction_ok_of_parts
    (benv := benv.beginTransaction) (bout := transactionPreludeBout bout tx index) (tx := tx)
    (sender := deployer) (blobGas := 0) (effectiveGasPrice := 120202843721)
    (maxFee := 578453587272692952) (maxFee' := 578453587272692952) (blobHashes := [])
    hgas ?_ (recoveredSender _) ?_ rfl rfl rfl ?_
  · simp only [checkTransactionChainId, tx]
    rfl
  · change checkTransactionLegacyGasFee benv.stat.baseFeePerGas 4812312 120202843721 = _
    rw [hbasefee]
    decide
  · apply checkTransactionSenderAccount_ok_of_noCode
    · exact hnonce
    · exact hfunds
    · exact hsenderCode

/-- Exact stage equations of the prepared creation and the constructor's postcondition. -/
structure PreparedCreation (benv : Benv) (bout : BlockOutput) (index : Nat)
    (debit : Jaune.State) (msg : Msg) (post : Devm) : Prop where
  validated : validateTransaction benv.stat.rules tx 0 = .ok (385884, 0)
  checked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
    .ok (deployer, 120202843721, [], 0)
  debited : (benv.state.incrNonce deployer).subBal deployer
    (578453587272692952 : Nat).toB256 = some debit
  prepared : prepareMessage { benv.beginTransaction with state := debit }
    (transactionTenv benv.beginTransaction tx index deployer 120202843721 385884 []) tx =
    .ok msg
  target : msg.currentTarget = poolAddress
  creation : msg.target = none
  collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false
  rules : msg.benv.stat.rules = muirGlacierRules
  gas : msg.gas = 4426428
  process : processCreateMessage msg = .ok post
  installed : (post.getCode poolAddress).toList = Blanc.Lift.Curve3Pool.code.toList
  storage : Devm.getStor post poolAddress = deployedStor deployTime
  error : post.error = none
  refund : post.refundCounter = 0
  logs : post.logs = []
  deletions : post.accountsToDelete = .emptyWithCapacity
  gasLeft : post.gasLeft = 0

/-- Prepare the recorded signed CREATE and execute its constructor under Muir Glacier from honest
pre-execution facts. -/
theorem prepare_muir_actual_creation
    (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (htime : benv.stat.time = deployTime)
    (hnonce : benv.state.getNonce deployer = 43)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 578453587272692952 ≤ (benv.state.bal deployer).toNat)
    (hroom : 4812312 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hfresh : accountHasCodeOrNonce benv.state poolAddress = false) :
    ∃ debit msg post, PreparedCreation benv bout index debit msg post := by
  have hrules : benv.beginTransaction.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hnonceMax : (benv.state.get deployer).nonce ≠ UInt64.max := by
    change benv.state.getNonce deployer ≠ UInt64.max
    rw [hnonce]
    decide
  have hfeeWord : (578453587272692952 : Nat).toB256.toNat = 578453587272692952 :=
    B256.toNat_toB256_of_lt (by decide)
  have hpay : (578453587272692952 : Nat).toB256 ≤ benv.state.bal deployer := by
    rw [B256.le_iff_toNat_le_toNat, hfeeWord]
    exact hfunds
  let debit := (benv.state.incrNonce deployer).setBal deployer
    (benv.state.bal deployer - (578453587272692952 : Nat).toB256)
  have hdebit : (benv.state.incrNonce deployer).subBal deployer
      (578453587272692952 : Nat).toB256 = some debit := subBal_incrNonce_of_le hpay
  have hnonceDebit : debit.getNonce deployer = 44 := by
    change (debit.get deployer).nonce = 44
    dsimp only [debit]
    rw [debit_get_self hnonceMax]
    change benv.state.getNonce deployer + 1 = 44
    rw [hnonce]
    rfl
  have htargetAccount : debit.get poolAddress = benv.state.get poolAddress :=
    debit_get_ne (by decide : deployer ≠ poolAddress)
  have hcollision : accountHasCodeOrNonce debit poolAddress = false := by
    unfold accountHasCodeOrNonce State.getNonce State.getCode
    rw [htargetAccount]
    exact hfresh
  let tenv := transactionTenv benv.beginTransaction tx index deployer 120202843721 385884 []
  let msg : Msg :=
    { benv := { benv.beginTransaction with state := debit }, tenv := tenv,
      caller := deployer, target := none, gas := tx.gas - 385884,
      value := 0, data := [], code := .mk (.mk tx.data), depth := 1024,
      currentTarget := poolAddress, codeAddress := none,
      shouldTransferValue := true, isStatic := false,
      accessedAddresses := tenv.stat.accessListAddresses.insertMany
        (benv.beginTransaction.stat.rules.precompiles ++ [deployer, poolAddress]),
      accessedStorageKeys := tenv.stat.accessListStorageKeys, disablePrecompiles := false }
  have htarget : computeContractAddress deployer (debit.getNonce deployer - 1) =
      poolAddress := by
    rw [hnonceDebit, poolAddress_eq]
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
  have hmsgGas : msg.gas = 4426428 := rfl
  have hmsgTime : msg.benv.stat.time = deployTime := htime
  obtain ⟨post, hrun, hinstalled, hstor, herror, hrefund, hlogs, hdeletions, hleft⟩ :=
    pool_create_muir_meta msg rfl rfl hcode (Nat.le_of_eq hmsgGas.symm) hmsgRules rfl
      (by rw [hmsgTime]; decide)
  rw [hmsgTime] at hstor
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

/-! ## Settlement -/

/-- Muir's gas used for the transaction (refund quotient 2, no calldata floor, no refund). -/
def muirGasUsed (post : Devm) : Nat :=
  selectedTxGasUsed 2 tx.gas 0 post.gasLeft 0

theorem muirGasUsed_eq (post : Devm) : muirGasUsed post = tx.gas - post.gasLeft := by
  simp only [muirGasUsed, selectedTxGasUsed, Nat.min_zero, Nat.sub_zero, Nat.max_zero]

/-- The Muir sweep after the sender's gas refund and coinbase's fee credit. -/
def muirSettledState (benv : Benv) (post : Devm) : Jaune.State :=
  sweepTouchedAccounts muirGlacierRules post.meta.touchedAccounts.toList
    ((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 120202843721).toB256).addBal benv.stat.coinbase
      (muirGasUsed post * 120202843721).toB256)

/-- The prepared transaction executes its CREATE wrapper cleanly. -/
theorem msgCall_muir {benv : Benv} {bout : BlockOutput} {index : Nat}
    {debit : Jaune.State} {msg : Msg} {post : Devm}
    (p : PreparedCreation benv bout index debit msg post) :
    processMessageCall msg = .ok (post.state, directCreateMessageOutputOf post) := by
  simpa only [directCreateMessageOutputOf, p.error, Nat.cast_zero] using
    (processMessageCall_create_of_message (refund := 0)
      (by rw [p.rules]; rfl) (by rw [p.creation])
      p.collision p.process p.error (by rw [p.refund]; rfl))

/-- **The gas used is the signed gas limit**, reproduced. -/
theorem muirGasUsed_eq_limit {benv : Benv} {bout : BlockOutput} {index : Nat}
    {debit : Jaune.State} {msg : Msg} {post : Devm}
    (p : PreparedCreation benv bout index debit msg post) : muirGasUsed post = 4812312 := by
  rw [muirGasUsed_eq, p.gasLeft]
  rfl

/-- The transaction settles from the producer's stages. -/
theorem settle_muir_prepared_creation
    {benv : Benv} {bout : BlockOutput} {index : Nat}
    {debit : Jaune.State} {msg : Msg} {post : Devm}
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (p : PreparedCreation benv bout index debit msg post) :
    ∃ bout', processTransaction benv bout tx index = .ok (muirSettledState benv post, bout') ∧
      bout'.blockGasUsed = bout.blockGasUsed + muirGasUsed post ∧
      bout'.blockLogs = bout.blockLogs := by
  have hrules : benv.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hquot : muirGlacierRules.settle.refundQuotient = 2 := rfl
  have hdebit : (benv.state.incrNonce deployer).subBal deployer
      (tx.gas * 120202843721 + transactionBlobGasFee benv tx).toB256 = some debit := by
    change (benv.state.incrNonce deployer).subBal deployer
      (tx.gas * 120202843721 + 0).toB256 = some debit
    rw [Nat.add_zero, fee_eq]
    exact p.debited
  have hvalid : validateTransaction benv.stat.rules tx 0 = .ok (385884, 0) := p.validated
  obtain ⟨bout', htx, -, hblk, -, -, hlogs⟩ :=
    processTransaction_of_stages_selected_receipts
      (by rw [hrules]; rfl) (by rw [hrules]; rfl) hvalid p.checked
      hdebit p.prepared (msgCall_muir p) (by rfl)
  refine ⟨bout', ?_, ?_, ?_⟩
  · simpa only [selectedTxFinalState, directCreateMessageOutputOf, p.deletions,
      Std.HashSet.toList_emptyWithCapacity, List.foldl_nil, hrules, hquot, hbasefee,
      Nat.sub_zero, muirGasUsed, muirSettledState] using htx
  · simpa only [hrules, hquot, directCreateMessageOutputOf, muirGasUsed] using hblk
  · simpa only [directCreateMessageOutputOf, p.logs, List.append_nil] using hlogs

/-- The certified runtime is nonempty. -/
theorem runtime_ne_nil : Blanc.Lift.Curve3Pool.code.toList ≠ [] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The two balance credits and the Muir sweep preserve the pool's code and storage, also for a
coinbase equal to the pool's address. -/
theorem muirSettledState_installed {benv : Benv} {bout : BlockOutput} {index : Nat}
    {debit : Jaune.State} {msg : Msg} {post : Devm}
    (p : PreparedCreation benv bout index debit msg post) :
    ((muirSettledState benv post).getCode poolAddress).toList =
        Blanc.Lift.Curve3Pool.code.toList ∧
      (muirSettledState benv post).getStor poolAddress = deployedStor deployTime := by
  have hcode : (post.state.getCode poolAddress).toList ≠ [] := by
    rw [show (post.state.getCode poolAddress).toList =
      Blanc.Lift.Curve3Pool.code.toList from p.installed]
    exact runtime_ne_nil
  have hcode1 : ((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 120202843721).toB256).getCode poolAddress).toList ≠ [] := by
    rw [State.addBal_getCode]
    exact hcode
  have hcode2 : (((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 120202843721).toB256).addBal benv.stat.coinbase
        (muirGasUsed post * 120202843721).toB256).getCode poolAddress).toList ≠ [] := by
    rw [State.addBal_getCode]
    exact hcode1
  constructor
  · unfold muirSettledState
    rw [sweepTouchedAccounts_getCode_of_nonempty _ _ hcode2,
      State.addBal_getCode, State.addBal_getCode]
    exact p.installed
  · unfold muirSettledState
    rw [sweepTouchedAccounts_getStor_of_nonempty _ _ hcode2,
      addBal_getStor_of_codenonempty hcode1, addBal_getStor_of_codenonempty hcode]
    exact p.storage

/-- **The recorded signed Muir CREATE is admitted, executed and settled** from honest
pre-execution conditions. -/
theorem settle_muir_actual_creation
    (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (htime : benv.stat.time = deployTime)
    (hnonce : benv.state.getNonce deployer = 43)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 578453587272692952 ≤ (benv.state.bal deployer).toNat)
    (hroom : 4812312 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hfresh : accountHasCodeOrNonce benv.state poolAddress = false) :
    ∃ post bout',
      processTransaction benv bout tx index = .ok (muirSettledState benv post, bout') ∧
      bout'.blockGasUsed = bout.blockGasUsed + 4812312 ∧
      bout'.blockLogs = bout.blockLogs ∧
      ((muirSettledState benv post).getCode poolAddress).toList =
        Blanc.Lift.Curve3Pool.code.toList ∧
      (muirSettledState benv post).getStor poolAddress = deployedStor deployTime := by
  obtain ⟨_, _, post, p⟩ := prepare_muir_actual_creation benv bout index
    hfork hbasefee htime hnonce hsenderCode hfunds hroom hfresh
  obtain ⟨bout', htx, hblk, hlogs⟩ := settle_muir_prepared_creation hfork hbasefee p
  rw [muirGasUsed_eq_limit p] at hblk
  obtain ⟨hcode, hstor⟩ := muirSettledState_installed p
  exact ⟨post, bout', htx, hblk, hlogs, hcode, hstor⟩

/-! ## On a retained trace -/

/-- Actual checked Muir admission supplies every account/capacity input of the forward
constructor; the sender is the kernel-recovered signer. -/
theorem actual_prechecks {benv : Benv} {bout : BlockOutput} {state : Jaune.State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.sender = deployer ∧ trace.effectiveGasPrice = 120202843721 ∧
      benv.state.getNonce deployer = 43 ∧
      (benv.state.getCode deployer).isEmpty = true ∧
      578453587272692952 ≤ (benv.state.bal deployer).toNat ∧
      4812312 ≤ benv.stat.blockGasLimit - bout.blockGasUsed := by
  have recovery := checkTransaction_sender trace.checked
  change recoverSender benv.stat.chainId tx = .ok trace.sender at recovery
  rw [recoveredSender] at recovery
  have senderEq : trace.sender = deployer := (Except.ok.inj recovery).symm
  obtain ⟨feeBeforeBlob, fee, gasStage, feeStage, blobStage, accountStage⟩ :=
    checkTransaction_admission_parts trace.checked
  have feeKnown : checkTransactionGasFee benv.beginTransaction tx =
      .ok (120202843721, 578453587272692952) := by
    change checkTransactionLegacyGasFee benv.stat.baseFeePerGas 4812312 120202843721 = _
    rw [hbasefee]
    decide +kernel
  have feePair := Prod.mk.inj (Except.ok.inj (feeStage.symm.trans feeKnown))
  have blobKnown : checkTransactionBlobData benv.beginTransaction tx feeBeforeBlob =
      .ok (feeBeforeBlob, []) := rfl
  have blobPair := Prod.mk.inj (Except.ok.inj (blobStage.symm.trans blobKnown))
  have feeEq : fee = 578453587272692952 := blobPair.1.trans feePair.2
  have nonce := checkTransaction_sender_nonce trace.checked
  change benv.state.getNonce trace.sender = 43 at nonce
  rw [senderEq] at nonce
  have disabled : benv.beginTransaction.stat.rules.delegationEnabled = false := by
    change benv.stat.fork.ruleSet.delegationEnabled = false
    rw [hfork]
    rfl
  have noCode := checkTransactionSenderAccountFor_code_empty disabled accountStage
  change (benv.state.getCode trace.sender).isEmpty = true at noCode
  rw [senderEq] at noCode
  have funds := checkTransactionSenderAccountFor_funds accountStage
  change fee + 0 ≤ (benv.state.bal trace.sender).toNat at funds
  rw [feeEq, senderEq, Nat.add_zero] at funds
  have room := checkTransactionGasLimits_room (by
    change benv.stat.fork.ruleSet.stateGas = none
    rw [hfork]
    rfl) gasStage
  exact ⟨senderEq, feePair.1, nonce, noCode, funds, room⟩

/-- The actual up-front state is fixed by the checked sender and fee. -/
theorem actual_debit {benv : Benv} {bout : BlockOutput} {state : Jaune.State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.debitState.getNonce deployer = 44 ∧
      trace.debitState.get poolAddress = benv.state.get poolAddress := by
  obtain ⟨senderEq, priceEq, nonce, -, funds, -⟩ :=
    actual_prechecks trace hfork hbasefee
  have paid : (578453587272692952 : Nat).toB256 ≤ benv.state.bal deployer := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by decide)]
    exact funds
  have debit := trace.debit
  rw [senderEq, priceEq] at debit
  change (benv.state.incrNonce deployer).subBal deployer
    (578453587272692952 : Nat).toB256 = some trace.debitState at debit
  have same : trace.debitState = (benv.state.incrNonce deployer).setBal deployer
      (benv.state.bal deployer - (578453587272692952 : Nat).toB256) :=
    Option.some.inj (debit.symm.trans (subBal_incrNonce_of_le paid))
  refine ⟨?_, ?_⟩
  · rw [same]
    change (((benv.state.incrNonce deployer).setBal deployer
      (benv.state.bal deployer - (578453587272692952 : Nat).toB256)).get deployer).nonce = 44
    rw [debit_get_self (by change benv.state.getNonce deployer ≠ UInt64.max; rw [nonce]; decide)]
    change benv.state.getNonce deployer + 1 = 44
    rw [nonce]
    rfl
  · rw [same]
    exact debit_get_ne (by decide : deployer ≠ poolAddress)

/-- The prepared message of that same checked trace is the actual signed CREATE target. -/
theorem actual_message_target {benv : Benv} {bout : BlockOutput} {state : Jaune.State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.msg.target = none ∧ trace.msg.currentTarget = poolAddress := by
  have senderEq := (actual_prechecks trace hfork hbasefee).1
  have nonce := (actual_debit trace hfork hbasefee).1
  have prepared := trace.prepared
  have receiver : tx.type.receiver? = none := rfl
  simp only [prepareMessage, receiver] at prepared
  have same := Except.ok.inj prepared
  have creation := congrArg Msg.target same
  have target := congrArg Msg.currentTarget same
  change none = trace.msg.target at creation
  change computeContractAddress trace.sender
    (trace.debitState.getNonce trace.sender - 1) = trace.msg.currentTarget at target
  rw [senderEq, nonce] at target
  exact ⟨creation.symm, target.symm.trans poolAddress_eq.symm⟩

/-- Actual message success rules out the collision arm. -/
theorem actual_fresh_of_success {benv : Benv} {bout : BlockOutput} {state : Jaune.State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (success : trace.messageOut.error = none) :
    accountHasCodeOrNonce benv.state poolAddress = false := by
  obtain ⟨creation, target⟩ := actual_message_target trace hfork hbasefee
  have world := prepareMessage_benv trace.prepared
  have hsg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [world]
    change benv.stat.fork.ruleSet.stateGas = none
    rw [hfork]
    rfl
  have noCollision : accountHasCodeOrNonce trace.msg.benv.state trace.msg.currentTarget = false := by
    cases collision : accountHasCodeOrNonce trace.msg.benv.state trace.msg.currentTarget with
    | false => rfl
    | true =>
        have result := trace.message.result
        simp only [processMessageCall, creation, Option.isNone_none, ↓reduceIte,
          processMessageCall.create, hsg, collision] at result
        have error := congrArg (fun result : Jaune.State × MsgCallOutput => result.2.error)
          (Except.ok.inj result)
        rw [success] at error
        cases error
  rw [target, world] at noCollision
  have account := (actual_debit trace hfork hbasefee).2
  unfold accountHasCodeOrNonce State.getCode State.getNonce at noCollision ⊢
  rw [account] at noCollision
  exact noCollision

/-- **The 3pool creation transaction inside its Muir block.** In a retained `HistFork` mainnet
block at the deployment coordinates (block 10,809,473, timestamp 1,599,414,978), a transaction cut
whose transaction is the recorded signed CREATE and whose receipt in the block output reports
success leaves, right after the transaction, the certified runtime at `poolAddress` with storage
`deployedStor deployTime`. Fork, base fee, clock, sender, funds, nonce, sender code, block-gas room
and target freshness are all derived; the receipt status is used only to exclude the CREATE
collision arm. -/
theorem actual_block_cut {pre D : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (number : block.block.header.number = 10809473)
    (timestamp : block.block.header.timestamp = 1599414978) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (sameTx : cut.tx = tx)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    (cut.txState.getCode poolAddress).toList = Blanc.Lift.Curve3Pool.code.toList ∧
      cut.txState.getStor poolAddress = deployedStor deployTime := by
  obtain ⟨forkEq, hfork, hbasefee, htime⟩ := block.txSplit_muir (by
    rw [number, timestamp]; decide +kernel) cut
  have success := block.txSplit_error_eq_none_of_receipt cut (by rw [forkEq]; rfl)
    lookup succeeded
  obtain ⟨index, tx', benv, bout, txState, txBout, _, _, head, _, _, _⟩ := cut
  subst sameTx
  obtain ⟨-, -, nonce, senderCode, funds, room⟩ := actual_prechecks head hfork hbasefee
  have fresh := actual_fresh_of_success head hfork hbasefee success
  have htime' : benv.stat.time = deployTime := by
    rw [htime, timestamp]
    rfl
  obtain ⟨post, bout', transaction, -, -, code, storage⟩ :=
    settle_muir_actual_creation benv bout index hfork hbasefee htime' nonce senderCode funds room
      fresh
  have same := Prod.mk.inj (Except.ok.inj (transaction.symm.trans head.result))
  change (txState.getCode poolAddress).toList = _ ∧ txState.getStor poolAddress = _
  rw [← same.1]
  exact ⟨code, storage⟩

end Blanc.Lift.Curve3Pool.Creation.HistoricalTx
