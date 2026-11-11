import Blanc.Lift.BeaconDeposit.Creation.HistoricalTxSettle
import Blanc.TransactionAdmissionProjection
import Blanc.ExecutionMidHistoryIn

/-! The recovered transaction's real retained index-2 admission and settlement cut.
Successful creation remains an explicit field of that same trace; concrete receipt
and historical block-output bindings are separate obligations. -/

namespace Blanc.Lift.BeaconDeposit.Creation.HistoricalTx

open Jaune Blanc.BeaconDeposit ExecutionTrace

/-- Actual checked Muir admission supplies every account/capacity input of the
existing forward constructor; the sender is the already kernel-recovered signer. -/
theorem actual_prechecks {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier) (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.sender = deployer ∧ trace.effectiveGasPrice = 147000000000 ∧
      trace.blobVersionedHashes = [] ∧
      benv.state.getNonce deployer = 0 ∧
      (benv.state.getCode deployer).isEmpty = true ∧
      461814024000000000 ≤ (benv.state.bal deployer).toNat ∧
      3141592 ≤ benv.stat.blockGasLimit - bout.blockGasUsed := by
  have recovery := checkTransaction_sender trace.checked
  change recoverSender benv.stat.chainId tx = .ok trace.sender at recovery
  rw [hchain, recoveredSender] at recovery
  have senderEq : trace.sender = deployer := (Except.ok.inj recovery).symm
  obtain ⟨feeBeforeBlob, fee, gasStage, feeStage, blobStage, accountStage⟩ :=
    checkTransaction_admission_parts trace.checked
  have feeKnown : checkTransactionGasFee benv.beginTransaction tx =
      .ok (147000000000, 461814024000000000) := by
    change checkTransactionLegacyGasFee benv.stat.baseFeePerGas 3141592 147000000000 = _
    rw [hbasefee]
    decide +kernel
  have feePair := Prod.mk.inj (Except.ok.inj (feeStage.symm.trans feeKnown))
  have blobKnown : checkTransactionBlobData benv.beginTransaction tx feeBeforeBlob =
      .ok (feeBeforeBlob, []) := rfl
  have blobPair := Prod.mk.inj (Except.ok.inj (blobStage.symm.trans blobKnown))
  have feeEq : fee = 461814024000000000 := blobPair.1.trans feePair.2
  have nonce := checkTransaction_sender_nonce trace.checked
  change benv.state.getNonce trace.sender = 0 at nonce
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
  exact ⟨senderEq, feePair.1, blobPair.2, nonce, noCode, funds, room⟩

/-- The actual up-front state is fixed by the checked sender and fee. -/
def muirDebit (benv : Benv) : State :=
  (benv.state.incrNonce deployer).setBal deployer
    (benv.state.bal deployer - (461814024000000000 : Nat).toB256)

theorem actual_debit {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier) (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.debitState = muirDebit benv ∧ trace.debitState.getNonce deployer = 1 ∧
      trace.debitState.get depositAddress = benv.state.get depositAddress := by
  obtain ⟨senderEq, priceEq, -, nonce, -, funds, -⟩ :=
    actual_prechecks trace hfork hchain hbasefee
  have paid : (461814024000000000 : Nat).toB256 ≤ benv.state.bal deployer := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by decide)]
    exact funds
  have debit := trace.debit
  rw [senderEq, priceEq] at debit
  change (benv.state.incrNonce deployer).subBal deployer
    (461814024000000000 : Nat).toB256 = some trace.debitState at debit
  have same : trace.debitState = muirDebit benv :=
    Option.some.inj (debit.symm.trans (subBal_incrNonce_of_le paid))
  refine ⟨same, ?_, ?_⟩
  · rw [same]
    change ((muirDebit benv).get deployer).nonce = 1
    unfold muirDebit
    rw [debit_get_self (by change benv.state.getNonce deployer ≠ UInt64.max; rw [nonce]; decide)]
    change benv.state.getNonce deployer + 1 = 1
    rw [nonce]
    rfl
  · rw [same]
    exact debit_get_ne (by decide : deployer ≠ depositAddress)

/-- The prepared message of that same checked trace is the actual signed CREATE target. -/
theorem actual_message_target {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier) (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.msg.target = none ∧ trace.msg.currentTarget = depositAddress := by
  have senderEq := (actual_prechecks trace hfork hchain hbasefee).1
  have nonce := (actual_debit trace hfork hchain hbasefee).2.1
  have prepared := trace.prepared
  have receiver : tx.type.receiver? = none := rfl
  simp only [prepareMessage, receiver] at prepared
  have same := Except.ok.inj prepared
  have creation := congrArg Msg.target same
  have target := congrArg Msg.currentTarget same
  change none = trace.msg.target at creation
  change computeContractAddress trace.sender
    (trace.debitState.getNonce trace.sender - 1) = trace.msg.currentTarget at target
  rw [senderEq, nonce, UInt64.sub_self] at target
  exact ⟨creation.symm, target.symm.trans depositAddress_eq.symm⟩

/-- Actual message success rules out the collision arm. This is an intermediate
same-trace success condition, not a claim that historical receipt evidence is bound. -/
theorem actual_fresh_of_success {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier) (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (success : trace.messageOut.error = none) :
    accountHasCodeOrNonce benv.state depositAddress = false := by
  obtain ⟨creation, target⟩ := actual_message_target trace hfork hchain hbasefee
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
        have error := congrArg (fun result : State × MsgCallOutput => result.2.error)
          (Except.ok.inj result)
        rw [success] at error
        cases error
  rw [target, world] at noCollision
  have account := (actual_debit trace hfork hchain hbasefee).2.2
  unfold accountHasCodeOrNonce State.getCode State.getNonce at noCollision ⊢
  rw [account] at noCollision
  exact noCollision

/-- The existing forward constructor/settlement result is forced to be this
actual retained index-2 post-state by deterministic transaction evaluation. -/
theorem actual_settled_cut {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier) (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (success : trace.messageOut.error = none) :
    (state.getCode depositAddress).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (state.getStor depositAddress) [] ∧ bout'.blockLogs = bout.blockLogs := by
  obtain ⟨-, -, -, nonce, senderCode, funds, room⟩ :=
    actual_prechecks trace hfork hchain hbasefee
  have fresh := actual_fresh_of_success trace hfork hchain hbasefee success
  obtain ⟨intrinsic, debit, msg, post, output, prepared, -, transaction,
      -, -, -, -, logs, code, invariant⟩ :=
    settle_muir_actual_creation benv bout index hfork hchain hbasefee nonce senderCode funds room fresh
  have same := Prod.mk.inj (Except.ok.inj (transaction.symm.trans trace.result))
  rw [← same.1, ← same.2]
  exact ⟨code, invariant, logs⟩

/-- Transaction identity is transported on the supplied retained witness itself. -/
theorem actual_settled_cut_of_tx_eq {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {currentTx : Tx} {index : Nat}
    (trace : TransactionTrace benv bout currentTx index state bout') (sameTx : currentTx = tx)
    (hfork : benv.stat.fork = .muirGlacier) (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0) (success : trace.messageOut.error = none) :
    (state.getCode depositAddress).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (state.getStor depositAddress) [] ∧ bout'.blockLogs = bout.blockLogs := by
  subst currentTx
  exact actual_settled_cut trace hfork hchain hbasefee success

/-- The real index-2 cut of a retained mainnet deployment block. Fork, chain ID,
and absent historical base fee follow from its actual selection/header validation.
The exact body identity and same-trace success remain honest concrete-binding inputs. -/
theorem actual_block_cut {pre D : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (cut : block.bodyTrace.transactions.TxSplit 2)
    (number : block.block.header.number = 11052984)
    (timestamp : block.block.header.timestamp = 1602667372)
    (atTwo : block.bodyTrace.decodedTxs[2]? = some tx)
    (success : cut.head.messageOut.error = none) :
    (cut.txState.getCode depositAddress).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (cut.txState.getStor depositAddress) [] ∧ cut.txBout.blockLogs = cut.bout.blockLogs := by
  have selected : mainnetChainConfig.forkAt block.block.header.number
      block.block.header.timestamp = .ok .muirGlacier := by
    rw [number, timestamp]
    decide +kernel
  have forkEq : block.fork = .muirGlacier := Except.ok.inj (block.forkAt.symm.trans selected)
  have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
    block.txSplit_stat cut
  have forkAtCut : cut.benv.stat.fork = .muirGlacier := by rw [stat]; exact forkEq
  have chain : cut.benv.stat.chainId = 1 := by
    rw [stat]
    exact (stateTransitionUsing_success_chainId_eq block.transition).symm
  have last : D.blocks.getLast? = some block.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) block.postEq).trans
      (appendBlock_getLast? _ _)
  obtain ⟨selectedFork, lookup, shape⟩ := stateTransitionUsing_shapeCoherent block.transition _ last
  have shapeFork : selectedFork = .muirGlacier := Except.ok.inj (lookup.symm.trans selected)
  have absent : block.block.header.baseFeePerGas = none := by
    have present := checkHeaderShape_baseFee shape
    rw [shapeFork] at present
    change block.block.header.baseFeePerGas.isSome = false at present
    exact Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp present)
  have baseFee : cut.benv.stat.baseFeePerGas = 0 := by
    rw [stat]
    change block.block.header.baseFeePerGas.getD 0 = 0
    rw [absent]
    rfl
  have sameTx : cut.tx = tx := Option.some.inj (cut.putIndex_eq.2.symm.trans atTwo)
  exact actual_settled_cut_of_tx_eq cut.head sameTx forkAtCut chain baseFee success

end Blanc.Lift.BeaconDeposit.Creation.HistoricalTx
