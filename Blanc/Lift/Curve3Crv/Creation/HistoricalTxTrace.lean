import Blanc.Lift.Curve3Crv.Creation.HistoricalTxSettle
import Blanc.TransactionAdmissionProjection
import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionIndexedReceipts

/-!
# The 3Crv creation transaction as a retained transaction trace and block cut

On any `TransactionTrace` of the recorded transaction under Muir Glacier with no base fee, the
checked admission fixes the sender (the kernel-recovered deployer), price, nonce 42, empty
sender code, funds and block-gas room (`actual_prechecks`), the debit and the CREATE target
(`actual_debit`, `actual_message_target`); success of the message excludes the collision arm
(`actual_fresh_of_success`); and deterministic evaluation forces the forward settlement
(`actual_settled_cut`). `actual_block_cut` places this inside a retained configured mainnet
block, deriving the fork and base fee from the header and success from the block's receipt.
-/

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx

open Jaune Blanc.Lift ExecutionTrace

/-- Actual checked Muir admission supplies every account/capacity input of the
existing forward constructor; the sender is the already kernel-recovered signer. -/
theorem actual_prechecks {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.sender = deployer ∧ trace.effectiveGasPrice = 120427120878 ∧
      trace.blobVersionedHashes = [] ∧
      benv.state.getNonce deployer = 42 ∧
      (benv.state.getCode deployer).isEmpty = true ∧
      81690894457745154 ≤ (benv.state.bal deployer).toNat ∧
      678343 ≤ benv.stat.blockGasLimit - bout.blockGasUsed := by
  have recovery := checkTransaction_sender trace.checked
  change recoverSender benv.stat.chainId tx = .ok trace.sender at recovery
  rw [recoveredSender] at recovery
  have senderEq : trace.sender = deployer := (Except.ok.inj recovery).symm
  obtain ⟨feeBeforeBlob, fee, gasStage, feeStage, blobStage, accountStage⟩ :=
    checkTransaction_admission_parts trace.checked
  have feeKnown : checkTransactionGasFee benv.beginTransaction tx =
      .ok (120427120878, 81690894457745154) := by
    change checkTransactionLegacyGasFee benv.stat.baseFeePerGas 678343 120427120878 = _
    rw [hbasefee]
    decide +kernel
  have feePair := Prod.mk.inj (Except.ok.inj (feeStage.symm.trans feeKnown))
  have blobKnown : checkTransactionBlobData benv.beginTransaction tx feeBeforeBlob =
      .ok (feeBeforeBlob, []) := rfl
  have blobPair := Prod.mk.inj (Except.ok.inj (blobStage.symm.trans blobKnown))
  have feeEq : fee = 81690894457745154 := blobPair.1.trans feePair.2
  have nonce := checkTransaction_sender_nonce trace.checked
  change benv.state.getNonce trace.sender = 42 at nonce
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
    (benv.state.bal deployer - (81690894457745154 : Nat).toB256)

theorem actual_debit {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.debitState = muirDebit benv ∧ trace.debitState.getNonce deployer = 43 ∧
      trace.debitState.get tokenAddress = benv.state.get tokenAddress := by
  obtain ⟨senderEq, priceEq, -, nonce, -, funds, -⟩ :=
    actual_prechecks trace hfork hbasefee
  have paid : (81690894457745154 : Nat).toB256 ≤ benv.state.bal deployer := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by decide)]
    exact funds
  have debit := trace.debit
  rw [senderEq, priceEq] at debit
  change (benv.state.incrNonce deployer).subBal deployer
    (81690894457745154 : Nat).toB256 = some trace.debitState at debit
  have same : trace.debitState = muirDebit benv :=
    Option.some.inj (debit.symm.trans (subBal_incrNonce_of_le paid))
  refine ⟨same, ?_, ?_⟩
  · rw [same]
    change ((muirDebit benv).get deployer).nonce = 43
    unfold muirDebit
    rw [debit_get_self (by change benv.state.getNonce deployer ≠ UInt64.max; rw [nonce]; decide)]
    change benv.state.getNonce deployer + 1 = 43
    rw [nonce]
    rfl
  · rw [same]
    exact debit_get_ne (by decide : deployer ≠ tokenAddress)

/-- The prepared message of that same checked trace is the actual signed CREATE target. -/
theorem actual_message_target {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0) :
    trace.msg.target = none ∧ trace.msg.currentTarget = tokenAddress := by
  have senderEq := (actual_prechecks trace hfork hbasefee).1
  have nonce := (actual_debit trace hfork hbasefee).2.1
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
  exact ⟨creation.symm, target.symm.trans tokenAddress_eq.symm⟩

/-- Actual message success rules out the collision arm. This is an intermediate
same-trace success condition, not a claim that historical receipt evidence is bound. -/
theorem actual_fresh_of_success {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (success : trace.messageOut.error = none) :
    accountHasCodeOrNonce benv.state tokenAddress = false := by
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
        have error := congrArg (fun result : State × MsgCallOutput => result.2.error)
          (Except.ok.inj result)
        rw [success] at error
        cases error
  rw [target, world] at noCollision
  have account := (actual_debit trace hfork hbasefee).2.2
  unfold accountHasCodeOrNonce State.getCode State.getNonce at noCollision ⊢
  rw [account] at noCollision
  exact noCollision

/-- The forward constructor and settlement result is forced to be the retained post-state by
deterministic transaction evaluation. -/
theorem actual_settled_cut {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (success : trace.messageOut.error = none) :
    (state.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      state.getStor tokenAddress = deployedStor deployer.toB256 ∧
      bout'.blockLogs = bout.blockLogs ++ [creationLog] ∧
      bout'.blockGasUsed = bout.blockGasUsed + 678343 := by
  obtain ⟨-, -, -, nonce, senderCode, funds, room⟩ :=
    actual_prechecks trace hfork hbasefee
  have fresh := actual_fresh_of_success trace hfork hbasefee success
  obtain ⟨debit, msg, post, output, -, transaction, -, -, used, -, logs, code, storage⟩ :=
    settle_muir_actual_creation benv bout index hfork hbasefee nonce senderCode funds room fresh
  have same := Prod.mk.inj (Except.ok.inj (transaction.symm.trans trace.result))
  rw [← same.1, ← same.2]
  exact ⟨code, storage, logs, used⟩

/-- Transaction identity is transported on the supplied retained witness itself. -/
theorem actual_settled_cut_of_tx_eq {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {currentTx : Tx} {index : Nat}
    (trace : TransactionTrace benv bout currentTx index state bout') (sameTx : currentTx = tx)
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0) (success : trace.messageOut.error = none) :
    (state.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      state.getStor tokenAddress = deployedStor deployer.toB256 ∧
      bout'.blockLogs = bout.blockLogs ++ [creationLog] ∧
      bout'.blockGasUsed = bout.blockGasUsed + 678343 := by
  subst currentTx
  exact actual_settled_cut trace hfork hbasefee success

/-- The deployment block's fork is Muir Glacier, and inside it every cut has Muir rules and no
base fee. -/
theorem block_muir {pre D : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (number : block.block.header.number = 10809467)
    (timestamp : block.block.header.timestamp = 1599414946) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    block.fork = .muirGlacier ∧ cut.benv.stat.fork = .muirGlacier ∧
      cut.benv.stat.baseFeePerGas = 0 := by
  have selected : mainnetChainConfig.forkAt block.block.header.number
      block.block.header.timestamp = .ok .muirGlacier := by
    rw [number, timestamp]
    decide +kernel
  have forkEq : block.fork = .muirGlacier := Except.ok.inj (block.forkAt.symm.trans selected)
  have stat : cut.benv.stat = (initBenv block.fork pre block.block.header).stat :=
    block.txSplit_stat cut
  have forkAtCut : cut.benv.stat.fork = .muirGlacier := by rw [stat]; exact forkEq
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
  exact ⟨forkEq, forkAtCut, baseFee⟩

/-- **The 3Crv creation transaction inside its Muir block.** In a retained `HistFork` mainnet
block at the deployment coordinates (block 10,809,467, timestamp 1,599,414,946), a transaction
cut whose transaction is the recorded signed CREATE and whose receipt in the block output
reports success leaves, right after the transaction, the certified runtime at `tokenAddress`
with storage `deployedStor deployer`; the block's log list gains exactly the creation log and its
gas used grows by exactly 678,343. Fork, base fee, sender, funds, nonce, sender code, block-gas
room and target freshness are all derived; the receipt status is used only to exclude the
CREATE collision arm. -/
theorem actual_block_cut {pre D : BlockChain}
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre D)
    (number : block.block.header.number = 10809467)
    (timestamp : block.block.header.timestamp = 1599414946) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (sameTx : cut.tx = tx)
    {receipt : Fin 5 × Receipt}
    (lookup : block.blockOutput.receiptsTrie[BLT.toBytes (.bytes cut.index.toBytes)]? =
      some receipt) (succeeded : receipt.2.succeeded = true) :
    (cut.txState.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      cut.txState.getStor tokenAddress = deployedStor deployer.toB256 ∧
      cut.txBout.blockLogs = cut.bout.blockLogs ++ [creationLog] ∧
      cut.txBout.blockGasUsed = cut.bout.blockGasUsed + 678343 := by
  obtain ⟨forkEq, forkAtCut, baseFee⟩ := block_muir block number timestamp cut
  have success := block.txSplit_error_eq_none_of_receipt cut (by rw [forkEq]; rfl)
    lookup succeeded
  exact actual_settled_cut_of_tx_eq cut.head sameTx forkAtCut baseFee success

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx
