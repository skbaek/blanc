import Blanc.ExecutionTrace
import Blanc.MessageExecution

/-!
# The forward direction of a successful transaction

`ExecutionTrace.exists_transactionTrace` and `TransactionTrace.exists_finalStateForm` invert a
successful `processTransaction`: they read its validation, admission, debit, prepared message and
settlement out of the result.  This module is the converse, contract-neutral, for the forks
without a state-gas dimension or a block access list (`CoveredFork`): given each stage's
successful result, Jaune's `processTransaction` returns the exact settled state.  A transaction
of one contract's theorem therefore needs only its own stage facts (which for a concrete
transaction are evaluations) and the message's outcome, never a private copy of the envelope.

* `processMessageCall_call_of_message`: the call wrapper of a code-free-of-delegation, auth-free
  message over a successful `processMessage`.
* `processTransaction_of_stages`: the whole transaction.
-/

namespace Blanc

open Jaune ExecutionTrace

/-- **The call wrapper over a successful raw message.**  A call message (`target` present) with
no authorizations whose code is not an EIP-7702 delegation, under a fork without a state-gas
dimension, settles as its `processMessage` core: the same state, the core's gas, and (with no
core error) its logs, accounts to delete and non-negative refund counter. -/
theorem processMessageCall_call_of_message {msg : Msg} {post : Devm} {refund : Nat}
    (hsg : msg.benv.stat.rules.stateGas = none) (htarget : msg.target.isNone = false)
    (hauths : msg.tenv.stat.auths.isEmpty = true)
    (hdelegation : getDelegatedCodeAddress msg.code = none)
    (hprocess : processMessage msg = .ok post) (herror : post.error = none)
    (hrefund : Int.toNat? post.refundCounter = some refund) :
    processMessageCall msg = .ok (post.state,
      { gasLeft := post.gasLeft, refundCounter := ((0 + refund : Nat) : Int),
        logs := post.logs, accountsToDelete := post.accountsToDelete,
        error := none, returnData := post.output }) := by
  unfold processMessageCall
  simp only [htarget, Bool.false_eq_true, ↓reduceIte]
  unfold processMessageCall.call
  rw [hsg]
  simp only [hauths, ↓reduceIte, hdelegation, hprocess, bind, Except.bind, Except.bimap, id,
    herror, Option.isNone_none, hrefund, Option.toExcept]
  rfl

/-- **The admission check from its parts.**  Jaune's `checkTransaction` is the conjunction, in
order, of its gas-limit, chain-id, sender-recovery, fee, blob, receiver, authorization-list and
sender-account checks: when each part succeeds the whole succeeds with the recovered sender, the
effective gas price, the blob hashes and the blob gas. -/
theorem checkTransaction_ok_of_parts {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {blobGas effectiveGasPrice maxFee maxFee' : Nat} {blobHashes : List B256}
    (hgas : checkTransactionGasLimits benv bout tx = .ok blobGas)
    (hchain : checkTransactionChainId benv tx = .ok ())
    (hrecover : recoverSender benv.stat.chainId tx = .ok sender)
    (hfee : checkTransactionGasFee benv tx = .ok (effectiveGasPrice, maxFee))
    (hblob : checkTransactionBlobData benv tx maxFee = .ok (maxFee', blobHashes))
    (hreceiver : checkTransactionReceiver tx = .ok ())
    (hauth : checkTransactionAuthorizationList tx = .ok ())
    (hsender : checkTransactionSenderAccount (benv.state.get sender) tx maxFee' = .ok ()) :
    checkTransaction benv bout tx = .ok (sender, effectiveGasPrice, blobHashes, blobGas) := by
  unfold checkTransaction
  simp only [bind, Except.bind, Except.mapError, hgas, hchain, hrecover, hfee, hblob, hreceiver,
    hauth, hsender]

/-- The block-gas check of a transaction without a state-gas dimension: the transaction's gas
fits the block's remaining execution gas and its blob gas the remaining blob gas. -/
theorem checkTransactionGasLimits_ok_of_room {benv : Benv} {bout : BlockOutput} {tx : Tx}
    (hsg : benv.stat.rules.stateGas = none)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hblob : calculateTotalBlobGas tx ≤ benv.stat.rules.blob.max - bout.blobGasUsed) :
    checkTransactionGasLimits benv bout tx = .ok (calculateTotalBlobGas tx) := by
  unfold checkTransactionGasLimits
  simp only [hsg, gt_iff_lt, Nat.not_lt.mpr hroom, Nat.not_lt.mpr hblob, ↓reduceIte]

/-! ### The admission checks of a type-2 transaction, from stated facts -/

/-- The fee rules of a type-2 transaction: when the priority fee is at most the fee cap, the block's
base fee is at most the fee cap and the maximum gas fee fits a word, the effective gas price is the
priority fee (capped by the fee cap less the base fee) over the base fee, and the maximum gas fee is
`gas * maxFee`. -/
theorem checkTransactionGasFee_two {benv : Benv} {tx : Tx} {chainId : UInt64}
    {maxPriorityFee maxFee : Nat} {receiver : Option Adr} {accessList : AccessList}
    (htype : tx.type = .two chainId maxPriorityFee maxFee receiver accessList)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hfit : tx.gas * maxFee ≤ B256.max.toNat) :
    checkTransactionGasFee benv tx = .ok
      (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas,
        tx.gas * maxFee) := by
  unfold checkTransactionGasFee
  rw [htype]
  unfold checkTransactionDynamicGasFee
  simp only [Nat.not_lt.mpr hprio, Nat.not_lt.mpr hbase, Nat.not_lt.mpr hfit, ↓reduceIte]

/-- A type-2 transaction's chain id is the block's. -/
theorem checkTransactionChainId_two {benv : Benv} {tx : Tx} {chainId : UInt64}
    {maxPriorityFee maxFee : Nat} {receiver : Option Adr} {accessList : AccessList}
    (htype : tx.type = .two chainId maxPriorityFee maxFee receiver accessList)
    (hchain : chainId = benv.stat.chainId) : checkTransactionChainId benv tx = .ok () := by
  unfold checkTransactionChainId
  rw [htype]
  simp only [hchain, ↓reduceIte]

/-- A type-2 transaction carries no blobs: the blob check passes the maximum gas fee through. -/
theorem checkTransactionBlobData_two {benv : Benv} {tx : Tx} {chainId : UInt64}
    {maxPriorityFee maxFee : Nat} {receiver : Option Adr} {accessList : AccessList}
    (htype : tx.type = .two chainId maxPriorityFee maxFee receiver accessList) (m : Nat) :
    checkTransactionBlobData benv tx m = .ok (m, []) := by
  unfold checkTransactionBlobData
  rw [htype]

/-- A type-2 transaction is no blob transaction: the receiver check passes. -/
theorem checkTransactionReceiver_two {tx : Tx} {chainId : UInt64}
    {maxPriorityFee maxFee : Nat} {receiver : Option Adr} {accessList : AccessList}
    (htype : tx.type = .two chainId maxPriorityFee maxFee receiver accessList) :
    checkTransactionReceiver tx = .ok () := by
  unfold checkTransactionReceiver Tx.isTypeThree
  rw [htype]
  rfl

/-- A type-2 transaction carries no authorization list: the check passes. -/
theorem checkTransactionAuthorizationList_two {tx : Tx} {chainId : UInt64}
    {maxPriorityFee maxFee : Nat} {receiver : Option Adr} {accessList : AccessList}
    (htype : tx.type = .two chainId maxPriorityFee maxFee receiver accessList) :
    checkTransactionAuthorizationList tx = .ok () := by
  unfold checkTransactionAuthorizationList
  rw [htype]

/-- **The sender-account check from its facts**: the account's nonce is the transaction's, its
balance covers the maximum gas fee and the value, and it has no code (an externally owned account,
EIP-3607). -/
theorem checkTransactionSenderAccount_ok_of_noCode {acct : Acct} {tx : Tx} {maxGasFee : Nat}
    (hnonce : acct.nonce = tx.nonce) (hbal : maxGasFee + tx.value ≤ acct.bal.toNat)
    (hcode : acct.code.isEmpty = true) :
    checkTransactionSenderAccount acct tx maxGasFee = .ok () := by
  unfold checkTransactionSenderAccount checkTransactionSenderCode
  have h1 : ¬ acct.nonce > tx.nonce := by rw [hnonce]; exact lt_irrefl _
  have h2 : ¬ acct.nonce < tx.nonce := by rw [hnonce]; exact lt_irrefl _
  have h3 : ¬ acct.bal.toNat < maxGasFee + tx.value := Nat.not_lt.mpr hbal
  simp only [h1, h2, h3, hcode, true_or, not_true_eq_false, ↓reduceIte]


/-- **Validation from its facts** (no state-gas dimension): the transaction's gas covers the larger of
its intrinsic cost and calldata floor, its nonce is not the maximal one, it has a receiver (so no
initcode-size check applies) and the fork's per-transaction gas cap (if any) admits its gas. -/
theorem validateTransaction_ok_of_facts {rules : ForkRules} {tx : Tx} {sender : Adr} {i f : Nat}
    (hsg : rules.stateGas = none) (hcost : calculateIntrinsicCost rules tx sender = (i, f))
    (hgas : max i f ≤ tx.gas) (hnonce : tx.nonce ≠ UInt64.max)
    (hreceiver : tx.type.receiver?.isSome = true)
    (hcap : checkTransactionGasCap rules.tx tx.gas = .ok ()) :
    validateTransaction rules tx sender = .ok (i, f) := by
  have hnone : tx.type.receiver?.isNone = false := by
    cases h : tx.type.receiver? <;> simp_all
  have hinit : checkInitcodeSize rules.code tx.type.receiver? tx.data.length = .ok () := by
    unfold checkInitcodeSize
    simp [hnone]
  unfold validateTransaction
  simp only [hsg, hcost, Nat.not_lt.mpr hgas, ↓reduceIte]
  cases hm : rules.tx.maxGas with
  | none =>
    simp [hnonce, hinit, bind, Except.bind]
  | some m =>
    simp [hnonce, hinit, hcap, bind, Except.bind]

/-- The message a call transaction with receiver `t` prepares: it calls `t`'s current code with the
transaction's data and value, from the origin, at the outermost depth, with the origin, the receiver
and the precompiles pre-warmed on top of the transaction's access list. -/
def callMessage (benv : Benv) (tenv : Tenv) (tx : Tx) (t : Adr) : Msg :=
  { benv := benv, tenv := tenv, caller := tenv.stat.origin, target := some t,
    gas := tenv.stat.gas, value := tx.value.toB256, data := tx.data,
    code := benv.state.getCode t, depth := 1024, currentTarget := t, codeAddress := some t,
    shouldTransferValue := true, isStatic := false,
    accessedAddresses := tenv.stat.accessListAddresses.insertMany
      (benv.stat.rules.precompiles ++ [tenv.stat.origin, t]),
    accessedStorageKeys := tenv.stat.accessListStorageKeys, disablePrecompiles := false,
    stateGasGrant := tenv.stat.stateGasReservoir }

/-- **The prepared message of a call transaction** is `callMessage`. -/
theorem prepareMessage_call {benv : Benv} {tenv : Tenv} {tx : Tx} {t : Adr}
    (hreceiver : tx.type.receiver? = some t) :
    prepareMessage benv tenv tx = .ok (callMessage benv tenv tx t) := by
  unfold prepareMessage
  simp only [hreceiver]
  rfl

/-- **A zero-value message entry leaves every account as it was** (the debit and the credit of the
value `0` change nothing, including in the self-call case): the environment after the transfer has the
message's accounts. -/
theorem benvAfterTransfer_get_of_value_zero {msg : Msg} {benv : Benv}
    (hzero : msg.value = 0) (h : msg.benvAfterTransfer = .ok benv) (a : Adr) :
    benv.state.get a = msg.benv.state.get a := by
  by_cases hstv : msg.shouldTransferValue = true
  · obtain ⟨debit, hsub, rfl⟩ := of_benvAfterTransfer hstv h
    rw [hzero] at hsub ⊢
    obtain ⟨_, rfl⟩ := State.of_subBal hsub
    have hself : ∀ (st : State) (b : Adr) (v : B256), v = st.bal b →
        (st.setBal b v).get a = st.get a := by
      intro st b v hv
      by_cases hb : b = a
      · subst hb; rw [State.setBal_get_self, hv]; rfl
      · rw [State.setBal_get_ne hb]
    show ((msg.benv.state.setBal msg.caller _).setBal msg.currentTarget _).get a = _
    rw [hself _ _ _ (by simp only [State.bal]; exact B256.add_zero _)]
    exact hself _ _ _ (B256.sub_zero _)
  · rw [of_benvAfterTransfer_no hstv h]

/-- **A call message with a code address that is no precompile settles as its raw execution**: when the
value moved at entry is zero and the interpreter run from the entry environment succeeds with no frame
error, `processMessage` returns that machine. -/
theorem processMessage_call_of_exec {msg : Msg} {benv : Benv} {post : Devm} {t : Adr}
    (hentry : msg.benvAfterTransfer = .ok benv) (hcodeAddress : msg.codeAddress = some t)
    (hprec : msg.benv.stat.rules.isPrecomp t = false)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post) (herror : post.error = none) :
    processMessage msg = .ok post := by
  refine MessageExecution.processMessage_clean_of_exec_afterTransfer_of_codeEntry msg benv post hentry ?_ hexec herror
  refine MessageExecution.executeCode_enter_of_codeAddress_not_precompile msg benv t hcodeAddress ?_
  rw [benvAfterTransfer_stat hentry]
  simp [hprec]

/-- **A transaction from its stages, with its gas accounting.**  The stages of
`processTransaction_of_stages`, and the block output the transaction leaves: its cumulative and block
gas used advance by the transaction's gas used (the larger of its gas less the gas left after the
refund, capped at a fifth of the gas spent, and its calldata floor). -/
theorem processTransaction_of_stages_gasUsed
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {intrinsicGas calldataFloorGas : Nat} {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    {debit : State} {msg : Msg} {mpost : State} {mout : MsgCallOutput} {refund : Nat}
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    (hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas))
    (hchecked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed))
    (hdebit : (benv.state.incrNonce sender).subBal sender
      (tx.gas * effectiveGasPrice + transactionBlobGasFee benv tx).toB256 = some debit)
    (hprepared : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index sender effectiveGasPrice intrinsicGas
        blobVersionedHashes) tx = .ok msg)
    (hcall : processMessageCall msg = .ok (mpost, mout))
    (hrefund : Int.toNat? mout.refundCounter = some refund) :
    ∃ bout', processTransaction benv bout tx index = .ok
      (mout.accountsToDelete.toList.foldl destroyAccount
        ((mpost.addBal sender
            ((tx.gas -
                max (tx.gas - mout.gasLeft - min ((tx.gas - mout.gasLeft) / 5) refund)
                  calldataFloorGas) * effectiveGasPrice).toB256).addBal
          benv.stat.coinbase
            (max (tx.gas - mout.gasLeft - min ((tx.gas - mout.gasLeft) / 5) refund)
                calldataFloorGas * (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256),
        bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        max (tx.gas - mout.gasLeft - min ((tx.gas - mout.gasLeft) / 5) refund) calldataFloorGas ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        max (tx.gas - mout.gasLeft - min ((tx.gas - mout.gasLeft) / 5) refund) calldataFloorGas := by
  have hsg' : benv.beginTransaction.stat.rules.stateGas = none := hsg
  unfold processTransaction
  simp only [bind, Except.bind]
  rw [recoverValidationSender_of_stateGas_none tx hsg']
  simp only [BenvStat.rules, Benv.beginTransaction, transactionPreludeBout, transactionBlobGasFee,
    transactionTenv, Except.mapError] at hvalid hchecked hdebit hprepared hsg hbal hsg' ⊢
  generalize benv.stat.fork.ruleSet = R at *
  simp only [hvalid, hchecked, hdebit, hprepared, Option.toExcept, allocateEvmGas, hsg, hcall, hrefund]
  apply Exists.intro
  simp only [settleSelfdestructs, hsg, hbal, settleTransactionGas]
  refine ⟨rfl, rfl, rfl⟩

/-- **A transaction from its stages.**  Without a state-gas dimension or a block access list,
the successful validation, admission check, debit, message preparation and message-call outcome
of a transaction are its `processTransaction`: the returned state is the message's, with the
sender's gas refund and the coinbase's priority fee credited and the message's accounts to
delete removed. -/
theorem processTransaction_of_stages
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {intrinsicGas calldataFloorGas : Nat} {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    {debit : State} {msg : Msg} {mpost : State} {mout : MsgCallOutput} {refund : Nat}
    (hsg : benv.stat.rules.stateGas = none) (hbal : benv.stat.rules.bal = none)
    (hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas))
    (hchecked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed))
    (hdebit : (benv.state.incrNonce sender).subBal sender
      (tx.gas * effectiveGasPrice + transactionBlobGasFee benv tx).toB256 = some debit)
    (hprepared : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index sender effectiveGasPrice intrinsicGas
        blobVersionedHashes) tx = .ok msg)
    (hcall : processMessageCall msg = .ok (mpost, mout))
    (hrefund : Int.toNat? mout.refundCounter = some refund) :
    ∃ bout', processTransaction benv bout tx index = .ok
      (mout.accountsToDelete.toList.foldl destroyAccount
        ((mpost.addBal sender
            ((tx.gas -
                max (tx.gas - mout.gasLeft - min ((tx.gas - mout.gasLeft) / 5) refund)
                  calldataFloorGas) * effectiveGasPrice).toB256).addBal
          benv.stat.coinbase
            (max (tx.gas - mout.gasLeft - min ((tx.gas - mout.gasLeft) / 5) refund)
                calldataFloorGas * (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256),
        bout') := by
  obtain ⟨bout', h, -⟩ := processTransaction_of_stages_gasUsed hsg hbal hvalid hchecked hdebit
    hprepared hcall hrefund
  exact ⟨bout', h⟩

/-! ### A type-2 call transaction from the outcome of its message's execution -/

/-- The gas a transaction uses: the gas spent less the refund (capped at a fifth of the gas spent),
but at least the calldata floor. -/
def txGasUsed (gas calldataFloor gasLeft refund : Nat) : Nat :=
  max (gas - gasLeft - min ((gas - gasLeft) / 5) refund) calldataFloor

theorem calculateTotalBlobGas_two {tx : Tx} {chainId : UInt64}
    {maxPriorityFee maxFee : Nat} {receiver : Option Adr} {accessList : AccessList}
    (htype : tx.type = .two chainId maxPriorityFee maxFee receiver accessList) :
    calculateTotalBlobGas tx = 0 := by
  unfold calculateTotalBlobGas
  rw [htype]

theorem transactionBlobGasFee_two {benv : Benv} {tx : Tx} {chainId : UInt64}
    {maxPriorityFee maxFee : Nat} {receiver : Option Adr} {accessList : AccessList}
    (htype : tx.type = .two chainId maxPriorityFee maxFee receiver accessList) :
    transactionBlobGasFee benv tx = 0 := by
  unfold transactionBlobGasFee Tx.isTypeThree
  rw [htype]
  rfl

theorem Int.toNat?_eq_some_of_nonneg {i : Int} (h : 0 ≤ i) : Int.toNat? i = some i.toNat := by
  unfold Int.toNat?
  split <;> simp_all

/-- The debit of a sender that can pay: the nonce is bumped and the amount taken from the balance. -/
theorem subBal_incrNonce_of_le {st : State} {E : Adr} {v : B256} (h : v ≤ st.bal E) :
    (st.incrNonce E).subBal E v = some ((st.incrNonce E).setBal E (st.bal E - v)) := by
  unfold State.subBal
  rw [State.incrNonce_bal]
  simp only [B256.not_lt.mpr h, ↓reduceIte]

/-- **A type-2 call transaction, from the outcome of its message's execution.**  A type-2 transaction
from an externally owned account `E` to `t` with value `0`, whose fees, nonce, funds, gas and
signature pass Jaune's admission checks (stated as facts about the fields and the sender's account),
is processed exactly when its message's interpreter run succeeds: given that run (`hexec`, for the
debited state, the prepared message and its entry environment) succeeding with no frame error and a
non-negative refund counter, `processTransaction` returns the message's world with the sender's gas
refund and the coinbase's priority fee credited and the message's accounts to delete removed, and the
block's gas counters advance by the transaction's gas used. -/
theorem processTransaction_call_of_exec
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E t : Adr}
    {chainId : UInt64} {maxPriorityFee maxFee intrinsicGas calldataFloorGas : Nat}
    {Q : State → Devm → Prop}
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some t) [])
    (hvalue : tx.value = 0) (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hcost : calculateIntrinsicCost benv.stat.rules tx E = (intrinsicGas, calldataFloorGas))
    (hgas : max intrinsicGas calldataFloorGas ≤ tx.gas)
    (hcap : checkTransactionGasCap benv.stat.rules.tx tx.gas = .ok ())
    (hnonceMax : tx.nonce ≠ UInt64.max)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce)
    (hnocode : (benv.state.get E).code.isEmpty = true)
    (hfunds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat)
    (hnodeleg : getDelegatedCodeAddress (benv.state.getCode t) = none)
    (hprec : benv.stat.rules.isPrecomp t = false)
    (hexec : ∀ (debit : State) (msg : Msg) (after : Benv),
      (benv.state.incrNonce E).subBal E
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256 = some debit →
      prepareMessage { benv.beginTransaction with state := debit }
        (transactionTenv benv.beginTransaction tx index E
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
          intrinsicGas []) tx = .ok msg →
      msg.benvAfterTransfer = .ok after →
      ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧ post.error = none ∧
        0 ≤ post.refundCounter ∧ Q debit post) :
    ∃ (debit : State) (post : Devm) (bout' : BlockOutput), Q debit post ∧
      processTransaction benv bout tx index = .ok
        (post.accountsToDelete.toList.foldl destroyAccount
          ((post.state.addBal E
              ((tx.gas - txGasUsed tx.gas calldataFloorGas post.gasLeft post.refundCounter.toNat) *
                (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
                  benv.stat.baseFeePerGas)).toB256).addBal
            benv.stat.coinbase
              (txGasUsed tx.gas calldataFloorGas post.gasLeft post.refundCounter.toNat *
                (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas))).toB256),
          bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        txGasUsed tx.gas calldataFloorGas post.gasLeft post.refundCounter.toNat ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        txGasUsed tx.gas calldataFloorGas post.gasLeft post.refundCounter.toNat := by
  have hsg : benv.stat.rules.stateGas = none := CoveredFork.rules_stateGas_none hfork
  have hbalr : benv.stat.rules.bal = none := CoveredFork.rules_bal_none hfork
  have hmax : B256.max.toNat = 2 ^ 256 - 1 := by decide +kernel
  have hlt256 := B256.toNat_lt (benv.state.get E).bal
  have hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas) := by
    refine validateTransaction_ok_of_facts hsg ?_ hgas hnonceMax (by rw [htype]; rfl) hcap
    rw [calculateIntrinsicCost_sender_congr_none hsg]
    exact hcost
  have hfit : tx.gas * maxFee ≤ B256.max.toNat := by omega
  have hfee := checkTransactionGasFee_two (benv := benv.beginTransaction) htype hprio hbase hfit
  have hgaslim := checkTransactionGasLimits_ok_of_room (benv := benv.beginTransaction)
    (bout := transactionPreludeBout bout tx index) (tx := tx) hsg hroom
    (by rw [calculateTotalBlobGas_two htype]; exact Nat.zero_le _)
  have hchecked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (E, min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas, [],
        calculateTotalBlobGas tx) :=
    checkTransaction_ok_of_parts hgaslim (checkTransactionChainId_two htype hchain) hrecover hfee
      (checkTransactionBlobData_two htype _) (checkTransactionReceiver_two htype)
      (checkTransactionAuthorizationList_two htype)
      (checkTransactionSenderAccount_ok_of_noCode hnonce
        (by show tx.gas * maxFee + tx.value ≤ (benv.state.get E).bal.toNat; omega) hnocode)
  have heff_le : min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas ≤
      maxFee := by omega
  have hpay : tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas) ≤ (benv.state.get E).bal.toNat :=
    le_trans (Nat.mul_le_mul_left _ heff_le) hfunds
  have hle : (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas)).toB256 ≤ benv.state.bal E := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by omega)]
    exact hpay
  have hdebit := subBal_incrNonce_of_le hle
  have hprepared := prepareMessage_call (benv := { benv.beginTransaction with state :=
      ((benv.state.incrNonce E).setBal E (benv.state.bal E -
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256)) })
    (tenv := transactionTenv benv.beginTransaction tx index E
      (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
      intrinsicGas []) (tx := tx) (t := t) (by rw [htype]; rfl)
  obtain ⟨after, hentry⟩ := benvAfterTransfer_exists_of_value_zero
    (msg := callMessage { benv.beginTransaction with state :=
      ((benv.state.incrNonce E).setBal E (benv.state.bal E -
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256)) }
      (transactionTenv benv.beginTransaction tx index E
        (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        intrinsicGas []) tx t) (by simp [callMessage, hvalue]; rfl)
  have hdebit' : (benv.state.incrNonce E).subBal E
      (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas) + transactionBlobGasFee benv tx).toB256 = some
      ((benv.state.incrNonce E).setBal E (benv.state.bal E -
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256)) := by
    rw [transactionBlobGasFee_two htype, Nat.add_zero]
    exact hdebit
  obtain ⟨post, hex, herr, hrf, hQ⟩ := hexec _ _ after hdebit hprepared hentry
  have hpm := processMessage_call_of_exec (t := t) hentry rfl hprec hex herr
  have hcode : getDelegatedCodeAddress (callMessage { benv.beginTransaction with state :=
      ((benv.state.incrNonce E).setBal E (benv.state.bal E -
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256)) }
      (transactionTenv benv.beginTransaction tx index E
        (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        intrinsicGas []) tx t).code = none := by
    show getDelegatedCodeAddress (((benv.state.incrNonce E).setBal E _).getCode t) = none
    rw [State.setBal_getCode]
    show getDelegatedCodeAddress (((benv.state.incrNonce E).get t).code) = none
    rw [State.incrNonce_get_code]
    exact hnodeleg
  have hcall := processMessageCall_call_of_message (msg := callMessage { benv.beginTransaction with
      state := ((benv.state.incrNonce E).setBal E (benv.state.bal E -
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256)) }
      (transactionTenv benv.beginTransaction tx index E
        (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        intrinsicGas []) tx t) hsg rfl (by simp [callMessage, transactionTenv, Tx.auths, htype]) hcode
    hpm herr (Int.toNat?_eq_some_of_nonneg hrf)
  obtain ⟨bout', hproc, hcum, hblk⟩ := processTransaction_of_stages_gasUsed (benv := benv)
    (bout := bout) (tx := tx) (index := index) (intrinsicGas := intrinsicGas)
    (calldataFloorGas := calldataFloorGas) (sender := E)
    (effectiveGasPrice := min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas) (blobVersionedHashes := []) (txBlobGasUsed := calculateTotalBlobGas tx)
    hsg hbalr hvalid hchecked hdebit' hprepared hcall
    (by rw [Int.toNat?_eq_some_of_nonneg (by omega : (0 : Int) ≤ ((0 + post.refundCounter.toNat : Nat) : Int))])
  refine ⟨_, post, bout', hQ, ?_, ?_, ?_⟩
  · simpa only [txGasUsed, Nat.zero_add, Nat.add_sub_cancel, Int.toNat_natCast] using hproc
  · simpa only [txGasUsed, Nat.zero_add, Int.toNat_natCast] using hcum
  · simpa only [txGasUsed, Nat.zero_add, Int.toNat_natCast] using hblk

/-! ### The intrinsic gas of a plain call -/

/-- The calldata tokens of a byte string: one for a zero byte, four for any other. -/
def calldataTokens (data : Bytes) : Nat :=
  data.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) 0

theorem calldataTokens_foldl (l : Bytes) (n : Nat) :
    l.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) n = n + calldataTokens l := by
  unfold calldataTokens
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih (n + _), ih (0 + _)]
    omega

theorem calldataTokens_append (a b : Bytes) :
    calldataTokens (a ++ b) = calldataTokens a + calldataTokens b := by
  unfold calldataTokens
  rw [List.foldl_append, calldataTokens_foldl b, calldataTokens]

theorem calldataTokens_le (data : Bytes) : calldataTokens data ≤ 4 * data.length := by
  induction data with
  | nil => simp [calldataTokens]
  | cons x xs ih =>
    have h := calldataTokens_foldl xs (if x = 0 then 1 else 4)
    have : calldataTokens (x :: xs) = (if x = 0 then 1 else 4) + calldataTokens xs := by
      unfold calldataTokens at h ⊢
      simpa only [List.foldl_cons, Nat.zero_add] using h
    rw [this, List.length_cons]
    split_ifs <;> omega

/-- The transaction base cost is 21000 on every covered fork. -/
theorem CoveredFork.rules_txBase {s : BenvStat} (h : CoveredFork s.fork) :
    s.rules.gas.txBase = 21000 :=
  h.cases (motive := fun f => (Fork.ruleSet f).gas.txBase = 21000) rfl rfl rfl rfl

/-- The calldata floor token costs 10 gas on every covered fork. -/
theorem CoveredFork.rules_floorTokenCost {s : BenvStat} (h : CoveredFork s.fork) :
    s.rules.gas.floorTokenCost = 10 :=
  h.cases (motive := fun f => (Fork.ruleSet f).gas.floorTokenCost = 10) rfl rfl rfl rfl

/-- Clearing a storage slot refunds 4800 gas on every covered fork. -/
theorem CoveredFork.rules_storageClearRefund {s : BenvStat} (h : CoveredFork s.fork) :
    s.rules.gas.storageClearRefund = 4800 :=
  h.cases (motive := fun f => (Fork.ruleSet f).gas.storageClearRefund = 4800) rfl rfl rfl rfl

/-- **The intrinsic cost of a plain type-2 call** (a receiver, no access list, no state-gas dimension):
the transaction base cost plus four gas per calldata token, and the calldata floor of the tokens at the
floor token cost over the base cost. -/
theorem calculateIntrinsicCost_two_call {rules : ForkRules} {tx : Tx} {sender : Adr}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat} {t : Adr}
    (hsg : rules.stateGas = none)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some t) []) :
    calculateIntrinsicCost rules tx sender =
      (rules.gas.txBase + calldataTokens tx.data * standardCallDataTokenCost,
        calldataTokens tx.data * rules.gas.floorTokenCost + rules.gas.txBase) := by
  unfold calculateIntrinsicCost calldataTokens
  simp [hsg, htype, TxType.receiver?]

/-- **The per-transaction gas cap on the covered forks**: no cap at Prague, the EIP-7825 cap `2 ^ 24`
from Osaka; a transaction whose gas is at most `2 ^ 24` passes on every covered fork. -/
theorem CoveredFork.checkTransactionGasCap_ok {s : BenvStat} (h : CoveredFork s.fork) {gas : Nat}
    (hgas : gas ≤ 16777216) : checkTransactionGasCap s.rules.tx gas = .ok () := by
  have hcap : s.rules.tx.maxGas = none ∨ s.rules.tx.maxGas = some 16777216 :=
    h.cases (motive := fun f => (Fork.ruleSet f).tx.maxGas = none ∨
      (Fork.ruleSet f).tx.maxGas = some 16777216) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  unfold checkTransactionGasCap
  rcases hcap with hc | hc <;> rw [hc]
  simp [Nat.not_lt.mpr hgas]

/-- The sender's debit (nonce bump and balance write) leaves every other account alone. -/
theorem debit_get_ne {st : State} {E a : Adr} {v : B256} (h : E ≠ a) :
    ((st.incrNonce E).setBal E v).get a = st.get a := by
  rw [State.setBal_get_ne h]
  unfold State.incrNonce
  rw [State.get_set_ne _ h]

/-- The sender's debit: the account keeps its storage and code, gains one in its nonce, and takes
the written balance. -/
theorem debit_get_self {st : State} {E : Adr} {v : B256} :
    ((st.incrNonce E).setBal E v).get E =
      { st.get E with nonce := (st.get E).nonce + 1, bal := v } := by
  rw [State.setBal_get_self]
  unfold State.incrNonce
  rw [State.get_set_self]
  rfl

/-- A nonce that is not the maximal one can be incremented without wrapping. -/
theorem UInt64.add_one_ne_zero {n : UInt64} (h : n ≠ UInt64.max) : n + 1 ≠ 0 := by
  intro h'
  apply h
  have h2 := congrArg UInt64.toNat h'
  rw [UInt64.toNat_add] at h2
  have h3 : n.toNat < 2 ^ 64 := UInt64.toNat_lt_size n
  have h4 : (1 : UInt64).toNat = 1 := rfl
  have h5 : (0 : UInt64).toNat = 0 := rfl
  rw [h4, h5] at h2
  apply UInt64.toNat_inj.mp
  have h6 : UInt64.max.toNat = 2 ^ 64 - 1 := by decide
  rw [h6]
  omega

/-- A credit reads back as the account with the raised balance. -/
theorem addBal_get_self (st : State) (a : Adr) (v : B256) :
    (st.addBal a v).get a = (st.get a).withBal (st.bal a + v) :=
  State.setBal_get_self

/-- A credit leaves every other account alone. -/
theorem addBal_get_ne {st : State} {a b : Adr} (v : B256) (h : a ≠ b) :
    (st.addBal a v).get b = st.get b :=
  State.setBal_get_ne h

/-- **The sender's balance across a transaction, in naturals**: pay the up-front fee `F`, receive `wad`,
get back the refund `R ≤ F`; when the balance plus `wad` fits a word nothing wraps. -/
theorem sender_net_toNat {b0 wad : B256} {F R : Nat} (hF : F ≤ b0.toNat) (hR : R ≤ F)
    (hnof : b0.toNat + wad.toNat < 2 ^ 256) :
    (b0 - F.toB256 + wad + R.toB256).toNat = b0.toNat - F + wad.toNat + R := by
  have hb0 := B256.toNat_lt b0
  have hFt : F.toB256.toNat = F := B256.toNat_toB256_of_lt (by omega)
  have hRt : R.toB256.toNat = R := B256.toNat_toB256_of_lt (by omega)
  have h1 : (b0 - F.toB256).toNat = b0.toNat - F := by
    rw [B256.toNat_sub_eq_of_le _ _ (by rw [B256.le_iff_toNat_le_toNat, hFt]; exact hF), hFt]
  have h2 : (b0 - F.toB256 + wad).toNat = b0.toNat - F + wad.toNat := by
    rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; omega), h1]
  rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; omega), h2, hRt]

end Blanc
