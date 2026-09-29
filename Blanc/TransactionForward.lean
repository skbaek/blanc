import Blanc.ExecutionTrace

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
  rfl

end Blanc
