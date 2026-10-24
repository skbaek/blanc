import Blanc.TransactionForward
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionAccountingAdmissionIn

/-!
# The forward direction of a transaction, from rule facts

`Blanc/TransactionForward.lean` assembles `processTransaction` from its stages under the
settlement facts of the covered forks (no touched-account sweep, refund quotient 5). This module
is the same converse with no settlement fact beyond `rules.stateGas = none` and
`rules.bal = none`, so that it applies to every pre-Amsterdam schedule:

* `processMessageCall_create_of_message`: the creation wrapper of a top-level CREATE message
  whose target has neither code nor nonce, over a successful `processCreateMessage`;
* `txGasUsedQ`: the gas a transaction uses under refund quotient `q`;
* `processTransaction_of_stagesH`: the whole transaction, whose settled state is the message's
  state with the sender's refund and the coinbase's fee credited, the accounts to delete
  destroyed and the touched accounts swept under the rules' own `touchedSweep`.
-/

namespace Blanc

open Jaune ExecutionTrace

/-- **The creation wrapper over a successful raw creation.**  A creation message (`target`
absent) under rules without a state-gas dimension, whose target has neither code nor nonce,
settles as its `processCreateMessage` core: the same state, the core's gas, and (with no core
error) its logs, accounts to delete, touched accounts and non-negative refund counter. -/
theorem processMessageCall_create_of_message {msg : Msg} {post : Devm} {refund : Nat}
    (hsg : msg.benv.stat.rules.stateGas = none) (htarget : msg.target = none)
    (hfresh : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false)
    (hcreate : processCreateMessage msg = .ok post) (herror : post.error = none)
    (hrefund : Int.toNat? post.refundCounter = some refund) :
    processMessageCall msg = .ok (post.state,
      { gasLeft := post.gasLeft, refundCounter := (refund : Int),
        logs := post.logs, accountsToDelete := post.accountsToDelete,
        error := none, returnData := post.output,
        touchedAccounts := post.meta.touchedAccounts }) := by
  unfold processMessageCall
  simp only [htarget, Option.isNone_none, ↓reduceIte]
  unfold processMessageCall.create
  rw [hsg]
  simp only [hfresh, Bool.false_eq_true, ↓reduceIte, hcreate, bind, Except.bind, Except.bimap, id,
    herror, Option.isNone_none, hrefund, Option.toExcept]

/-- The gas a transaction uses under refund quotient `q`: the gas spent less the refund (capped
at the `q`-th part of the gas spent), but at least the calldata floor. -/
def txGasUsedQ (q gas calldataFloor gasLeft refund : Nat) : Nat :=
  max (gas - gasLeft - min ((gas - gasLeft) / q) refund) calldataFloor

/-- **A transaction from its stages, under any rules without state gas or a block access
list.**  The successful validation, admission check, debit, message preparation and
message-call outcome of a transaction are its `processTransaction`: the returned state is the
message's, with the sender's gas refund and the coinbase's priority fee credited, the message's
accounts to delete destroyed, and the message's touched accounts swept by the rules' own
EIP-161 sweep (the identity where the rules have none). -/
theorem processTransaction_of_stagesH
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
      (sweepTouchedAccounts benv.stat.rules mout.touchedAccounts.toList
        (mout.accountsToDelete.toList.foldl destroyAccount
          ((mpost.addBal sender
              ((tx.gas - txGasUsedQ benv.stat.rules.settle.refundQuotient tx.gas
                  calldataFloorGas mout.gasLeft refund) * effectiveGasPrice).toB256).addBal
            benv.stat.coinbase
              (txGasUsedQ benv.stat.rules.settle.refundQuotient tx.gas calldataFloorGas
                  mout.gasLeft refund * (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256)),
        bout') := by
  have hsg' : benv.beginTransaction.stat.rules.stateGas = none := hsg
  unfold processTransaction
  simp only [bind, Except.bind]
  rw [recoverValidationSender_of_stateGas_none tx hsg']
  simp only [BenvStat.rules, Benv.beginTransaction, transactionPreludeBout, transactionBlobGasFee,
    transactionTenv, Except.mapError] at hvalid hchecked hdebit hprepared hsg hbal hsg' ⊢
  simp only [hvalid, hchecked, hdebit, hprepared, Option.toExcept, allocateEvmGas, hsg, hcall,
    hrefund]
  apply Exists.intro
  simp only [settleSelfdestructs, hsg, hbal, settleTransactionGas, txGasUsedQ]
  rfl

/-- A credit leaves an account's storage alone when that account holds nonempty code. -/
theorem getStor_addBal_of_code_nonempty {st : State} {w a : Adr} (v : B256)
    (hcode : (st.getCode w).toList ≠ []) : (st.addBal a v).getStor w = st.getStor w := by
  rw [getStor_addBal]
  refine ite_eq_right (fun h => ?_)
  obtain ⟨rfl, hempty⟩ := h
  apply hcode
  have hsize : (st.getCode a).size = 0 := hempty.1
  rw [ByteArray.size_eq_length_toList] at hsize
  exact List.eq_nil_of_length_eq_zero hsize

/-- **An installed account through transaction settlement.**  An account `w` with nonempty code
in the message's post-state keeps its code and storage through the settlement of
`processTransaction_of_stagesH`: the two balance credits, a deletion fold that never names `w`,
and the touched sweep (which only erases empty accounts). -/
theorem settled_getCode_getStor_of_code_nonempty {rules : ForkRules} {touched dels : List Adr}
    {st : State} {s c w : Adr} {r f : B256}
    (hdel : ∀ a ∈ dels, a ≠ w) (hcode : (st.getCode w).toList ≠ []) :
    (sweepTouchedAccounts rules touched
        (dels.foldl destroyAccount ((st.addBal s r).addBal c f))).getCode w = st.getCode w ∧
      (sweepTouchedAccounts rules touched
        (dels.foldl destroyAccount ((st.addBal s r).addBal c f))).getStor w = st.getStor w := by
  have hcodeY : ((st.addBal s r).addBal c f).getCode w = st.getCode w := by
    rw [State.addBal_getCode, State.addBal_getCode]
  have hstorY : ((st.addBal s r).addBal c f).getStor w = st.getStor w := by
    rw [getStor_addBal_of_code_nonempty f (by rw [State.addBal_getCode]; exact hcode),
      getStor_addBal_of_code_nonempty r hcode]
  have hfold := foldl_destroyAccount_get_eq (state := (st.addBal s r).addBal c f) hdel
  have hcodeZ : ((dels.foldl destroyAccount ((st.addBal s r).addBal c f)).getCode w).toList ≠ [] := by
    change ((dels.foldl destroyAccount ((st.addBal s r).addBal c f)).get w).code.toList ≠ []
    rw [hfold]
    change (((st.addBal s r).addBal c f).getCode w).toList ≠ []
    rw [hcodeY]
    exact hcode
  have hsweep := sweepTouchedAccounts_get_of_code_nonempty rules touched hcodeZ
  refine ⟨?_, ?_⟩
  · unfold State.getCode
    rw [hsweep, hfold]
    exact hcodeY
  · unfold State.getStor
    rw [hsweep, hfold]
    exact hstorY

/-- **An account installed by the message survives the transaction.**  From the stages of
`processTransaction_of_stagesH`, an account that holds nonempty code in the message-call
post-state and that the message does not schedule for deletion has, in the settled
post-transaction state, the message's code and storage. -/
theorem processTransaction_installed_of_stagesH
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {intrinsicGas calldataFloorGas : Nat} {sender : Adr} {effectiveGasPrice : Nat}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    {debit : State} {msg : Msg} {mpost : State} {mout : MsgCallOutput} {refund : Nat} {w : Adr}
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
    (hrefund : Int.toNat? mout.refundCounter = some refund)
    (hcode : (mpost.getCode w).toList ≠ []) (hdel : w ∉ mout.accountsToDelete) :
    ∃ post bout', processTransaction benv bout tx index = .ok (post, bout') ∧
      post.getCode w = mpost.getCode w ∧ post.getStor w = mpost.getStor w := by
  obtain ⟨bout', htx⟩ := processTransaction_of_stagesH hsg hbal hvalid hchecked hdebit hprepared
    hcall hrefund
  exact ⟨_, bout', htx, settled_getCode_getStor_of_code_nonempty
    (fun a ha heq => hdel (heq ▸ Std.HashSet.mem_toList.mp ha)) hcode⟩

end Blanc
