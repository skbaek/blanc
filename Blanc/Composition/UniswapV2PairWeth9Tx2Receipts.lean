import Blanc.TransactionForward

/-!
# A type-2 call transaction, with the receipts it leaves untouched

`processTransaction_call_value_of_exec_receipts_frame` is `processTransaction_call_value_of_exec_receipts`
(`Blanc/TransactionForward.lean`) with one more conjunct: every receipt key other than the
transaction's own reads back as before.  A later transaction of a block needs it to carry the earlier
receipts (for `parseDepositRequests`).  Hoist candidate: the extra conjunct belongs on the original
lemmas.
-/

namespace Blanc

open Jaune ExecutionTrace

theorem processTransaction_of_stages_receipts_frame
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
        max (tx.gas - mout.gasLeft - min ((tx.gas - mout.gasLeft) / 5) refund) calldataFloorGas ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx mout.error bout'.cumulativeGasUsed mout.logs) ∧
      (∀ key, key ≠ BLT.toBytes (.bytes index.toBytes) →
        bout'.receiptsTrie[key]? = bout.receiptsTrie[key]?) := by
  have hsg' : benv.beginTransaction.stat.rules.stateGas = none := hsg
  unfold processTransaction
  simp only [bind, Except.bind]
  rw [recoverValidationSender_of_stateGas_none tx hsg']
  simp only [BenvStat.rules, Benv.beginTransaction, transactionPreludeBout, transactionBlobGasFee,
    transactionTenv, Except.mapError] at hvalid hchecked hdebit hprepared hsg hbal hsg' ⊢
  simp only [hvalid, hchecked, hdebit, hprepared, Option.toExcept, allocateEvmGas, hsg, hcall, hrefund]
  apply Exists.intro
  simp only [settleSelfdestructs, hsg, hbal, settleTransactionGas]
  refine ⟨rfl, rfl, rfl, rfl, Std.TreeMap.getElem?_insert_self, fun key hne => ?_⟩
  exact Std.TreeMap.getElem?_insert.trans (if_neg (fun e => hne (Std.LawfulEqCmp.eq_of_compare e).symm))

theorem processTransaction_call_value_of_exec_receipts_frame
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E t : Adr}
    {chainId : UInt64} {maxPriorityFee maxFee intrinsicGas calldataFloorGas : Nat}
    {Q : State → Devm → Prop}
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some t) [])
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hcost : calculateIntrinsicCost benv.stat.rules tx E = (intrinsicGas, calldataFloorGas))
    (hgas : max intrinsicGas calldataFloorGas ≤ tx.gas)
    (hcap : checkTransactionGasCap benv.stat.rules.tx tx.gas = .ok ())
    (hnonceMax : tx.nonce ≠ UInt64.max)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce)
    (hnocode : (benv.state.get E).code.isEmpty = true)
    (hfunds : tx.gas * maxFee + tx.value ≤ (benv.state.get E).bal.toNat)
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
        txGasUsed tx.gas calldataFloorGas post.gasLeft post.refundCounter.toNat ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx none bout'.cumulativeGasUsed post.logs) ∧
      (∀ key, key ≠ BLT.toBytes (.bytes index.toBytes) →
        bout'.receiptsTrie[key]? = bout.receiptsTrie[key]?) := by
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
      (checkTransactionSenderAccount_ok_of_noCode hnonce hfunds hnocode)
  have heff_le : min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas ≤
      maxFee := by omega
  have hpay : tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas) ≤ (benv.state.get E).bal.toNat :=
    le_trans (Nat.mul_le_mul_left _ heff_le) (by omega)
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
  have hvalueFit : tx.value < 2 ^ 256 := by omega
  have hfeeFit : tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas) < 2 ^ 256 := by omega
  have hremaining : tx.value.toB256 ≤ benv.state.bal E -
      (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas)).toB256 := by
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt hvalueFit,
      B256.toNat_sub_eq_of_le _ _ hle, B256.toNat_toB256_of_lt hfeeFit]
    have heffTotal := Nat.mul_le_mul_left tx.gas heff_le
    change tx.value ≤ (benv.state.get E).bal.toNat - _
    omega
  let entryMsg := (callMessage { benv.beginTransaction with state :=
      ((benv.state.incrNonce E).setBal E (benv.state.bal E -
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256)) }
      (transactionTenv benv.beginTransaction tx index E
        (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        intrinsicGas []) tx t)
  have affordable : ¬ entryMsg.benv.state.bal entryMsg.caller < entryMsg.value := by

      apply B256.not_lt.mpr
      change tx.value.toB256 ≤
        (((benv.state.incrNonce E).setBal E (benv.state.bal E -
          (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256)).get E).bal
      rw [State.setBal_get_self, Acct.clearIfEmpty_bal]
      exact hremaining
  obtain ⟨after, hentry⟩ : ∃ after, entryMsg.benvAfterTransfer = .ok after := by
    by_cases zero : entryMsg.value = 0
    · exact ⟨_, Msg.benvAfterTransfer_of_value_zero zero⟩
    · obtain ⟨_, _, transfer⟩ := Msg.benvAfterTransfer_of_affordable entryMsg rfl affordable zero
      exact ⟨_, transfer⟩
  have hdebit' : (benv.state.incrNonce E).subBal E
      (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas) + transactionBlobGasFee benv tx).toB256 = some
      ((benv.state.incrNonce E).setBal E (benv.state.bal E -
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256)) := by
    rw [transactionBlobGasFee_two htype, Nat.add_zero]
    exact hdebit
  obtain ⟨post, hex, herr, hrf, hQ⟩ := hexec _ _ _ hdebit hprepared hentry
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
        intrinsicGas []) tx t) hsg rfl
    (by simp only [callMessage, transactionTenv, Tx.auths, htype, List.isEmpty_nil]) hcode
    hpm herr (Int.toNat?_eq_some_of_nonneg hrf)
  obtain ⟨bout', hproc, hcum, hblk, hkeys, hreceipt, hother⟩ := processTransaction_of_stages_receipts_frame
    (benv := benv)
    (bout := bout) (tx := tx) (index := index) (intrinsicGas := intrinsicGas)
    (calldataFloorGas := calldataFloorGas) (sender := E)
    (effectiveGasPrice := min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas) (blobVersionedHashes := []) (txBlobGasUsed := calculateTotalBlobGas tx)
    hsg hbalr hvalid hchecked hdebit' hprepared hcall
    (by rw [Int.toNat?_eq_some_of_nonneg (by omega : (0 : Int) ≤ ((0 + post.refundCounter.toNat : Nat) : Int))])
  refine ⟨_, post, bout', hQ, ?_, ?_, ?_, hkeys, hreceipt, hother⟩
  · simpa only [txGasUsed, Nat.zero_add, Nat.add_sub_cancel, Int.toNat_natCast] using hproc
  · simpa only [txGasUsed, Nat.zero_add, Int.toNat_natCast] using hcum
  · simpa only [txGasUsed, Nat.zero_add, Int.toNat_natCast] using hblk

end Blanc
