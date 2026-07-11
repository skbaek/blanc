import Blanc.Solvent

-- Helper: `toB256` truncates, so its `toNat` is at most the original Nat.
lemma toB256_toNat_le (n : Nat) : n.toB256.toNat ≤ n := by
  rw [toNat_toB256]
  unfold Nat.lo
  exact Nat.mod_le _ _

-- Erasing an account removes its balance from the total: nonincreasing.
lemma destroyAccount_sum_le (w : _root_.State) (a : Adr) :
    sum (_root_.destroyAccount w a).bal ≤ sum w.bal := by
  have h0 : ((_root_.destroyAccount w a).get a).bal = 0 := by
    show (State.get (w.erase a) a).bal = 0
    unfold State.get
    rw [Std.TreeMap.getD_erase]; simp [Acct.nil]
  have hdec : Decrease a (w.bal a) w.bal (_root_.destroyAccount w a).bal := by
    intro b; constructor
    · intro heq; subst heq
      show w.bal a - w.bal a = ((_root_.destroyAccount w a).get a).bal
      rw [h0, B256.sub_self]
    · intro hnb
      show w.bal b = (State.get (w.erase a) b).bal
      rw [State.get_erase_ne (Ne.symm hnb)]; rfl
  have hsum := sum_sub_assoc hdec (le_refl _)
  omega

lemma foldl_destroyAccount_sum_le :
    ∀ (as : List Adr) (w : _root_.State),
      sum ((as.foldl _root_.destroyAccount w).bal) ≤ sum w.bal
  | [], _ => le_refl _
  | a :: as, w => by
    rw [List.foldl_cons]
    exact le_trans (foldl_destroyAccount_sum_le as _) (destroyAccount_sum_le w a)

-- Affordability: a successfully checked transaction's up-front debit
-- (gas fee plus blob fee) fits in 256 bits, because `checkTransaction`
-- verifies the sender's (256-bit) balance covers the *max* gas fee.
lemma checkTransaction_fee_lt {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {egp : Nat} {bvh : List B256} {tbgu : Nat}
    (h : checkTransaction benv bout tx = .ok ⟨sender, egp, bvh, tbgu⟩) :
    tx.gas * egp +
      (if tx.isTypeThree = true then
        calculate_data_fee benv.stat.excessBlobGas tx
      else 0) < 2 ^ 256 := by
  unfold checkTransaction at h
  rcases of_bind_eq_ok h with ⟨tbgu', hlim, h⟩
  rcases of_bind_eq_ok h with ⟨senderAddress, hrecover, h⟩
  rcases of_bind_eq_ok h with ⟨fee, hfee, h⟩
  rcases fee with ⟨egp', maxGasFee⟩
  rcases of_bind_eq_ok h with ⟨blob, hblob, h⟩
  rcases blob with ⟨maxGasFee2, bvh'⟩
  rcases of_bind_eq_ok h with ⟨u1, hrecv, h⟩
  rcases of_bind_eq_ok h with ⟨u2, hauth, h⟩
  rcases of_bind_eq_ok h with ⟨u3, hacct, h⟩
  have h' := Except.ok.inj h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
  -- the sender's balance covers `maxGasFee2`
  have hbal : maxGasFee2 ≤ ((benv.state.get senderAddress).bal).toNat := by
    unfold checkTransactionSenderAccount at hacct
    split at hacct <;> try contradiction
    split at hacct <;> try contradiction
    split at hacct <;> try contradiction
    rename_i hlt
    omega
  have hbal_lt : ((benv.state.get senderAddress).bal).toNat < 2 ^ 256 :=
    B256.toNat_lt _
  -- gas fee bound: `tx.gas * egp' ≤ maxGasFee`
  cases htt : tx.type with
  | zero gasPrice recv =>
    simp only [checkTransactionGasFee, htt, checkTransactionLegacyGasFee] at hfee
    split at hfee
    · cases hfee
    · have hfe := Except.ok.inj hfee
      simp only [Prod.mk.injEq] at hfe
      obtain ⟨rfl, rfl⟩ := hfe
      simp only [checkTransactionBlobData, htt] at hblob
      have hbe := Except.ok.inj hblob
      simp only [Prod.mk.injEq] at hbe
      obtain ⟨rfl, rfl⟩ := hbe
      simp only [Tx.isTypeThree, htt, Bool.false_eq_true, if_false]
      omega
  | one cid gasPrice recv al =>
    simp only [checkTransactionGasFee, htt, checkTransactionLegacyGasFee] at hfee
    split at hfee
    · cases hfee
    · have hfe := Except.ok.inj hfee
      simp only [Prod.mk.injEq] at hfe
      obtain ⟨rfl, rfl⟩ := hfe
      simp only [checkTransactionBlobData, htt] at hblob
      have hbe := Except.ok.inj hblob
      simp only [Prod.mk.injEq] at hbe
      obtain ⟨rfl, rfl⟩ := hbe
      simp only [Tx.isTypeThree, htt, Bool.false_eq_true, if_false]
      omega
  | two cid mpf maxFee recv al =>
    simp only [checkTransactionGasFee, htt, checkTransactionDynamicGasFee] at hfee
    split at hfee
    · cases hfee
    · split at hfee
      · cases hfee
      · rename_i hmp hbf
        have hfe := Except.ok.inj hfee
        simp only [Prod.mk.injEq] at hfe
        obtain ⟨rfl, rfl⟩ := hfe
        simp only [checkTransactionBlobData, htt] at hblob
        have hbe := Except.ok.inj hblob
        simp only [Prod.mk.injEq] at hbe
        obtain ⟨rfl, rfl⟩ := hbe
        simp only [Tx.isTypeThree, htt, Bool.false_eq_true, if_false]
        have hegp : min mpf (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas ≤ maxFee := by omega
        have hmul : tx.gas * (min mpf (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas) ≤ tx.gas * maxFee :=
          Nat.mul_le_mul_left _ hegp
        omega
  | three cid mpf maxFee recv al mbf bh =>
    simp only [checkTransactionGasFee, htt, checkTransactionDynamicGasFee] at hfee
    split at hfee
    · cases hfee
    · split at hfee
      · cases hfee
      · rename_i hmp hbf
        have hfe := Except.ok.inj hfee
        simp only [Prod.mk.injEq] at hfe
        obtain ⟨rfl, rfl⟩ := hfe
        simp only [checkTransactionBlobData, htt] at hblob
        split at hblob
        · cases hblob
        · split at hblob
          · cases hblob
          · split at hblob
            · cases hblob
            · rename_i hbfee
              have hbe := Except.ok.inj hblob
              simp only [Prod.mk.injEq] at hbe
              obtain ⟨rfl, rfl⟩ := hbe
              simp only [Tx.isTypeThree, htt, reduceIte]
              have hegp : min mpf (maxFee - benv.stat.baseFeePerGas) +
                  benv.stat.baseFeePerGas ≤ maxFee := by omega
              have hmul : tx.gas * (min mpf (maxFee - benv.stat.baseFeePerGas) +
                  benv.stat.baseFeePerGas) ≤ tx.gas * maxFee :=
                Nat.mul_le_mul_left _ hegp
              have hblobmul : calculate_data_fee benv.stat.excessBlobGas tx ≤
                  calculateTotalBlobGas tx * mbf := by
                unfold calculate_data_fee
                exact Nat.mul_le_mul_left _ (by omega)
              omega
  | four cid mpf maxFee recv al auths =>
    simp only [checkTransactionGasFee, htt, checkTransactionDynamicGasFee] at hfee
    split at hfee
    · cases hfee
    · split at hfee
      · cases hfee
      · rename_i hmp hbf
        have hfe := Except.ok.inj hfee
        simp only [Prod.mk.injEq] at hfe
        obtain ⟨rfl, rfl⟩ := hfe
        simp only [checkTransactionBlobData, htt] at hblob
        have hbe := Except.ok.inj hblob
        simp only [Prod.mk.injEq] at hbe
        obtain ⟨rfl, rfl⟩ := hbe
        simp only [Tx.isTypeThree, htt, Bool.false_eq_true, if_false]
        have hegp : min mpf (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas ≤ maxFee := by omega
        have hmul : tx.gas * (min mpf (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas) ≤ tx.gas * maxFee :=
          Nat.mul_le_mul_left _ hegp
        omega

-- Validation bound: the calldata floor gas cost never exceeds the gas limit.
lemma validateTransaction_floor_le {tx : Tx}
    {intrinsicGas calldataFloorGasCost : Nat}
    (h : validateTransaction tx = .ok ⟨intrinsicGas, calldataFloorGasCost⟩) :
    calldataFloorGasCost ≤ tx.gas := by
  unfold validateTransaction at h
  rcases hic : calculateIntrinsicCost tx with ⟨ig, cdf⟩
  rw [hic] at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i hgas _ _
        have h' := Except.ok.inj h
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        omega

-- One-step wei conservation for `processTransaction`.
lemma processTransaction_sum_le {benv : Benv} {bout bout' : BlockOutput}
    {tx : Tx} {i : Nat} {st : _root_.State}
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩) :
    sum st.bal ≤ sum benv.state.bal := by
  unfold processTransaction at h_run
  rcases of_bind_eq_ok h_run with ⟨bout0, hbout0, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨gasInfo, hval, h_run⟩
  rcases gasInfo with ⟨intrinsicGas, calldataFloorGasCost⟩
  rcases of_bind_eq_ok h_run with ⟨chk, hcheck, h_run⟩
  rcases chk with ⟨sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed⟩
  rcases of_bind_eq_ok h_run with ⟨state1, hsub, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨msg, hprep, h_run⟩
  rcases of_bind_eq_ok h_run with ⟨pmout, hpm, h_run⟩
  rcases pmout with ⟨state2, txOutput⟩
  rcases of_bind_eq_ok h_run with ⟨refundCounter, hrefund, h_run⟩
  simp only [Prod.mk.injEq] at h_run
  rcases h_run with ⟨rfl, rfl⟩
  have hsub_some :
      (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculate_data_fee benv.stat.excessBlobGas tx
          else
            0).toB256 = some state1 := by
    generalize hopt : (benv.state.incrNonce sender).subBal sender
        (tx.gas * effectiveGasPrice +
          if tx.isTypeThree = true then
            calculate_data_fee benv.stat.excessBlobGas tx
          else
            0).toB256 = o at hsub ⊢
    cases o with
    | none => simp [Option.toExcept] at hsub
    | some s => simpa [Option.toExcept] using hsub
  -- the up-front debit does not wrap
  have hfee_lt := checkTransaction_fee_lt hcheck
  have hcdf := validateTransaction_floor_le hval
  -- sum bookkeeping
  have h1 := foldl_destroyAccount_sum_le txOutput.accountsToDelete.toList
    ((state2.addBal sender
        ((tx.gas -
            max (tx.gas - txOutput.gasLeft -
              min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
              calldataFloorGasCost) *
          effectiveGasPrice).toB256).addBal
      benv.stat.coinbase
        (max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost *
          (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256)
  have h2 := State.addBal_growth
    (state2.addBal sender
      ((tx.gas -
          max (tx.gas - txOutput.gasLeft -
            min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
            calldataFloorGasCost) *
        effectiveGasPrice).toB256)
    benv.stat.coinbase
      (max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas)).toB256
  have h3 := State.addBal_growth state2 sender
    ((tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice).toB256
  have h4 : sum state2.bal ≤ sum state1.bal := by
    have h := processMessageCall_sum_le hpm
    rw [prepareMessage_benv hprep] at h
    exact h
  have h5 := State.balSum_subBal hsub_some
  dsimp only [State.BalGrowth, State.balSum] at h2 h3 h5
  rw [State.incrNonce_bal] at h5
  -- credits are bounded by their Nat values
  have h7 := toB256_toNat_le
    ((tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice)
  have h8 := toB256_toNat_le
    (max (tx.gas - txOutput.gasLeft -
        min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
        calldataFloorGasCost *
      (effectiveGasPrice - benv.stat.baseFeePerGas))
  -- the debit is exactly its Nat value
  have h6 := toNat_toB256_of_lt hfee_lt
  -- Nat arithmetic: refund + tip ≤ gas fee
  have hGle : max (tx.gas - txOutput.gasLeft -
      min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
      calldataFloorGasCost ≤ tx.gas := by
    apply max_le _ hcdf
    omega
  have hkey : (tx.gas -
        max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost) *
      effectiveGasPrice +
      max (tx.gas - txOutput.gasLeft -
          min ((tx.gas - txOutput.gasLeft) / 5) refundCounter)
          calldataFloorGasCost *
        (effectiveGasPrice - benv.stat.baseFeePerGas) ≤
      tx.gas * effectiveGasPrice := by
    apply le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _)
    rw [← Nat.add_mul, Nat.sub_add_cancel hGle]
  omega

theorem main
    {txis : List (Nat × Tx)} {benv benv' : Benv}
    {bout bout' : BlockOutput}
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩) :
    sum benv'.state.bal ≤ sum benv.state.bal := by
  induction txis generalizing benv bout with
  | nil =>
    rw [applyTransactions] at h_run
    obtain ⟨hb, hbo⟩ := Prod.mk.inj (Except.ok.inj h_run)
    subst hb; exact le_refl _
  | cons hd tl ih =>
    obtain ⟨i, tx⟩ := hd
    rw [applyTransactions] at h_run
    obtain ⟨⟨st, bout''⟩, h1, h2⟩ := of_bind_eq_ok h_run
    exact le_trans (ih h2) (processTransaction_sum_le h1)
