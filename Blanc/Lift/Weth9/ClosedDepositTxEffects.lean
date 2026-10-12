import Blanc.Lift.Weth9.ClosedDepositTxData
import Blanc.Lift.Weth9.RepinBridge

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.Lift

theorem senderE_ne_contractAddress : senderE ≠ contractAddress := by decide +kernel
theorem senderE_ne_zero : senderE ≠ 0 := by decide +kernel
theorem contractAddress_ne_zero : contractAddress ≠ 0 := by decide +kernel

theorem deposit_settled_code (st : Jaune.State) (a : Adr) :
    (depositSettledState st).getCode a = st.getCode a := by
  rw [depositSettledState, State.addBal_getCode, State.addBal_getCode]
  unfold depositFrameState State.setStorVal State.getCode
  by_cases same : contractAddress = a
  · subst a
    rw [State.get_set_self]
    change (depositTransferState st).getCode contractAddress = st.getCode contractAddress
    rw [depositTransferState, State.addBal_getCode, State.setBal_getCode,
      depositDebitState, State.setBal_getCode]
    exact State.incrNonce_get_code
  · rw [State.get_set_ne _ same]
    change (depositTransferState st).getCode a = st.getCode a
    rw [depositTransferState, State.addBal_getCode, State.setBal_getCode,
      depositDebitState, State.setBal_getCode]
    exact State.incrNonce_get_code

/-- The settled deposit writes the contract's balance slot and keeps the rest of its storage, provided
the contract carries code (so no balance write normalizes it; cause SA). -/
theorem deposit_settled_stor (st : Jaune.State)
    (hcode : (st.get contractAddress).code.size ≠ 0) :
    (depositSettledState st).getStor contractAddress =
      (st.getStor contractAddress).set (balSlot senderE) 1 := by
  rw [depositSettledState, getStor_addBal, if_neg (fun h => contractAddress_ne_zero h.1.symm),
    getStor_addBal, if_neg (fun h => senderE_ne_contractAddress h.1)]
  unfold depositFrameState State.setStorVal State.getStor
  rw [State.get_set_self]
  change ((depositTransferState st).getStor contractAddress).set (balSlot senderE) 1 =
    (st.getStor contractAddress).set (balSlot senderE) 1
  have hmid : ((depositDebitState st).setBal senderE 899999).get contractAddress =
      st.get contractAddress := by
    rw [State.setBal_get_ne senderE_ne_contractAddress, depositDebitState,
      debit_get_ne senderE_ne_contractAddress]
  rw [depositTransferState, getStor_addBal, if_neg]
  · change (((depositDebitState st).setBal senderE 899999).get contractAddress).stor.set _ _ = _
    rw [hmid]
    rfl
  · rintro ⟨-, hE⟩
    apply hcode
    have h1 := hE.1
    change (((depositDebitState st).setBal senderE 899999).get contractAddress).code.size = 0 at h1
    rwa [hmid] at h1

/-- The settled deposit keeps every other account's storage, provided the sender's nonce does not wrap
and the coinbase's fee credit does not wrap (cause SA: a wrap could empty and normalize either). -/
theorem deposit_settled_other_stor (st : Jaune.State) (a : Adr)
    (other : contractAddress ≠ a) (hnonce : (st.get senderE).nonce ≠ UInt64.max)
    (hcb : B256.Nof (st.get 0).bal 45038) :
    (depositSettledState st).getStor a = st.getStor a := by
  rw [depositSettledState, getStor_addBal]
  by_cases h0 : (0 : Adr) = a
  · subst a
    rw [if_neg, getStor_addBal, if_neg (fun h => senderE_ne_zero h.1)]
    · unfold depositFrameState State.setStorVal State.getStor
      rw [State.get_set_ne _ other]
      change (depositTransferState st).getStor 0 = st.getStor 0
      rw [depositTransferState, getStor_addBal, if_neg (fun h => contractAddress_ne_zero h.1)]
      change (((depositDebitState st).setBal senderE 899999).get 0).stor = _
      rw [State.setBal_get_ne senderE_ne_zero, depositDebitState, debit_get_ne senderE_ne_zero]
      rfl
    · rintro ⟨-, hE⟩
      have hb : ((depositFrameState st).addBal senderE 9924).bal 0 = (st.get 0).bal := by
        change (((depositFrameState st).addBal senderE 9924).get 0).bal = _
        rw [addBal_get_ne _ senderE_ne_zero]
        unfold depositFrameState State.setStorVal
        rw [State.get_set_ne _ contractAddress_ne_zero]
        unfold depositTransferState
        rw [addBal_get_ne _ contractAddress_ne_zero, State.setBal_get_ne senderE_ne_zero,
          depositDebitState, debit_get_ne senderE_ne_zero]
      have hz := hE.2.2
      change ((depositFrameState st).addBal senderE 9924).bal 0 + 45038 = 0 at hz
      rw [hb] at hz
      have hn := B256.toNat_add_eq_of_nof _ _ hcb
      rw [hz, B256.toNat_zero] at hn
      have : (45038 : B256).toNat = 45038 := rfl
      omega
  rw [if_neg (fun h => h0 h.1), getStor_addBal]
  by_cases hE : senderE = a
  · subst a
    rw [if_neg]
    · unfold depositFrameState State.setStorVal State.getStor
      rw [State.get_set_ne _ other]
      change (depositTransferState st).getStor senderE = st.getStor senderE
      rw [depositTransferState, getStor_addBal, if_neg (fun h => other h.1)]
      change (((depositDebitState st).setBal senderE 899999).get senderE).stor = _
      rw [State.setBal_get_self, depositDebitState, debit_get_self hnonce,
        Acct.clearIfEmpty_of_not_empty]
      · rfl
      · rintro ⟨-, -, hz⟩
        have ne : (899999 : B256) ≠ 0 := by decide +kernel
        exact ne hz
    · rintro ⟨-, hz⟩
      have hb : ((depositFrameState st).get senderE).bal = 899999 := by
        unfold depositFrameState State.setStorVal
        rw [State.get_set_ne _ senderE_ne_contractAddress.symm]
        unfold depositTransferState
        rw [addBal_get_ne _ senderE_ne_contractAddress.symm, State.setBal_get_self,
          Acct.clearIfEmpty_bal]
        rfl
      have hz' := hz.2.2
      change ((depositFrameState st).get senderE).bal + 9924 = 0 at hz'
      rw [hb] at hz'
      have ne : (899999 : B256) + 9924 ≠ 0 := by decide +kernel
      exact ne hz'
  · rw [if_neg (fun h => hE h.1)]
    unfold depositFrameState State.setStorVal State.getStor
    rw [State.get_set_ne _ other]
    change (depositTransferState st).getStor a = st.getStor a
    rw [depositTransferState, getStor_addBal, if_neg (fun h => other h.1)]
    change (((depositDebitState st).setBal senderE 899999).get a).stor = _
    rw [State.setBal_get_ne hE, depositDebitState, debit_get_ne hE]
    rfl

/-- The holder after the settled deposit: nonce advanced, `909923` ether (its nonce must not wrap, since the
debit would otherwise normalize it; cause SA). -/
theorem deposit_settled_holder (st : Jaune.State) (hnonce : (st.get senderE).nonce ≠ UInt64.max) :
    (depositSettledState st).get senderE =
      { st.get senderE with nonce := (st.get senderE).nonce + 1, bal := 909923 } := by
  unfold depositSettledState
  rw [addBal_get_ne _ senderE_ne_zero.symm, addBal_get_self]
  have frame : (depositFrameState st).get senderE =
      { st.get senderE with nonce := (st.get senderE).nonce + 1, bal := 899999 } := by
    unfold depositFrameState State.setStorVal
    rw [State.get_set_ne _ senderE_ne_contractAddress.symm]
    unfold depositTransferState
    rw [addBal_get_ne _ senderE_ne_contractAddress.symm, State.setBal_get_self,
      depositDebitState, debit_get_self hnonce]
    rw [Acct.clearIfEmpty_of_not_empty]
    · rfl
    · rintro ⟨-, -, hz⟩
      have ne : (899999 : B256) ≠ 0 := by decide +kernel
      exact ne hz
  change (((depositFrameState st).get senderE).withBal
    (((depositFrameState st).get senderE).bal + 9924)).clearIfEmpty = _
  rw [frame]
  have sum : (899999 : B256) + 9924 = 909923 := by decide +kernel
  rw [Acct.clearIfEmpty_of_not_empty]
  · change { st.get senderE with nonce := (st.get senderE).nonce + 1, bal := (899999 : B256) + 9924 } = _
    rw [sum]
  · rintro ⟨-, -, hz⟩
    have ne : (899999 : B256) + 9924 ≠ 0 := by decide +kernel
    exact ne hz

theorem deposit_settled_contract_balance (st : Jaune.State)
    (balance : st.bal contractAddress = 0) :
    (depositSettledState st).bal contractAddress = 1 := by
  change ((depositSettledState st).get contractAddress).bal = 1
  unfold depositSettledState
  rw [addBal_get_ne _ contractAddress_ne_zero.symm,
    addBal_get_ne _ senderE_ne_contractAddress]
  unfold depositFrameState State.setStorVal
  rw [State.get_set_self]
  change ((depositTransferState st).get contractAddress).bal = 1
  unfold depositTransferState
  rw [addBal_get_self, Acct.clearIfEmpty_bal]
  change (((depositDebitState st).setBal senderE 899999).get contractAddress).bal + 1 = 1
  rw [State.setBal_get_ne senderE_ne_contractAddress]
  rw [depositDebitState, debit_get_ne senderE_ne_contractAddress]
  change st.bal contractAddress + 1 = 1
  rw [balance]
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
