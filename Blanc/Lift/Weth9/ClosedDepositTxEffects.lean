import Blanc.Lift.Weth9.ClosedDepositTxData

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

theorem deposit_settled_stor (st : Jaune.State) :
    (depositSettledState st).getStor contractAddress =
      (st.getStor contractAddress).set (balSlot senderE) 1 := by
  rw [depositSettledState, getStor_addBal, getStor_addBal]
  unfold depositFrameState State.setStorVal State.getStor
  rw [State.get_set_self]
  change ((depositTransferState st).getStor contractAddress).set (balSlot senderE) 1 =
    (st.getStor contractAddress).set (balSlot senderE) 1
  rw [depositTransferState, getStor_addBal]
  change (((depositDebitState st).setBal senderE 899999).get contractAddress).stor.set _ _ = _
  rw [State.setBal_get_stor, depositDebitState, State.setBal_get_stor,
    State.incrNonce_get_stor]
  rfl

theorem deposit_settled_other_stor (st : Jaune.State) (a : Adr)
    (other : contractAddress ≠ a) :
    (depositSettledState st).getStor a = st.getStor a := by
  rw [depositSettledState, getStor_addBal, getStor_addBal]
  unfold depositFrameState State.setStorVal State.getStor
  rw [State.get_set_ne _ other]
  change (depositTransferState st).getStor a = st.getStor a
  rw [depositTransferState, getStor_addBal]
  change (((depositDebitState st).setBal senderE 899999).get a).stor = _
  rw [State.setBal_get_stor, depositDebitState, State.setBal_get_stor,
    State.incrNonce_get_stor]
  rfl

theorem deposit_settled_holder (st : Jaune.State) :
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
      depositDebitState, debit_get_self]
    rfl
  change ((depositFrameState st).get senderE).withBal
    (((depositFrameState st).get senderE).bal + 9924) = _
  rw [frame]
  change { st.get senderE with nonce := (st.get senderE).nonce + 1, bal := (899999 : B256) + 9924 } = _
  have sum : (899999 : B256) + 9924 = 909923 := by decide +kernel
  rw [sum]

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
  rw [addBal_get_self]
  change (((depositDebitState st).setBal senderE 899999).get contractAddress).bal + 1 = 1
  rw [State.setBal_get_ne senderE_ne_contractAddress]
  rw [depositDebitState, debit_get_ne senderE_ne_contractAddress]
  change st.bal contractAddress + 1 = 1
  rw [balance]
  decide +kernel

end Blanc.Lift.Weth9.ClosedInstance
