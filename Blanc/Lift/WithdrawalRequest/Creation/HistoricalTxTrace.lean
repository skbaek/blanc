import Blanc.Lift.WithdrawalRequest.Creation.HistoricalTxRecover
import Blanc.Lift.WithdrawalRequest.Creation.Transaction
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionTransactionGas

/-!
# The EIP-7002 deployment transaction as a retained Cancun transaction trace

On any `TransactionTrace` of the candidate transaction under Cancun rules, checked admission
fixes the sender (the kernel-recovered keyless deployer) and its nonce 0, so preparation
targets `computeContractAddress deployer 0`, the EIP-7002 predeploy address, with the
creation input as code, zero value and `250000 - 61616` gas (`validated_cancun`). Success of
the retained message excludes the collision arm. Together these are exactly the
`CanonicalDeploymentInput` consumed by the deployment-rooted EIP-7002 results; no installed
code, storage or constructor outcome is assumed.
-/

namespace Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx

open Jaune Blanc.ExecutionTrace

theorem intrinsic_cancun (s : Adr) :
    calculateIntrinsicCost Fork.cancun.ruleSet tx s = (61616, 0) := by
  have same : calculateIntrinsicCost Fork.cancun.ruleSet tx s =
      calculateIntrinsicCost Fork.cancun.ruleSet tx 0 := rfl
  rw [same]
  decide +kernel

/-- Cancun validation of the candidate CREATE: intrinsic gas 61,616 and no calldata floor. -/
theorem validated_cancun (s : Adr) :
    validateTransaction Fork.cancun.ruleSet tx s = .ok (61616, 0) := by
  unfold validateTransaction
  rw [intrinsic_cancun]
  decide +kernel

/-- Checked Cancun admission of the candidate transaction: its sender is the kernel-recovered
deployer, and the prepared message's sender nonce, after the debit's increment, is 1. -/
theorem actual_sender {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout') :
    trace.sender = deployer ∧ trace.debitState.getNonce deployer = 1 := by
  have recovery := checkTransaction_sender trace.checked
  rw [recoveredSender] at recovery
  have senderEq : trace.sender = deployer := (Except.ok.inj recovery).symm
  refine ⟨senderEq, ?_⟩
  have nonce := checkTransaction_sender_nonce trace.checked
  change (benv.state.get trace.sender).nonce = 0 at nonce
  rcases State.of_subBal trace.debit with ⟨_, debitEq⟩
  change (trace.debitState.get deployer).nonce = 1
  rw [debitEq, ← senderEq, State.setBal_get_nonce]
  simp only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce, nonce]
  rfl

/-- **The retained Cancun message is the canonical EIP-7002 deployment input.** Sender
recovery, the checked nonce and preparation fix the CREATE target, code, value and gas; the
retained message's success excludes the collision arm. -/
theorem actual_input {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} {index : Nat} (trace : TransactionTrace benv bout tx index state bout')
    (hfork : benv.stat.fork = .cancun) (success : trace.messageOut.error = none) :
    CanonicalDeploymentInput trace.msg := by
  obtain ⟨senderEq, nonce⟩ := actual_sender trace
  have prepared := trace.prepared
  have receiver : tx.type.receiver? = none := rfl
  simp only [prepareMessage, receiver] at prepared
  have same := Except.ok.inj prepared
  have creation : trace.msg.target = none := (congrArg Msg.target same).symm
  have target : trace.msg.currentTarget = withdrawalRequestPredeployAddress := by
    have target := congrArg Msg.currentTarget same
    change computeContractAddress trace.sender
      (trace.debitState.getNonce trace.sender - 1) = trace.msg.currentTarget at target
    rw [senderEq, nonce] at target
    exact target.symm.trans deployer_address
  have world := prepareMessage_benv trace.prepared
  have hsg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [world]
    change benv.stat.fork.ruleSet.stateGas = none
    rw [hfork]
    rfl
  have validation := trace.validation
  change validateTransaction benv.stat.fork.ruleSet tx trace.validationSender = _ at validation
  rw [hfork, validated_cancun] at validation
  have intrinsic := (Prod.mk.inj (Except.ok.inj validation)).1
  refine
    { target := creation
      address := target
      code := ?_
      value := (congrArg Msg.value same).symm
      gas := ?_
      collision := ?_ }
  · have code := (congrArg Msg.code same).symm
    rw [code]
    change ByteArray.mk (Array.mk tx.data) = creationCode
    rw [tx_data, ByteArray.toList_eq_toList_data]
  · rw [trace.msg_gas_noStateGas, ← intrinsic]
    decide
  · cases collision : messageCreateCollision trace.msg with
    | false => rfl
    | true =>
        unfold messageCreateCollision at collision
        have result := trace.message.result
        simp only [processMessageCall, creation, Option.isNone_none, ↓reduceIte,
          processMessageCall.create, hsg, collision] at result
        have error := congrArg (fun result : State × MsgCallOutput => result.2.error)
          (Except.ok.inj result)
        rw [success] at error
        cases error

end Blanc.Lift.WithdrawalRequest.Creation.HistoricalTx
