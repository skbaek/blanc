import Blanc.TransactionForward
import Blanc.ExecutionTransactionEffects

/-! Success projections of the actual transaction checker. These invert the
same checked stages; they do not supply account, fee or capacity assumptions. -/

namespace Blanc

open Jaune

/-- The actual fee/account and gas-limit stages retained by successful admission. -/
theorem checkTransaction_admission_parts {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {price : Nat} {hashes : List B256} {blobGas : Nat}
    (checked : checkTransaction benv bout tx = .ok (sender, price, hashes, blobGas)) :
    ∃ feeBeforeBlob fee,
      checkTransactionGasLimits benv bout tx = .ok blobGas ∧
      checkTransactionGasFee benv tx = .ok (price, feeBeforeBlob) ∧
      checkTransactionBlobData benv tx feeBeforeBlob = .ok (fee, hashes) ∧
      checkTransactionSenderAccountFor benv.stat.rules (benv.state.get sender) tx fee = .ok () := by
  unfold checkTransaction at checked
  obtain ⟨actualBlobGas, gas, checked⟩ := Except.bind_eq_ok checked
  obtain ⟨_, _, checked⟩ := Except.bind_eq_ok checked
  obtain ⟨actualSender, _, checked⟩ := Except.bind_eq_ok checked
  obtain ⟨⟨actualPrice, feeBeforeBlob⟩, feeStage, checked⟩ := Except.bind_eq_ok checked
  obtain ⟨⟨fee, actualHashes⟩, blobStage, checked⟩ := Except.bind_eq_ok checked
  obtain ⟨_, _, checked⟩ := Except.bind_eq_ok checked
  obtain ⟨_, _, checked⟩ := Except.bind_eq_ok checked
  obtain ⟨accountUnit, accountStage, checked⟩ := Except.bind_eq_ok checked
  cases accountUnit
  have same := Except.ok.inj checked
  rcases Prod.mk.inj same with ⟨rfl, restSame⟩
  rcases Prod.mk.inj restSame with ⟨rfl, tailSame⟩
  rcases Prod.mk.inj tailSame with ⟨rfl, rfl⟩
  exact ⟨feeBeforeBlob, fee, Except.mapError_eq_ok_iff.mp gas,
    Except.mapError_eq_ok_iff.mp feeStage, Except.mapError_eq_ok_iff.mp blobStage,
    Except.mapError_eq_ok_iff.mp accountStage⟩

/-- Historical disabled-delegation admission forces an empty sender code. -/
theorem checkTransactionSenderAccountFor_code_empty {rules : ForkRules}
    {account : Acct} {tx : Tx} {fee : Nat}
    (disabled : rules.delegationEnabled = false)
    (checked : checkTransactionSenderAccountFor rules account tx fee = .ok ()) :
    account.code.isEmpty = true := by
  unfold checkTransactionSenderAccountFor at checked
  obtain ⟨codeUnit, _, codeStage⟩ := Except.bind_eq_ok checked
  cases codeUnit
  rw [checkTransactionSenderCodeFor_disabled disabled] at codeStage
  split at codeStage
  · assumption
  · cases codeStage

/-- The checked sender's actual balance covers the admitted maximum fee and value. -/
theorem checkTransactionSenderAccountFor_funds {rules : ForkRules}
    {account : Acct} {tx : Tx} {fee : Nat}
    (checked : checkTransactionSenderAccountFor rules account tx fee = .ok ()) :
    fee + tx.value ≤ account.bal.toNat := by
  unfold checkTransactionSenderAccountFor at checked
  obtain ⟨_, accountStage, _⟩ := Except.bind_eq_ok checked
  unfold checkTransactionSenderAccount at accountStage
  split at accountStage
  · cases accountStage
  · split at accountStage
    · cases accountStage
    · split at accountStage
      · cases accountStage
      · rename_i enough
        exact Nat.le_of_not_gt enough

/-- Without state gas, the actual checker reserves the transaction's full gas. -/
theorem checkTransactionGasLimits_room {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {blobGas : Nat} (noStateGas : benv.stat.rules.stateGas = none)
    (checked : checkTransactionGasLimits benv bout tx = .ok blobGas) :
    tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed := by
  simp only [checkTransactionGasLimits, noStateGas] at checked
  split at checked
  · cases checked
  · rename_i enough
    exact Nat.le_of_not_gt enough

end Blanc
