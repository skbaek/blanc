import Blanc.ExecutionAccountingAdmission
import Blanc.TransactionForward
import Blanc.ExecutionTraceCreateResult

/-!
# Recovering an untouched account from a transaction's actual debit state

A zero nonce after the admitted sender's nonce increment excludes that sender.
The same trace's debit equation then recovers the entire original account.
-/
namespace Blanc.ExecutionTrace

open Jaune

/-- A zero nonce in the actual debit state excludes the admitted sender and
identifies the target's complete account with its pre-debit account. -/
theorem TransactionTrace.account_eq_of_debit_nonce_zero
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {target : Adr}
    (trace : TransactionTrace benv bout tx index state bout')
    (zero : (trace.debitState.get target).nonce = 0) :
    trace.sender ≠ target ∧ trace.debitState.get target = benv.state.get target := by
  have nonzero := trace.msg_caller_nonce_ne_zero
  rw [trace.msg_caller, prepareMessage_benv trace.prepared] at nonzero
  change (trace.debitState.get trace.sender).nonce ≠ 0 at nonzero
  have different : trace.sender ≠ target := by
    intro equal
    exact nonzero (equal ▸ zero)
  refine ⟨different, ?_⟩
  rcases State.of_subBal trace.debit with ⟨_, debitEq⟩
  rw [debitEq]
  exact debit_get_ne different

/-- The actual up-front debit proves gas funding when there is no blob fee.
No balance observation or sender-account assumption is needed. -/
theorem TransactionTrace.gas_funds_of_no_blob_fee
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (noBlobFee : transactionBlobGasFee benv tx = 0) :
    (tx.gas * trace.effectiveGasPrice).toB256 ≤ benv.state.bal trace.sender := by
  simpa only [noBlobFee, Nat.add_zero, State.incrNonce_bal] using
    (State.of_subBal trace.debit).1

/-- A successful creation message excludes a collision in the original
pre-debit state as well. The admitted sender's increment rules out aliasing
with the zero-nonce target, so its complete account survives the debit. -/
theorem TransactionTrace.creation_entry_of_clean
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (target : trace.msg.target.isNone = true)
    (hsg : benv.stat.rules.stateGas = none)
    (clean : trace.messageOut.error = none) :
    trace.sender ≠ trace.msg.currentTarget ∧
      accountHasCodeOrNonce benv.state trace.msg.currentTarget = false := by
  obtain ⟨_, _, _, collision, _, _⟩ := trace.message.exists_clean_create target
    (by rw [prepareMessage_benv trace.prepared]; exact hsg) clean
  have unprotected := messageCreateCollision_false_target_unprotected collision
  rw [prepareMessage_benv trace.prepared] at unprotected
  change ¬ State.Protected trace.debitState trace.msg.currentTarget at unprotected
  have zero : (trace.debitState.get trace.msg.currentTarget).nonce = 0 :=
    not_ne_iff.mp (fun nonzero => unprotected (Or.inl nonzero))
  obtain ⟨different, account⟩ := trace.account_eq_of_debit_nonce_zero zero
  refine ⟨different, ?_⟩
  change accountHasCodeOrNonce trace.msg.benv.state trace.msg.currentTarget = false at collision
  rw [prepareMessage_benv trace.prepared] at collision
  change accountHasCodeOrNonce trace.debitState trace.msg.currentTarget = false at collision
  unfold accountHasCodeOrNonce State.getNonce State.getCode at collision ⊢
  rw [← account]
  exact collision

end Blanc.ExecutionTrace
