import Blanc.ExecutionAccountingAdmission
import Blanc.TransactionForward

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

end Blanc.ExecutionTrace
