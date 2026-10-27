import Blanc.Lift.Usdc.ProxyCreation.Transaction
import Blanc.ExecutionNoDelSafeHistory

/-!
# Existing code through the original proxy constructor

The same admitted zero-value constructor preserves every account whose code
is nonempty in its actual transaction prestate. The retained CREATE supplies
the code invariant and excludes a collision with that account. The certified
constructor supplies the empty deletion set through full transaction settlement.
This is transport between the original states, not a historical code observation.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune ExecutionTrace

/-- Existing nonempty code survives the actual registered proxy constructor,
including the debit, CREATE, refund, fee, deletion fold and touched sweep.
The account need not be separately assumed different from the created proxy. -/
theorem constructor_foreign_code_of_transactionTrace
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (receiver : tx.type.receiver? = none)
    (input : tx.data = code.toList) (value : tx.value = 0)
    (clean : trace.messageOut.error = none) {a : Adr}
    (nonempty : (benv.state.getCode a).toList ≠ []) :
    state.getCode a = benv.state.getCode a := by
  have preparedBenv := prepareMessage_benv trace.prepared
  have messageSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [preparedBenv]
    exact hsg
  have entryCode : trace.msg.benv.state.getCode a = benv.state.getCode a := by
    rw [preparedBenv, State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have entryNonempty : (trace.msg.benv.state.getCode a).toList ≠ [] := by
    rw [entryCode]
    exact nonempty
  have target := (transaction_constructor_message trace receiver input value).1
  obtain ⟨installed, ⟨retained⟩, _, collision, _, sameState⟩ :=
    trace.message.exists_clean_create (by rw [target]; rfl) messageSg clean
  have different : trace.msg.currentTarget ≠ a :=
    ne_wa_of_not_hasCodeOrNonce entryNonempty
      (by simpa only [messageCreateCollision] using collision)
  have messageCode : trace.messageState.getCode a = benv.state.getCode a := by
    rw [sameState]
    exact (ProcessCreateMessage.codePreserve
      (Xlot.invGetCode_of_filled retained.retained.toFilled) retained.run a
      different.symm entryNonempty).trans entryCode
  have noDelete : a ∉ trace.messageOut.accountsToDelete := by
    rw [transaction_constructor_deletions trace hsg receiver input value clean]
    exact AdrSet.not_mem_empty
  obtain ⟨refund, _, finalState⟩ := trace.exists_selectedFinalStateForm hsg
  rw [congrArg (fun s => s.getCode a) finalState]
  have preserved (r f : B256) := settled_getCode_getStor_of_code_nonempty
    (rules := benv.stat.rules) (touched := trace.messageOut.touchedAccounts.toList)
    (st := trace.messageState) (s := trace.sender) (c := benv.stat.coinbase)
    (w := a) (dels := trace.messageOut.accountsToDelete.toList) (r := r) (f := f)
    (fun b member equal => noDelete (equal ▸ Std.HashSet.mem_toList.mp member))
    (by rw [messageCode]; exact nonempty)
  exact (preserved _ _).1.trans messageCode

end Blanc.Lift.Usdc.ProxyCreation
