import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTransactionEffects

/-!
# Nonempty code along transactions

`Blanc/ExecutionTraceCodeAt.lean` carries the code at `a` through message calls, but through a
whole transaction only when it is empty, because a transaction ends by destroying the accounts its
frames self-destructed and destroying an account with code would change it.  An account whose code
is nonempty and not an EIP-7702 delegation designator, in a block that has not created it, is never
among the accounts a transaction destroys (`processMessageCall_accountsToDelete_ne`), so its code
survives the transaction as well.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Destroying an account other than `a` leaves the code at `a`. -/
theorem destroyAccount_getCode_ne {w : State} {x a : Adr} (h : x ≠ a) :
    (destroyAccount w x).getCode a = w.getCode a := by
  unfold destroyAccount State.getCode State.get
  rw [Std.TreeMap.getD_erase]
  split
  · rename_i heq
    exact absurd (Std.compare_eq_iff_eq.mp heq) h
  · rfl

theorem foldl_destroyAccount_getCode_ne {a : Adr} :
    ∀ (xs : List Adr) {w : State}, (∀ x ∈ xs, x ≠ a) →
      (xs.foldl destroyAccount w).getCode a = w.getCode a := by
  intro xs
  induction xs with
  | nil => intros; rfl
  | cons x xs ih =>
      intro w h
      simp only [List.foldl_cons]
      rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy)),
        destroyAccount_getCode_ne (h x (List.mem_cons_self ..))]

/-- **A transaction keeps nonempty, non-delegating code at `a`, and so does every frame it
enters**, when no frame it enters targets `a`, none of its authorizations recovers to `a`, and `a`
was not created in the block. -/
theorem TransactionTrace.codeAt_keep
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (hauth : ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
      authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hne : (benv.state.getCode a).toList ≠ [])
    (hnd : ¬ isValidDelegation (benv.state.getCode a))
    (notCreated : a ∉ benv.createdAccounts) :
    (∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a) ∧
      state.getCode a = benv.state.getCode a := by
  have hbenv := prepareMessage_benv trace.prepared
  obtain ⟨htenv, hca⟩ := prepareMessage_fields trace.prepared
  have hdebit : trace.debitState.getCode a = benv.state.getCode a := by
    have h1 := State.subBal_getCode trace.debit (a := a)
    rw [h1]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode a = benv.state.getCode a := by
    rw [hbenv]
    exact hdebit
  have hmsgFork : CoveredFork trace.msg.benv.stat.fork := by
    rw [hbenv]
    exact hfork
  have hmsgAuth : ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a := by
    rw [htenv]
    simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using hauth
  obtain ⟨hpost, hroots⟩ := trace.message.codeAt hmsgFork hca hmsgAuth avoid
  refine ⟨fun root member => (hroots root member).trans hmsgState, ?_⟩
  obtain ⟨refundCounter, -, hfinal⟩ := trace.exists_finalStateForm hfork
  have hnodel : Msg.NoDel a trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hne
  have hndMsg : ¬ isValidDelegation (trace.msg.benv.state.getCode a) := by
    rw [hmsgState]
    exact hnd
  have hnotDel := processMessageCall_accountsToDelete_ne hmsgFork trace.message.result
    hnodel hndMsg
  rw [hfinal]
  rw [foldl_destroyAccount_getCode_ne _ hnotDel]
  rw [State.addBal_getCode, State.addBal_getCode]
  exact hpost.trans hmsgState

theorem ApplyTransactionsTrace.codeAt_keep
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (hauth : ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hne : (benv.state.getCode a).toList ≠ [])
    (hnd : ¬ isValidDelegation (benv.state.getCode a))
    (notCreated : a ∉ benv.createdAccounts) :
    finalBenv.state.getCode a = benv.state.getCode a := by
  induction trace with
  | nil => rfl
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      obtain ⟨-, hstate⟩ := head.codeAt_keep hfork
        (hauth _ (List.mem_cons_self ..))
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inl member)) hne hnd notCreated
      have hcode : (benv.withState txState).state.getCode a = benv.state.getCode a := hstate
      have := ih hfork
        (fun p hp => hauth p (List.mem_cons_of_mem _ hp))
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inr member))
        (by rw [hcode]; exact hne) (by rw [hcode]; exact hnd) notCreated
      exact this.trans hcode

end ExecutionTrace

end Blanc
