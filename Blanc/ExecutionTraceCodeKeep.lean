import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTransactionEffects

/-!
# Nonempty code along transactions

`Blanc/ExecutionTraceCodeAt.lean` carries the code at `a` through message calls, but through a
whole transaction only when it is empty, because a transaction ends by destroying the accounts its
frames self-destructed and destroying an account with code would change it.  An account whose code
is nonempty and not an EIP-7702 delegation designator, in a block that has not created it, is never
among the accounts a transaction destroys (`processMessageCall_accountsToDelete_ne`), so its code
survives the transaction as well.  The primary forms take the schedule facts as explicit
hypotheses (`stateGas = none`, the EIP-6780 flag, refund quotient, no touched sweep) and so serve
historical (`In`) callers; the `CoveredFork` forms are one-line specializations.
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

/-- Exact post-message transaction settlement form, without coverage: the
schedule facts enter as explicit hypotheses (covered form
`TransactionTrace.exists_finalStateForm`). -/
theorem TransactionTrace.exists_finalStateForm_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false) :
    ∃ refundCounter : Nat,
      Int.toNat? trace.messageOut.refundCounter = some refundCounter ∧
      state =
        trace.messageOut.accountsToDelete.toList.foldl destroyAccount
          ((trace.messageState.addBal trace.sender
              ((tx.gas -
                  max (tx.gas - trace.messageOut.gasLeft -
                    min ((tx.gas - trace.messageOut.gasLeft) / 5)
                      refundCounter)
                    trace.calldataFloorGasCost) *
                trace.effectiveGasPrice).toB256).addBal
            benv.stat.coinbase
              (max (tx.gas - trace.messageOut.gasLeft -
                  min ((tx.gas - trace.messageOut.gasLeft) / 5)
                    refundCounter)
                  trace.calldataFloorGasCost *
                (trace.effectiveGasPrice -
                  benv.stat.baseFeePerGas)).toB256) := by
  rcases trace.exists_selectedFinalStateForm hsg with
    ⟨refundCounter, hrc, hfinal⟩
  have hrefund' : benv.stat.rules.settle.refundQuotient = 5 := by
    simpa only [BenvStat.rules] using hrefund
  have hsweep' : benv.stat.rules.settle.touchedSweep = false := by
    simpa only [BenvStat.rules] using hsweep
  refine ⟨refundCounter, hrc, ?_⟩
  simpa only [settleTransactionGas, sweepTouchedAccounts, hsg,
    hrefund', hsweep', Bool.false_eq_true, ↓reduceIte] using hfinal

/-- **A transaction keeps nonempty, non-delegating code at `a`, and so does
every frame it enters**, when no frame it enters targets `a`, `a` was not
created in the block, and either delegation is disabled or none of its
authorizations recovers to `a`. -/
theorem TransactionTrace.codeAt_keep_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (hflag : benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false) {a : Adr}
    (hdis : benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
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
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [hbenv]
    exact hsg
  have hmsgFlag :
      trace.msg.benv.stat.rules.settle.selfdestructOnlyCreated = true := by
    rw [hbenv]
    exact hflag
  have hdis_msg : trace.msg.benv.stat.rules.delegationEnabled = false ∨
      ∀ auth ∈ trace.msg.tenv.stat.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a := by
    rcases hdis with hdis | hauth
    · exact Or.inl (by rw [hbenv]; exact hdis)
    · exact Or.inr (by
        rw [htenv]
        simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using
          hauth)
  obtain ⟨hpost, hroots⟩ := trace.message.codeAt_noStateGas hmsgSg hca hdis_msg
    avoid
  refine ⟨fun root member => (hroots root member).trans hmsgState, ?_⟩
  obtain ⟨refundCounter, -, hfinal⟩ :=
    trace.exists_finalStateForm_noStateGas hsg hrefund hsweep
  have hnodel : Msg.NoDel a trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hne
  have hndMsg : ¬ isValidDelegation (trace.msg.benv.state.getCode a) := by
    rw [hmsgState]
    exact hnd
  have inherited : a ∉ trace.msg.inheritedDeletions :=
    trace.not_mem_msg_inheritedDeletions a
  have hnotDel := processMessageCall_accountsToDelete_ne_noStateGas hmsgSg
    hmsgFlag trace.message.result hnodel hndMsg inherited
  rw [hfinal]
  rw [foldl_destroyAccount_getCode_ne _ hnotDel]
  rw [State.addBal_getCode, State.addBal_getCode]
  exact hpost.trans hmsgState

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
      state.getCode a = benv.state.getCode a :=
  trace.codeAt_keep_noStateGas hfork.rules_stateGas_none hfork.rules_selfdestructOnlyCreated
    hfork.rules_refundQuotient hfork.rules_touchedSweep (Or.inr hauth) avoid hne hnd notCreated

/-- **A transaction list keeps nonempty, non-delegating code at `a`.** -/
theorem ApplyTransactionsTrace.codeAt_keep_noStateGas
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (hflag : benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false) {a : Adr}
    (hdis : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
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
      have hdis_head : benv.stat.rules.delegationEnabled = false ∨
          ∀ auth ∈ tx.auths, ∀ authority, recoverAuthority auth = .ok authority →
            authority ≠ a := by
        rcases hdis with hdis | hdis
        · exact Or.inl hdis
        · exact Or.inr (hdis _ (List.mem_cons_self ..))
      obtain ⟨-, hstate⟩ := head.codeAt_keep_noStateGas hsg hflag hrefund hsweep
        hdis_head
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inl member)) hne hnd notCreated
      have hcode : (benv.withState txState).state.getCode a = benv.state.getCode a :=
        hstate
      have hdis_tail :
          (benv.withState txState).stat.rules.delegationEnabled = false ∨
            ∀ p ∈ txs, ∀ auth ∈ p.2.auths, ∀ authority,
              recoverAuthority auth = .ok authority → authority ≠ a := by
        rcases hdis with hdis | hdis
        · exact Or.inl hdis
        · exact Or.inr (fun p hp => hdis p (List.mem_cons_of_mem _ hp))
      have := ih hsg hflag hrefund hsweep hdis_tail
        (fun root member => avoid root (by
          simp only [ApplyTransactionsTrace.rawFrames, List.mem_append]
          exact Or.inr member))
        (by rw [hcode]; exact hne) (by rw [hcode]; exact hnd) notCreated
      exact this.trans hcode

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
    finalBenv.state.getCode a = benv.state.getCode a :=
  trace.codeAt_keep_noStateGas hfork.rules_stateGas_none hfork.rules_selfdestructOnlyCreated
    hfork.rules_refundQuotient hfork.rules_touchedSweep (Or.inr hauth) avoid hne hnd notCreated

end ExecutionTrace

end Blanc
