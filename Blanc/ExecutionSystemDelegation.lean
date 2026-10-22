import Blanc.ExecutionDelegationEligibility

/-!
# Empty authorization phase of canonical system messages

Canonical system preparation supplies no authorization tuples. These laws
identify only that wrapper phase; system VM execution, child calls, recovery
queries and storage effects remain governed by their actual retained traces.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- An empty actual authorization list needs no cryptographic exclusion. -/
theorem MessageCallDelegationTrace.noEligibleAuthorityAt_of_auths_nil
    {msg delegated : Msg} {refund : Nat}
    (trace : MessageCallDelegationTrace msg delegated refund)
    (auths : msg.tenv.stat.auths = []) (a : Adr) :
    trace.NoEligibleAuthorityAt a := by
  apply trace.excluded_of_all
  intro auth member
  rw [auths] at member
  cases member

/-- This is Jaune's canonical system preparation, not a supplied empty list. -/
theorem systemTransactionMessage_auths_nil (benv : Benv) (target : Adr) (data : Bytes) :
    (systemTransactionMessage benv target data).tenv.stat.auths = [] := by
  rfl

/-- The actual authorization wrapper takes its skipped arm, for any rules. -/
def systemTransactionDelegationTrace (benv : Benv) (target : Adr) (data : Bytes) :
    MessageCallDelegationTrace (systemTransactionMessage benv target data)
      (systemTransactionMessage benv target data) 0 :=
  .skipped (by
    rw [systemTransactionMessage_auths_nil]
    exact Bool.or_true _)

/-- Skipping authorization preserves the exact canonical message and refund. -/
theorem systemTransactionMessage_delegation_eq (benv : Benv) (target : Adr) (data : Bytes) :
    messageCallDelegation (systemTransactionMessage benv target data) =
      .ok (systemTransactionMessage benv target data, 0) := by
  exact (systemTransactionDelegationTrace benv target data).result

/-- The retained system wrapper is an actual call arm with no authorization
phase. Its VM trace and outcome are not restricted by this statement. -/
theorem SystemMessageTrace.delegation_empty
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (a : Adr) :
    match trace.message with
    | .createCollision .. => False
    | .createRun .. => False
    | .callRun _ delegated refund _ _ _ _ _ _ _ =>
        delegated = systemTransactionMessage benv target data ∧ refund = 0 ∧
          ∀ phase : MessageCallDelegationTrace
              (systemTransactionMessage benv target data) delegated refund,
            phase.NoEligibleAuthorityAt a := by
  cases trace.message with
  | createCollision target =>
      simp only [systemTransactionMessage, processSystemTransactionMsg,
        Option.isNone_some, Bool.false_eq_true] at target
  | createRun target =>
      simp only [systemTransactionMessage, processSystemTransactionMsg,
        Option.isNone_some, Bool.false_eq_true] at target
  | callRun _ delegated refund run =>
      have same := Except.ok.inj
        (run.symm.trans (systemTransactionMessage_delegation_eq benv target data))
      exact ⟨(Prod.mk.inj same).1, (Prod.mk.inj same).2, fun phase =>
        phase.noEligibleAuthorityAt_of_auths_nil
          (systemTransactionMessage_auths_nil benv target data) a⟩

end Blanc.ExecutionTrace
