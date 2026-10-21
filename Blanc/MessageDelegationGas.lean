import Blanc.ExecutionTrace

/-! # Gas preservation through the EIP-7702 delegation prefix

Its own small module so that the widely imported `Blanc/LadderBase.lean` need not import
`Blanc.ExecutionTrace`. -/

namespace Blanc

open Jaune

/-! ### Delegation-prefix gas preservation

An EIP-7702 authorization never changes the message's grant. One public copy
lives here (the `setDelegation*_fields` lemmas over the same functions are in `Blanc/LadderBase.lean`);
`Blanc/ExecutionMessageGas.lean` and `Blanc/Lift/HistoryGas.lean` use these
instead of their own private copies. -/

/-- An EIP-7702 authorization step never changes the message's grant. -/
theorem setDelegationStep_gas {auth : Auth} {msg : Msg} {rc : B256}
    {p : Msg × B256} (run : setDelegationStep auth msg rc = .ok p) :
    p.1.gas = msg.gas := by
  unfold setDelegationStep at run
  split at run
  · cases run; rfl
  · split at run
    · cases run; rfl
    · cases recovered : recoverAuthority auth with
      | error error =>
        cases error <;> simp only [recovered] at run
        all_goals cases run
        rfl
      | ok authority =>
        simp only [recovered] at run
        split at run
        · cases run; rfl
        · split at run
          · cases run; rfl
          · cases run; rfl

/-- Every authorization step of the loop keeps the grant. -/
theorem setDelegationLoop_gas :
    ∀ (auths : List Auth) {msg : Msg} {rc : B256} {p : Msg × B256},
      setDelegationLoop auths msg rc = .ok p → p.1.gas = msg.gas
  | [], _, _, _, run => by cases run; rfl
  | _ :: _, _, _, _, run => by
      unfold setDelegationLoop at run
      obtain ⟨next, step, rest⟩ := Except.bind_eq_ok run
      exact (setDelegationLoop_gas _ rest).trans (setDelegationStep_gas step)

/-- The delegation prefix hands the call its original grant. -/
theorem setDelegation_gas {msg : Msg} {p : Msg × B256}
    (run : setDelegation msg = .ok p) : p.1.gas = msg.gas := by
  unfold setDelegation at run
  obtain ⟨next, loop, run⟩ := Except.bind_eq_ok run
  have gas := setDelegationLoop_gas _ loop
  cases codeAddress : next.1.codeAddress with
  | none =>
    simp only [codeAddress] at run
    cases run
  | some address =>
    simp only [codeAddress] at run
    cases run
    exact gas

/-- A delegated message call runs under the original grant. -/
theorem messageCallDelegation_gas {msg delegated : Msg} {refund : Nat}
    (run : ExecutionTrace.messageCallDelegation msg = .ok (delegated, refund)) :
    delegated.gas = msg.gas := by
  unfold ExecutionTrace.messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · cases run
    rfl
  · obtain ⟨next, set, rest⟩ := Except.bind_eq_ok run
    cases rest
    exact setDelegation_gas set

end Blanc
