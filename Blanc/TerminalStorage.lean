import Blanc.CommonProofs

/-!
# Storage at successful terminal steps

Balance updates may erase an unprotected account's storage when they clear an
empty account. A terminal instruction therefore preserves each storage map or
replaces it with the empty map. Transaction settlement is a separate boundary.
-/

namespace Blanc

open Jaune

private def ErasesOnly (pre post : Devm) : Prop :=
  ∀ a, post.getStor a = pre.getStor a ∨ post.getStor a = .empty

private theorem ErasesOnly.of_eq {pre post : Devm}
    (storage : post.getStor = pre.getStor) : ErasesOnly pre post :=
  fun a => Or.inl (congrFun storage a)

private theorem ErasesOnly.trans {pre mid post : Devm}
    (first : ErasesOnly pre mid) (second : ErasesOnly mid post) : ErasesOnly pre post := by
  intro a
  rcases second a with same | empty
  · rcases first a with original | erased
    · exact Or.inl (same.trans original)
    · exact Or.inr (same.trans erased)
  · exact Or.inr empty

private theorem setBal_erasesOnly (d : Devm) (owner : Adr) (value : B256) :
    ErasesOnly d (d.setBal owner value) := by
  intro a
  change ((d.state.setBal owner value).get a).stor = (d.state.get a).stor ∨
    ((d.state.setBal owner value).get a).stor = .empty
  rw [State.setBal_get_stor]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem addBal_erasesOnly (d : Devm) (owner : Adr) (value : B256) :
    ErasesOnly d (d.addBal owner value) :=
  setBal_erasesOnly d owner _

private theorem subBal_erasesOnly {d d' : Devm} {owner : Adr} {value : B256}
    (debit : d.subBal owner value = some d') : ErasesOnly d d' := by
  unfold Devm.subBal at debit
  obtain ⟨state, changed, output⟩ := Jaune.of_bind_eq_some debit
  obtain ⟨_, rfl⟩ := State.of_subBal changed
  cases output
  exact setBal_erasesOnly d owner _

private theorem creditBeneficiary_erasesOnly (rules : ForkRules) (d : Devm)
    (owner : Adr) (value : B256) : ErasesOnly d (d.creditBeneficiary rules owner value) := by
  unfold Devm.creditBeneficiary
  split
  · exact addBal_erasesOnly d owner value
  · apply ErasesOnly.of_eq
    funext a
    change ((d.state.setPresent owner
      ((d.state.get owner).withBal (d.state.bal owner + value))).get a).stor =
      (d.state.get a).stor
    by_cases same : owner = a
    · subst a
      rw [State.get_setPresent_self]
      rfl
    · rw [State.get_setPresent_ne _ same]

/-- Actual SELFDESTRUCT may clear an empty account through balance writes, but
it cannot replace any account's storage with a nonempty different map. This
holds in both state-gas lanes without a fork or account-protection premise. -/
theorem Linst.selfdestruct_getStor_eq_or_empty {sevm : Sevm} {pre post : Devm}
    (run : Linst.Run sevm pre .selfdestruct (.ok post)) :
    ∀ a, post.getStor a = pre.getStor a ∨ post.getStor a = .empty := by
  dsimp only [Linst.Run, Linst.run, Except.bind_ok, ne_eq, ite_not,
    Lean.Elab.WF.paramLet, Devm.balReadAccount_accessedAddresses,
    Devm.balReadAccount_getAcct] at run
  cases lane : sevm.benvStat.rules.stateGas with
  | none =>
      simp only [lane] at run
      obtain ⟨⟨donee, popped⟩, pop, run⟩ := Except.bind_eq_ok run
      dsimp only [Except.bind_ok] at run
      obtain ⟨charged, charge, run⟩ := Except.bind_eq_ok run
      obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
      obtain ⟨debited, debit, run⟩ := Except.bind_eq_ok run
      have accessStorage :
          (match sevm.benvStat.rules.access with
          | .eip2929 =>
              if donee ∉ popped.accessedAddresses then
                (addAccessedAddress
                  ((popped.balReadAccount sevm.benvStat.rules donee).balReadAccount
                    sevm.benvStat.rules sevm.currentTarget) donee,
                  gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess)
              else
                ((popped.balReadAccount sevm.benvStat.rules donee).balReadAccount
                  sevm.benvStat.rules sevm.currentTarget, gasSelfDestruct)
          | .flat _ =>
              ((popped.balReadAccount sevm.benvStat.rules donee).balReadAccount
                sevm.benvStat.rules sevm.currentTarget, gasSelfDestruct)).1.getStor =
            popped.getStor := by
        cases sevm.benvStat.rules.access with
        | flat _ => rfl
        | eip2929 => dsimp only; split <;> rfl
      simp only [Devm.balReadAccount_accessedAddresses] at charge
      have chargedStorage : charged.getStor = pre.getStor :=
        (chargeGas_getStor_eq charge).symm.trans
          (accessStorage.trans (Devm.popToAdr_getStor_eq pop).symm)
      have debitedStorage : ErasesOnly pre debited :=
        (ErasesOnly.of_eq chargedStorage).trans
          (subBal_erasesOnly (Jaune.Option.toExcept_eq_ok debit))
      let credited := debited.creditBeneficiary sevm.benvStat.rules donee
        (popped.getAcct sevm.currentTarget).bal
      have creditedStorage : ErasesOnly pre credited :=
        debitedStorage.trans (creditBeneficiary_erasesOnly _ _ _ _)
      change (if sevm.currentTarget ∈ credited.createdAccounts ∨
          sevm.benvStat.rules.settle.selfdestructOnlyCreated = false then
        .ok (creditSelfdestructRefund sevm.benvStat.rules
          (sevm.currentTarget ∈ credited.accountsToDelete)
          (addAccountToDelete (credited.setBal sevm.currentTarget 0) sevm.currentTarget))
        else .ok credited : Execution) = .ok post at run
      by_cases scheduled : sevm.currentTarget ∈ credited.createdAccounts ∨
        sevm.benvStat.rules.settle.selfdestructOnlyCreated = false
      · rw [ite_eq_left scheduled] at run
        rw [← Except.ok.inj run]
        have cleared := creditedStorage.trans
          (setBal_erasesOnly credited sevm.currentTarget 0)
        intro a
        change ((creditSelfdestructRefund _ _ _).state.get a).stor = _ ∨
          ((creditSelfdestructRefund _ _ _).state.get a).stor = _
        rw [creditSelfdestructRefund_state]
        exact cleared a
      · rw [ite_eq_right scheduled] at run
        rw [← Except.ok.inj run]
        exact creditedStorage
  | some state =>
      simp only [lane] at run
      obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
      obtain ⟨⟨donee, popped⟩, pop, run⟩ := Except.bind_eq_ok run
      obtain ⟨_, _, run⟩ := Except.bind_eq_ok run
      obtain ⟨charged, charge, run⟩ := Except.bind_eq_ok run
      obtain ⟨stateCharged, stateCharge, run⟩ := Except.bind_eq_ok run
      obtain ⟨debited, debit, run⟩ := Except.bind_eq_ok run
      have chargedStorage : charged.getStor = pre.getStor :=
        (chargeGas_getStor_eq charge).symm.trans (by
          split <;> exact (Devm.popToAdr_getStor_eq pop).symm)
      have stateStorage : stateCharged.getStor = pre.getStor :=
        (Devm.chargeStateGas_getStor stateCharge).symm.trans chargedStorage
      have debitedStorage : ErasesOnly pre debited :=
        (ErasesOnly.of_eq stateStorage).trans
          (subBal_erasesOnly (Jaune.Option.toExcept_eq_ok debit))
      let value := ((if donee ∉ popped.accessedAddresses then
        addAccessedAddress popped donee else popped).getAcct sevm.currentTarget).bal
      let credited := debited.addBal donee value
      have creditedStorage : ErasesOnly pre credited := debitedStorage.trans
        (addBal_erasesOnly debited donee value)
      let logged := credited.emitTransferLog sevm.currentTarget donee value
      have loggedStorage : ErasesOnly pre logged := creditedStorage.trans
        (ErasesOnly.of_eq (funext fun a =>
          ((Devm.emitTransferLog_instructionFrame _ _ _ _).getStor a).symm))
      change (if sevm.currentTarget ∈ logged.createdAccounts then
        .ok (addAccountToDelete logged sevm.currentTarget)
        else .ok logged : Execution) = .ok post at run
      by_cases scheduled : sevm.currentTarget ∈ logged.createdAccounts
      · rw [ite_eq_left scheduled] at run
        rw [← Except.ok.inj run]
        exact loggedStorage
      · rw [ite_eq_right scheduled] at run
        rw [← Except.ok.inj run]
        exact loggedStorage

/-- Every successful terminal keeps each storage map or clears it. Logs and
balances are not asserted equal, and transaction settlement is not included. -/
theorem Linst.run_getStor_eq_or_empty {sevm : Sevm} {pre post : Devm} {l : Linst}
    (run : Linst.Run sevm pre l (.ok post)) :
    ∀ a, post.getStor a = pre.getStor a ∨ post.getStor a = .empty := by
  by_cases destruct : l = .selfdestruct
  · subst l
    exact Linst.selfdestruct_getStor_eq_or_empty run
  · have frame := Linst.run_instructionFrame sevm pre l destruct
    rw [run] at frame
    exact fun a => Or.inl (frame.getStor a).symm

end Blanc
