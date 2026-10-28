import Blanc.Lift.Weth9.CommittedReplay

/-!
# WETH9 allowance preservation along committed replay

Only an owner's `approve` can increase its allowance. The transfer-from debit
is checked before subtraction, so it cannot wrap upward. No balance-total or
backing premise is needed for this allowance-only fact. The final theorem
consumes the retained invocation list supplied by the historical replay;
reverted frames and reverted ancestors contribute no invocation to that list.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc

namespace Ledger

/-- A successful transfer-from never increases any allowance. -/
theorem transferFrom_allow_le {l l' : Ledger} {who src dst h g : Adr} {wad : B256}
    (run : l.transferFrom who src dst wad = some l') :
    (l'.allow h g).toNat ≤ (l.allow h g).toNat := by
  unfold transferFrom at run
  split at run
  · cases run
  · split at run
    · split at run
      · cases run
      · rename_i enough
        cases run
        change ((l.setAllow src who (l.allow src who - wad)).allow h g).toNat ≤ _
        by_cases owner : h = src
        · subst h
          by_cases spender : g = who
          · subst g
            simp only [setAllow, Function.update_self]
            rw [B256.toNat_sub_eq_of_le _ _ (B256.not_lt.mp enough)]
            exact Nat.sub_le _ _
          · simp only [setAllow, Function.update_self, Function.update_of_ne spender,
              Nat.le_refl]
        · simp only [setAllow, Function.update_of_ne owner, Nat.le_refl]
    · cases run
      exact Nat.le_refl _

/-- Without an approval by `h`, a successful call cannot raise `h`'s allowances. -/
theorem step_allow_le_of_noApprove {l l' : Ledger} {c : Call} {h g : Adr}
    (run : l.step c = some l') (noApprove : ∀ spender amount, c ≠ .approve h spender amount) :
    (l'.allow h g).toNat ≤ (l.allow h g).toNat := by
  cases c with
  | deposit who value => cases run; exact Nat.le_refl _
  | withdraw who wad =>
    simp only [step] at run
    split at run
    · cases run
    · cases run; exact Nat.le_refl _
  | transfer who dst wad => exact transferFrom_allow_le run
  | transferFrom who src dst wad => exact transferFrom_allow_le run
  | approve who spender amount =>
    have other : h ≠ who := by
      intro same
      subst h
      exact noApprove spender amount rfl
    cases run
    simp only [setAllow, Function.update_of_ne other, Nat.le_refl]

/-- A successful replay without owner approvals preserves zero allowances. -/
theorem run_allow_zero_of_noApprove {l l' : Ledger} {cs : List Call} {h : Adr}
    (run : l.run cs = some l') (zero : ∀ g, l.allow h g = 0)
    (noApprove : ∀ c ∈ cs, ∀ spender amount, c ≠ .approve h spender amount) :
    ∀ g, l'.allow h g = 0 := by
  induction cs generalizing l with
  | nil => cases run; exact zero
  | cons c cs ih =>
    rw [run_cons] at run
    cases stepRun : l.step c with
    | none => rw [stepRun] at run; cases run
    | some next =>
      rw [stepRun, Option.bind_some] at run
      apply ih run
      · intro g
        have le := step_allow_le_of_noApprove (g := g) stepRun
          (noApprove c List.mem_cons_self)
        rw [zero g] at le
        exact B256.toNat_inj _ _ (Nat.eq_zero_of_le_zero le)
      · intro call member
        exact noApprove call (List.mem_cons_of_mem c member)

end Ledger

/-- An actual decoded approval identifies both the caller and the selector. -/
theorem decodeCall_approve_source {e : Sevm} {h g : Adr} {wad : B256}
    (decoded : decodeCall e = some (.approve h g wad)) :
    e.caller = h ∧ Sevm.selector e = 0x095ea7b3 := by
  unfold decodeCall at decoded
  split_ifs at decoded <;> cases decoded
  exact ⟨rfl, ‹Sevm.selector e = 0x095ea7b3›⟩

/-- Caller/selector exclusion on retained invocations gives zero final allowances. -/
theorem replay_allow_zero {l l' : Ledger} {invs : List Invocation} {h : Adr}
    (run : l.run (replayCalls invs) = some l') (zero : ∀ g, l.allow h g = 0)
    (noApprove : ∀ inv ∈ invs, inv.sevm.caller = h →
      Sevm.selector inv.sevm ≠ 0x095ea7b3) :
    ∀ g, l'.allow h g = 0 := by
  apply Ledger.run_allow_zero_of_noApprove run zero
  intro c member spender amount same
  obtain ⟨inv, member, decoded⟩ := List.mem_filterMap.mp member
  rw [same] at decoded
  obtain ⟨caller, selector⟩ := decodeCall_approve_source decoded
  exact noApprove inv member caller selector

end Blanc.Lift.Weth9
