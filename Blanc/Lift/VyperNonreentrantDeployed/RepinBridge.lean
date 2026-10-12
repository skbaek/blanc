import Blanc.Lift.WitnessChild

/-!
# Vyper re-pin bridge (Jaune ca9f27d)

Unit-local helpers for the re-pin to Jaune `ca9f27d`. Generic in shape (nothing here names a
Vyper contract): hoisting candidates for the integrator.

Under machine-sensitive original storage (OS), an `SSTORE`'s original value reads the
transaction's created-account set, so a kernel decision over a settled child supplied as data
fixes that child's created set (`Devm.withCreatedAccounts_of_eq` restores the child).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.RepinBridge

open Jaune

/-- A machine whose created-account set is `E` is itself with that set replaced by `E`. -/
theorem withCreatedAccounts_of_eq {d : Devm} {E : AdrSet} (h : d.createdAccounts = E) :
    d.withCreatedAccounts E = d := by
  rcases d with ⟨_, ⟨_, _, _, _, _, _, _, _, _, _, _⟩, _⟩
  simp only [Devm.createdAccounts] at h
  subst h
  rfl

end Blanc.Lift.VyperNonreentrantDeployed.RepinBridge

namespace Blanc.Lift.VyperNonreentrantDeployed.RepinBridge

open Jaune Blanc.Lift Blanc.Lift.Witness

/-- A balance write at an owner with a nonzero nonce deletes nothing from the storage shadow. -/
theorem storSetBal_of_nonce {stor : StorShadow} {acs : AcctShadow} {owner : Adr} {v : B256}
    (h : (lookupA acs owner).nonce ≠ 0) : storSetBal stor acs owner v = stor := by
  unfold storSetBal
  rw [ite_eq_right_iff.mpr (fun he => absurd he.2.1 h)]

theorem lookupA_acsSetBal_nonce (acs : AcctShadow) (a : Adr) (v : B256) (b : Adr) :
    (lookupA (acsSetBal acs a v) b).nonce = (lookupA acs b).nonce := by
  unfold acsSetBal
  simp only [lookupA]
  split
  · next h => subst h; rfl
  · rfl

/-- Whether a message's value transfer provably keeps the storage shadow: no value moves, or
both its caller and its target have a nonzero nonce in the account shadow (so neither balance
write can delete an account). Decided by evaluation. -/
def transferKeepsStor (m : Msg) (acs : AcctShadow) : Bool :=
  !(decide (m.shouldTransferValue ∧ m.value ≠ 0)) ||
    (decide ((lookupA acs m.caller).nonce ≠ 0) && decide ((lookupA acs m.currentTarget).nonce ≠ 0))

theorem storTransfer_of_keeps {m : Msg} {stor : StorShadow} {acs : AcctShadow}
    (h : transferKeepsStor m acs = true) : storTransfer m stor acs = stor := by
  unfold storTransfer
  split
  · next hv =>
    have hd : decide (m.shouldTransferValue ∧ m.value ≠ 0) = true := decide_eq_true hv
    rw [transferKeepsStor, hd, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    simp only []
    rw [storSetBal_of_nonce (of_decide_eq_true h.1),
      storSetBal_of_nonce (by rw [lookupA_acsSetBal_nonce]; exact of_decide_eq_true h.2)]
  · rfl

end Blanc.Lift.VyperNonreentrantDeployed.RepinBridge

namespace Blanc.Lift.VyperNonreentrantDeployed.RepinBridge

open Jaune Blanc.Lift Blanc.Lift.Witness

/-- `frameStart_agree` when the entry's value transfer keeps the storage shadow
(`transferKeepsStor`): the start configuration carries the parent's storage shadow itself. -/
theorem frameStart_agree_keep {f : Frame} {acs : AcctShadow} {cevm : Evm}
    {keys : List (Adr × B256)} {adrs : List Adr} {stor : StorShadow} (f0 : SFunc)
    (he : frameEnterS f acs = .run cevm)
    (hK : ∀ x, x ∈ f.inner.accessedStorageKeys ↔ x ∈ keys)
    (hA : ∀ a, a ∈ f.inner.accessedAddresses ↔ a ∈ adrs)
    (hS : ∀ a k, storOf f.inner.benv.state a k = lookupS stor a k)
    (hC : AcctAgree f.inner.benv.state acs) (hk : transferKeepsStor f.inner acs = true) :
    Agree ⟨cevm.dyna, f0, [], keys, adrs, stor, acsTransfer f.inner acs⟩ := by
  have h := frameStart_agree f0 he hK hA hS hC
  rwa [storTransfer_of_keeps hk] at h

/-- The created-account set of a run's halted machine (the empty set off a halt): a kernel
decision about it reads only that field. -/
def haltCreated : Res → AdrSet
  | .done (.halted d) _ => d.createdAccounts
  | _ => .emptyWithCapacity

end Blanc.Lift.VyperNonreentrantDeployed.RepinBridge
