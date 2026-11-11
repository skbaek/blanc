import Blanc.Corpus.Freeze.DepositLedger
import JauneConsensus.Facts.PendingDeposits

/-! Exact frozen deposit-application outcomes from the original successful call. -/
namespace Blanc.Composition.DepositConsensusOutcomes

open Jaune JauneConsensus JauneConsensus.Facts

variable {P : Preset} {f : CFork}

/-- The new-validator arm's exact writes. Only balance-list length growth needs alignment. -/
private theorem newValidator_effects {s s' : BeaconState P f} {d : PendingDeposit}
    (h : addValidatorToRegistry s d.pubkey d.withdrawal_credentials d.amount = .ok s') :
    s'.validators.length = s.validators.length + 1 ∧
    (∀ idx < s.validators.length,
      s'.validators.toArray[idx]? = s.validators.toArray[idx]?) ∧
    (∃ v : Validator, s'.validators.toArray[s.validators.length]? = some v ∧
      v.pubkey = d.pubkey ∧ v.withdrawal_credentials = d.withdrawal_credentials) ∧
    s'.balances.toArray[s.validators.length]? = some d.amount ∧
    (∀ idx, idx ≠ s.validators.length →
      s'.balances.toArray[idx]? = s.balances.toArray[idx]?) ∧
    (s.balances.length = s.validators.length →
      s'.balances.length = s.balances.length + 1) := by
  have original := h
  unfold addValidatorToRegistry at h
  obtain ⟨index, hindex, h⟩ := bind_ok_elim h
  obtain ⟨v, hv, h⟩ := bind_ok_elim h
  obtain ⟨vals, hvals, h⟩ := bind_ok_elim h
  obtain ⟨bals, hbals, h⟩ := bind_ok_elim h
  obtain ⟨p1, _, h⟩ := bind_ok_elim h
  obtain ⟨p2, _, h⟩ := bind_ok_elim h
  obtain ⟨p3, _, h⟩ := bind_ok_elim h
  cases h
  have hix : index.toNat = s.validators.toArray.size := U64.toNat_ofNat? hindex
  have registry := setOrAppendList_at_length hix hvals
  have key : v.pubkey = d.pubkey ∧ v.withdrawal_credentials = d.withdrawal_credentials := by
    unfold getValidatorFromDeposit at hv
    obtain ⟨maxEb, _, hv⟩ := bind_ok_elim hv
    obtain ⟨modulus, _, hv⟩ := bind_ok_elim hv
    obtain ⟨remainder, _, hv⟩ := bind_ok_elim hv
    obtain ⟨rounded, _, hv⟩ := bind_ok_elim hv
    cases hv
    exact ⟨rfl, rfl⟩
  have balances : ∀ idx, bals.toArray[idx]? =
      if idx = index.toNat then some d.amount else s.balances.toArray[idx]? := by
    unfold setOrAppendList at hbals
    split at hbals
    · rename_i heq
      have heq' : index.toNat = s.balances.toArray.size := by
        simpa only [beq_iff_eq, SszList.length] using heq
      rw [push_ok hbals, heq']
      intro idx
      exact Array.getElem?_push
    · obtain ⟨hi, harr⟩ := set_ok hbals
      rw [harr]
      intro idx
      simpa only [eq_comm] using (Array.getElem?_set (v := d.amount) (j := idx) hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change vals.toArray.size = s.validators.toArray.size + 1
    rw [registry, Array.size_push]
  · intro idx hi
    change idx < s.validators.toArray.size at hi
    change vals.toArray[idx]? = _
    rw [registry, Array.getElem?_push]
    exact ite_eq_right (by change idx ≠ s.validators.toArray.size; omega)
  · refine ⟨v, ?_, key.1, key.2⟩
    change vals.toArray[s.validators.toArray.size]? = some v
    rw [registry]
    exact Array.getElem?_push_size
  · change bals.toArray[s.validators.toArray.size]? = some d.amount
    rw [balances, hix, ite_eq_left rfl]
  · intro idx hne
    change idx ≠ s.validators.toArray.size at hne
    change bals.toArray[idx]? = _
    rw [balances, hix, ite_eq_right hne]
  · intro aligned
    obtain ⟨_, _, _, _, pushed⟩ := applyPendingDeposit_newValidator_credit aligned original
    change bals.toArray.size = s.balances.toArray.size + 1
    change bals.toArray = s.balances.toArray.push d.amount at pushed
    rw [pushed, Array.size_push]

open Blanc.Corpus.Freeze.Deposit (ApplyOutcome ApplyOutcomeSpec classifyApply)

/-- Every original successful call has exactly the frozen three-arm outcome,
with its actual classifier, writes and checked credit. No alignment is assumed. -/
theorem applyOutcome_of_success (ccfg : Config) (bls : Bool)
    (s s' : BeaconState P f) (d : PendingDeposit)
    (h : applyPendingDeposit (jointCtx ccfg bls) s d = .ok s') :
    ∃ o : ApplyOutcome, ApplyOutcomeSpec ccfg bls s s' d o := by
  have splitSuccess := h
  rw [applyPendingDeposit_eq] at splitSuccess
  obtain ⟨outcome, classified, applied⟩ := bind_ok_elim splitSuccess
  cases outcome with
  | newValidator =>
    obtain ⟨found, signature⟩ := classifyPendingDeposit_newValidator classified
    have added : addValidatorToRegistry s d.pubkey d.withdrawal_credentials d.amount = .ok s' :=
      applied
    refine ⟨.newValidator, ?_, h, Or.inl ⟨rfl, found, signature, added,
      newValidator_effects added⟩⟩
    unfold classifyApply
    rw [found, signature]
    rfl
  | topUp index =>
    have found := classifyPendingDeposit_topUp classified
    have checked : U64.ofNat? index.toNat "ValidatorIndex" = .ok index := by
      unfold classifyPendingDeposit at classified
      rw [found] at classified
      obtain ⟨iv, hiv, same⟩ := bind_ok_elim classified
      cases same
      exact hiv
    obtain ⟨oldBal, newBal, oldRead, credit, balances, validators⟩ :=
      applyPendingDeposit_topUp_credit applied
    have length : s'.balances.length = s.balances.length := by
      change increaseBalance s index d.amount = .ok s' at applied
      unfold increaseBalance at applied
      obtain ⟨bals, modified, applied⟩ := bind_ok_elim applied
      cases applied
      unfold SszList.modify at modified
      obtain ⟨old, _, modified⟩ := bind_ok_elim modified
      obtain ⟨new, _, written⟩ := bind_ok_elim modified
      obtain ⟨hi, harr⟩ := set_ok written
      change bals.toArray.size = s.balances.toArray.size
      rw [harr, Array.size_set]
    refine ⟨.topUp index.toNat, ?_, h, Or.inr (Or.inl
      ⟨index.toNat, rfl, found, ⟨index, checked, applied⟩, validators, length,
        ⟨oldBal, newBal, oldRead, ?_, credit⟩, ?_⟩)⟩
    · unfold classifyApply
      rw [found]
      rfl
    · simpa only [ite_true] using balances index.toNat
    · intro idx hne
      rw [balances, ite_eq_right hne]
  | noCredit =>
    obtain ⟨found, signature⟩ := classifyPendingDeposit_noCredit classified
    have unchanged : s' = s := (Except.ok.inj applied).symm
    subst s'
    refine ⟨.noCredit, ?_, h, Or.inr (Or.inr ⟨rfl, found, signature, rfl, rfl, rfl⟩)⟩
    unfold classifyApply
    rw [found, signature]
    rfl

end Blanc.Composition.DepositConsensusOutcomes
