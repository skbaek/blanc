import Blanc.Lift.BuilderRequest.Occurrence
import Blanc.Lift.BuilderRequest.LoadBound
/-!
# Actual retained request fees

Read the original pre-storage word quote of each ordinary submission. The
matched delivery frames identify exactly the same fees, without replacing the
wrapped recurrence by its natural specification or counting principal or gas.
-/

namespace Blanc.Lift.BuilderRequest.WordFees
open Jaune RequestSystem Delivery ChainLink

/-- The actual word quote charged to an ordinary submission, excluding all other value. -/
noncomputable def frameFee (c : Contract) (f : Exec.Frame) : Nat :=
  if f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = c.payload then
    RequestFeeWord.quotedFee
      (targetExcess c.target ((Devm.getStor f.pre c.address).get 0)
        ((Devm.getStor f.pre c.address).get 1))
  else 0

/-- Actual request fees of all users in the whole retained history. -/
noncomputable def actualFeeSum (c : Contract) (blocks : List KeptBlock) : Nat :=
  ((History.kept c.address blocks).map (frameFee c)).sum

variable {c : Contract}

theorem quote_word (g : Frame c) {q : B256} (hq : g.quotedFee = some q) :
    q.toNat = RequestFeeWord.quotedFee (targetExcess c.target (g.before.get 0) (g.before.get 1)) := by
  obtain ⟨i, o, rfl, run⟩ := g.quote_run hq
  exact (RequestFeeWord.wordFee_of_run run).2.1.symm

theorem matches_feePaid {g : Frame c} {f : Exec.Frame} (m : Matches c g f) :
    LoadBound.feePaid g = frameFee c f := by
  cases he : g.event with
  | submission r =>
    have caller : f.sevm.caller ≠ systemAddress := by
      intro hs
      have bad := m.system hs
      rw [he] at bad
      cases bad
    have length : f.sevm.data.length = c.payload := by
      by_contra hn
      have ev := m.event.trans (keptEvent_user hn caller)
      rw [he] at ev
      cases ev
    obtain ⟨q, hq⟩ : ∃ q, g.quotedFee = some q := by
      cases g <;> first | exact ⟨_, rfl⟩ | cases he
    rw [frameFee, ite_eq_left ⟨caller, length⟩, ← m.before]
    simpa only [LoadBound.feePaid, he, hq, Option.getD_some] using quote_word g hq
  | feeRead =>
    have no : ¬ (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = c.payload) := by
      rintro ⟨_, hl⟩
      have ev := m.event.trans (keptEvent_of_length hl)
      rw [he] at ev
      cases ev
    simp only [LoadBound.feePaid, he, frameFee, ite_eq_right no]
  | system latch =>
    have no : ¬ (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = c.payload) := by
      rintro ⟨_, hl⟩
      have ev := m.event.trans (keptEvent_of_length hl)
      rw [he] at ev
      cases ev
    simp only [LoadBound.feePaid, he, frameFee, ite_eq_right no]

theorem corresponds_fees {frames : List (Frame c)} {kept : List Exec.Frame}
    (corr : Corresponds c frames kept) :
    LoadBound.fees frames = (kept.map (frameFee c)).sum := by
  induction corr with
  | nil => rfl
  | cons m rest ih =>
    rw [LoadBound.fees_cons, List.map_cons, List.sum_cons, matches_feePaid m, ih]

end Blanc.Lift.BuilderRequest.WordFees
