import Blanc.Lift.WriteSiteRows

/-! Recover a slot term from a checked singleton selector guard. -/
namespace Blanc.Lift.WriteSite

open Jaune

/-- Every site has one selector guard, and the chosen selectors name exactly
the requested slot term. This checks the supplied descriptors, not execution. -/
def Site.slotSelectorCheck (selectorTerm slot : Term) (selected : B256 → Prop)
    [DecidablePred selected] (site : Site) : Bool :=
  match site.guards with
  | [(term, selector)] => decide (term = selectorTerm) &&
      decide (site.slot = slot ↔ selected selector)
  | _ => false

/-- A checked selector/slot table applies to a site whose actual guards hold.
The selector term must be known; no separation or hash premise is involved. -/
theorem Site.slot_eq_iff_of_selectorCheck {selectorTerm slot : Term}
    {selected : B256 → Prop} [DecidablePred selected] {sites : List Site}
    (table : sites.all (Site.slotSelectorCheck selectorTerm slot selected) = true)
    (known : selectorTerm.known = true) {site : Site} (member : site ∈ sites)
    {ε : Env} (guards : site.GuardsHold ε) :
    site.slot = slot ↔ selected (selectorTerm.eval ε) := by
  have checked := (List.all_eq_true.mp table) site member
  unfold Site.slotSelectorCheck at checked
  split at checked
  next term selector shape =>
    obtain ⟨termEq, slotCheck⟩ := Bool.and_eq_true_iff.mp checked
    have termIs : term = selectorTerm := of_decide_eq_true termEq
    subst term
    have guard := guards (selectorTerm, selector) (by
      rw [shape]
      exact List.mem_cons_self)
    have guardEq : selector = selectorTerm.eval ε := guard known
    have slots := of_decide_eq_true slotCheck
    rw [guardEq] at slots
    exact slots
  next => contradiction

end Blanc.Lift.WriteSite
