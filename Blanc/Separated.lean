import Blanc.SlotFootprint

/-!
# Pairwise separation over a finite list

`Separated f xs` says `f` identifies no two distinct members of the finite list `xs`. It is the
only shape a hash premise may take here: a universal injectivity statement about Keccak (or a
trie root) is false by pigeonhole, so a theorem assuming it is vacuous, whereas separation over
finitely many values that a trace itself computes is satisfiable (`Separated.pair_self`) and not
refutable.

In context the premise is no weaker than the equation it delivers: `Separated f [a, b]` with
`f a = f b` is exactly `a = b` (`Separated.pair_iff`). Its gain is epistemic: it fails only under a
collision of `f` on those two values, not because supplied data were wrong.

HASH-T's footprint premise is an instance: the second conjunct of `SlotFootprint.FreshKeys` is
`Separated slot ks` (`SlotFootprint.FreshKeys.separated`, `SlotFootprint.freshKeys_iff`).
-/

namespace Blanc

/-- `f` identifies no two distinct members of `xs`. -/
def Separated {α β : Type _} (f : α → β) (xs : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y

namespace Separated

variable {α β : Type _} {f : α → β}

/-- Satisfiable: a value separated from itself. -/
theorem pair_self (a : α) : Separated f [a, a] := by
  intro x hx y hy _
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx hy
  rw [hx, hy]

/-- The binding step: equal images of a separated pair are equal values. -/
theorem pair_eq {a b : α} (h : Separated f [a, b]) (e : f a = f b) : a = b :=
  h a (by simp only [List.mem_cons, true_or]) b
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]) e

/-- A separated pair is exactly the implication it is used for. -/
theorem pair_iff {a b : α} : Separated f [a, b] ↔ (f a = f b → a = b) := by
  refine ⟨pair_eq, fun h x hx y hy e => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact h e
  · exact (h e.symm).symm
  · rfl

end Separated

namespace SlotFootprint

open Jaune

variable {κ : Type} {slot : κ → B256} {fixed : List B256} {K : κ → Prop} {ks : List κ}

/-- HASH-T's footprint premise is freshness of each touched key plus separation of the slot
function over the touched keys. -/
theorem freshKeys_iff :
    FreshKeys slot fixed K ks ↔ (∀ k ∈ ks, Fresh slot fixed K k) ∧ Separated slot ks :=
  Iff.rfl

theorem FreshKeys.separated (h : FreshKeys slot fixed K ks) : Separated slot ks := h.2

end SlotFootprint

end Blanc
