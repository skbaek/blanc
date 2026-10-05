import Blanc.Lift.WitnessArms

/-! # Reading the witness engine's world shadows

The witness engine (`Blanc/Lift/WitnessArms.lean`) keeps the world as list shadows, newest
first: storage writes (`StorShadow`, read by `lookupS`) and account views (`AcctShadow`, read by
`lookupA`). A run's final shadow is its start shadow with the run's entries prepended. These
lemmas read such a shadow without enumerating addresses or keys: a prefix that only restates the
start's views changes no account; a prefix that writes elsewhere leaves another address's
storage; a start that holds nothing at an address leaves the prefix's values there. -/

namespace Blanc.Lift.Witness

open Jaune

/-- A prefix of account entries each restating the start's view leaves every lookup. -/
theorem lookupA_append_of_restate {p l : AcctShadow} (h : ∀ e ∈ p, e.2 = lookupA l e.1)
    (a : Adr) : lookupA (p ++ l) a = lookupA l a := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    obtain ⟨b, v⟩ := e
    simp only [List.cons_append, lookupA]
    split
    · next hb =>
      subst hb
      exact h _ List.mem_cons_self
    · exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- A prefix of storage writes at other addresses leaves `a`'s storage. -/
theorem lookupS_append_of_ne {p l : StorShadow} {a : Adr} (h : ∀ e ∈ p, e.1.1 ≠ a)
    (k : B256) : lookupS (p ++ l) a k = lookupS l a k := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    obtain ⟨⟨b, j⟩, v⟩ := e
    simp only [List.cons_append, lookupS]
    rw [if_neg fun hb => h _ List.mem_cons_self hb.1]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- A start shadow with no entry at `a` leaves `a`'s storage to the prefix. -/
theorem lookupS_append_of_absent {p l : StorShadow} {a : Adr} (h : ∀ e ∈ l, e.1.1 ≠ a)
    (k : B256) : lookupS (p ++ l) a k = lookupS p a k := by
  induction p with
  | nil =>
    simp only [List.nil_append, lookupS]
    induction l with
    | nil => rfl
    | cons e l ih =>
      obtain ⟨⟨b, j⟩, v⟩ := e
      simp only [lookupS]
      rw [if_neg fun hb => h _ List.mem_cons_self hb.1]
      exact ih fun e he => h e (List.mem_cons_of_mem _ he)
  | cons e p ih =>
    obtain ⟨⟨b, j⟩, v⟩ := e
    simp only [List.cons_append, lookupS]
    split
    · rfl
    · exact ih

/-- A shadow whose every entry at `(a, k)` holds zero reads zero there. -/
theorem lookupS_eq_zero_of {l : StorShadow} {a : Adr} {k : B256}
    (h : ∀ e ∈ l, e.1 = (a, k) → e.2 = 0) : lookupS l a k = 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨⟨b, j⟩, v⟩ := e
    simp only [lookupS]
    split
    · next hb =>
      obtain ⟨rfl, rfl⟩ := hb
      exact h _ List.mem_cons_self rfl
    · exact ih fun e he => h e (List.mem_cons_of_mem _ he)

end Blanc.Lift.Witness
