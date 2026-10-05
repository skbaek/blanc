import Blanc.Lift.WitnessArms

/-!
# Reading a walk's shadows back as finite maps

The witness engine's shadows (`Blanc/Lift/WitnessArms.lean`) are write logs, newest first:
the storage shadow `StorShadow` and the account shadow `AcctShadow`.  A run's final shadow
repeats keys and records zero writes.  This module states what such a log means pointwise:

* `canonS`: the storage log with every shadowed write and every zero value dropped;
  `lookupS_canonS` says it reads the same at every address and key, so a kernel equation
  `canonS l = l'` turns a run's log into a short canonical table (`lookupS_eq_of_canonS`);
* `lookupA_eq_of_keys`: two account logs read the same at every address once they agree at
  the addresses either one names (elsewhere both read `Acct.nil`).

Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune

/-- The storage log with shadowed writes and zero values dropped (newest first). -/
def canonS : StorShadow → StorShadow
  | [] => []
  | (key, v) :: l =>
    let r := (canonS l).filter (fun e => decide (e.1 ≠ key))
    if v = 0 then r else (key, v) :: r

theorem lookupS_filter_ne (l : StorShadow) (key : Adr × B256) (a : Adr) (k : B256)
    (h : (a, k) ≠ key) :
    lookupS (l.filter (fun e => decide (e.1 ≠ key))) a k = lookupS l a k := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨⟨a', k'⟩, v⟩ := e
    by_cases he : (a', k') = key
    · subst he
      have hne : ¬ (a' = a ∧ k' = k) := fun ⟨h1, h2⟩ => h (by rw [h1, h2])
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte, ih, lookupS, hne]
    · simp only [List.filter_cons, ne_eq, he, not_false_eq_true, decide_true, ↓reduceIte,
        lookupS, ih]

theorem lookupS_filter_eq (l : StorShadow) (a : Adr) (k : B256) :
    lookupS (l.filter (fun e => decide (e.1 ≠ (a, k)))) a k = 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨⟨a', k'⟩, v⟩ := e
    by_cases he : (a', k') = (a, k)
    · simp only [List.filter_cons, ne_eq, he, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, ih]
    · have hne : ¬ (a' = a ∧ k' = k) := fun ⟨h1, h2⟩ => he (by rw [h1, h2])
      simp only [List.filter_cons, ne_eq, he, not_false_eq_true, decide_true, ↓reduceIte,
        lookupS, hne, ih]

/-- **The canonical log reads like the log**, at every address and key. -/
theorem lookupS_canonS : ∀ (l : StorShadow) (a : Adr) (k : B256),
    lookupS (canonS l) a k = lookupS l a k
  | [], _, _ => rfl
  | ((a', k'), v) :: l, a, k => by
    by_cases he : (a, k) = (a', k')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hr := lookupS_filter_eq (canonS l) a k
      by_cases hv : v = 0
      · simp only [canonS, hv, ↓reduceIte, hr, lookupS, and_self]
      · simp only [canonS, hv, ↓reduceIte, lookupS, and_self]
    · have hne : ¬ (a' = a ∧ k' = k) := fun ⟨h1, h2⟩ => he (by rw [h1, h2])
      have hr := lookupS_filter_ne (canonS l) (a', k') a k he
      by_cases hv : v = 0
      · simp only [canonS, hv, ↓reduceIte, hr, lookupS, hne, lookupS_canonS l a k]
      · simp only [canonS, hv, ↓reduceIte, lookupS, hne, hr, lookupS_canonS l a k]

/-- Two storage logs with one canonical form read the same everywhere. -/
theorem lookupS_eq_of_canonS {l l' : StorShadow} (h : canonS l = canonS l') (a : Adr) (k : B256) :
    lookupS l a k = lookupS l' a k := by
  rw [← lookupS_canonS l, h, lookupS_canonS]

theorem lookupA_of_not_mem {l : AcctShadow} {a : Adr} (h : a ∉ l.map Prod.fst) :
    lookupA l a = .nil := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a', ac⟩ := e
    have hne : a' ≠ a := fun he => h (by simp only [List.map_cons, he, List.mem_cons, true_or])
    have h' : a ∉ l.map Prod.fst := fun hm => h (List.mem_cons_of_mem _ hm)
    simp only [lookupA, hne, ↓reduceIte, ih h']

/-- **Two account logs read the same everywhere** once they agree at every address either
names. -/
theorem lookupA_eq_of_keys {l l' : AcctShadow}
    (h : ∀ a ∈ l.map Prod.fst ++ l'.map Prod.fst, lookupA l a = lookupA l' a) (a : Adr) :
    lookupA l a = lookupA l' a := by
  by_cases hm : a ∈ l.map Prod.fst ++ l'.map Prod.fst
  · exact h a hm
  · rw [List.mem_append, not_or] at hm
    rw [lookupA_of_not_mem hm.1, lookupA_of_not_mem hm.2]

/-- **Two account logs read the same everywhere**, from one closed list equation a kernel
check decides (`Acct` has no decidable equality): their reads agree along the addresses either
names. -/
theorem lookupA_eq_of_map {l l' : AcctShadow}
    (h : (l.map Prod.fst ++ l'.map Prod.fst).map (lookupA l) =
      (l.map Prod.fst ++ l'.map Prod.fst).map (lookupA l')) (a : Adr) :
    lookupA l a = lookupA l' a :=
  lookupA_eq_of_keys (fun b hb => List.map_inj_left.mp h b hb) a

end Blanc.Lift.Witness
