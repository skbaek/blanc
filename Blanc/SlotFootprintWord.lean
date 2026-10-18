import Blanc.SlotFootprint

/-!
# The tracked words of a storage footprint

`trackedWord slot K s k` is the word at a tracked key's slot and `0` at an untracked key: the raw
reading a footprint ledger is built from.  A write at a tracked key's slot is that key's row update
when the tracked slots are injective (`trackedWord_set`); a write at a slot no tracked key uses leaves
every row alone (`trackedWord_set_off`); touching fresh keys leaves the rows alone, since a fresh
untracked key reads zero (`trackedWord_extend`).  `Support.set_fixed` is `Support.set`'s twin for a
write at a fixed slot.  Nothing here mentions a contract.
-/

namespace Blanc.SlotFootprint

open Jaune

variable {κ : Type} {slot : κ → B256} {fixed : List B256} {K : κ → Prop} {s : Stor}

open Classical in
/-- The word at each tracked key's slot, `0` at an untracked key. -/
noncomputable def trackedWord (slot : κ → B256) (K : κ → Prop) (s : Stor) (k : κ) : B256 :=
  if K k then s.get (slot k) else 0

theorem trackedWord_of_mem {k : κ} (h : K k) : trackedWord slot K s k = s.get (slot k) := by
  simp only [trackedWord, h, ↓reduceIte]

theorem trackedWord_of_not {k : κ} (h : ¬ K k) : trackedWord slot K s k = 0 := by
  simp only [trackedWord, h, ↓reduceIte]

/-- **A write at a tracked key's slot is that key's row update** (the tracked slots injective). -/
theorem trackedWord_set [DecidableEq κ] (inj : Inj slot K) {k : κ} (hk : K k) (w : B256) :
    trackedWord slot K (s.set (slot k) w) = Function.update (trackedWord slot K s) k w := by
  funext k'
  by_cases e : k' = k
  · subst e
    rw [Function.update_self, trackedWord_of_mem hk, Stor.get_set_self]
  · rw [Function.update_of_ne e]
    by_cases hk' : K k'
    · rw [trackedWord_of_mem hk', trackedWord_of_mem hk', Stor.get_set_ne]
      exact fun hs => e (inj k' k hk' hk hs.symm)
    · rw [trackedWord_of_not hk', trackedWord_of_not hk']

/-- A write at a slot no tracked key uses leaves every tracked word alone. -/
theorem trackedWord_set_off {x : B256} (off : ∀ k, K k → slot k ≠ x) (w : B256) :
    trackedWord slot K (s.set x w) = trackedWord slot K s := by
  funext k
  by_cases hk : K k
  · rw [trackedWord_of_mem hk, trackedWord_of_mem hk, Stor.get_set_ne]
    exact fun hs => off k hk hs.symm
  · rw [trackedWord_of_not hk, trackedWord_of_not hk]

/-- **Touching fresh keys leaves the tracked words alone**: a fresh untracked key reads zero. -/
theorem trackedWord_extend {ks : List κ} (support : Support slot fixed K s)
    (fresh : FreshKeys slot fixed K ks) :
    trackedWord slot (extendBy K ks) s = trackedWord slot K s := by
  funext k
  by_cases hK : K k
  · rw [trackedWord_of_mem (K := extendBy K ks) (Or.inl hK), trackedWord_of_mem hK]
  · by_cases hks : k ∈ ks
    · rw [trackedWord_of_mem (K := extendBy K ks) (Or.inr hks), trackedWord_of_not hK]
      exact support.get_eq_zero (fresh.1 k hks) hK
    · rw [trackedWord_of_not hK, trackedWord_of_not (K := extendBy K ks) (fun hh => hh.elim hK hks)]

/-- A write at a fixed slot keeps the support. -/
theorem Support.set_fixed (h : Support slot fixed K s) {x : B256} (hx : x ∈ fixed) (w : B256) :
    Support slot fixed K (s.set x w) := by
  intro y hy
  by_cases hyx : y = x
  · exact .inl (hyx ▸ hx)
  · rw [Stor.get_set_ne _ (Ne.symm hyx)] at hy
    exact h y hy

end Blanc.SlotFootprint
