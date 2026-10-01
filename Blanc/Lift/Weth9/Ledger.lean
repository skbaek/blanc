import Blanc.Lift.Weth9.Footprint
import Blanc.Lift.Weth9.Model

/-!
# The ledger a footprint carries

`ledger K s` reads the two mappings of a WETH9 storage `s` at the tracked keys `K` (zero elsewhere).  A
storage write at a tracked key's slot is the matching write of the model's ledger provided the tracked slots
are pairwise distinct (`KeyInj K`), so a run whose storage effect is a sequence of such writes is a
`Ledger.step` (`ledger_set_bal`, `ledger_set_allow`).  Nothing here mentions a frame.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc

open Classical in
/-- The word at each tracked allowance slot, `0` at an untracked pair. -/
noncomputable def trackedAllow (K : Key → Prop) (s : Stor) : Adr → Adr → B256 :=
  fun o p => if K (.allow o p) then s.get (allowSlot o p) else 0

/-- The model ledger a storage carries over the tracked keys `K`. -/
noncomputable def ledger (K : Key → Prop) (s : Stor) : Ledger :=
  ⟨tracked K s, trackedAllow K s⟩

section Ledger

variable {K : Key → Prop} {s : Stor}

theorem trackedAllow_self {o p : Adr} (h : K (.allow o p)) :
    trackedAllow K s o p = s.get (allowSlot o p) := by
  simp only [trackedAllow, h, ↓reduceIte]

theorem trackedAllow_of_not {o p : Adr} (h : ¬ K (.allow o p)) : trackedAllow K s o p = 0 := by
  simp only [trackedAllow, h, ↓reduceIte]

/-- **A balance write is the ledger's balance write.** -/
theorem ledger_set_bal (hK : KeyInj K) {a : Adr} (ha : K (.bal a)) (w : B256) :
    ledger K (s.set (balSlot a) w) = (ledger K s).setBal a w := by
  unfold ledger
  simp only [Ledger.setBal, Ledger.mk.injEq]
  constructor
  · funext b
    by_cases hb : b = a
    · subst hb
      rw [tracked_self ha, Function.update_self, Stor.get_set_self]
    · rw [Function.update_of_ne hb]
      by_cases hbK : K (.bal b)
      · rw [tracked_self hbK, tracked_self hbK, Stor.get_set_ne]
        intro hslot
        exact hb (Key.bal_injective (hK _ _ ha hbK hslot)).symm
      · rw [tracked_of_not hbK, tracked_of_not hbK]
  · funext o p
    by_cases hop : K (.allow o p)
    · rw [trackedAllow_self hop, trackedAllow_self hop, Stor.get_set_ne]
      intro hslot
      exact Key.noConfusion (hK _ _ ha hop hslot)
    · rw [trackedAllow_of_not hop, trackedAllow_of_not hop]

/-- **An allowance write is the ledger's allowance write.** -/
theorem ledger_set_allow (hK : KeyInj K) {o p : Adr} (h : K (.allow o p)) (w : B256) :
    ledger K (s.set (allowSlot o p) w) = (ledger K s).setAllow o p w := by
  unfold ledger
  simp only [Ledger.setAllow, Ledger.mk.injEq]
  constructor
  · funext b
    by_cases hbK : K (.bal b)
    · rw [tracked_self hbK, tracked_self hbK, Stor.get_set_ne]
      intro hslot
      exact Key.noConfusion (hK _ _ h hbK hslot)
    · rw [tracked_of_not hbK, tracked_of_not hbK]
  · funext o' p'
    by_cases hoo : o' = o
    · subst hoo
      by_cases hpp : p' = p
      · subst hpp
        rw [trackedAllow_self h, Function.update_self, Function.update_self, Stor.get_set_self]
      · rw [Function.update_self, Function.update_of_ne hpp]
        by_cases hK' : K (.allow o' p')
        · rw [trackedAllow_self hK', trackedAllow_self hK', Stor.get_set_ne]
          intro hslot
          have := hK _ _ h hK' hslot
          exact hpp (Key.allow.inj this).2.symm
        · rw [trackedAllow_of_not hK', trackedAllow_of_not hK']
    · rw [Function.update_of_ne hoo]
      by_cases hK' : K (.allow o' p')
      · rw [trackedAllow_self hK', trackedAllow_self hK', Stor.get_set_ne]
        intro hslot
        have := hK _ _ h hK' hslot
        exact hoo (Key.allow.inj this).1.symm
      · rw [trackedAllow_of_not hK', trackedAllow_of_not hK']

/-- **The ledger reads storage only through its words.** -/
theorem ledger_congr_get {K : Key → Prop} {s s' : Stor} (h : ∀ x, s.get x = s'.get x) :
    ledger K s = ledger K s' := by
  unfold ledger tracked trackedAllow
  simp only [Ledger.mk.injEq]
  constructor <;> funext a <;> try funext b
  · simp only [h]
  · simp only [h]

/-- **Touching fresh keys leaves the ledger alone**: a fresh, untracked key reads zero, so the tracked
ledger over the extended keys is the ledger over the old ones. -/
theorem ledger_extend {K : Key → Prop} {s : Stor} {b : B256} {ks : List Key}
    (h : FootInv K s b) (hf : KeysFresh K ks) : ledger (Key.extend K ks) s = ledger K s := by
  unfold ledger
  simp only [Ledger.mk.injEq]
  constructor
  · funext a
    by_cases hK : K (.bal a)
    · rw [tracked_self hK, tracked_self (Or.inl hK)]
    · by_cases hks : Key.bal a ∈ ks
      · rw [tracked_self (Or.inr hks), tracked_of_not hK]
        exact h.support.get_eq_zero (hf.1 _ hks) hK
      · rw [tracked_of_not hK, tracked_of_not (fun hh => hh.elim hK hks)]
  · funext o p
    by_cases hK : K (.allow o p)
    · rw [trackedAllow_self hK, trackedAllow_self (Or.inl hK)]
    · by_cases hks : Key.allow o p ∈ ks
      · rw [trackedAllow_self (Or.inr hks), trackedAllow_of_not hK]
        exact h.support.get_eq_zero (hf.1 _ hks) hK
      · rw [trackedAllow_of_not hK, trackedAllow_of_not (fun hh => hh.elim hK hks)]

end Ledger

end Blanc.Lift.Weth9
