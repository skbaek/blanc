import Blanc.CommonCore

/-!
# Storage footprints over a set of tracked keys

A contract that keeps values at hashed slots cannot state "every key's slot holds its value" over
all keys: two keys may hash to one slot, and the map key type is enormous compared with the number of
keys a history touches.  A *footprint* instead names a set `K` of **tracked keys** and says: their
slots are pairwise distinct and off the contract's fixed slots (`Inj`, `Apart`), and every nonzero
storage word sits at a fixed slot or at a tracked key's slot (`Support`).  A frame that touches keys
`ks` needs only the local premise `FreshKeys K ks` — each is tracked or on a slot none of the finitely
many slots in use — to extend the footprint to `extendBy K ks`; and a whole history that touches keys `ks`
supplies it once, at its checkpoint, so every frame's touched keys are tracked from the start
(`FreshKeys.of_universe`).

Nothing here mentions a contract: the key type `κ`, its slot function and the fixed slots are
parameters.
-/

namespace Blanc.SlotFootprint

open Jaune

section Defs

variable {κ : Type} (slot : κ → B256) (fixed : List B256)

/-- Every nonzero storage word sits at a fixed slot or at a tracked key's slot. -/
def Support (K : κ → Prop) (s : Stor) : Prop :=
  ∀ x, s.get x ≠ 0 → x ∈ fixed ∨ ∃ k, K k ∧ slot k = x

/-- The slots of the tracked keys are pairwise distinct. -/
def Inj (K : κ → Prop) : Prop :=
  ∀ k k', K k → K k' → slot k = slot k' → k = k'

/-- No tracked key's slot is a fixed slot. -/
def Apart (K : κ → Prop) : Prop := ∀ k, K k → slot k ∉ fixed

/-- The frame-local premise for a touched key: it is tracked, or its slot is none of the slots in
use (a fixed slot or a tracked key's slot). -/
def Fresh (K : κ → Prop) (k : κ) : Prop :=
  K k ∨ (slot k ∉ fixed ∧ ∀ k', K k' → slot k' ≠ slot k)

/-- The premise for the keys `ks` a frame or history touches: each is `Fresh`, and any two with one
slot are one key. -/
def FreshKeys (K : κ → Prop) (ks : List κ) : Prop :=
  (∀ k ∈ ks, Fresh slot fixed K k) ∧ ∀ k ∈ ks, ∀ k' ∈ ks, slot k = slot k' → k = k'

/-- The tracked keys after touching `ks`. -/
def extendBy (K : κ → Prop) (ks : List κ) : κ → Prop := fun k => K k ∨ k ∈ ks

end Defs

section Lemmas

variable {κ : Type} {slot : κ → B256} {fixed : List B256} {K : κ → Prop}

end Lemmas

/-! ## Executable finite separation checks

The two lists are explicit data. The checks do not enumerate the key type,
and do not require nonzero-storage support or a pristine untracked cell. -/

/-- Check that each written key aliases only itself among the requested observations. -/
def checkFaithfulOn {κ : Type} [DecidableEq κ] (slot : κ → B256)
    (observed written : List κ) : Bool :=
  written.all fun t => observed.all fun k => decide (slot k = slot t → k = t)

/-- The finite check's exact soundness boundary, including repeated written keys. -/
theorem checkFaithfulOn_eq_true {κ : Type} [DecidableEq κ] {slot : κ → B256}
    {observed written : List κ} :
    checkFaithfulOn slot observed written = true ↔
      ∀ t ∈ written, ∀ k ∈ observed, slot k = slot t → k = t := by
  simp only [checkFaithfulOn, List.all_eq_true, decide_eq_true_eq]

/-- Check that each raw foreign slot misses every requested key's slot. -/
def checkApartOn {κ : Type} (slot : κ → B256)
    (observed : List κ) (foreign : List B256) : Bool :=
  foreign.all fun w => observed.all fun k => decide (slot k ≠ w)

/-- Exact soundness of the finite foreign-slot check. -/
theorem checkApartOn_eq_true {κ : Type} {slot : κ → B256}
    {observed : List κ} {foreign : List B256} :
    checkApartOn slot observed foreign = true ↔
      ∀ w ∈ foreign, ∀ k ∈ observed, slot k ≠ w := by
  simp only [checkApartOn, List.all_eq_true, decide_eq_true_eq]

end Blanc.SlotFootprint
