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
parameters.  (WETH9's `Blanc/Lift/Weth9/Footprint.lean` is the first consumer.  Curve's
`Blanc/Lift/Curve3Crv/Layout.lean` states the same notions for its own key type.)
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

/-- A fresh key that is not tracked reads zero. -/
theorem Support.get_eq_zero {s : Stor} (h : Support slot fixed K s) {k : κ}
    (hf : Fresh slot fixed K k) (hK : ¬ K k) : s.get (slot k) = 0 := by
  by_contra hne
  rcases h _ hne with hx | ⟨k', hk', he⟩
  · exact (hf.resolve_left hK).1 hx
  · exact (hf.resolve_left hK).2 k' hk' he

/-- Support over more tracked keys: monotone. -/
theorem Support.mono {K' : κ → Prop} {s : Stor} (h : Support slot fixed K s)
    (hle : ∀ k, K k → K' k) : Support slot fixed K' s := by
  intro x hx
  rcases h x hx with hx | ⟨k, hk, he⟩
  · exact .inl hx
  · exact .inr ⟨k, hle k hk, he⟩

/-- A write at a tracked key's slot keeps the support. -/
theorem Support.set {s : Stor} (h : Support slot fixed K s) {k : κ} (hk : K k) (w : B256) :
    Support slot fixed K (s.set (slot k) w) := by
  intro x hx
  by_cases hxk : x = slot k
  · exact .inr ⟨k, hk, hxk.symm⟩
  · rw [Stor.get_set_ne _ (Ne.symm hxk)] at hx
    exact h x hx

/-- Touching fresh keys extends the footprint's injectivity. -/
theorem Inj.extend {ks : List κ} (h : Inj slot K) (hf : FreshKeys slot fixed K ks) :
    Inj slot (extendBy K ks) := by
  intro k k' hk hk' he
  rcases hk with hk | hk <;> rcases hk' with hk' | hk'
  · exact h k k' hk hk' he
  · rcases hf.1 k' hk' with hK' | ⟨-, hoff⟩
    · exact h k k' hk hK' he
    · exact absurd he (hoff k hk)
  · rcases hf.1 k hk with hK | ⟨-, hoff⟩
    · exact h k k' hK hk' he
    · exact absurd he.symm (hoff k' hk')
  · exact hf.2 k hk k' hk' he

/-- Touching fresh keys extends the footprint's apartness from the fixed slots. -/
theorem Apart.extend {ks : List κ} (h : Apart slot fixed K) (hf : FreshKeys slot fixed K ks) :
    Apart slot fixed (extendBy K ks) := by
  intro k hk
  rcases hk with hk | hk
  · exact h k hk
  · rcases hf.1 k hk with hK | ⟨hfix, -⟩
    · exact h k hK
    · exact hfix

/-- **A history's touched keys are fresh against any tracked subset of a universe** whose slots are
injective and off the fixed slots. -/
theorem FreshKeys.of_universe {U : κ → Prop} {ks : List κ}
    (injective : Inj slot U) (apart : Apart slot fixed U)
    (included : ∀ k, K k → U k) (touched : ∀ k ∈ ks, U k) :
    FreshKeys slot fixed K ks := by
  constructor
  · intro k hk
    by_cases hK : K k
    · exact Or.inl hK
    · right
      refine ⟨apart k (touched k hk), ?_⟩
      intro k' hk' heq
      exact hK ((injective k' k (included k' hk') (touched k hk) heq) ▸ hk')
  · intro k hk k' hk' heq
    exact injective k k' (touched k hk) (touched k' hk') heq

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
