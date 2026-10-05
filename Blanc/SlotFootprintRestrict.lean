import Blanc.SlotFootprint

/-!
# Freshness against a universe restricts to its tracked subsets

`FreshKeys.of_universe` turns a separated trace-fixed universe into freshness of keys the universe holds.
A key that a *later* frame touches need not lie in that universe; its HASH-T premise is freshness
against the universe itself.  `FreshKeys.restrict` carries that premise to every tracked subset of the
universe, so a consumer holding a footprint `K ⊆ U` (for instance the rows a replay has tracked so far)
can use it unchanged.
-/

namespace Blanc.SlotFootprint

open Jaune

variable {κ : Type} {slot : κ → B256} {fixed : List B256}

/-- **Freshness against a separated universe restricts to every tracked subset of it.** -/
theorem FreshKeys.restrict {U K : κ → Prop} {ks : List κ}
    (injective : Inj slot U) (apart : Apart slot fixed U) (included : ∀ k, K k → U k)
    (fresh : FreshKeys slot fixed U ks) : FreshKeys slot fixed K ks := by
  refine ⟨fun k member => ?_, fresh.2⟩
  by_cases tracked : K k
  · exact Or.inl tracked
  · right
    rcases fresh.1 k member with inU | ⟨offFixed, offU⟩
    · refine ⟨apart k inU, fun k' inK same => tracked ?_⟩
      exact (injective k' k (included k' inK) inU same) ▸ inK
    · exact ⟨offFixed, fun k' inK => offU k' (included k' inK)⟩

end Blanc.SlotFootprint
