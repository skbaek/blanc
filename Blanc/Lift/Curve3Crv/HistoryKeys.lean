import Blanc.Lift.Curve3Crv.Layout

/-! # Curve live-key freshness inside a collision-free universe

The universe may conservatively include keys of rolled-back raw entries.
Live keys remain dynamic; this lemma provides independent slot separation
for the keys touched by a call from its membership in that universe.
-/

namespace Blanc.Lift.Curve3Crv

open Jaune

/-- Every touched key is fresh against any carried live subset of a universe
whose slots are injective and disjoint from the fixed storage slots. -/
theorem FreshKeys.of_universe {U K : Key → Prop} {ks : List Key}
    (injective : ∀ k k', U k → U k' → k.slot = k'.slot → k = k')
    (apart : ∀ k, U k → k.slot ∉ vyFixedSlots)
    (included : ∀ k, K k → U k)
    (touched : ∀ k ∈ ks, U k) : FreshKeys K ks := by
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

end Blanc.Lift.Curve3Crv
