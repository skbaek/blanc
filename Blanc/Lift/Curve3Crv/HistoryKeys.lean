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
    (touched : ∀ k ∈ ks, U k) : FreshKeys K ks :=
  SlotFootprint.FreshKeys.of_universe (slot := Key.slot) (fixed := vyFixedSlots)
    injective apart included touched

end Blanc.Lift.Curve3Crv
