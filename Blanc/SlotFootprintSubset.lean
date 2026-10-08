import Blanc.SlotFootprint

namespace Blanc.SlotFootprint

/-- Extending tracked keys by rows in the same universe preserves inclusion. -/
theorem extendBy_subset {κ : Type} {U K : κ → Prop} {keys : List κ}
    (sub : ∀ k, K k → U k) (good : ∀ k ∈ keys, U k) :
    ∀ k, extendBy K keys k → U k :=
  fun k member => Or.elim member (sub k) (good k)

end Blanc.SlotFootprint
