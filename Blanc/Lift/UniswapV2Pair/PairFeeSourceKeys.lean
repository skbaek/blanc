import Blanc.Lift.UniswapV2Pair.FeeMintSource

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Every incoming tracked key remains represented after the actual fee
branch, including its conditional finite recipient extension. -/
theorem feeBranchSourceKeys_contains {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b : Devm} {w r0 r1 : B256} {key : WriterKey}
    (tracked : K key) : feeBranchSourceKeys K st sevm b w r0 r1 key := by
  unfold feeBranchSourceKeys
  split
  · exact tracked
  · split
    · exact tracked
    · split
      · split
        · exact tracked
        · exact Or.inl tracked
      · exact tracked

end Blanc.Lift.UniswapV2Pair
