import Blanc.Lift.Token.Core
import Blanc.Lift.UniswapV2Pair.PropertiesSides

/-!
# The joint relation of the Pair and a token core

`JointAt C tr pair side st w` (Appendix A §6b, frozen): at the world `w`, the side's stored reserve of
the Pair's model state `st` is at most the token's booked balance of the Pair, and the Pair has
granted no allowance.  It is stated against the token core `C` only (no storage layout); the C3
headline (`PairTokenJoint.lean`) propagates it along a history, and the joint checkpoint supplies it
at the start (`JointCheckpoint.toCore`).
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-- The joint relation at a world: the side's stored reserve is at most the token's booked balance
of the Pair, and the Pair has granted no allowance. -/
def JointAt {T : Adr} {B : Book} (C : Core T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (pair : Adr) (side : TokenSide) (st : UniswapV2Pair.State) (w : Jaune.State) : Prop :=
  st.reserveOn side ≤ B.bal (C.ledgerOf tr w) pair ∧ ∀ g, B.allow (C.ledgerOf tr w) pair g = 0

end Blanc.Composition.PairTokenJoint
