import Blanc.Lift.Token.Core
import Blanc.Lift.Token.CoreW
import Blanc.Lift.UniswapV2Pair.PropertiesSides

/-!
# The joint relation of the Pair and a token core

`JointAt C tr pair side st w` (Appendix A §6b, frozen): at the world `w`, the side's stored reserve of
the Pair's model state `st` is at most the token's booked balance of the Pair, and the Pair has
granted no allowance.  It is stated against the token core `C` only (no storage layout); the C3
headline (`PairTokenJoint.lean`) propagates it along a history, and the joint checkpoint supplies it
at the start (`JointCheckpoint.toCore`).  `JointAtW` is the same relation over the writer-shadowed
core `CoreW` (Route R); at `C.weak` it is `JointAt C` by definition (`jointAt_weak`).
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair

/-- The joint relation at a world: the side's stored reserve is at most the token's booked balance
of the Pair, and the Pair has granted no allowance. -/
def JointAt {T : Adr} {B : Book} (C : Core T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (pair : Adr) (side : TokenSide) (st : UniswapV2Pair.State) (w : Jaune.State) : Prop :=
  st.reserveOn side ≤ B.bal (C.ledgerOf tr w) pair ∧ ∀ g, B.allow (C.ledgerOf tr w) pair g = 0

/-- The joint relation over the writer-shadowed core (Route R). -/
def JointAtW {T : Adr} {B : Book} (C : CoreW T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (pair : Adr) (side : TokenSide) (st : UniswapV2Pair.State) (w : Jaune.State) : Prop :=
  st.reserveOn side ≤ B.bal (C.ledgerOf tr w) pair ∧ ∀ g, B.allow (C.ledgerOf tr w) pair g = 0

/-- At `C.weak`, the writer-shadowed joint relation is the joint relation. -/
theorem jointAt_weak {T : Adr} {B : Book} (C : Core T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (pair : Adr) (side : TokenSide) (st : UniswapV2Pair.State) (w : Jaune.State) :
    JointAt C tr pair side st w = JointAtW C.weak tr pair side st w := rfl

end Blanc.Composition.PairTokenJoint
