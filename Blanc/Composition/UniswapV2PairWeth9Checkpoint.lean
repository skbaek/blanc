import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.UniswapV2Pair.PropertiesSides
import Blanc.Lift.Weth9.Contract
import Blanc.Lift.Weth9.Footprint

/-!
# The joint checkpoint of the Uniswap V2 Pair and WETH9

`JointCheckpoint` is a predicate on one world state, however it was produced: both codes installed,
the Pair's storage representing an unlocked model state whose `side` token is WETH9, WETH9's
footprint invariant with the Pair's balance row tracked and its allowance rows zero, and the side's
reserve at most WETH9's booked balance of the Pair.  `JointCheckpoint.allowance_control` is the C5
statement control.  The finite checker deciding it is `UniswapV2PairWeth9CheckJoint.lean`.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9
  Blanc.Lift.UniswapV2Pair

/-- **The joint checkpoint** (a predicate on one world state, however it was produced): both codes
installed, the Pair's storage represents an unlocked model state whose `side` token is WETH9,
WETH9's footprint invariant with the Pair's balance row tracked and its allowance rows zero, and the
side's reserve at most WETH9's booked balance of the Pair. -/
structure JointCheckpoint (pair weth : Adr) (K₀ : Key → Prop) (KP : WriterKey → Prop)
    (st₀ : UniswapV2Pair.State) (side : TokenSide) (w : Jaune.State) : Prop where
  pairCode : some (w.getCode pair).toList = pairSem.image
  pairRep : WriterRep KP (w.getStor pair) st₀
  token : st₀.tokenOn side = weth
  unlocked : st₀.unlocked = 1
  wethCode : some (w.getCode weth).toList = weth9Sem.image
  wethFoot : FootInv K₀ (w.getStor weth) (w.bal weth)
  sumNof : SumNof w.bal
  tracked : K₀ (.bal pair)
  noAllowance : ∀ g, K₀ (.allow pair g) → (w.getStor weth).get (allowSlot pair g) = 0
  reserve : st₀.reserveOn side ≤ ((w.getStor weth).get (balSlot pair)).toNat
  apart : pair ≠ weth

/-- **C5 control.**  A world where the Pair already holds a nonzero tracked WETH9 allowance row
fails the predicate. -/
theorem JointCheckpoint.allowance_control {pair weth : Adr} {K₀ : Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State} {side : TokenSide} {w : Jaune.State}
    {g : Adr} (row : K₀ (.allow pair g)) (granted : (w.getStor weth).get (allowSlot pair g) ≠ 0) :
    ¬ JointCheckpoint pair weth K₀ KP st₀ side w := fun h =>
  granted (h.noAllowance g row)

end Blanc.Composition.UniswapV2PairWeth9Joint
