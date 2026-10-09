import Blanc.Lift.UniswapV2Pair.SwapFrontTurns
import Blanc.Lift.UniswapV2Pair.SwapCut

/-! The swap front half, pc 0 to the post-callback join `t_09c3_c5`: every successful raw swap
run reaches the join with the back half's cut predicate `SwapCut`, and the typed source swap
exactly consumes the actual optional transfer and callback turns up to its `balance0`
suspension. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The eleven body words at the join, as the source names them. -/
def swapCutWords (sevm : Sevm) (st : State) : SwapCutWords :=
  { token1 := st.token1.toB256, token0 := st.token0.toB256,
    reserve1 := Nat.toB256 st.reserve1.val, reserve0 := Nat.toB256 st.reserve0.val,
    dataLength := swapDataLength sevm, dataOffset := swapDataStart sevm,
    recipient := swapRecipientWord sevm, amount1Out := swapAmount1Out sevm,
    amount0Out := swapAmount0Out sevm }

/-- The source swap locals of a decoded swap at the entry state. -/
def swapFrontLocals (sevm : Sevm) (st : State) : SwapLocals :=
  swapSourceLocals st (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm) (swapData sevm)

theorem swapRecipientWord_eq (sevm : Sevm) :
    swapRecipientWord sevm = (swapRecipient sevm).toB256 := by
  rw [swapRecipientWord, B256.and_comm]
  exact ff20_and_word _

end Blanc.Lift.UniswapV2Pair
