import Blanc.Lift.PrecompileAnswer

/-!
# The two hash precompiles' answers to `feeTo()` (kernel evaluation)

The Pair's HASH-T rows of a frame include the rows a precompile's answer to the `feeTo()` request
selects (`mintFeeReplyKeys`); the `SHA256` and `RIPEMD160` answers are evaluated here.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune

/-- `feeTo()`'s calldata. -/
def feeToData : Bytes := [0x01, 0x7e, 0x7e, 0x58]

end Blanc.Composition.UniswapV2PairWeth9Capstone
