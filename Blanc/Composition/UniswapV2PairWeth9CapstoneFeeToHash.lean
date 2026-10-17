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

theorem feeTo_sha256 : (Bytes.sha256 feeToData).toBytes =
    [52, 73, 89, 67, 101, 127, 183, 69, 16, 28, 81, 117, 186, 212, 242, 136, 6, 108, 112, 249,
      159, 144, 163, 30, 123, 141, 2, 169, 227, 15, 244, 100] := by
  decide +kernel

theorem feeTo_ripemd160 : Bytes.ripemd160 feeToData =
    [162, 133, 206, 9, 176, 136, 198, 82, 29, 125, 243, 151, 144, 52, 240, 161, 255, 154, 227, 9] := by
  decide +kernel

end Blanc.Composition.UniswapV2PairWeth9Capstone
