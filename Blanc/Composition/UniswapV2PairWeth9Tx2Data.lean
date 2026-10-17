import Blanc.Composition.UniswapV2PairWeth9Tx1Frame

/-!
# The closed instance's second transaction: data

The second transaction of the closed instance (goal C6(b)) is `pair.swap(0, swapOut, trader, "")`
from the trader: type 2, chain 1, priority fee 1, fee cap 8, nonce 1, value 0, to the Pair.  The
calldata is the standard ABI encoding (selector `0x022c0d9f`, `amount0Out = 0`,
`amount1Out = swapOut`, `to = trader`, offset `0x80` and length `0` of the empty `data`).

`swapOut = 996` is the largest amount the Pair accepts after `tx1` moved `amountIn = 1000` of `X`
into it (`getAmountOut(1000, 10^6, 10^6) = 996`).  The gas limit `300000` is a generous margin over
the swap's execution; the exact gas is the transaction unit's.  As with `tx1`, the signature is a
parameter; the signing modules fix it and prove its recovery.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift

/-- The amount of WETH the trader takes out of the Pair in `tx2`. -/
def swapOut : B256 := 996

/-- `swap(0, swapOut, trader, "")` calldata: selector `0x022c0d9f`, `0`, `swapOut`, the trader
word, the offset `0x80` of the empty bytes argument and its length `0`. -/
def tx2Data : Bytes :=
  abiSelectorBytes 0x022c0d9f ++ (0 : B256).toBytes ++ swapOut.toBytes ++ trader.toB256.toBytes ++
    (0x80 : B256).toBytes ++ (0 : B256).toBytes

/-- **The second transaction**: type 2, chain 1, priority fee 1, fee cap 8, gas 300000, nonce 1,
value 0, to the Pair, calldata `swap(0, swapOut, trader, "")`, signed by `(v, r, s)`. -/
def tx2 (v : Nat) (r s : Bytes) : Tx :=
  { nonce := 1, gas := 300000, value := 0, data := tx2Data, v := v, r := r, s := s
    type := .two 1 1 8 (some pair) [] }

end Blanc.Composition.UniswapV2PairWeth9Instance
