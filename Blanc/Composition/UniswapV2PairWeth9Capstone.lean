import Blanc.Composition.UniswapV2PairWeth9CapstoneUniversal

/-!
# C6(b): the minimal closed instance, every hypothesis discharged

`uniswap_weth9_closed_instance`: on the synthetic world `W0` (C6(a)), the configured BPO2 block
with the two signed type-2 transactions `X.transfer(pair, 1000)` and `pair.swap(0, 996, trader, "")`
executes, and on its configured history the trader gains `996` WETH and the Pair loses `996` in
WETH9's ledger, the Pair's reserves equal its new balances (`1001000`, `999004`), C3 holds, and C4(a)
holds with share value rising strictly at equal supply.  No premise is left: `W0` is canonical
(kernel), its total ether is representable (C6(a)'s checkpoint), and it agrees with itself.

C6's control: `b = 996 > 0` and the swap moves WETH out of the Pair (`999004 < 10^6`), so the
WETH9-side callee premise C4 discharges is exercised, at frame level inside `tx2` (A13).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Blanc.Composition.UniswapV2PairWeth9Instance

/-- **The minimal closed instance (C6(b)), with no hypothesis.** -/
theorem uniswap_weth9_closed_instance : ClosedSwapOutcome W0 :=
  uniswap_weth9_closed_agreeing w0_canonical w0_jointCheckpoint.sumNof (fun _ _ => rfl)

end Blanc.Composition.UniswapV2PairWeth9Capstone
