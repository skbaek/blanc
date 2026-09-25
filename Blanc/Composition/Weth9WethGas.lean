import Blanc.Lift.Weth9.Live
import Blanc.WethGas

/-! # Deployed WETH9 against Blanc-WETH: exact gas side by side

A measurement over two contract families (the lifted WETH9 in
`Blanc/Lift/Weth9/Live.lean` and Blanc-WETH in `Blanc/WethGas.lean`), so it
lives in the composition stratum. -/

namespace Blanc

/-! ## The deployed WETH9 against Blanc-WETH (a measurement)

| call | Blanc-WETH `wethGas` | WETH9 `weth9Gas` |
|---|---|---|
| `balanceOf`, cold key | 2260 | 2534 (+274) |
| `balanceOf`, warm key | 260 | 534 (+274) |
| `decimals()` | 158 (constant, no storage) | 2444 cold / 444 warm |

The +274 on `balanceOf` is solc 0.4's code shape, not the storage read: the
free-memory-pointer store (12), the `CALLDATASIZE < 4` fallback test (21), a
`DIV`/`AND` selector extraction instead of `SHR` (23), a linear comparison
chain (6 × 22 before the wrapper, against Blanc-WETH's four-level tree), the
`calldataload(4) & mask` decode and internal call/return (≈70), `keccak`-based
mapping addressing (42 + its two `mstore`s), and ABI encoding through the
free-memory pointer (one more word of memory).  `decimals()` differs in kind:
WETH9 keeps it in storage slot 2, so it pays an `SLOAD`. -/

theorem balanceOf_weth9_vs_weth :
    Lift.Weth9.balanceOfGas9 = balanceOfGas + 274 ∧
      Lift.Weth9.balanceOfGas9Warm = balanceOfGasWarm + 274 := by
  decide

theorem decimals_weth9_vs_weth :
    Lift.Weth9.decimalsGas9 = decimalsGas + 2286 ∧
      Lift.Weth9.decimalsGas9Warm = decimalsGas + 286 := by
  decide

end Blanc
