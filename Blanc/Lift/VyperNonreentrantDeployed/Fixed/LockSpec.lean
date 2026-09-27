import Blanc.Lift.LockCheck

/-!
# The corrected comparator's reentrancy lock

Vyper 0.3.7's `@nonreentrant('lock')` in the Curve pool implementation
0x847e (`Fixed/Cert.lean`): one storage slot `0` shared by all seven guarded
functions, held word `2`, released word `3`.  Each guarded function checks
`PUSH1 0; SLOAD; PUSH1 2; EQ; PUSH2 0x477e; JUMPI`; the five mutating ones then
set the lock (`PUSH1 2; PUSH1 0; SSTORE`) and release it
(`PUSH1 3; PUSH1 0; SSTORE`) just before returning.  The pcs are read from the
runtime (Plans `reports/vplus-design-v1.md` §1):

| function | set `SSTORE` | body start | release `SSTORE` |
|---|---|---|---|
| `add_liquidity` | 0x0061 | 0x0062 | 0x061c |
| `exchange` | 0x068f | 0x0690 | 0x0bbd |
| `price_oracle` (view) | — | 0x1624 | — |
| `get_virtual_price` (view) | — | 0x1653 | — |
| `remove_liquidity` | 0x1bad | 0x1bae | 0x1e57 |
| `remove_liquidity_imbalance` | 0x1ea8 | 0x1ea9 | 0x2462 |
| `remove_liquidity_one_coin` | 0x2509 | 0x250a | 0x2777 |
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed

open Blanc.Lift.LockCheck

/-- The seven guarded body starts. -/
def lockBodies : List Nat := [0x0062, 0x0690, 0x1624, 0x1653, 0x1bae, 0x1ea9, 0x250a]

/-- The five mutating body starts. -/
def lockMutBodies : List Nat := [0x0062, 0x0690, 0x1bae, 0x1ea9, 0x250a]

/-- The five release `SSTORE`s. -/
def lockReleasePcs : List Nat := [0x061c, 0x0bbd, 0x1e57, 0x2462, 0x2777]

def lockSpec : Spec where
  slot := 0
  locked := 2
  bodies := lockBodies
  mutBodies := lockMutBodies
  setPcs := [0x0061, 0x068f, 0x1bad, 0x1ea8, 0x2509]
  releasePcs := lockReleasePcs

end Blanc.Lift.VyperNonreentrantDeployed.Fixed
