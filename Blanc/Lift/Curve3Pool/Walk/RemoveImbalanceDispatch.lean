import Blanc.Lift.Curve3Pool.Walk.Dispatch

/-!
# The dispatcher hands `remove_liquidity_imbalance` its body, on the actual derivation

From the frame's start (pc `0`, empty stack and memory) with the
`remove_liquidity_imbalance` selector, the dispatcher (`xa_dispatch`) falls through the
`0x9fdaea0c` test into the arm's body at `0x304f` with the prologue's exact memory and no
remaining-children change.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The dispatcher hands `remove_liquidity_imbalance` its body** (past the arm's own
test), with the prologue's exact memory and the frame's remaining children unchanged. -/
theorem xa_dispatch_removeLiquidityImbalance {sevm : Sevm} {post b : Devm}
    {L : List Exec.Frame} {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x304f (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L :=
  xa_dispatch hcode hlen hcd hsel h

end Blanc.Lift.Curve3Pool
