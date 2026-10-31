import Blanc.Lift.Curve3Pool.Walk.Dispatch

/-!
# `exchange`: the dispatcher, on the actual derivation

`xa_dispatch_exchange`: with the `exchange` selector, the frame reaches `0x2319` (the arm's body,
past its test) with empty stack, the prologue's exact memory `vyMem Mem.empty w` and the same
remaining children: `xa_dispatch` at the `exchange` selector.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The dispatcher hands `exchange` its body** (past the arm's own test), with the prologue's
exact memory and the frame's remaining children unchanged. -/
theorem xa_dispatch_exchange {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    {G : Nat} (hcode : sevm.code = code)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (h : XAt sevm post 0 (St b [] Mem.empty G) L) :
    ∃ G', XAt sevm post 0x2319 (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G') L :=
  xa_dispatch hcode hlen hcd hsel h

end Blanc.Lift.Curve3Pool
