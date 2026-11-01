import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveKit
import Blanc.Lift.Curve3Pool.Walk.DispatchLive
import Blanc.Lift.Curve3Pool.Walk.ExchangeSafe

/-!
# `exchange`, forward: the dispatcher and the front of the frame

The forward twins of `xa_dispatch_exchange` and `xa_ex_front`'s segments, over the certificate's
trees: each segment builds the run of its tree from the run of the rest (continuation passing).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **The dispatcher, forward**: with the `exchange` selector, the frame's entry tree runs to the
arm's body `t_2319_c0` over the prologue's memory, at 422 gas. -/
theorem rx_dispatch_ex {sevm : Sevm} {b : Devm} {G : Nat} {Q : Outcome → Prop}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (k : SFunc.RunEx cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G)
      t_2319_c0 Q) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty (G + 422)) t_0000_c0 Q :=
  rxe_dispatch hlen hcd hsel (by kernel_rfl) (by decide) k

end Blanc.Lift.Curve3Pool
