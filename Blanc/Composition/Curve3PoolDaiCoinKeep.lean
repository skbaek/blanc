import Blanc.Lift.DaiKeep
import Blanc.Composition.Curve3PoolCoinKeep

/-!
# The pool's keep premises at a DAI coin

`dai_childKeepsAt`: a pool frame's children at an address holding DAI's certified runtime keep the
foreign world, whatever call the frame makes there. With each other coin's `ChildKeepsAt`, that gives
`PoolCoinCallsKeepToken` and the keep premises of an `exchange` frame.
-/

namespace Blanc.Composition.Curve3PoolDai

open Jaune Blanc Blanc.Lift
open Blanc.Composition.Curve3PoolCoinKeep

/-- **A pool frame's children at DAI keep the foreign world.** -/
theorem dai_childKeepsAt {sevm : Sevm} {b post : Devm} {t : Adr} (hcode : sevm.code = Curve3Pool.code)
    (hfork : CoveredFork sevm.benvStat.fork) (exc : Exec 0 sevm b (.ok post))
    (htc : b.getCode t = Dai.code) : ChildKeepsAt exc t :=
  childKeepsAt_of_keepsForeign hcode hfork exc Dai.dai_keepsForeign
    Dai.dai_code_ne Dai.dai_not_delegation htc

end Blanc.Composition.Curve3PoolDai
