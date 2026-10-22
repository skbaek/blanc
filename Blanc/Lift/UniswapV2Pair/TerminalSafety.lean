import Blanc.Lift.UniswapV2Pair.Check
import Blanc.Lift.CallRestriction

/-!
# Terminal safety of the checked Uniswap V2 Pair runtime

The actual runtime certificate excludes SELFDESTRUCT terminals. The common
cursor proof transports this checked fact to every same-frame prefix, without
a successful-outcome premise. Child routing and deletion safety are separate.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Every function of the actual Uniswap V2 Pair certificate excludes SELFDESTRUCT. -/
theorem cert_noSelfdestruct : Blanc.Lift.UniswapV2Pair.cert.noSelfdestruct = true := by
  decide +kernel

/-- No same-frame prefix of the checked Uniswap V2 Pair runtime decodes SELFDESTRUCT,
regardless of the frame's eventual outcome. -/
theorem runtime_not_selfdestruct {F node : Exec.Deriv} (hpc : F.pc = 0)
    (hcode : F.sevm.code = Blanc.Lift.UniswapV2Pair.code) (hstateGas : F.sevm.benvStat.rules.stateGas = none)
    (hprefix : Exec.Deriv.ParentPrefix F node) :
    ¬ Linst.At node.sevm.code node.pc .selfdestruct :=
  not_selfdestruct_of_parentPrefix_noStateGas
    (code := Blanc.Lift.UniswapV2Pair.code) (c := Blanc.Lift.UniswapV2Pair.cert)
    Blanc.Lift.UniswapV2Pair.cert_check Blanc.Lift.UniswapV2Pair.cert_noSelfdestruct
    hpc hcode hstateGas hprefix

end Blanc.Lift.UniswapV2Pair
