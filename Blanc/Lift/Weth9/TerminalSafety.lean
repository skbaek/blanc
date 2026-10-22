import Blanc.Lift.Weth9.Check
import Blanc.Lift.CallRestriction

/-!
# Terminal safety of the checked WETH9 runtime

The actual runtime certificate excludes SELFDESTRUCT terminals. The common
cursor proof transports this checked fact to every same-frame prefix, without
a successful-outcome premise. Child routing and deletion safety are separate.
-/

namespace Blanc.Lift.Weth9

open Jaune

/-- Every function of the actual WETH9 certificate excludes SELFDESTRUCT. -/
theorem cert_noSelfdestruct : Blanc.Lift.Weth9.cert.noSelfdestruct = true := by
  decide +kernel

/-- No same-frame prefix of the checked WETH9 runtime decodes SELFDESTRUCT,
regardless of the frame's eventual outcome. -/
theorem runtime_not_selfdestruct {F node : Exec.Deriv} (hpc : F.pc = 0)
    (hcode : F.sevm.code = Blanc.Lift.Weth9.code) (hstateGas : F.sevm.benvStat.rules.stateGas = none)
    (hprefix : Exec.Deriv.ParentPrefix F node) :
    ¬ Linst.At node.sevm.code node.pc .selfdestruct :=
  not_selfdestruct_of_parentPrefix_noStateGas
    (code := Blanc.Lift.Weth9.code) (c := Blanc.Lift.Weth9.cert)
    Blanc.Lift.Weth9.cert_check Blanc.Lift.Weth9.cert_noSelfdestruct
    hpc hcode hstateGas hprefix

end Blanc.Lift.Weth9
