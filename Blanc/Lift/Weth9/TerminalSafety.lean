import Blanc.Lift.Weth9.Check
import Blanc.Lift.CallRestriction
import Blanc.ExecutionNoDelProducer

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

/-- Every function of the actual WETH9 certificate spawns only by `CALL`/`STATICCALL`. -/
theorem cert_callOnly : Blanc.Lift.Weth9.cert.callOnly = true := by
  decide +kernel

/-- The checked WETH9 runtime is no EIP-7702 delegation designator. -/
theorem code_not_delegation : ¬ isValidDelegation Blanc.Lift.Weth9.code := by
  decide +kernel

/-- Every same-frame prefix of the checked WETH9 runtime spawns only by `CALL` or
`STATICCALL`, regardless of the frame's eventual outcome and with no fork premise. -/
theorem runtime_call_or_staticcall {F node : Exec.Deriv} (hpc : F.pc = 0)
    (hcode : F.sevm.code = Blanc.Lift.Weth9.code) (hstateGas : F.sevm.benvStat.rules.stateGas = none)
    (hprefix : Exec.Deriv.ParentPrefix F node) {x : Xinst}
    (hat : Ninst.At node.sevm.code node.pc (.exec x)) :
    x = .call ∨ x = .staticcall :=
  call_or_staticcall_of_parentPrefix_noStateGas
    (code := Blanc.Lift.Weth9.code) (c := Blanc.Lift.Weth9.cert)
    Blanc.Lift.Weth9.cert_check cert_callOnly hpc hcode hstateGas hprefix hat

/-- **All-outcome no-deletion of an account holding the checked WETH9 runtime.** Under
state-gas absence and no fork premise, a complete execution keeps `Devm.NoDel wa` when `wa`'s
installed code is the checked runtime and the root, if it owns `wa`'s storage, enters that runtime
at pc `0`. Reentrant and foreign frames are covered by `Exec.inv_noDel_of_installedCert`. -/
theorem exec_noDel {wa : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (installed : pre.getCode wa = Blanc.Lift.Weth9.code)
    (root : sevm.currentTarget = wa → pc = 0 ∧ sevm.code = Blanc.Lift.Weth9.code)
    (initial : Devm.NoDel wa pre) : Execution.NoDel wa out :=
  Exec.inv_noDel_of_installedCert Blanc.Lift.Weth9.cert_check cert_callOnly cert_noSelfdestruct
    code_not_delegation run hsg installed root initial

end Blanc.Lift.Weth9
