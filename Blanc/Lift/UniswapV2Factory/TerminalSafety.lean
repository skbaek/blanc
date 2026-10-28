import Blanc.Lift.UniswapV2Factory.CallShape
import Blanc.ExecutionNoDelProducer

/-! All-outcome terminal safety of the actual factory, including CREATE2. -/
namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc

/-- Every checked factory function excludes SELFDESTRUCT. -/
theorem cert_noSelfdestruct : cert.noSelfdestruct = true := by
  decide +kernel

/-- The factory permits CREATE2, but its checked functions never delegate. -/
theorem cert_undelegated : ∀ f ∈ cert.prog,
    f.execsSatisfy Blanc.Lift.Xinst.notDelegatecall = true := by
  decide +kernel

/-- The checked factory runtime supplies the shared transport bundle without
requiring a call-only certificate or caller-provided safety oracle. -/
theorem runtimeSafety : InstalledRuntimeSafety code :=
  InstalledRuntimeSafety.of_undelegatedCert cert_check cert_undelegated cert_noSelfdestruct
    (factorySem.not_delegation rfl) (factorySem.ne_nil rfl)

/-- Every raw node at an installed factory account excludes SELFDESTRUCT.
The collision guard prevents CREATE2 from entering that same coded account;
recursive calls and failed frames are included. -/
theorem exec_safe {wa : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (installed : pre.getCode wa = code)
    (root : sevm.currentTarget = wa → pc = 0 ∧ sevm.code = code) :
    ∀ node ∈ Exec.rawNodes run, node.sevm.currentTarget = wa →
      ¬ Linst.At node.sevm.code node.pc .selfdestruct :=
  Exec.safe_of_installedUndelegatedCert cert_check cert_undelegated cert_noSelfdestruct
    (factorySem.not_delegation rfl) run hsg installed (factorySem.ne_nil rfl) root

/-- The installed factory survives execution without scheduling its deletion.
No call-only certificate, final-code premise or assumed raw safety is used. -/
theorem exec_noDel {wa : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (installed : pre.getCode wa = code)
    (root : sevm.currentTarget = wa → pc = 0 ∧ sevm.code = code)
    (initial : Devm.NoDel wa pre) : Execution.NoDel wa out :=
  Exec.inv_noDel_of_raw_terminal_safe run hsg (exec_safe run hsg installed root) initial

end Blanc.Lift.UniswapV2Factory
