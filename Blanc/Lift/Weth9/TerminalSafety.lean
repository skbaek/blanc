import Blanc.Lift.Weth9.Check
import Blanc.Lift.CallRestriction
import Blanc.ExecutionNoDelProducer
import Blanc.ExecutionNoDelTransaction
import Blanc.ExecutionNoDelHistory

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

/-- The checked WETH9 runtime is nonempty. -/
theorem code_toList_ne_nil : Blanc.Lift.Weth9.code.toList ≠ [] := by
  intro h
  have hsize : Blanc.Lift.Weth9.code.size = 0 := by
    rw [ByteArray.size_eq_length_toList, h, List.length_nil]
  exact absurd hsize (by decide +kernel)

/-- **One selected transaction keeps an account holding the checked WETH9 runtime.** Under
`stateGas = none` and no fork premise, when `wa` holds the runtime at transaction entry and was not
created in the block, the transaction never schedules `wa` for deletion and `wa` still holds the
runtime after the message and in the final state. -/
theorem transaction_noDel {wa : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : ExecutionTrace.TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = Blanc.Lift.Weth9.code)
    (notCreated : wa ∉ benv.createdAccounts) :
    wa ∉ trace.messageOut.accountsToDelete ∧ trace.messageState.getCode wa = Blanc.Lift.Weth9.code ∧
      state.getCode wa = Blanc.Lift.Weth9.code :=
  trace.noDel_of_installedCert Blanc.Lift.Weth9.cert_check cert_callOnly cert_noSelfdestruct
    code_not_delegation code_toList_ne_nil hsg installed notCreated

/-- The checked WETH9 runtime meets every fact the installed-runtime producer consumes. -/
theorem installedCert : InstalledCert Blanc.Lift.Weth9.code :=
  ⟨⟨_, Blanc.Lift.Weth9.cert_check, cert_callOnly, cert_noSelfdestruct⟩, code_not_delegation,
    code_toList_ne_nil⟩

/-- **A configured history keeps an account holding the checked WETH9 runtime.** If the
checkpoint holds the runtime at `wa`, every later state holds it, and no selected transaction
along the history schedules `wa` for deletion; per-block `stateGas = none` comes from the
history's own capability evidence, with no fork or targeting premise. -/
theorem history_noDel {wa : Adr} {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : ExecutionTrace.BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = Blanc.Lift.Weth9.code) :
    history.NoDelScheduled wa ∧ future.state.getCode wa = Blanc.Lift.Weth9.code :=
  history.noDel_of_installedCert installedCert capabilities installed

end Blanc.Lift.Weth9
