import Blanc.Lift.UniswapV2Pair.Check
import Blanc.Lift.CallRestriction
import Blanc.ExecutionNoDelProducer
import Blanc.ExecutionNoDelTransaction
import Blanc.ExecutionNoDelHistory

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

/-- Every function of the actual Uniswap V2 Pair certificate spawns only by `CALL`/`STATICCALL`. -/
theorem cert_callOnly : Blanc.Lift.UniswapV2Pair.cert.callOnly = true := by
  decide +kernel

/-- The checked Uniswap V2 Pair runtime is no EIP-7702 delegation designator. -/
theorem code_not_delegation : ¬ isValidDelegation Blanc.Lift.UniswapV2Pair.code := by
  decide +kernel

/-- Every same-frame prefix of the checked Uniswap V2 Pair runtime spawns only by `CALL` or
`STATICCALL`, regardless of the frame's eventual outcome and with no fork premise. -/
theorem runtime_call_or_staticcall {F node : Exec.Deriv} (hpc : F.pc = 0)
    (hcode : F.sevm.code = Blanc.Lift.UniswapV2Pair.code) (hstateGas : F.sevm.benvStat.rules.stateGas = none)
    (hprefix : Exec.Deriv.ParentPrefix F node) {x : Xinst}
    (hat : Ninst.At node.sevm.code node.pc (.exec x)) :
    x = .call ∨ x = .staticcall :=
  call_or_staticcall_of_parentPrefix_noStateGas
    (code := Blanc.Lift.UniswapV2Pair.code) (c := Blanc.Lift.UniswapV2Pair.cert)
    Blanc.Lift.UniswapV2Pair.cert_check cert_callOnly hpc hcode hstateGas hprefix hat

/-- **All-outcome no-deletion of an account holding the checked Uniswap V2 Pair runtime.** Under
state-gas absence and no fork premise, a complete execution keeps `Devm.NoDel wa` when `wa`'s
installed code is the checked runtime and the root, if it owns `wa`'s storage, enters that runtime
at pc `0`. Reentrant and foreign frames are covered by `Exec.inv_noDel_of_installedCert`. -/
theorem exec_noDel {wa : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (hsg : sevm.benvStat.rules.stateGas = none)
    (installed : pre.getCode wa = Blanc.Lift.UniswapV2Pair.code)
    (root : sevm.currentTarget = wa → pc = 0 ∧ sevm.code = Blanc.Lift.UniswapV2Pair.code)
    (initial : Devm.NoDel wa pre) : Execution.NoDel wa out :=
  Exec.inv_noDel_of_installedCert Blanc.Lift.UniswapV2Pair.cert_check cert_callOnly cert_noSelfdestruct
    code_not_delegation run hsg installed root initial

/-- The checked Uniswap V2 Pair runtime is nonempty. -/
theorem code_toList_ne_nil : Blanc.Lift.UniswapV2Pair.code.toList ≠ [] := by
  intro h
  have hsize : Blanc.Lift.UniswapV2Pair.code.size = 0 := by
    rw [ByteArray.size_eq_length_toList, h, List.length_nil]
  exact absurd hsize (by decide +kernel)

/-- **One selected transaction keeps an account holding the checked Uniswap V2 Pair runtime.** Under
`stateGas = none` and no fork premise, when `wa` holds the runtime at transaction entry and was not
created in the block, the transaction never schedules `wa` for deletion and `wa` still holds the
runtime after the message and in the final state. -/
theorem transaction_noDel {wa : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : ExecutionTrace.TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = Blanc.Lift.UniswapV2Pair.code)
    (notCreated : wa ∉ benv.createdAccounts) :
    wa ∉ trace.messageOut.accountsToDelete ∧ trace.messageState.getCode wa = Blanc.Lift.UniswapV2Pair.code ∧
      state.getCode wa = Blanc.Lift.UniswapV2Pair.code :=
  trace.noDel_of_installedCert Blanc.Lift.UniswapV2Pair.cert_check cert_callOnly cert_noSelfdestruct
    code_not_delegation code_toList_ne_nil hsg installed notCreated

/-- The checked Uniswap V2 Pair runtime meets every fact the installed-runtime producer consumes. -/
theorem installedCert : InstalledCert Blanc.Lift.UniswapV2Pair.code :=
  ⟨⟨_, Blanc.Lift.UniswapV2Pair.cert_check, cert_callOnly, cert_noSelfdestruct⟩, code_not_delegation,
    code_toList_ne_nil⟩

/-- **A configured history keeps an account holding the checked Uniswap V2 Pair runtime.** If the
checkpoint holds the runtime at `wa`, every later state holds it, and no selected transaction
along the history schedules `wa` for deletion; per-block `stateGas = none` comes from the
history's own capability evidence, with no fork or targeting premise. -/
theorem history_noDel {wa : Adr} {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : ExecutionTrace.BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = Blanc.Lift.UniswapV2Pair.code) :
    history.NoDelScheduled wa ∧ future.state.getCode wa = Blanc.Lift.UniswapV2Pair.code :=
  history.noDel_of_installedCert installedCert capabilities installed

end Blanc.Lift.UniswapV2Pair
