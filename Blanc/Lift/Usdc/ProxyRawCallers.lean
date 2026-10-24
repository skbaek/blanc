import Blanc.Lift.HistSpawnExact
import Blanc.Lift.Usdc.ProxyReachH
import Blanc.ExecutionCallerExclusion

/-! Caller and calldata provenance through raw proxy forwarding.
These results use actual entered children and do not filter by settlement. -/

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- An actual child of a raw proxy frame, called by an address different from
the proxy target, can only be the fallback DELEGATECALL. It inherits the
parent's caller, target, value and static flag, and receives the actual copied
calldata window. Neither the child nor the enclosing frame need commit. -/
theorem proxy_rawChild_inheritsH {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (codeEq : sevm.code = Proxy.code)
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    {x : Xinst} (hat : Ninst.At N.sevm.code N.pc (.exec x))
    {frame : Jaune.Frame} {resume : Resume} {child : Evm}
    (spawn : Xinst.step N.sevm N.devm x = .spawn frame resume)
    (enter : frame.enter = .run child) {pair : Adr}
    (apart : pair ≠ sevm.currentTarget) (caller : child.sta.caller = pair) :
    x = .delegatecall ∧ child.sta.currentTarget = sevm.currentTarget ∧
      child.sta.caller = sevm.caller ∧ sevm.caller = pair ∧
      child.sta.value = sevm.value ∧ child.sta.isStatic = sevm.isStatic ∧
      child.sta.data = sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0 := by
  have env : N.sevm = sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  obtain ⟨f, K, ⟨rfl, delegated⟩ | ⟨rfl, self, selector⟩⟩ :=
    proxy_nodeH run codeEq hsg bal chain hat
  · obtain ⟨_, b, gas, S, M, G, tail, state, tree, input⟩ := delegated
    change N.devm = _ at input
    rw [input] at spawn
    obtain ⟨target, inherited, value, static, data⟩ :=
      Xinst.step_delegatecall_spawn_St_noStateGas (env ▸ hsg) spawn
    obtain ⟨benv, transfer, childEq⟩ := Frame.enter_run_inv enter
    have childCaller : child.sta.caller = sevm.caller := by
      rw [childEq]
      exact inherited.trans (congrArg Sevm.caller env)
    refine ⟨rfl, ?_, childCaller, childCaller.symm.trans caller, ?_, ?_, ?_⟩
    · rw [childEq]; exact target.trans (congrArg Sevm.currentTarget env)
    · rw [childEq]; exact value.trans (congrArg Sevm.value env)
    · rw [childEq]; exact static.trans (congrArg Sevm.isStatic env)
    · rw [childEq]
      change frame.inner.data = _
      rw [data]
      have read : ((M.write 0
          (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)).read 0
          sevm.data.length.toB256.toNat).1 =
          sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0 := by
        by_cases empty : sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0 = []
        · have length := congrArg List.length empty
          simp only [List.length_sliceD, List.length_nil] at length
          rw [empty, length]
          rfl
        · simpa only [List.length_sliceD] using Mem.read_write_zero M empty
      simpa only [show (0 : B256).toNat = 0 from rfl] using read
  · have childCaller : child.sta.caller = sevm.currentTarget := by
      rw [Frame.enter_run_caller enter, Xinst.step_call_spawn_caller spawn, env]
    exact (apart (caller.symm.trans childCaller)).elim

/-- With the trace-derived calldata word bound, a raw forwarded Pair caller
has exactly the parent calldata and selector, even when the frame later reverts. -/
theorem proxy_rawChild_caller_selectorH {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (codeEq : sevm.code = Proxy.code)
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none)
    (size : sevm.data.length < 2 ^ 256)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    {x : Xinst} (hat : Ninst.At N.sevm.code N.pc (.exec x))
    {frame : Jaune.Frame} {resume : Resume} {child : Evm}
    (spawn : Xinst.step N.sevm N.devm x = .spawn frame resume)
    (enter : frame.enter = .run child) {pair : Adr}
    (apart : pair ≠ sevm.currentTarget) (caller : child.sta.caller = pair) :
    sevm.caller = pair ∧ child.sta.currentTarget = sevm.currentTarget ∧
      child.sta.data = sevm.data ∧ Blanc.Sevm.selector child.sta = Blanc.Sevm.selector sevm := by
  obtain ⟨_, target, _, parentCaller, _, _, window⟩ :=
    proxy_rawChild_inheritsH run codeEq hsg bal chain hat spawn enter apart caller
  have data : child.sta.data = sevm.data := by
    rw [window, B256.toNat_toB256_of_lt size]
    exact Bytes.sliceD_zero_length rfl
  refine ⟨parentCaller, target, data, ?_⟩
  simp only [Blanc.Sevm.selector, Sevm.dataWord, data]

end Blanc.Lift.Usdc.Proxy
