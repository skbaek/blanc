import Blanc.Lift.VyperNonreentrantDeployed.ProxyEntry

/-! Native return/revert tail of the exact deployed Vyper proxy. -/

namespace Blanc.Lift.VyperNonreentrantDeployed

open Jaune

private theorem tail_at_returndatasize_32 :
    Ninst.At proxyCode 32 (.reg .returndatasize) := by rfl

private theorem tail_at_dup3_33 :
    Ninst.At proxyCode 33 (.reg (.dup 2)) := by rfl

private theorem tail_at_dup1_34 :
    Ninst.At proxyCode 34 (.reg (.dup 0)) := by rfl

private theorem tail_at_returndatacopy_35 :
    Ninst.At proxyCode 35 (.reg .returndatacopy) := by rfl

private theorem tail_at_swap1_36 :
    Ninst.At proxyCode 36 (.reg (.swap 0)) := by rfl

private theorem tail_at_returndatasize_37 :
    Ninst.At proxyCode 37 (.reg .returndatasize) := by rfl

private theorem tail_at_swap2_38 :
    Ninst.At proxyCode 38 (.reg (.swap 1)) := by rfl

private theorem tail_at_push1_39 :
    Ninst.At proxyCode 39 (.push [0x2b] (by decide)) := by rfl

private theorem tail_at_jumpi_41 :
    Jinst.At proxyCode 41 .jumpi := by rfl

private theorem tail_at_revert_42 :
    Linst.At proxyCode 42 .revert := by rfl

private theorem tail_at_jumpdest_43 :
    Jinst.At proxyCode 43 .jumpdest := by rfl

private theorem tail_at_return_44 :
    Linst.At proxyCode 44 .return_ := by rfl

private theorem tail_jumpable_43 : jumpable proxyCode 43 = true := by rfl

private theorem tail_step_dup {e : Sevm} {d : Devm} {pc : Nat}
    {n : Fin 16} {w : B256}
    (hcode : e.code = proxyCode)
    (hat : Ninst.At proxyCode pc (.reg (.dup n)))
    (hget : d.stack[n.val]? = some w)
    (hgas : gVerylow ≤ d.gasLeft) (hroom : d.stack.length < 1024) :
    Evm.step ⟨pc, e, d⟩ = .cont (pc + 1)
      (d.setMach ⟨w :: d.stack, d.memory,
        d.gasLeft - gVerylow, d.stateGas⟩) := by
  have hat' : Ninst.At e.code pc (.reg (.dup n)) := by
    rw [hcode]
    exact hat
  rw [Evm.step_next hat', Ninst.step_reg]
  change Step.ofExecution (pc + 1) (Rinst.runCore pc d e (.dup n)) = _
  rw [Rinst.runCore_dup_eq_ok hget hgas hroom]
  rfl

private theorem tail_step_swap {e : Sevm} {d : Devm} {pc : Nat}
    {n : Fin 16} {s : List B256}
    (hcode : e.code = proxyCode)
    (hat : Ninst.At proxyCode pc (.reg (.swap n)))
    (hswap : Jaune.List.swap d.stack n.val = some s)
    (hgas : gVerylow ≤ d.gasLeft) :
    Evm.step ⟨pc, e, d⟩ = .cont (pc + 1)
      (d.setMach ⟨s, d.memory,
        d.gasLeft - gVerylow, d.stateGas⟩) := by
  have hat' : Ninst.At e.code pc (.reg (.swap n)) := by
    rw [hcode]
    exact hat
  rw [Evm.step_next hat', Ninst.step_reg]
  change Step.ofExecution (pc + 1) (Rinst.runCore pc d e (.swap n)) = _
  rw [Rinst.runCore_swap_eq_ok hswap hgas]
  rfl

private theorem tail_step_copy {e : Sevm} {d : Devm} {pc : Nat}
    {di ri sz : B256} {s : List B256}
    (hcode : e.code = proxyCode)
    (hat : Ninst.At proxyCode pc (.reg .returndatacopy))
    (hstack : d.stack = di :: ri :: sz :: s)
    (hgas : gVerylow + gReturnDataCopy * ceilDiv sz.toNat 32 +
      d.extCost [⟨di.toNat, sz.toNat⟩] ≤ d.gasLeft)
    (hbound : ri.toNat + sz.toNat ≤ d.returnData.length) :
    Evm.step ⟨pc, e, d⟩ = .cont (pc + 1)
      (d.setMach ⟨s, d.memory.write di.toNat
          (d.returnData.sliceD ri.toNat sz.toNat 0),
        d.gasLeft - (gVerylow + gReturnDataCopy * ceilDiv sz.toNat 32 +
          d.extCost [⟨di.toNat, sz.toNat⟩]), d.stateGas⟩) := by
  have hat' : Ninst.At e.code pc (.reg .returndatacopy) := by
    rw [hcode]
    exact hat
  rw [Evm.step_next hat', Ninst.step_reg]
  change Step.ofExecution (pc + 1) (Rinst.runCore pc d e .returndatacopy) = _
  rw [Rinst.runCore_returndatacopy_eq_ok hstack hgas hbound]
  rfl

/-- The retained child certificate and its actual resume equation determine
the same settled child state; no independently chosen call result is admitted. -/
theorem proxy_tail_settled_of_certificate
    {e : Sevm} {pre child post : Devm}
    (desc : DelegatecallSpawnDescriptor e pre)
    (certificate : Nonempty
      (DelegatedChildCertificate desc.child (.ok child)))
    (resume : desc.resume.run (.ok child) = .ok post)
    (parentStackRoom : desc.parent.stack.length < 1024) :
    DelegatecallSettledBoundary desc child post := by
  rcases certificate with ⟨certificate⟩
  have run := desc.runCompiled_of_certificate certificate resume
  obtain ⟨child', settled⟩ := desc.settled_of_runCompiled run parentStackRoom
  rcases settled with ⟨certificate', resumed, hreturn, hstack, hstate, htra, hlogs⟩
  rcases certificate' with ⟨certificate'⟩
  have hsame : child' = child := by
    have h₁ := certificate'.result
    have h₂ := certificate.result
    exact Except.ok.inj (h₁.symm.trans h₂)
  subst child'
  exact .intro ⟨certificate'⟩ resumed hreturn hstack hstate htra hlogs

end Blanc.Lift.VyperNonreentrantDeployed
