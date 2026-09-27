import Blanc.Lift.VyperNonreentrantDeployed.Concrete.Fixture

/-!
Kernel-stepping pilot, task 3: the exact 45-byte proxy's eleven childless
steps (pc 0 to its `DELEGATECALL` at pc 31) on concrete 132-byte
`remove_liquidity` calldata, checked by kernel evaluation of `Evm.step`
through `stepN`, then the real spawn through `proxy_spawn_at_call`.
Compare `ProxyEntry.proxy_prefix` (symbolic, general calldata).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Concrete

open Jaune Blanc.ConcreteRun

/-- Pool storage plus the implementation account's code. -/
def proxyWorld : State :=
  poolState.set implementationAddress { Acct.nil with code := implementationCode }

def proxyGas : Nat := 10000000

def proxyEntryW : Evm :=
  ⟨0, proxySevm removeCalldata, implDevm proxyGas proxyWorld⟩

/-- The machine at the proxy's `DELEGATECALL`. -/
def proxyAtCall : Devm :=
  (implDevm proxyGas proxyWorld).setMach
    ⟨[(proxyGas - 54).toB256, implementationAddress.toB256, 0, (132 : Nat).toB256,
      0, 0, 0], Mem.empty.write 0 removeCalldata, proxyGas - 54, .zero⟩

set_option profiler true in
/-- Eleven continuing steps, by kernel evaluation. -/
theorem proxy_prefix_concrete :
    (stepN 11 proxyEntryW).map proj = some (proj ⟨31, proxySevm removeCalldata, proxyAtCall⟩) := by
  decide +kernel

set_option profiler true in
/-- The same run as an equation on the full machine state (kernel `rfl`). -/
theorem proxy_prefix_concrete_eq :
    stepN 11 proxyEntryW = some ⟨31, proxySevm removeCalldata, proxyAtCall⟩ := by
  kernel_rfl

theorem removeCalldata_length : removeCalldata.length = 132 := by decide +kernel

set_option profiler true in
/-- The concrete prefix followed by the real `DELEGATECALL` spawn. -/
theorem proxy_concrete_to_delegatecall :
    stepN 11 proxyEntryW = some ⟨31, proxySevm removeCalldata, proxyAtCall⟩ ∧
    ∃ desc : DelegatecallSpawnDescriptor (proxySevm removeCalldata) proxyAtCall,
      desc.resolvedCodeAddress = implementationAddress ∧
      desc.code = implementationCode ∧
      desc.child.data = removeCalldata ∧
      Evm.step ⟨31, proxySevm removeCalldata, proxyAtCall⟩ =
        .spawn (Frame.ofCall desc.child) desc.resume 32 := by
  refine ⟨proxy_prefix_concrete_eq, ?_⟩
  have himpl : proxyAtCall.state.getCode implementationAddress = implementationCode := by
    change (proxyWorld.get implementationAddress).code = implementationCode
    rw [proxyWorld, State.get_set_self]
  obtain ⟨desc, h1, h2, _, _, _, h6, _, _, _, _, h11⟩ :=
    proxy_spawn_at_call (proxySevm removeCalldata) proxyAtCall (proxyGas - 54).toB256
      rfl rfl rfl removeCalldata_length (by kernel_rfl) himpl (by decide +kernel) (by decide +kernel)
  exact ⟨desc, h1, h2, h6, h11⟩

end Blanc.Lift.VyperNonreentrantDeployed.Concrete
