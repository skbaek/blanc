import Blanc.Lift.VyperNonreentrantDeployed.Concrete.Fixture

/-!
Kernel-stepping pilot, task 3: the exact 45-byte proxy's eleven childless
steps (pc 0 to its `DELEGATECALL` at pc 31) on concrete 132-byte
`remove_liquidity` calldata, checked by kernel evaluation of `Evm.step`
through `stepN`.  Compare `ProxyEntry.proxy_prefix` (symbolic, general calldata).
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

end Blanc.Lift.VyperNonreentrantDeployed.Concrete
