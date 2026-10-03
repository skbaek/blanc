import Blanc.Lift.VyperNonreentrantDeployed.Concrete.Fixture

/-!
Kernel-stepping pilot, task 3: the exact 45-byte proxy's eleven childless
steps (pc 0 to its `DELEGATECALL` at pc 31) on concrete 132-byte
`remove_liquidity` calldata, checked by kernel evaluation of `Evm.step`
through `stepN`.  Compare `ProxyEntry.proxy_prefix` (symbolic, general calldata).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Concrete

open Jaune Blanc.ConcreteRun


end Blanc.Lift.VyperNonreentrantDeployed.Concrete
