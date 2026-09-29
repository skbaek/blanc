import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Run
import Blanc.Lift.WitnessFork

/-!
V- as an admitted transaction under every covered fork: the closed facts the transport needs
(kernel only; do not open this file in the language server).

The transport of the transaction's message-level run (`Fork.lean`, the frame modules) needs, of
each frame the run spawns, that its entry avoids the two fork-sensitive precompiles: `MODEXP`
(0x05) and `P256VERIFY` (0x100).  The top-level frame's code address is the dispatcher attacker
`A'`; the frames spawned by `A'`'s `CALL`s are the pool proxy `P`; the frames spawned by the
proxy's `DELEGATECALL`s run the implementation.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- The code addresses of the frames the run spawns: the top-level frame `f0C` (`A'`), the proxy
frames `cp0C` (frame 1) and `cp4C` (frame 4), and the implementation frames `cp2C` (frame 2) and
`cp5C` (frame 5). -/
theorem spawned_codeAddressesC :
    (f0C.inner.codeAddress, cp0C.f.inner.codeAddress, cp2C.f.inner.codeAddress,
      cp4C.f.inner.codeAddress, cp5C.f.inner.codeAddress) =
    (some a2Address, some proxyAddress, some implementationAddress, some proxyAddress,
      some implementationAddress) := by
  kernel_rfl

theorem msgC_stat : msgC.benv.stat = benvStatTx := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
