import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Locks
import Blanc.Lift.WitnessFork

/-!
V- witness under every covered fork: the closed facts the transport needs (kernel only; do
not open this file in the language server).

The transport of the message-level witness (`ForkFrames.lean`, `ForkTop.lean`) needs, of each
frame the run spawns, that its entry avoids the two fork-sensitive precompiles: `MODEXP` (0x05)
and `P256VERIFY` (0x100).  Frame 0's code address is the proxy `P`; frame 1's, 2's and 3's are
`P`, `A` and `P`; the implementation frames (1 and 4) are entered through the proxy's
`DELEGATECALL`, whose code address is the implementation.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

/-- The code addresses of the frames the run spawns: the top-level proxy frame `f0`, and the
frames spawned by the proxy's `DELEGATECALL` (frame 1), the attacker's `CALL` of the proxy
(frame 3) and the proxy's `DELEGATECALL` (frame 4). -/
theorem spawned_codeAddresses :
    (f0.inner.codeAddress, cp1.f.inner.codeAddress, cp3.f.inner.codeAddress,
      cp4.f.inner.codeAddress) =
    (some proxyAddress, some implementationAddress, some proxyAddress,
      some implementationAddress) := by
  kernel_rfl

/-- The block environment every frame of the witness inherits: Prague, and no excess blob
gas. -/
theorem sevm1_block : sevm1.benvStat.fork = .prague ∧ sevm1.benvStat.excessBlobGas = 0 :=
  ⟨rfl, rfl⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top
