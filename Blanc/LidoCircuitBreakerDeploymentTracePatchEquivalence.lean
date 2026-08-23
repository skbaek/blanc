-- LidoCircuitBreakerDeploymentTracePatchEquivalence.lean : patch-state normalization.
--
-- The twelve named writes are normalized once to the canonical patched memory.

import Blanc.LidoCircuitBreakerDeploymentTracePatchRun9_12

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorPatchMemory12_eq_patched :
    officialConstructorPatchMemory12 = officialConstructorPatchedMemory := by
  rfl

end LidoCircuitBreaker

end Blanc
