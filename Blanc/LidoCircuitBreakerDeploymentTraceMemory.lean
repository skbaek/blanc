-- LidoCircuitBreakerDeploymentTraceMemory.lean : patched-memory facts.
--
-- The twelfth named write and its invariant are the canonical patched-memory
-- checkpoint, so size and image correspondence are direct projections.

import Blanc.LidoCircuitBreakerDeploymentTracePatchRun9_12

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorPatchedMemory_size :
    officialConstructorPatchedMemory.size = 4512 := by
  exact officialConstructorPatchInvariant12.memory_size

/-! ## Memory/image correspondence -/

theorem officialConstructorPatchedMemory_wf :
    Mem.Wf officialConstructorPatchedMemory := by
  exact officialConstructorPatchInvariant12.memory_wf

theorem officialConstructorPatchedMemory_reads :
    Mem.Reads officialConstructorPatchedMemory
      officialConstructorPatchedImage := by
  exact officialConstructorPatchInvariant12.memory_reads

theorem officialConstructorPatchedMemory_read_argument
    (i : Fin 7) :
    Bytes.toB256
        ((officialConstructorPatchedMemory.read (32 * i.val) 32).1) =
      officialConstructorArgumentWord i := by
  simpa only [officialConstructorPatchedMemory] using
    officialConstructorPatchInvariant12.read_argument i

end LidoCircuitBreaker

end Blanc
