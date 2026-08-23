-- LidoCircuitBreakerDeploymentTraceRuntime.lean : exact return window.
--
-- The full 4,282-byte patched-image normalization is isolated from both the
-- memory construction and the later constructor effect walk.

import Blanc.LidoCircuitBreakerDeploymentTraceFinalMemory

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

set_option maxHeartbeats 3000000 in
private theorem officialConstructorFinalImage_runtime :
    officialConstructorFinalImage.sliceD constructorRuntimeBase 4282 0 =
      lidoCircuitBreakerCode officialParams := by
  rw [← patchRuntimeTemplate_official]
  rcases constructor_immutable_word_offsets_exact with
    ⟨hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat⟩
  simp only [officialConstructorFinalImage, patchRuntimeTemplate,
    runtimeImmutablePatches, immutableParameters,
    List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    hadmin, hminPause, hmaxPause, hminHeartbeat, hmaxHeartbeat,
    ImmutableParameter.value, constructorRuntimeBase]
  decide +kernel

/-- The final `RETURN` window reads the exact official runtime artifact. -/
theorem officialConstructorFinalMemory_read_runtime :
    (officialConstructorFinalMemory.read constructorRuntimeBase 4282).1 =
      lidoCircuitBreakerCode officialParams := by
  rw [Mem.Reads.read officialConstructorFinalMemory_reads]
  exact officialConstructorFinalImage_runtime

private theorem officialConstructorFinalMemory_read_memory :
    (officialConstructorFinalMemory.read constructorRuntimeBase 4282).2 =
      officialConstructorFinalMemory := by
  apply Mem.read_snd_eq_self
  apply memExtSize_of_le
  · rw [officialConstructorFinalMemory_size]
  · rw [officialConstructorFinalMemory_size]
    unfold constructorRuntimeBase constructorArgumentBytes
    decide

/-- The terminal return window reads the exact runtime without extending the
named final memory. -/
theorem officialConstructorFinalMemory_read :
    officialConstructorFinalMemory.read constructorRuntimeBase 4282 =
      (lidoCircuitBreakerCode officialParams,
        officialConstructorFinalMemory) := by
  cases hread : officialConstructorFinalMemory.read
      constructorRuntimeBase 4282 with
  | mk out memory =>
      have hout : out = lidoCircuitBreakerCode officialParams := by
        simpa only [hread] using officialConstructorFinalMemory_read_runtime
      have hmemory : memory = officialConstructorFinalMemory := by
        simpa only [hread] using officialConstructorFinalMemory_read_memory
      simp only [hout, hmemory]

end LidoCircuitBreaker

end Blanc
