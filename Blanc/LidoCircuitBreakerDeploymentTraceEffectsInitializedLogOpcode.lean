-- LidoCircuitBreakerDeploymentTraceEffectsInitializedLogOpcode.lean : initialized LOG2 certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBlocksLog2

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorInitializedBase_eq_addLog
    (sevm : Sevm) (base : Devm) :
    officialConstructorInitializedBase sevm base =
      base.addLog
        ⟨sevm.currentTarget,
          [circuitBreakerInitializedEvent, officialParams.admin],
          officialParams.minPauseDuration.toBytes ++
            officialParams.maxPauseDuration.toBytes ++
            officialParams.minHeartbeatInterval.toBytes ++
            officialParams.maxHeartbeatInterval.toBytes⟩ := by
  rfl

theorem officialConstructorInitializedLogOpcode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(1 : B256) * 32, (4 : B256) * 32,
            circuitBreakerInitializedEvent, officialParams.admin],
          officialConstructorPatchedMemory, G + 2149⟩)
      (Ninst.log (Fin.succ 1) ::: rest) post := by
  apply constructorEventLog2Opcode_runCompiled
      (topic0 := circuitBreakerInitializedEvent)
      (topic1 := officialParams.admin)
      (data := officialParams.minPauseDuration.toBytes ++
        officialParams.maxPauseDuration.toBytes ++
        officialParams.minHeartbeatInterval.toBytes ++
        officialParams.maxHeartbeatInterval.toBytes)
      (Gafter := G)
  · omega
  · rw [officialConstructorPatchedMemory_size]
  · rw [officialConstructorPatchedMemory_size]
    decide
  · exact officialConstructorPatchedMemory_read_initializedData
  · exact officialConstructorPatchedMemory_read_initializedMemory
  · exact hstatic
  · rw [← officialConstructorInitializedBase_eq_addLog]
    exact hrest

end LidoCircuitBreaker

end Blanc
