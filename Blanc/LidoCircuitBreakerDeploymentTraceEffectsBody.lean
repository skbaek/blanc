-- LidoCircuitBreakerDeploymentTraceEffectsBody.lean : initialized log and complete effect body.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsConfiguration
import Blanc.LidoCircuitBreakerDeploymentTraceEffectsInitializedLog
import Blanc.LidoCircuitBreakerDeploymentTracePatchAssembly

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorEffectBody_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hpauseCold : (sevm.currentTarget, pauseDurationSlot) ∉
      (officialConstructorPauseLoggedBase sevm base).accessedStorageKeys)
    (hpauseOriginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hpauseCurrent : (officialConstructorPauseLoggedBase sevm base).getStorVal
      sevm.currentTarget pauseDurationSlot = 0)
    (hheartbeatCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (hheartbeatOriginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hheartbeatCurrent :
      (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
        sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, G + 49961⟩)
      officialConstructorEffectBody
      (officialConstructorPost sevm base G) := by
  have hconfiguration := officialConstructorConfigurationSuffix_runCompiled
    (fs := fs) (G := G) hpauseCold hpauseOriginal hpauseCurrent
    hheartbeatCold hheartbeatOriginal hheartbeatCurrent hstatic
  have hinitialized := officialConstructorInitializedLogLine_runCompiled
    hstatic hconfiguration
  have hcopy := officialConstructorCopyPatch_runCompiled hcode hinitialized
  unfold officialConstructorEffectBody
  have hstart :
      base.setMach
          ⟨[(224 : B256), (616 : B256), (4282 : B256)],
            officialConstructorDecodedMemory,
            G + 46813 + 2163 + 985⟩ =
        base.setMach
          ⟨[(224 : B256), (616 : B256), (4282 : B256)],
            officialConstructorDecodedMemory, G + 49961⟩ := by
    congr
  rw [← hstart]
  exact hcopy

end LidoCircuitBreaker

end Blanc
