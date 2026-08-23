-- LidoCircuitBreakerDeploymentTraceEffectsConfigurationSuffix.lean : configuration suffix certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsConfigurationScratch

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorConfigurationSuffix_eq_prefix :
    officialConstructorConfigurationSuffix =
      officialConstructorConfigurationPrefix +++
        officialConstructorHeartbeatSuffix := by
  rfl

theorem officialConstructorConfigurationSuffix_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
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
      ((officialConstructorInitializedBase sevm base).setMach
        ⟨[], officialConstructorPatchedMemory, G + 46813⟩)
      officialConstructorConfigurationSuffix
      (officialConstructorPost sevm base G) := by
  have hheartbeat := officialConstructorHeartbeatSuffix_runCompiled
    (fs := fs) (G := G) hheartbeatCold hheartbeatOriginal
    hheartbeatCurrent hstatic
  have hpauseStore := officialConstructorPauseStoreLine_runCompiled
    hpauseCold hpauseOriginal hpauseCurrent hstatic hheartbeat
  have hpauseLog := officialConstructorPauseLogLine_runCompiled
    hstatic hpauseStore
  have hpauseScratch :=
    officialConstructorPauseScratchLine_runCompiled hpauseLog
  unfold officialConstructorConfigurationSuffix
    officialConstructorConfigurationPrefix
  convert hpauseScratch using 1
  simp only [List.append_assoc, prepend_append, prepend]

end LidoCircuitBreaker

end Blanc
