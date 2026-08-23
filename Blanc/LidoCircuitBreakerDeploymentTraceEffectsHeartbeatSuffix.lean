-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatSuffix.lean : complete heartbeat residual suffix.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatScratch

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem officialConstructorHeartbeatSuffix_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    (hcold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hcurrent : (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      ((officialConstructorPauseStoredBase sevm base).setMach
        ⟨[], officialConstructorPauseMemory, G + 23406⟩)
      officialConstructorHeartbeatSuffix
      (officialConstructorPost sevm base G) := by
  have hret := officialConstructorReturn_runCompiled
    (fs := fs) (sevm := sevm) (base := base) (G := G)
  have hreturn := officialConstructorReturnLine_runCompiled hret
  have hstore := officialConstructorHeartbeatStoreLine_runCompiled
    hcold horiginal hcurrent hstatic hreturn
  have hlog := officialConstructorHeartbeatLogLine_runCompiled hstatic hstore
  have hscratch :=
    officialConstructorHeartbeatScratchLine_runCompiled hlog
  unfold officialConstructorHeartbeatSuffix
  convert hscratch using 1

end LidoCircuitBreaker

end Blanc
