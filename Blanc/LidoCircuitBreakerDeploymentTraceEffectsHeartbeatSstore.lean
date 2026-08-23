-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatSstore.lean : heartbeat SSTORE certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsReturn

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorHeartbeatStore_eq_effectBase
    (sevm : Sevm) (base : Devm) :
    officialConstructorColdStore sevm
        (officialConstructorHeartbeatLoggedBase sevm base)
        heartbeatIntervalSlot
        officialConstructorArgs.initialHeartbeatInterval =
      officialConstructorEffectBase sevm base := by
  rfl

theorem officialConstructorHeartbeatSstore_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hcold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      (officialConstructorHeartbeatLoggedBase sevm base).accessedStorageKeys)
    (horiginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hcurrent : (officialConstructorHeartbeatLoggedBase sevm base).getStorVal
      sevm.currentTarget heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((officialConstructorEffectBase sevm base).setMach
        ⟨[], officialConstructorFinalMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      ((officialConstructorHeartbeatLoggedBase sevm base).setMach
        ⟨[heartbeatIntervalSlot,
            officialConstructorArgs.initialHeartbeatInterval],
          officialConstructorHeartbeatMemory, G + 22100⟩)
      (sstore ::: rest) post := by
  have hrest' : Func.RunCompiled fs sevm
      ((officialConstructorColdStore sevm
          (officialConstructorHeartbeatLoggedBase sevm base)
          heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval).setMach
        ⟨[], officialConstructorHeartbeatMemory, G⟩)
      rest post := by
    rw [officialConstructorHeartbeatStore_eq_effectBase,
      officialConstructorHeartbeatMemory_eq_final]
    exact hrest
  exact officialConstructorColdStore_runCompiled hcold horiginal hcurrent
    (by unfold officialConstructorArgs; decide)
    (by simp only [gCallStipend]; omega) hstatic hrest'

end LidoCircuitBreaker

end Blanc
