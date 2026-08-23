-- LidoCircuitBreakerDeploymentTrace.lean : exact official constructor walk.
--
-- This compatibility facade composes the independently elaborated validation
-- and effect certificates and exposes the public successful execution API.

import Blanc.LidoCircuitBreakerDeploymentTraceValidation
import Blanc.LidoCircuitBreakerDeploymentTraceEffects

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorProgram_runCompiled
    {sevm : Sevm} {base : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
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
    Prog.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩)
      lidoCircuitBreakerConstructorProgram
      (officialConstructorPost sevm base G) := by
  have heffect := officialConstructorEffectBody_runCompiled
    (fs := lidoCircuitBreakerConstructorProgram.main ::
      lidoCircuitBreakerConstructorProgram.aux)
    (G := G) hcode hpauseCold hpauseOriginal hpauseCurrent
    hheartbeatCold hheartbeatOriginal hheartbeatCurrent hstatic
  have heffect' : Func.RunCompiled
      (lidoCircuitBreakerConstructorProgram.main ::
        lidoCircuitBreakerConstructorProgram.aux)
      sevm
      (base.setMach
        ⟨[(224 : B256), (616 : B256), (4282 : B256)],
          officialConstructorDecodedMemory, (G + 50328) - 367⟩)
      officialConstructorEffectBody
      (officialConstructorPost sevm base G) := by
    have hgas : (G + 50328) - 367 = G + 49961 := by omega
    rw [hgas]
    exact heffect
  have hmain := officialConstructorValidationPrefix_runCompiled
    (base := base) (g := G + 50328) hvalue hcode (by omega) heffect'
  apply Prog.runCompiled_intro
    (G := G + 50328)
    (mid := base.setMach ⟨[], Mem.empty, G + 50328⟩)
  · simp only [Devm.gasLeft_setMach, officialConstructorRequiredGas,
      gJumpdest]
  · simp only [Devm.stack_setMach, Devm.memory_setMach,
      Devm.setMach_setMach]
  · exact hmain

/-- The exact official constructor run from a fresh target frame. The cold and
zero-valued premises are stated on the incoming frame; the proof derives the
corresponding intermediate premises after the first logs and configuration
write. -/
theorem officialConstructorProgram_runCompiled_fresh
    {sevm : Sevm} {base : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hpauseCold : (sevm.currentTarget, pauseDurationSlot) ∉
      base.accessedStorageKeys)
    (hpauseOriginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hpauseCurrent : base.getStorVal sevm.currentTarget
      pauseDurationSlot = 0)
    (hheartbeatCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hheartbeatOriginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hheartbeatCurrent : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    Prog.RunCompiled sevm
      (base.setMach ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩)
      lidoCircuitBreakerConstructorProgram
      (officialConstructorPost sevm base G) := by
  apply officialConstructorProgram_runCompiled hvalue hcode
  · rw [officialConstructorPauseLoggedBase_accessedStorageKeys]
    exact hpauseCold
  · exact hpauseOriginal
  · rw [officialConstructorPauseLoggedBase_getStorVal]
    exact hpauseCurrent
  · rw [officialConstructorHeartbeatLoggedBase_accessedStorageKeys]
    apply not_mem_hashSet_insert hheartbeatCold
    intro hpair
    have hslots : pauseDurationSlot = heartbeatIntervalSlot :=
      congrArg Prod.snd hpair
    exact (show pauseDurationSlot ≠ heartbeatIntervalSlot by decide) hslots
  · exact hheartbeatOriginal
  · change (Devm.getStor
      (officialConstructorHeartbeatLoggedBase sevm base)
        sevm.currentTarget).get heartbeatIntervalSlot = 0
    rw [officialConstructorHeartbeatLoggedBase_getStor,
      Stor.get_set_ne _
        (show pauseDurationSlot ≠ heartbeatIntervalSlot by decide)]
    exact hheartbeatCurrent
  · exact hstatic

/-- The gas-exact fresh-frame run executes against the complete official code
image: the compiled constructor prefix followed by the runtime template and
the seven-word ABI suffix observed by `CODESIZE` and `CODECOPY`. -/
theorem officialConstructor_exec_fresh
    {sevm : Sevm} {base : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
    (hcode : sevm.code.toList = officialFullCreateInput)
    (hpauseCold : (sevm.currentTarget, pauseDurationSlot) ∉
      base.accessedStorageKeys)
    (hpauseOriginal : getOrigStorVal sevm sevm.currentTarget
      pauseDurationSlot = 0)
    (hpauseCurrent : base.getStorVal sevm.currentTarget
      pauseDurationSlot = 0)
    (hheartbeatCold : (sevm.currentTarget, heartbeatIntervalSlot) ∉
      base.accessedStorageKeys)
    (hheartbeatOriginal : getOrigStorVal sevm sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hheartbeatCurrent : base.getStorVal sevm.currentTarget
      heartbeatIntervalSlot = 0)
    (hstatic : sevm.isStatic = false) :
    exec ⟨0, sevm,
        base.setMach ⟨[], Mem.empty, G + officialConstructorRequiredGas⟩⟩ =
      .ok (officialConstructorPost sevm base G) := by
  apply Prog.exec_of_runCompiled_appended
    (pfxCode := lidoCircuitBreakerInitPrefix)
    (sfxData := runtimeTemplateCode ++
      abiEncodeConstructorArgs officialConstructorArgs)
    (officialConstructorProgram_runCompiled_fresh hvalue hcode
      hpauseCold hpauseOriginal hpauseCurrent hheartbeatCold
      hheartbeatOriginal hheartbeatCurrent hstatic)
  · exact lidoCircuitBreakerConstructorProgram_compile.symm
  · rw [hcode, officialFullCreateInput_eq_layout, List.append_assoc]

end LidoCircuitBreaker

end Blanc
