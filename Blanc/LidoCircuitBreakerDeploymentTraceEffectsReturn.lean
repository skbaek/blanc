-- LidoCircuitBreakerDeploymentTraceEffectsReturn.lean : exact constructor return and post-frame.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBase

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private def officialConstructorReturnPre
    (sevm : Sevm) (base : Devm) (G : Nat) : Devm :=
  (officialConstructorEffectBase sevm base).setMach
    ⟨[Nat.toB256 constructorRuntimeBase, (4282 : B256)],
      officialConstructorFinalMemory, G⟩

private def officialConstructorReturnRead
    (sevm : Sevm) (base : Devm) (G : Nat) : Bytes × Devm :=
  let pre := officialConstructorReturnPre sevm base G
  (pre.setMach ⟨[], pre.memory, G⟩).memRead constructorRuntimeBase 4282

/-- Exact successful constructor post-frame at its final remaining gas. -/
def officialConstructorPost
    (sevm : Sevm) (base : Devm) (G : Nat) : Devm :=
  let returned := officialConstructorReturnRead sevm base G
  returned.2.withOutput returned.1

private theorem withMemory_setMach_same
    (base : Devm) (stack : List B256) (memory : Mem) (gas : Nat) :
    (base.setMach ⟨stack, memory, gas⟩).withMemory memory =
      base.setMach ⟨stack, memory, gas⟩ := by
  rfl

private theorem memRead_setMach_of_read
    (base : Devm) (stack : List B256) (memory : Mem)
    (gas i sz : Nat) (output : Bytes)
    (hread : memory.read i sz = (output, memory)) :
    let pre := base.setMach ⟨stack, memory, gas⟩
    (pre.setMach ⟨[], pre.memory, gas⟩).memRead i sz =
      (output, base.setMach ⟨[], memory, gas⟩) := by
  dsimp only
  unfold Devm.memRead
  simp only [Devm.memory_setMach]
  rw [hread]
  simp only [withMemory_setMach_same, Devm.setMach_setMach]

private theorem officialConstructorReturnRead_eq
    (sevm : Sevm) (base : Devm) (G : Nat) :
    officialConstructorReturnRead sevm base G =
      (lidoCircuitBreakerCode officialParams,
        (officialConstructorEffectBase sevm base).setMach
          ⟨[], officialConstructorFinalMemory, G⟩) := by
  unfold officialConstructorReturnRead officialConstructorReturnPre
  exact memRead_setMach_of_read
    (base := officialConstructorEffectBase sevm base)
    (stack := [Nat.toB256 constructorRuntimeBase, (4282 : B256)])
    (memory := officialConstructorFinalMemory) (gas := G)
    (i := constructorRuntimeBase) (sz := 4282)
    (output := lidoCircuitBreakerCode officialParams)
    officialConstructorFinalMemory_read

/-- The exact constructor post-frame is the named two-write/three-log effect
frame with empty stack, final memory, residual gas, and official runtime
output. -/
theorem officialConstructorPost_eq
    (sevm : Sevm) (base : Devm) (G : Nat) :
    officialConstructorPost sevm base G =
      ((officialConstructorEffectBase sevm base).setMach
        ⟨[], officialConstructorFinalMemory, G⟩).withOutput
          (lidoCircuitBreakerCode officialParams) := by
  unfold officialConstructorPost
  rw [officialConstructorReturnRead_eq]

theorem officialConstructorReturnLine_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[Nat.toB256 constructorRuntimeBase, (4282 : B256)], memory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 6⟩)
      (pushFixedNat 4282 :::
        pushCompactNat constructorRuntimeBase ::: rest) post := by
  unfold pushFixedNat pushCompactNat
  simp only [if_pos (show 4282 < 2 ^ 16 by decide)]
  func_run (2)
  exact hrest

theorem officialConstructorReturn_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat} :
    Func.RunCompiled fs sevm
      (officialConstructorReturnPre sevm base G) Func.ret
      (officialConstructorPost sevm base G) := by
  have hindex : (Nat.toB256 constructorRuntimeBase).toNat =
      constructorRuntimeBase := by
    apply B256.toNat_toB256_of_lt
    unfold constructorRuntimeBase constructorArgumentBytes
    decide
  have hstack : (officialConstructorReturnPre sevm base G).stack =
      [Nat.toB256 constructorRuntimeBase, (4282 : B256)] := by
    simp only [officialConstructorReturnPre, Devm.stack_setMach]
  have hext : (officialConstructorReturnPre sevm base G).extCost
      [⟨constructorRuntimeBase, 4282⟩] = 0 := by
    unfold officialConstructorReturnPre
    exact Devm.extCost_zero_of_le
      (N := officialConstructorFinalMemory)
      (i := constructorRuntimeBase) (sz := 4282)
      (by rw [officialConstructorFinalMemory_size])
      (by
        rw [officialConstructorFinalMemory_size]
        unfold constructorRuntimeBase constructorArgumentBytes
        decide)
  have hgas : (officialConstructorReturnPre sevm base G).gasLeft =
      G + (officialConstructorReturnPre sevm base G).extCost
        [⟨(Nat.toB256 constructorRuntimeBase).toNat,
          (4282 : B256).toNat⟩] := by
    rw [hindex, show (4282 : B256).toNat = 4282 by decide, hext]
    simp only [officialConstructorReturnPre, Devm.gasLeft_setMach, Nat.add_zero]
  have hread :
      ((officialConstructorReturnPre sevm base G).setMach
        ⟨[], (officialConstructorReturnPre sevm base G).memory, G⟩).memRead
          (Nat.toB256 constructorRuntimeBase).toNat (4282 : B256).toNat =
        officialConstructorReturnRead sevm base G := by
    unfold officialConstructorReturnRead
    rw [hindex, show (4282 : B256).toNat = 4282 by decide]
  have hrun := Func.runCompiled_ret
    (fs := fs) (sevm := sevm)
    (devm := officialConstructorReturnPre sevm base G)
    (i := Nat.toB256 constructorRuntimeBase) (sz := (4282 : B256))
    (s := []) (out := (officialConstructorReturnRead sevm base G).1)
    (d' := (officialConstructorReturnRead sevm base G).2) (G := G)
    hstack hgas (by simpa only [Prod.eta] using hread)
  simpa only [officialConstructorPost, Func.ret] using hrun

/-! ## Composed constructor effect suffix -/

theorem officialConstructorPost_getStor
    (sevm : Sevm) (base : Devm) (G : Nat) :
    Devm.getStor (officialConstructorPost sevm base G)
        sevm.currentTarget =
      ((Devm.getStor base sevm.currentTarget).set pauseDurationSlot
        officialConstructorArgs.initialPauseDuration).set
          heartbeatIntervalSlot
          officialConstructorArgs.initialHeartbeatInterval := by
  rw [officialConstructorPost_eq]
  change Devm.getStor (officialConstructorEffectBase sevm base)
    sevm.currentTarget = _
  exact officialConstructorEffectBase_getStor sevm base

/-- The official pause duration is readable in the raw constructor post-frame. -/
theorem officialConstructorPost_pauseDuration
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).getStorVal
        sevm.currentTarget pauseDurationSlot =
      officialConstructorArgs.initialPauseDuration := by
  change (Devm.getStor (officialConstructorPost sevm base G)
    sevm.currentTarget).get pauseDurationSlot = _
  rw [officialConstructorPost_getStor,
    Stor.get_set_ne _
      (show heartbeatIntervalSlot ≠ pauseDurationSlot by decide),
    Stor.get_set_self]

/-- The official heartbeat interval is readable in the raw constructor
post-frame. -/
theorem officialConstructorPost_heartbeatInterval
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).getStorVal
        sevm.currentTarget heartbeatIntervalSlot =
      officialConstructorArgs.initialHeartbeatInterval := by
  change (Devm.getStor (officialConstructorPost sevm base G)
    sevm.currentTarget).get heartbeatIntervalSlot = _
  rw [officialConstructorPost_getStor, Stor.get_set_self]

theorem officialConstructorPost_logs
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).logs =
      base.logs ++ officialConstructorLogs sevm.currentTarget := by
  rw [officialConstructorPost_eq]
  change (officialConstructorEffectBase sevm base).logs = _
  exact officialConstructorEffectBase_logs sevm base

/-- The successful constructor returns with an empty stack. -/
theorem officialConstructorPost_stack
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).stack = [] := by
  rw [officialConstructorPost_eq]
  rfl

private theorem withOutput_setMach_memory
    (base : Devm) (stack : List B256) (memory : Mem) (gas : Nat)
    (output : Bytes) :
    ((base.setMach ⟨stack, memory, gas⟩).withOutput output).memory =
      memory := by
  rfl

/-- The successful constructor retains the exact named final memory. -/
theorem officialConstructorPost_memory
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).memory =
      officialConstructorFinalMemory := by
  rw [officialConstructorPost_eq]
  exact withOutput_setMach_memory
    (officialConstructorEffectBase sevm base) []
    officialConstructorFinalMemory G (lidoCircuitBreakerCode officialParams)

/-- `G` is the exact residual gas after the 50,329-gas compiled run. -/
theorem officialConstructorPost_gasLeft
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).gasLeft = G := by
  rw [officialConstructorPost_eq]
  rfl

private theorem withOutput_output (base : Devm) (output : Bytes) :
    (base.withOutput output).output = output := by
  rfl

/-- The constructor's terminal output is the exact official runtime artifact. -/
theorem officialConstructorPost_output
    (sevm : Sevm) (base : Devm) (G : Nat) :
    (officialConstructorPost sevm base G).output =
      lidoCircuitBreakerCode officialParams := by
  rw [officialConstructorPost_eq]
  exact withOutput_output _ _

end LidoCircuitBreaker

end Blanc
