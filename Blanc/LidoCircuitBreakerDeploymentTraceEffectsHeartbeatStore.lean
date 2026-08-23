-- LidoCircuitBreakerDeploymentTraceEffectsHeartbeatStore.lean : heartbeat storage certificate.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsHeartbeatSstore

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

private theorem officialConstructorHeartbeatMemory_size_mod :
    officialConstructorHeartbeatMemory.size % 32 = 0 := by
  rw [officialConstructorHeartbeatMemory_size]

private theorem officialConstructorHeartbeatMemory_argument_window :
    192 + 32 ≤ officialConstructorHeartbeatMemory.size := by
  rw [officialConstructorHeartbeatMemory_size]
  decide

private theorem officialConstructorHeartbeatMemory_read_initialInterval :
    Bytes.toB256 ((officialConstructorHeartbeatMemory.read 192 32).1) =
      officialConstructorArgs.initialHeartbeatInterval := by
  simpa [officialConstructorArgumentWord] using
    officialConstructorHeartbeatMemory_read_argument ⟨6, by decide⟩

private theorem officialConstructorHeartbeatMemory_read_same :
    (officialConstructorHeartbeatMemory.read 192 32).2 =
      officialConstructorHeartbeatMemory := by
  simpa using officialConstructorHeartbeatMemory_read_argument_memory
    ⟨6, by decide⟩

private theorem officialConstructorHeartbeatStorePrefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {value : B256} {G : Nat} {rest : Func}
    (h32 : memory.size % 32 = 0)
    (hwindow : 192 + 32 ≤ memory.size)
    (hvalue : Bytes.toB256 ((memory.read 192 32).1) = value)
    (hmemory : (memory.read 192 32).2 = memory)
    (hstore : Func.RunCompiled fs sevm
      (base.setMach ⟨[heartbeatIntervalSlot, value], memory, G + 22100⟩)
      (sstore ::: rest) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 22109⟩)
      (loadArgumentIndex 6 +++
        pushB256 heartbeatIntervalSlot ::: sstore ::: rest) post := by
  have hindex : (Nat.toB256 (32 * 6)).toNat = 192 := by decide
  unfold loadArgumentIndex pushCompactNat
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := G + 22106)
    · decide
    · simp only [Devm.gasLeft_setMach]
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * 6))
          (v := value) (s := []) (M := memory)
          (c := 3) (G := G + 22103)
      · simp only [Devm.stack_setMach]
      · simp only [Devm.memory_setMach, hindex]
        rw [Devm.extCost_zero_of_le
          (N := memory) h32 hwindow]
        decide
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
      · simp only [List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushB256 (c := 3) (G := G + 22100)
        · simpa only [gVerylow] using pushCost_of_ne_zero
            (w := heartbeatIntervalSlot) (by decide +kernel)
        · simp only [Devm.gasLeft_setMach]
        · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
          omega
      · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hstore

theorem officialConstructorHeartbeatStoreLine_runCompiled
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
        ⟨[], officialConstructorHeartbeatMemory, G + 22109⟩)
      (loadArgumentIndex 6 +++
        pushB256 heartbeatIntervalSlot ::: sstore ::: rest) post := by
  apply officialConstructorHeartbeatStorePrefix_runCompiled
  · exact officialConstructorHeartbeatMemory_size_mod
  · exact officialConstructorHeartbeatMemory_argument_window
  · exact officialConstructorHeartbeatMemory_read_initialInterval
  · exact officialConstructorHeartbeatMemory_read_same
  · exact officialConstructorHeartbeatSstore_runCompiled
      hcold horiginal hcurrent hstatic hrest

end LidoCircuitBreaker

end Blanc
