-- LidoCircuitBreakerDeploymentTraceEffectsBlocksLog2.lean : reusable constructor LOG2 prefix.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBlocks

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-- Execute the deployment's 128-byte, two-topic initialized event from named
memory-read and continuation certificates. The concrete memory image and event
payload remain opaque at applications of this theorem. -/
theorem constructorEventLog2Opcode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {topic0 topic1 : B256} {data : Bytes} {memory : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter + 2149)
    (h32 : memory.size % 32 = 0)
    (hwindow : 32 + 128 ≤ memory.size)
    (hdata : (memory.read 32 128).1 = data)
    (hmemory : (memory.read 32 128).2 = memory)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((base.addLog ⟨sevm.currentTarget, [topic0, topic1], data⟩).setMach
        ⟨[], memory, Gafter⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(1 : B256) * 32, (4 : B256) * 32, topic0, topic1],
          memory, Gbefore⟩)
      (Ninst.log (Fin.succ 1) ::: rest) post := by
  rw [hgas]
  have hi : ((1 : B256) * 32).toNat = 32 := by decide
  have hsz : ((4 : B256) * 32).toNat = 128 := by decide
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_log_of
        (n := Fin.succ 1)
        (i := (1 : B256) * 32) (sz := (4 : B256) * 32)
        (topics := [topic0, topic1]) (s := [])
        (c := 2149) (G := Gafter) (M := memory) (data := data)
    · rfl
    · rfl
    · exact hstatic
    · rw [hi, hsz]
      rw [Devm.extCost_zero_of_le (N := memory) h32 hwindow]
      decide
    · simpa only [Devm.memory_setMach, hi, hsz] using hdata
    · simpa only [Devm.memory_setMach, hi, hsz] using hmemory
    · simp only [Devm.gasLeft_setMach]
  · change Func.RunCompiled fs sevm
      ((base.addLog ⟨sevm.currentTarget, [topic0, topic1], data⟩).setMach
        ⟨[], memory, Gafter⟩)
      rest post
    exact hrest

/-- Load one constructor argument as the indexed topic, push an event topic,
and prepare the fixed 128-byte initialized-event `LOG2`. Concrete memory is
represented only by read and charge certificates. -/
theorem constructorArgumentLog2Prefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {i : Fin 7} {eventTopic indexedTopic : B256} {memory : Mem}
    {indexPushCost loadCost eventPushCost : Nat}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter +
      (indexPushCost + loadCost + eventPushCost + 6))
    (hindexPush :
      pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = indexPushCost)
    (hloadCost : ∀ (S : List B256) (G : Nat),
      gVerylow +
        (base.setMach ⟨S, memory, G⟩).extCost
          [⟨32 * i.val, 32⟩] = loadCost)
    (hvalue :
      Bytes.toB256 ((memory.read (32 * i.val) 32).1) = indexedTopic)
    (hmemory : (memory.read (32 * i.val) 32).2 = memory)
    (heventPush : pushCost eventTopic.toBytes.sig = eventPushCost)
    (hlog : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[(1 : B256) * 32, (4 : B256) * 32,
            eventTopic, indexedTopic], memory, Gafter⟩)
      (Ninst.log (Fin.succ 1) ::: rest) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (loadArgumentIndex i.val +++
        pushB256 eventTopic ::: logWith 1 1 4 +++ rest) post := by
  rw [hgas]
  have hindexBound : 32 * i.val < 2 ^ 256 := by
    apply Nat.lt_trans (show 32 * i.val < 224 by
      have hi := i.isLt
      omega)
    decide
  have hindex : (Nat.toB256 (32 * i.val)).toNat = 32 * i.val :=
    B256.toNat_toB256_of_lt hindexBound
  unfold loadArgumentIndex pushCompactNat logWith
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256
        (c := indexPushCost)
        (G := Gafter + (loadCost + eventPushCost + 6))
        hindexPush
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * i.val))
          (v := indexedTopic) (s := []) (M := memory)
          (c := loadCost) (G := Gafter + (eventPushCost + 6))
      · simp only [Devm.stack_setMach]
      · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach, hindex] using
          hloadCost [Nat.toB256 (32 * i.val)]
            (Gafter + (loadCost + eventPushCost + 6))
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushB256
            (c := eventPushCost) (G := Gafter + 6) heventPush
        · simp only [Devm.gasLeft_setMach]
          omega
        · simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
      · apply Func.RunCompiled.next
        · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter + 3)
          · decide
          · simp only [Devm.gasLeft_setMach]
          · simp only [Devm.stack_setMach, List.length_cons,
              List.length_nil]
            omega
        · apply Func.RunCompiled.next
          · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter)
            · decide
            · simp only [Devm.gasLeft_setMach]
            · simp only [Devm.stack_setMach, List.length_cons,
                List.length_nil]
              omega
          · simpa only [prepend, Devm.setMach_setMach,
              Devm.stack_setMach, Devm.memory_setMach] using hlog

end LidoCircuitBreaker

end Blanc
