-- LidoCircuitBreakerDeploymentTraceEffectsBlocks.lean : reusable opaque constructor-effect blocks.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBase

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-- Prepend an in-bounds constructor argument load and a three-gas key push to
an already-certified `SSTORE` continuation. Concrete deployment memory stays
outside this declaration; callers provide only its named read certificate. -/
theorem constructorArgumentSstorePrefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {i : Fin 7} {key value : B256} {memory : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter + 9)
    (hloadPush : pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = 3)
    (hkeyPush : pushCost key.toBytes.sig = 3)
    (h32 : memory.size % 32 = 0)
    (hwindow : 32 * i.val + 32 ≤ memory.size)
    (hvalue : Bytes.toB256 ((memory.read (32 * i.val) 32).1) = value)
    (hmemory : (memory.read (32 * i.val) 32).2 = memory)
    (hstore : Func.RunCompiled fs sevm
      (base.setMach ⟨[key, value], memory, Gafter⟩)
      (sstore ::: rest) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (loadArgumentIndex i.val +++
        pushB256 key ::: sstore ::: rest) post := by
  rw [hgas]
  have hindexBound : 32 * i.val < 2 ^ 256 := by
    apply Nat.lt_trans (show 32 * i.val < 224 by
      have hi := i.isLt
      omega)
    decide
  have hindex : (Nat.toB256 (32 * i.val)).toNat = 32 * i.val :=
    B256.toNat_toB256_of_lt hindexBound
  unfold loadArgumentIndex pushCompactNat
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter + 6)
      hloadPush
    · simp only [Devm.gasLeft_setMach]
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * i.val))
          (v := value) (s := []) (M := memory)
          (c := 3) (G := Gafter + 3)
      · simp only [Devm.stack_setMach]
      · simp only [Devm.memory_setMach, hindex]
        rw [Devm.extCost_zero_of_le (N := memory) h32 hwindow]
        decide
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
      · simp only [List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter)
          hkeyPush
        · simp only [Devm.gasLeft_setMach]
        · simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
      · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hstore

/-- Execute the deployment's 64-byte, one-topic event opcode from named
memory-read and continuation certificates. The concrete memory image and event
payload remain opaque at applications of this theorem. -/
theorem constructorEventLog1Opcode_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {topic : B256} {data : Bytes} {memory : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter + 1262)
    (h32 : memory.size % 32 = 0)
    (hwindow : officialConstructorEventScratch + 64 ≤ memory.size)
    (hdata : (memory.read officialConstructorEventScratch 64).1 = data)
    (hmemory : (memory.read officialConstructorEventScratch 64).2 = memory)
    (hstatic : sevm.isStatic = false)
    (hrest : Func.RunCompiled fs sevm
      ((base.addLog ⟨sevm.currentTarget, [topic], data⟩).setMach
        ⟨[], memory, Gafter⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[Nat.toB256 (officialConstructorEventScratch / 32) * 32,
            (2 : B256) * 32, topic], memory, Gbefore⟩)
      (Ninst.log (Fin.succ 0) ::: rest) post := by
  rw [hgas]
  have hi :
      (Nat.toB256 (officialConstructorEventScratch / 32) * 32).toNat =
        officialConstructorEventScratch := by
    rw [officialConstructorEventScratch_eq]
    decide
  have hsz : ((2 : B256) * 32).toNat = 64 := by decide
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_log_of
        (n := Fin.succ 0)
        (i := Nat.toB256 (officialConstructorEventScratch / 32) * 32)
        (sz := (2 : B256) * 32)
        (topics := [topic]) (s := [])
        (c := 1262) (G := Gafter) (M := memory) (data := data)
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
      ((base.addLog ⟨sevm.currentTarget, [topic], data⟩).setMach
        ⟨[], memory, Gafter⟩)
      rest post
    exact hrest

set_option maxRecDepth 4096 in
/-- Prepend the event topic and the two `logWith` operands to an already
certified one-topic event opcode. -/
theorem constructorEventLog1Prefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {topic : B256} {memory : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hgas : Gbefore = Gafter + 9)
    (htopicPush : pushCost topic.toBytes.sig = 3)
    (hlog : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[Nat.toB256 (officialConstructorEventScratch / 32) * 32,
            (2 : B256) * 32, topic], memory, Gafter⟩)
      (Ninst.log (Fin.succ 0) ::: rest) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (pushB256 topic :::
        logWith 0
          (Nat.toB256 (officialConstructorEventScratch / 32)) 2 +++
        rest) post := by
  rw [hgas]
  unfold logWith
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 3) (G := Gafter + 6)
      htopicPush
    · simp only [Devm.gasLeft_setMach]
    · simp only [Devm.stack_setMach, List.length_nil]
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
        · rw [officialConstructorEventScratch_eq]
          decide
        · simp only [Devm.gasLeft_setMach]
        · simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
      · simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hlog

end LidoCircuitBreaker

end Blanc
