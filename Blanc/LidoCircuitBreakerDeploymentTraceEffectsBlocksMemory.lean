-- LidoCircuitBreakerDeploymentTraceEffectsBlocksMemory.lean : reusable constructor-memory blocks.

import Blanc.LidoCircuitBreakerDeploymentTraceEffectsBlocks

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-- Load one constructor argument and store it at a fixed two-byte memory
coordinate. Read, write, and expansion behavior are supplied as opaque
certificates, so the theorem never normalizes a concrete deployment image. -/
theorem constructorArgumentMstorePrefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {i : Fin 7} {offset indexPushCost loadCost storeExt : Nat}
    {value : B256} {memory memory' : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hoffsetLt : offset < 2 ^ 16)
    (hgas : Gbefore =
      Gafter + (indexPushCost + loadCost + 6 + storeExt))
    (hindexPush :
      pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = indexPushCost)
    (hloadCost : ∀ (S : List B256) (G : Nat),
      gVerylow +
        (base.setMach ⟨S, memory, G⟩).extCost
          [⟨32 * i.val, 32⟩] = loadCost)
    (hvalue : Bytes.toB256 ((memory.read (32 * i.val) 32).1) = value)
    (hmemory : (memory.read (32 * i.val) 32).2 = memory)
    (hstoreExt : ∀ (S : List B256) (G : Nat),
      (base.setMach ⟨S, memory, G⟩).extCost [⟨offset, 32⟩] = storeExt)
    (hwrite : memory.write offset value.toBytes = memory')
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory', Gafter⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (loadArgumentIndex i.val +++
        storeByteOffset offset +++ rest) post := by
  rw [hgas]
  have hindexBound : 32 * i.val < 2 ^ 256 := by
    apply Nat.lt_trans (show 32 * i.val < 224 by
      have hi := i.isLt
      omega)
    decide
  have hindex : (Nat.toB256 (32 * i.val)).toNat = 32 * i.val :=
    B256.toNat_toB256_of_lt hindexBound
  have hoffsetBound : offset < 2 ^ 256 :=
    Nat.lt_trans hoffsetLt (by decide)
  have hoffsetNat :
      (Bytes.toB256
        [(offset >>> 8).toUInt8, offset.toUInt8]).toNat = offset := by
    rw [List.toB256_pair offset hoffsetLt]
    exact B256.toNat_toB256_of_lt hoffsetBound
  unfold loadArgumentIndex storeByteOffset pushCompactNat pushFixedNat
  simp only [if_pos hoffsetLt]
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256
        (c := indexPushCost)
        (G := Gafter + (loadCost + 6 + storeExt))
        hindexPush
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_mload_of
          (i := Nat.toB256 (32 * i.val))
          (v := value) (s := []) (M := memory)
          (c := loadCost) (G := Gafter + (6 + storeExt))
      · simp only [Devm.stack_setMach]
      · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach, hindex] using
          hloadCost [Nat.toB256 (32 * i.val)]
            (Gafter + (loadCost + 6 + storeExt))
      · simpa only [Devm.memory_setMach, hindex] using hvalue
      · simpa only [Devm.memory_setMach, hindex] using hmemory
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_pushBytes
            (c := 3) (G := Gafter + (3 + storeExt))
        · rfl
        · simp only [Devm.gasLeft_setMach]
          omega
        · simp only [Devm.stack_setMach, List.length_cons,
            List.length_nil]
          omega
      · apply Func.RunCompiled.next
        · apply Ninst.runCompiled_mstore_of
              (i := Bytes.toB256
                [(offset >>> 8).toUInt8, offset.toUInt8])
              (v := value) (s := []) (G := Gafter)
              (e := storeExt) (M := memory')
          · simp only [Devm.stack_setMach]
          · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
              Devm.memory_setMach, Devm.gasLeft_setMach,
              hoffsetNat] using
              hstoreExt
                [Bytes.toB256
                  [(offset >>> 8).toUInt8, offset.toUInt8], value]
                (Gafter + (3 + storeExt))
          · simp only [Devm.gasLeft_setMach, gVerylow]
          · simpa only [Devm.memory_setMach, hoffsetNat] using hwrite
        · simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach] using hrest

/-- Store a zero word at a fixed two-byte memory coordinate. The expansion
charge is named by the caller, covering both in-bounds and extending writes. -/
theorem constructorZeroMstorePrefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {offset storeExt : Nat} {memory memory' : Mem}
    {Gbefore Gafter : Nat} {rest : Func}
    (hoffsetLt : offset < 2 ^ 16)
    (hgas : Gbefore = Gafter + (8 + storeExt))
    (hstoreExt : ∀ (S : List B256) (G : Nat),
      (base.setMach ⟨S, memory, G⟩).extCost [⟨offset, 32⟩] = storeExt)
    (hwrite : memory.write offset (0 : B256).toBytes = memory')
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory', Gafter⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, Gbefore⟩)
      (pushB256 0 ::: storeByteOffset offset +++ rest) post := by
  rw [hgas]
  have hoffsetBound : offset < 2 ^ 256 :=
    Nat.lt_trans hoffsetLt (by decide)
  have hoffsetNat :
      (Bytes.toB256
        [(offset >>> 8).toUInt8, offset.toUInt8]).toNat = offset := by
    rw [List.toB256_pair offset hoffsetLt]
    exact B256.toNat_toB256_of_lt hoffsetBound
  unfold storeByteOffset pushFixedNat
  simp only [if_pos hoffsetLt]
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := 2)
        (G := Gafter + (6 + storeExt))
    · simpa only [gBase] using pushCost_zero
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · apply Func.RunCompiled.next
    · apply Ninst.runCompiled_pushBytes
          (c := 3) (G := Gafter + (3 + storeExt))
      · rfl
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [Devm.stack_setMach, List.length_cons,
          List.length_nil]
        omega
    · apply Func.RunCompiled.next
      · apply Ninst.runCompiled_mstore_of
            (i := Bytes.toB256
              [(offset >>> 8).toUInt8, offset.toUInt8])
            (v := 0) (s := []) (G := Gafter)
            (e := storeExt) (M := memory')
        · simp only [Devm.stack_setMach]
        · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach, Devm.gasLeft_setMach,
            hoffsetNat] using
            hstoreExt
              [Bytes.toB256
                [(offset >>> 8).toUInt8, offset.toUInt8], 0]
              (Gafter + (3 + storeExt))
        · simp only [Devm.gasLeft_setMach, gVerylow]
        · simpa only [Devm.memory_setMach, hoffsetNat] using hwrite
      · simpa only [prepend, Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hrest

end LidoCircuitBreaker

end Blanc
