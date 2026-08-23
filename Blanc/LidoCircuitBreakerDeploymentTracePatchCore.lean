-- LidoCircuitBreakerDeploymentTracePatchCore.lean : one constructor patch step.
--
-- This isolates the generic gas-exact read/write lemma from the concrete patch
-- states and the twelve-step patch walk.

import Blanc.LidoCircuitBreakerDeploymentTraceImages

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

theorem constructorPatchPair_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {M M' : Mem} {i : Fin 7} {offset pushGas G : Nat}
    {value : B256} {rest : Func}
    (hoffset : offset < 2 ^ 16)
    (hpush : pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = pushGas)
    (hsize : M.size = 4512)
    (hfit : offset + 32 ≤ 4512)
    (hargument : Bytes.toB256 ((M.read (32 * i.val) 32).1) = value)
    (hargumentMemory : (M.read (32 * i.val) 32).2 = M)
    (hwrite : M.write offset value.toBytes = M')
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], M', G⟩) rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + (pushGas + 9)⟩)
      (loadArgumentIndex i.val +++ storeByteOffset offset +++ rest) post := by
  have hindexBound : 32 * i.val < 2 ^ 256 := by
    apply Nat.lt_trans (show 32 * i.val < 224 by
      have hi := i.isLt
      omega)
    decide
  have hindex : (Nat.toB256 (32 * i.val)).toNat = 32 * i.val :=
    B256.toNat_toB256_of_lt hindexBound
  have hoffsetBound : offset < 2 ^ 256 := by
    apply Nat.lt_trans hoffset
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  have hoffsetNat : (Nat.toB256 offset).toNat = offset :=
    B256.toNat_toB256_of_lt hoffsetBound
  unfold loadArgumentIndex storeByteOffset pushCompactNat pushFixedNat
  simp only [if_pos hoffset]
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_pushB256 (c := pushGas) (G := G + 9) hpush
    · simp only [Devm.gasLeft_setMach]
      omega
    · simp only [Devm.stack_setMach, List.length_nil]
      omega
  · func_run (3) [3, 0]
    all_goals try rw [List.toB256_pair offset hoffset, hoffsetNat]
    case h_cost =>
      simp only [Devm.memory_setMach, Devm.stack_setMach, hindex]
      rw [Devm.extCost_zero_of_le (N := M) (i := 32 * i.val) (sz := 32)
        (by rw [hsize]) (by
          rw [hsize]
          have hi := i.isLt
          omega)]
      rfl
    case h_ext =>
      simp only [Devm.memory_setMach, Devm.stack_setMach, hindex,
        hargumentMemory]
      exact Devm.extCost_zero_of_le (N := M) (i := offset) (sz := 32)
        (by rw [hsize]) (by rw [hsize]; exact hfit)
    case a =>
      simp only [Devm.memory_setMach, Devm.stack_setMach, hindex,
        hargumentMemory, hargument, Devm.setMach_setMach]
      rw [hwrite]
      have hg : G + 9 - 9 = G := by omega
      rw [hg]
      exact hrest

theorem ConstructorPatchInvariant.runCompiled_write
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {i : Fin 7} {offset pushGas G : Nat}
    {value : B256} {rest : Func}
    (h : ConstructorPatchInvariant memory)
    (hoffset : offset < 2 ^ 16)
    (hpush : pushCost ((Nat.toB256 (32 * i.val)).toBytes.sig) = pushGas)
    (hvalue : officialConstructorArgumentWord i = value)
    (hfit : offset + 32 ≤ 4512)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory.write offset value.toBytes, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + (pushGas + 9)⟩)
      (loadArgumentIndex i.val +++ storeByteOffset offset +++ rest) post := by
  apply constructorPatchPair_runCompiled hoffset hpush h.memory_size hfit
  · rw [h.read_argument i, hvalue]
  · exact h.read_memory i
  · rfl
  · exact hrest

end LidoCircuitBreaker

end Blanc
