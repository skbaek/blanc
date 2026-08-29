import Blanc.BeaconDepositInsertMemory

/-!
# Beacon deposit compiled insertion walk

Exact-cost carriers for the incremented-count store, the selected insertion
loop, its branch/node SHA-256 step, and the terminal first-live branch store.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

private theorem insertionLoopBit_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hroom : stack.length < 1022)
    (hinner : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨((1 : B256) &&& shiftedSize) :: height :: stack, memory, K⟩)
      (insertionLive <?> insertionDead) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 12⟩)
      insertionLoop ex := by
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by
    decide +kernel
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hread : Bytes.toB256 (memory.read 608 32).1 = shiftedSize :=
    hmem.readShiftedSize
  have hreadMem : (memory.read 608 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hmod
    · rw [hmem.size_eq]
      omega
  simp only [insertionLoop, loadWord, prepend]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := 3) (G := K + 9)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := shiftedSizeWord * 32) (v := shiftedSize)
      (s := height :: stack) (c := 3) (G := K + 6) (M := memory)
      rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by
          rw [hoff, hmem.size_eq]
          omega)]
        decide)
      (by
        rw [Devm.memory_setMach, hoff]
        exact hread)
      (by
        rw [Devm.memory_setMach, hoff]
        exact hreadMem)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 1) (c := 3) (G := K + 3)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .and) (f := B256.and)
      (cost := gVerylow) (x := 1) (y := shiftedSize)
      (v := (1 : B256) &&& shiftedSize) (s := height :: stack)
      (G := K)
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons]; omega)) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hinner

/-- Select the live insertion arm in exactly 26 gas. -/
theorem insertionLoopLive_dispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hbit : ((1 : B256) &&& shiftedSize) ≠ 0)
    (hroom : stack.length < 1022)
    (harm : Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K⟩)
      insertionLive ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 26⟩)
      insertionLoop ex := by
  apply insertionLoopBit_runCompiledTo hmem hroom
  exact Func.runCompiledTo_branch_succ
    (w := (1 : B256) &&& shiftedSize)
    (s := height :: stack) (G := K)
    hbit rfl
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using harm)

/-- Select the dead insertion arm in exactly 25 gas. -/
theorem insertionLoopDead_dispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hbit : ((1 : B256) &&& shiftedSize) = 0)
    (hroom : stack.length < 1022)
    (harm : Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K⟩)
      insertionDead ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 25⟩)
      insertionLoop ex := by
  apply insertionLoopBit_runCompiledTo hmem hroom
  exact Func.runCompiledTo_branch_zero
    (s := height :: stack) (G := K)
    (by simp only [Devm.stack_setMach, hbit])
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using harm)

end Blanc.BeaconDeposit
