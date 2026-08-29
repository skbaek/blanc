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

private theorem insertionStageLoadedLeft_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {rest : Func} {ex : Execution}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack,
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨left :: height :: stack, memory, K + 17⟩)
      (mstoreAt 0 +++ loadWord nodeWord +++ mstoreAt 1 +++ rest) ex := by
  let M1 := memory.write 0 left.toBytes
  have hmem1 : InsertionMemoryCarrier M1 oldCount shiftedSize node := by
    dsimp only [M1]
    exact hmem.writeBeforeRegisters 0 left.toBytes
      (by rw [B256.length_toBytes]; omega)
      (by rw [B256.length_toBytes]; omega)
  have hsize32 : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hnodeRead : Bytes.toB256 (M1.read 640 32).1 = node :=
    hmem1.readNode
  have hnodeMem : (M1.read 640 32).2 = M1 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hmem1.size_eq]
    · rw [hmem1.size_eq]
      omega
  simp only [loadWord, mstoreAt, prepend,
    show (0 * 32 : B256) = 0 by decide +kernel,
    show (nodeWord * 32 : B256) = 640 by decide +kernel,
    show (1 * 32 : B256) = 32 by decide +kernel]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 0) (c := 2) (G := K + 15)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := 0) (v := left) (s := height :: stack)
      (G := K + 12) (e := 0)
      rfl
      (Devm.extCost_zero_of_le hsize32 (by
        rw [hmem.size_eq]
        decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  change Func.RunCompiledTo fs sevm
    (base.setMach ⟨height :: stack, M1, K + 12⟩) _ ex
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 640) (c := 3) (G := K + 9)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := 640) (v := node) (s := height :: stack)
      (c := 3) (G := K + 6) (M := M1)
      rfl
      (by
        have hext :
            (base.setMach
              ⟨(640 : B256) :: height :: stack, M1, K + 9⟩).extCost
                [⟨(640 : B256).toNat, 32⟩] = 0 := by
          apply Devm.extCost_zero_of_le
          · rw [hmem1.size_eq]
          · rw [hmem1.size_eq]
            decide +kernel
        rw [hext]
        decide)
      hnodeRead hnodeMem
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 32) (c := 3) (G := K + 3)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := 32) (v := node) (s := height :: stack)
      (G := K) (e := 0)
      rfl
      (Devm.extCost_zero_of_le
        (by rw [hmem1.size_eq])
        (by rw [hmem1.size_eq]; decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, M1,
    show (32 : B256).toNat = 32 by decide +kernel] using htail

private theorem insertionDeadLoad_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height left : B256} {stack : List B256}
    {K : Nat} {rest : Func} {ex : Execution}
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      ((afterSload sevm base (branchBase + height)).setMach
        ⟨left :: height :: stack, memory, K + 17⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + sloadCost sevm base (branchBase + height)⟩)
      (dup 0 ::: pushB256 branchBase ::: add ::: sload ::: rest) ex := by
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup (n := 0) (w := height)
      (G := K + 23 + sloadCost sevm base (branchBase + height))
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := branchBase) (c := 3)
      (G := K + 20 + sloadCost sevm base (branchBase + height))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
      (cost := gVerylow) (x := branchBase) (y := height)
      (v := branchBase + height) (s := height :: stack)
      (G := K + 17 + sloadCost sevm base (branchBase + height))
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  exact Func.RunCompiledTo.next
    (Ninst.runCompiled_sload_selected hval
      (by simp only [List.length_cons]; omega))
    htail

/-- Stage one dead insertion pair.  The fixed work costs 26 gas in addition to
the state-dependent storage read. -/
theorem insertionDeadStage_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      ((afterSload sevm base (branchBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      (sha64 0 nodeWord (.call insertionContinuationSlot)) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + sloadCost sevm base (branchBase + height)⟩)
      insertionDead ex := by
  apply insertionDeadLoad_runCompiledTo hval hroom
  apply insertionStageLoadedLeft_runCompiledTo hmem hroom
  exact htail

end Blanc.BeaconDeposit
