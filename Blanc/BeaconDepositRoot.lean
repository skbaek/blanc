import Blanc.BeaconDepositRootMemory

/-!
# Beacon deposit root-fold compiled carriers

The executable root fold shifts its count register, advances its height, and
feeds a staged 64-byte pair through the warm SHA-256 precompile on every
iteration.  These carriers isolate the common 285-gas hash/continuation tail
from the live and dead staging arms.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- State-dependent cost of one root-fold storage read. -/
def rootSloadCost (sevm : Sevm) (base : Devm) (key : B256) : Nat :=
  if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      base.accessedStorageKeys then
    gasWarmAccess
  else
    gasColdSload

/-- Meta-state after one root-fold storage read. -/
def rootAfterSload (sevm : Sevm) (base : Devm) (key : B256) : Devm :=
  if (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
      base.accessedStorageKeys then
    base
  else
    addAccessedStorageKey base sevm.currentTarget key

private lemma root_addAccessedStorageKey_setMach_setMach
    {base : Devm} {target : Adr} {key : B256} {mach mach' : Mach} :
    (addAccessedStorageKey (base.setMach mach) target key).setMach mach' =
      (addAccessedStorageKey base target key).setMach mach' := rfl

/-- One storage read with its warm/cold choice confined to the carrier. -/
theorem rootSload_runCompiled
    {sevm : Sevm} {base : Devm} {key value : B256}
    {stack : List B256} {memory : Mem} {G : Nat}
    (hvalue : base.getStorVal sevm.currentTarget key = value)
    (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm
      (base.setMach
        ⟨key :: stack, memory, G + rootSloadCost sevm base key⟩)
      sload
      ((rootAfterSload sevm base key).setMach
        ⟨value :: stack, memory, G⟩) := by
  by_cases hwarm :
      (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
        base.accessedStorageKeys
  · rw [rootSloadCost, if_pos hwarm, rootAfterSload, if_pos hwarm]
    exact Ninst.runCompiled_sload_warm
      (k := key) (v := value) (s := stack) (G := G)
      rfl hwarm hvalue
      (by simp only [Devm.gasLeft_setMach, gasWarmAccess])
      hroom
  · rw [rootSloadCost, if_neg hwarm, rootAfterSload, if_neg hwarm]
    simpa only [root_addAccessedStorageKey_setMach_setMach,
      Devm.memory_setMach] using
      (Ninst.runCompiled_sload_cold
        (sevm := sevm)
        (devm := base.setMach
          ⟨key :: stack, memory, G + gasColdSload⟩)
        (k := key) (v := value) (s := stack) (G := G)
        rfl hwarm
        (by simpa only [Devm.getStorVal_setMach] using hvalue)
        (by simp only [Devm.gasLeft_setMach, gasColdSload])
        hroom)

private lemma Bytes.sliceD_writeAt_after_root
    (bs xs : Bytes) (start len n : Nat)
    (h : n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt]
  rw [if_neg]
  omega

private theorem rootStageLoadedLeft_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {rest : Func} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
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
  have hsize32 : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hsize1 : M1.size = 672 := by
    dsimp only [M1]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hmem.size_eq]
      omega), hmem.size_eq]
  have hreads1 : Mem.Reads M1
      (Bytes.writeAt hmem.image 0 left.toBytes) := by
    dsimp only [M1]
    exact Mem.Reads.write hmem.wf hmem.reads 0 _
  have hnodeRead : Bytes.toB256 (M1.read 640 32).1 = node := by
    rw [Mem.Reads.read hreads1]
    rw [Bytes.sliceD_writeAt_after_root _ _ _ _ _ (by
      rw [B256.length_toBytes]
      omega)]
    rw [hmem.node_read, B256.toB256_toBytes]
  have hnodeMem : (M1.read 640 32).2 = M1 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hsize1]
    · rw [hsize1]
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
          · rw [hsize1]
          · rw [hsize1]
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
        (by rw [hsize1])
        (by
          rw [hsize1]
          decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, M1,
    show (32 : B256).toNat = 32 by decide +kernel] using htail

private theorem rootLiveLoad_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height left : B256} {stack : List B256}
    {K : Nat} {rest : Func} {ex : Execution}
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      ((rootAfterSload sevm base (branchBase + height)).setMach
        ⟨left :: height :: stack, memory, K + 17⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + rootSloadCost sevm base (branchBase + height)⟩)
      (dup 0 ::: pushB256 branchBase ::: add ::: sload ::: rest) ex := by
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup (n := 0) (w := height)
      (G := K + 23 + rootSloadCost sevm base (branchBase + height))
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := branchBase) (c := 3)
      (G := K + 20 + rootSloadCost sevm base (branchBase + height))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
      (cost := gVerylow) (x := branchBase) (y := height)
      (v := branchBase + height) (s := height :: stack)
      (G := K + 17 + rootSloadCost sevm base (branchBase + height))
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  exact Func.RunCompiledTo.next
    (rootSload_runCompiled hval
      (by simp only [List.length_cons]; omega))
    htail

/-- Stage one live root-fold pair.  The fixed work costs 26 gas in addition to
the state-dependent storage read. -/
theorem rootLiveStage_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      ((rootAfterSload sevm base (branchBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + rootSloadCost sevm base (branchBase + height)⟩)
      rootLiveStep ex := by
  apply rootLiveLoad_runCompiledTo hval hroom
  apply rootStageLoadedLeft_runCompiledTo hmem hroom
  exact htail

private theorem rootStageNodeLeft_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {G : Nat} {rest : Func} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory.write 0 node.toBytes, G⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, G + 11⟩)
      (loadWord nodeWord +++ mstoreAt 0 +++ rest) ex := by
  have hsize32 : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hnodeRead : Bytes.toB256 (memory.read 640 32).1 = node := by
    rw [hmem.read_node, B256.toB256_toBytes]
  have hnodeMem : (memory.read 640 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hsize32
    · rw [hmem.size_eq]
  simp only [loadWord, mstoreAt, prepend,
    show (nodeWord * 32 : B256) = 640 by decide +kernel,
    show (0 * 32 : B256) = 0 by decide +kernel]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 640) (c := 3) (G := G + 8)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := 640) (v := node) (s := height :: stack)
      (c := 3) (G := G + 5) (M := memory)
      rfl
      (by
        have hext :
            (base.setMach
              ⟨(640 : B256) :: height :: stack, memory, G + 8⟩).extCost
                [⟨(640 : B256).toNat, 32⟩] = 0 := by
          apply Devm.extCost_zero_of_le
          · exact hsize32
          · rw [hmem.size_eq]
            decide +kernel
        rw [hext]
        decide)
      hnodeRead hnodeMem
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 0) (c := 2) (G := G + 3)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := 0) (v := node) (s := height :: stack)
      (G := G) (e := 0)
      rfl
      (Devm.extCost_zero_of_le hsize32 (by
        rw [hmem.size_eq]
        decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach,
    show (0 : B256).toNat = 0 by decide +kernel] using htail

private theorem rootDeadLoadRight_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height right : B256}
    {stack : List B256} {K : Nat} {rest : Func} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hval : base.getStorVal sevm.currentTarget
      (zeroHashBase + height) = right)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      ((rootAfterSload sevm base (zeroHashBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 node.toBytes).write 32 right.toBytes, K⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory.write 0 node.toBytes,
          K + 15 + rootSloadCost sevm base (zeroHashBase + height)⟩)
      (dup 0 ::: pushB256 zeroHashBase ::: add ::: sload :::
        mstoreAt 1 +++ rest) ex := by
  let M1 := memory.write 0 node.toBytes
  have hsize1 : M1.size = 672 := by
    dsimp only [M1]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hmem.size_eq]
      omega), hmem.size_eq]
  simp only [mstoreAt, prepend,
    show (1 * 32 : B256) = 32 by decide +kernel]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup (n := 0) (w := height)
      (G := K + 12 + rootSloadCost sevm base (zeroHashBase + height))
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := zeroHashBase) (c := 3)
      (G := K + 9 + rootSloadCost sevm base (zeroHashBase + height))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
      (cost := gVerylow) (x := zeroHashBase) (y := height)
      (v := zeroHashBase + height) (s := height :: stack)
      (G := K + 6 + rootSloadCost sevm base (zeroHashBase + height))
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  have hsload : Ninst.RunCompiled sevm
      (base.setMach
        ⟨(zeroHashBase + height) :: height :: stack,
          M1, K + 6 + rootSloadCost sevm base (zeroHashBase + height)⟩)
      sload
      ((rootAfterSload sevm base (zeroHashBase + height)).setMach
        ⟨right :: height :: stack, M1, K + 6⟩) :=
    rootSload_runCompiled hval
      (by simp only [List.length_cons]; omega)
  refine Func.RunCompiledTo.next hsload ?_
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 32) (c := 3) (G := K + 3)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := 32) (v := right) (s := height :: stack)
      (G := K) (e := 0)
      rfl
      (Devm.extCost_zero_of_le
        (by rw [hsize1])
        (by
          rw [hsize1]
          decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, M1,
    show (32 : B256).toNat = 32 by decide +kernel] using htail

/-- Stage one dead root-fold pair.  The fixed work costs 26 gas in addition to
the state-dependent storage read. -/
theorem rootDeadStage_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height right : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hval : base.getStorVal sevm.currentTarget
      (zeroHashBase + height) = right)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      ((rootAfterSload sevm base (zeroHashBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 node.toBytes).write 32 right.toBytes, K⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + rootSloadCost sevm base (zeroHashBase + height)⟩)
      rootDeadStep ex := by
  let C := rootSloadCost sevm base (zeroHashBase + height)
  have hload : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory.write 0 node.toBytes, K + 15 + C⟩)
      (dup 0 ::: pushB256 zeroHashBase ::: add ::: sload :::
        mstoreAt 1 +++ sha64 0 nodeWord (.call rootContinuationSlot)) ex :=
    rootDeadLoadRight_runCompiledTo hmem hval hroom htail
  have hstage := rootStageNodeLeft_runCompiledTo
    (G := K + 15 + C) hmem hroom hload
  have hgas : K + 15 + C + 11 = K + 26 + C := by omega
  rw [hgas] at hstage
  simpa only [rootDeadStep, C] using hstage

/-- Shift word 19, increment the loop height, and re-enter `rootLoop` in
exactly 36 gas. -/
theorem rootContinuation_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {height size : B256} {K : Nat} {ex : Execution}
    (hmod : memory.size % 32 = 0)
    (hsize : 640 ≤ memory.size)
    (hread : Bytes.toB256 (memory.read 608 32).1 = size)
    (hloop : fs[rootLoopSlot]? = some rootLoop)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[height + 1], memory.write 608 (size >>> 1).toBytes, K⟩)
      rootLoop ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[height], memory, K + 36⟩)
      rootContinuation ex := by
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by
    decide +kernel
  have hpushOff :
      pushCost (shiftedSizeWord * 32).toBytes.sig = gVerylow := by
    decide +kernel
  unfold rootContinuation loadWord mstoreAt
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow) (G := K + 33)
      hpushOff
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := shiftedSizeWord * 32) (v := size) (s := [height])
      (c := gVerylow) (G := K + 30) (M := memory)
      rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by rw [hoff]; omega)]
        omega)
      (by
        rw [Devm.memory_setMach, hoff]
        exact hread)
      (by
        rw [Devm.memory_setMach, hoff,
          Mem.read_snd_eq_self (memExtSize_of_le hmod (by omega))])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := (1 : B256)) (c := gVerylow) (G := K + 27)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary
      (r := .shr) (f := fun x y => y >>> x.toNat)
      (cost := gVerylow) (G := K + 24)
      (x := (1 : B256)) (y := size) (v := size >>> 1)
      (s := [height])
      (by rintro ⟨⟩) rfl rfl
      (by simp only [show (1 : B256).toNat = 1 by decide +kernel])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := shiftedSizeWord * 32) (c := gVerylow) (G := K + 21)
      hpushOff
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mstore_of
      (i := shiftedSizeWord * 32) (v := size >>> 1)
      (s := [height]) (G := K + 18) (e := 0)
      rfl
      (Devm.extCost_zero_of_le hmod (by rw [hoff]; omega))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simp only [Devm.setMach_setMach, hoff]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := (1 : B256)) (c := gVerylow) (G := K + 15)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary
      (r := .add) (f := (· + ·))
      (cost := gVerylow) (G := K + 12)
      (x := (1 : B256)) (y := height) (v := height + 1)
      (s := [])
      (by rintro ⟨⟩) rfl rfl
      (B256.add_comm (xs := (1 : B256)) (ys := height))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_call' (G := K) hloop
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest])
    (by
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach] using htail)

/-- Run the shared SHA-256 and continuation tail from a staged pair.

The continuation hypothesis begins at the next `rootLoop` entry.  The exposed
memory carrier records the digest in word 20 before word 19 is shifted.
-/
theorem rootShaTail_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {oldCount size left right height : B256} {K : Nat}
    (pair : RootPairMemoryCarrier
      base.memory oldCount size left right)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 269 < 2 ^ 256)
    (hrootContinuation :
      fs[rootContinuationSlot]? = some rootContinuation)
    (hrootLoop : fs[rootLoopSlot]? = some rootLoop) :
    ∃ callPost,
      callPost.stack = 1 :: [height] ∧
      callPost.memory = base.memory.write 640
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes ∧
      Nonempty (RootMemoryCarrier callPost.memory oldCount size
        (Bytes.sha256 (left.toBytes ++ right.toBytes))) ∧
      callPost.gasLeft = K + 85 ∧
      callPost.returnData =
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach
            ⟨[height + 1],
              callPost.memory.write 608 (size >>> 1).toBytes, K⟩)
          rootLoop ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨[height], base.memory, K + 285⟩)
          (sha64 0 nodeWord (.call rootContinuationSlot)) ex := by
  have hzero : ((0 : B256) * 32).toNat = 0 := by
    decide +kernel
  have hnode : (nodeWord * 32).toNat = 640 := by
    decide +kernel
  have hcovered : memExtsSize base.memory.size
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(nodeWord * 32).toNat, 32⟩] = base.memory.size := by
    rw [hzero, hnode, pair.size_eq]
    decide +kernel
  obtain ⟨callPost, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtput, herror, hlift⟩ :=
    sha64_success_prefix_runCompiledTo
      (fs := fs) (sevm := sevm) (base := base)
      (inputWord := 0) (outputWord := nodeWord)
      (stack := [height]) (success := .call rootContinuationSlot)
      (K := K + 48)
      hcovered hnodeleg hwarm hpre hdepth (by omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmemory' :
      callPost.memory = base.memory.write 640
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes := by
    simpa only [hzero, hnode, pair.shaInput] using hmemory
  have hreturn' :
      callPost.returnData =
        (Bytes.sha256 (left.toBytes ++ right.toBytes)).toBytes := by
    simpa only [hzero, pair.shaInput] using hreturn
  have hgas' : callPost.gasLeft = K + 85 := by
    omega
  have hcarrierBase := pair.finishHash
  have hcarrier : RootMemoryCarrier callPost.memory oldCount size
      (Bytes.sha256 (left.toBytes ++ right.toBytes)) := by
    rw [hmemory']
    exact hcarrierBase
  refine ⟨callPost, hstack, hmemory', ⟨hcarrier⟩, hgas', hreturn',
    hstorage, hcode, haddresses, hkeys,
    hlogs, houtput, herror, ?_⟩
  intro ex htail
  have hcallMod : callPost.memory.size % 32 = 0 := by
    rw [hcarrier.size_eq]
  have hcallSize : 640 ≤ callPost.memory.size := by
    rw [hcarrier.size_eq]
    omega
  have hcallRead :
      Bytes.toB256 (callPost.memory.read 608 32).1 = size := by
    rw [hcarrier.read_shiftedSize, B256.toB256_toBytes]
  have hroot : Func.RunCompiledTo fs sevm
      (callPost.setMach
        ⟨[height], callPost.memory, K + 36⟩)
      rootContinuation ex :=
    rootContinuation_runCompiledTo
      hcallMod hcallSize hcallRead hrootLoop htail
  have hsuccess : Func.RunCompiledTo fs sevm
      (callPost.setMach
        ⟨[height], callPost.memory, K + 48⟩)
      (.call rootContinuationSlot) ex := by
    exact Func.runCompiledTo_call' (G := K + 36) hrootContinuation
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest])
      (by
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hroot)
  have hwhole := hlift hsuccess
  simpa only [sha64SuccessCost_zero_node] using hwhole

end Blanc.BeaconDeposit
