import Blanc.BeaconDepositRootMemory
import Blanc.BeaconDepositMemory
import Blanc.BytesWrite

/-!
# Beacon deposit root-fold compiled carriers

The executable root fold shifts its count register, advances its height, and
feeds a staged 64-byte pair through the warm SHA-256 precompile on every
iteration.  These carriers isolate the common 285-gas hash/continuation tail
from the live and dead staging arms.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

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
        ⟨key :: stack, memory, G + sloadCost sevm base key⟩)
      sload
      ((afterSload sevm base key).setMach
        ⟨value :: stack, memory, G⟩) := by
  by_cases hwarm :
      (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈
        base.accessedStorageKeys
  · rw [sloadCost, if_pos hwarm, afterSload, if_pos hwarm]
    exact Ninst.runCompiled_sload_warm
      (k := key) (v := value) (s := stack) (G := G)
      rfl hwarm hvalue
      (by simp only [Devm.gasLeft_setMach, gasWarmAccess])
      hroom
  · rw [sloadCost, if_neg hwarm, afterSload, if_neg hwarm]
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
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
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
      ((afterSload sevm base (branchBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + sloadCost sevm base (branchBase + height)⟩)
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
      ((afterSload sevm base (zeroHashBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 node.toBytes).write 32 right.toBytes, K⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory.write 0 node.toBytes,
          K + 15 + sloadCost sevm base (zeroHashBase + height)⟩)
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
      (G := K + 12 + sloadCost sevm base (zeroHashBase + height))
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := zeroHashBase) (c := 3)
      (G := K + 9 + sloadCost sevm base (zeroHashBase + height))
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
      (cost := gVerylow) (x := zeroHashBase) (y := height)
      (v := zeroHashBase + height) (s := height :: stack)
      (G := K + 6 + sloadCost sevm base (zeroHashBase + height))
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  have hsload : Ninst.RunCompiled sevm
      (base.setMach
        ⟨(zeroHashBase + height) :: height :: stack,
          M1, K + 6 + sloadCost sevm base (zeroHashBase + height)⟩)
      sload
      ((afterSload sevm base (zeroHashBase + height)).setMach
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
      ((afterSload sevm base (zeroHashBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 node.toBytes).write 32 right.toBytes, K⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 26 + sloadCost sevm base (zeroHashBase + height)⟩)
      rootDeadStep ex := by
  let C := sloadCost sevm base (zeroHashBase + height)
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

private theorem rootLoopBit_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hheight : height < (32 : B256))
    (hroom : stack.length < 1022)
    (hinner : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨((1 : B256) &&& shiftedSize) :: height :: stack, memory, K⟩)
      (rootLiveStep <?> rootDeadStep) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 38⟩)
      rootLoop ex := by
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by
    decide +kernel
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hread :
      Bytes.toB256 (memory.read 608 32).1 = shiftedSize := by
    rw [hmem.read_shiftedSize, B256.toB256_toBytes]
  have hreadMem : (memory.read 608 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hmod
    · rw [hmem.size_eq]
      omega
  simp only [rootLoop, loadWord, prepend]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup (n := 0) (w := height) (G := K + 35)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 32) (c := 3) (G := K + 32)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_swap (n := 0)
      (S := height :: (32 : B256) :: height :: stack)
      (G := K + 29)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .lt) (f := B256.ltCheck)
      (cost := gVerylow) (x := height) (y := 32) (v := 1)
      (s := height :: stack) (G := K + 26)
      (by rintro ⟨⟩) rfl rfl
      (by simp [B256.ltCheck, hheight])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.runCompiledTo_branch_succ
    (w := (1 : B256)) (s := height :: stack) (G := K + 12)
    (by decide) rfl
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
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

/-- Select the live root-fold arm from the loop dispatcher in exactly 52
gas. -/
theorem rootLoopLive_dispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hheight : height < (32 : B256))
    (hbit : ((1 : B256) &&& shiftedSize) ≠ 0)
    (hroom : stack.length < 1022)
    (harm : Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K⟩)
      rootLiveStep ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 52⟩)
      rootLoop ex := by
  apply rootLoopBit_runCompiledTo hmem hheight hroom
  exact Func.runCompiledTo_branch_succ
    (w := (1 : B256) &&& shiftedSize)
    (s := height :: stack) (G := K)
    hbit rfl
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh, gJumpdest])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using harm)

/-- Select the dead root-fold arm from the loop dispatcher in exactly 51
gas. -/
theorem rootLoopDead_dispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hheight : height < (32 : B256))
    (hbit : ((1 : B256) &&& shiftedSize) = 0)
    (hroom : stack.length < 1022)
    (harm : Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K⟩)
      rootDeadStep ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 51⟩)
      rootLoop ex := by
  apply rootLoopBit_runCompiledTo hmem hheight hroom
  exact Func.runCompiledTo_branch_zero
    (s := height :: stack) (G := K)
    (by simp only [Devm.stack_setMach, hbit])
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using harm)

/-- Select and stage one live root-fold iteration. -/
theorem rootLoopLive_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hheight : height < (32 : B256))
    (hbit : ((1 : B256) &&& shiftedSize) ≠ 0)
    (hval : base.getStorVal sevm.currentTarget
      (branchBase + height) = left)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      ((afterSload sevm base (branchBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 left.toBytes).write 32 node.toBytes, K⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 78 + sloadCost sevm base (branchBase + height)⟩)
      rootLoop ex := by
  let C := sloadCost sevm base (branchBase + height)
  have harm : Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 26 + C⟩)
      rootLiveStep ex :=
    rootLiveStage_runCompiledTo hmem hval hroom htail
  have hdispatch :=
    rootLoopLive_dispatch_runCompiledTo
      (K := K + 26 + C) hmem hheight hbit hroom harm
  have hgas : K + 26 + C + 52 = K + 78 + C := by omega
  rw [hgas] at hdispatch
  simpa only [C] using hdispatch

/-- Select and stage one dead root-fold iteration. -/
theorem rootLoopDead_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height right : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hheight : height < (32 : B256))
    (hbit : ((1 : B256) &&& shiftedSize) = 0)
    (hval : base.getStorVal sevm.currentTarget
      (zeroHashBase + height) = right)
    (hroom : stack.length < 1022)
    (htail : Func.RunCompiledTo fs sevm
      ((afterSload sevm base (zeroHashBase + height)).setMach
        ⟨height :: stack,
          (memory.write 0 node.toBytes).write 32 right.toBytes, K⟩)
      (sha64 0 nodeWord (.call rootContinuationSlot)) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨height :: stack, memory,
          K + 77 + sloadCost sevm base (zeroHashBase + height)⟩)
      rootLoop ex := by
  let C := sloadCost sevm base (zeroHashBase + height)
  have harm : Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 26 + C⟩)
      rootDeadStep ex :=
    rootDeadStage_runCompiledTo hmem hval hroom htail
  have hdispatch :=
    rootLoopDead_dispatch_runCompiledTo
      (K := K + 26 + C) hmem hheight hbit hroom harm
  have hgas : K + 26 + C + 51 = K + 77 + C := by omega
  rw [hgas] at hdispatch
  simpa only [C] using hdispatch

/-- Dispatch an inactive root loop to its finishing arm in exactly 25 gas. -/
theorem rootLoopFinish_dispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (_hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hheight : ¬ height < (32 : B256))
    (hroom : stack.length < 1022)
    (hfinish : Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K⟩)
      rootFinish ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 25⟩)
      rootLoop ex := by
  simp only [rootLoop, loadWord, prepend]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup (n := 0) (w := height) (G := K + 22)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 32) (c := 3) (G := K + 19)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_swap (n := 0)
      (S := height :: (32 : B256) :: height :: stack)
      (G := K + 16)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .lt) (f := B256.ltCheck)
      (cost := gVerylow) (x := height) (y := 32) (v := 0)
      (s := height :: stack) (G := K + 13)
      (by rintro ⟨⟩) rfl rfl
      (by simp [B256.ltCheck, hheight])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach]
  exact Func.runCompiledTo_branch_zero
    (s := height :: stack) (G := K)
    rfl
    (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh])
    (by
      simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hfinish)

/-- The concrete height-32 terminal root-loop dispatch. -/
theorem rootLoopFinish32_dispatch_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hroom : stack.length < 1022)
    (hfinish : Func.RunCompiledTo fs sevm
      (base.setMach ⟨(32 : B256) :: stack, memory, K⟩)
      rootFinish ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨(32 : B256) :: stack, memory, K + 25⟩)
      rootLoop ex := by
  exact rootLoopFinish_dispatch_runCompiledTo
    hmem (by decide +kernel) hroom hfinish

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
      hlogs, houtput, herror, _htransfer, hlift⟩ :=
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

/-! ## Terminal count mix-in memory -/

private lemma Bytes.sliceD_writeAt_congr_rootFinish
    {bs cs xs : Bytes} {len n : Nat}
    (h : bs.sliceD 0 len 0 = cs.sliceD 0 len 0) :
    (Bytes.writeAt bs n xs).sliceD 0 len 0 =
      (Bytes.writeAt cs n xs).sliceD 0 len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [Nat.zero_add]
  rw [Bytes.getD_writeAt, Bytes.getD_writeAt]
  split
  · rfl
  · have hg := congrArg (fun zs : Bytes => zs.getD i 0) h
    simpa only [Bytes.getD_sliceD_of_lt _ 0 len i hi',
      Nat.zero_add] using hg

def rootFinishStagedMemory
    (memory : Mem) (oldCount node : B256) : Mem :=
  storeLe64Memory
    ((memory.write 0 node.toBytes).write 32 (0 : B256).toBytes)
    32 oldCount

structure RootFinishMemoryCarrier
    (memory : Mem) (oldCount node : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 672
  shaInput :
    memory.data.sliceD 0 64 0 =
      node.toBytes ++ le64 oldCount.toNat ++ zeros 24

def RootMemoryCarrier.stageFinish
    {memory : Mem} {oldCount shiftedSize node : B256}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node) :
    RootFinishMemoryCarrier
      (rootFinishStagedMemory memory oldCount node) oldCount node := by
  let pair := hmem.stagePair (left := node) (right := (0 : B256))
  have hinv := storeLe64Memory_inv
    (base := 32) (word := oldCount) pair.wf pair.reads
  have hsize : (rootFinishStagedMemory memory oldCount node).size =
      672 := by
    unfold rootFinishStagedMemory
    rw [storeLe64Memory_size_of_le (by rw [pair.size_eq]; omega),
      pair.size_eq]
  have hpairImage :
      pair.image.sliceD 0 64 0 =
        node.toBytes ++ (0 : B256).toBytes := by
    have hr := Mem.Reads.read pair.reads 0 64
    calc
      pair.image.sliceD 0 64 0 =
          (((memory.write 0 node.toBytes).write 32
            (0 : B256).toBytes).read 0 64).1 := hr.symm
      _ = node.toBytes ++ (0 : B256).toBytes := pair.shaInput
  have hzero :
      (0 : B256).toBytes = zeros 8 ++ zeros 24 := by
    decide +kernel
  let explicit : Bytes := node.toBytes ++ zeros 8 ++ zeros 24
  have hexplicitLength : explicit.length = 64 := by
    simp [explicit, zeros, B256.length_toBytes]
  have hpairExplicit :
      pair.image.sliceD 0 64 0 = explicit := by
    calc
      pair.image.sliceD 0 64 0 =
          node.toBytes ++ (0 : B256).toBytes := hpairImage
      _ = node.toBytes ++ (zeros 8 ++ zeros 24) :=
        congrArg (node.toBytes ++ ·) hzero
      _ = explicit := by simp only [explicit, List.append_assoc]
  have hprefixEq :
      pair.image.sliceD 0 64 0 = explicit.sliceD 0 64 0 := by
    rw [Bytes.sliceD_zero_length hexplicitLength]
    exact hpairExplicit
  have hcongr := Bytes.sliceD_writeAt_congr_rootFinish
    (bs := pair.image) (cs := explicit)
    (xs := le64 oldCount.toNat) (len := 64) (n := 32) hprefixEq
  have hwrite :
      Bytes.writeAt explicit 32 (le64 oldCount.toNat) =
        node.toBytes ++ le64 oldCount.toNat ++ zeros 24 := by
    dsimp only [explicit]
    exact Bytes.writeAt_append_middle_at
      (pre := node.toBytes) (old := zeros 8) (suffix := zeros 24)
      (replacement := le64 oldCount.toNat) (offset := 32)
      (B256.length_toBytes node)
      (by simp [zeros, le64])
  have hdesiredLength :
      (node.toBytes ++ le64 oldCount.toNat ++ zeros 24).length = 64 := by
    simp [B256.length_toBytes, le64, zeros]
  have himage :
      (Bytes.writeAt pair.image 32 (le64 oldCount.toNat)).sliceD 0 64 0 =
        node.toBytes ++ le64 oldCount.toNat ++ zeros 24 := by
    calc
      (Bytes.writeAt pair.image 32 (le64 oldCount.toNat)).sliceD 0 64 0 =
          (Bytes.writeAt explicit 32 (le64 oldCount.toNat)).sliceD
            0 64 0 := hcongr
      _ = node.toBytes ++ le64 oldCount.toNat ++ zeros 24 := by
        rw [hwrite,
          Bytes.sliceD_zero_length hdesiredLength]
  have hread := Mem.Reads.read hinv.2 0 64
  have hinput :
      (rootFinishStagedMemory memory oldCount node).data.sliceD 0 64 0 =
        node.toBytes ++ le64 oldCount.toNat ++ zeros 24 := by
    change
      (rootFinishStagedMemory memory oldCount node).data.sliceD 0 64 0 =
        (storeLe64Image pair.image 32 oldCount).sliceD 0 64 0 at hread
    rw [storeLe64Image_eq_le64] at hread
    exact hread.trans himage
  exact ⟨storeLe64Image pair.image 32 oldCount,
    hinv.1, hinv.2, hsize, hinput⟩

private theorem rootFinishPrefix_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {G : Nat} {rest : Func}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], rootFinishStagedMemory memory oldCount node, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[height], memory, G + 138⟩)
      (pop :::
        loadWord nodeWord +++ mstoreAt 0 +++
        pushB256 0 ::: mstoreAt 1 +++
        loadWord oldCountWord +++ storeLe64At 32 +++
        rest)
      post := by
  let M1 := memory.write 0 node.toBytes
  let M2 := M1.write 32 (0 : B256).toBytes
  have hsize32 : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hnodeRead : Bytes.toB256 (memory.read 640 32).1 = node := by
    rw [hmem.read_node, B256.toB256_toBytes]
  have hnodeMem : (memory.read 640 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hsize32
    · rw [hmem.size_eq]
  have hsize1 : M1.size = 672 := by
    dsimp only [M1]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hmem.size_eq]
      omega), hmem.size_eq]
  have hsize2 : M2.size = 672 := by
    dsimp only [M2]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hsize1]
      omega), hsize1]
  have hpair := hmem.stagePair (left := node) (right := (0 : B256))
  have holdRead : Bytes.toB256 (M2.read 576 32).1 = oldCount := by
    have hr := Mem.Reads.read hpair.reads 576 32
    change M2.data.sliceD 576 32 0 = hpair.image.sliceD 576 32 0 at hr
    rw [hpair.oldCount_read] at hr
    change Bytes.toB256 (M2.data.sliceD 576 32 0) = oldCount
    rw [hr, B256.toB256_toBytes]
  have holdMem : (M2.read 576 32).2 = M2 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hsize2]
    · rw [hsize2]
      omega
  have hstore : Func.RunCompiled fs sevm
      (base.setMach ⟨[oldCount], M2, G + 111⟩)
      (storeLe64At 32 +++ rest) post := by
    apply storeLe64At32_runCompiled
    · rw [hsize2]
    · rw [hsize2]
      omega
    · simpa only [rootFinishStagedMemory, M2, M1] using hrest
  simp only [loadWord, mstoreAt, prepend,
    show (nodeWord * 32 : B256) = 640 by decide +kernel,
    show (0 * 32 : B256) = 0 by decide +kernel,
    show (1 * 32 : B256) = 32 by decide +kernel,
    show (oldCountWord * 32 : B256) = 576 by decide +kernel]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pop (G := G + 136) rfl
      (by simp only [Devm.gasLeft_setMach, gBase])) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 640) (c := 3)
      (G := G + 133)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mload_of
      (i := 640) (v := node) (s := [])
      (c := 3) (G := G + 130) (M := memory)
      rfl
      (by
        rw [Devm.extCost_zero_of_le hsize32 (by
          rw [hmem.size_eq]
          decide +kernel)]
        decide)
      hnodeRead hnodeMem
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 0) (c := 2)
      (G := G + 128)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mstore_of
      (i := 0) (v := node) (s := [])
      (G := G + 125) (e := 0)
      rfl
      (Devm.extCost_zero_of_le hsize32 (by
        rw [hmem.size_eq]
        decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simp only [Devm.setMach_setMach]
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], M1, G + 125⟩) _ post
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 0) (c := 2)
      (G := G + 123)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 32) (c := 3)
      (G := G + 120)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mstore_of
      (i := 32) (v := 0) (s := [])
      (G := G + 117) (e := 0)
      rfl
      (Devm.extCost_zero_of_le
        (by rw [hsize1])
        (by rw [hsize1]; decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      rfl) ?_
  simp only [Devm.setMach_setMach]
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], M2, G + 117⟩) _ post
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 576) (c := 3)
      (G := G + 114)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mload_of
      (i := 576) (v := oldCount) (s := [])
      (c := 3) (G := G + 111) (M := M2)
      rfl
      (by
        rw [Devm.extCost_zero_of_le
          (by rw [hsize2])
          (by rw [hsize2]; decide +kernel)]
        decide)
      holdRead holdMem
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_nil]; omega)) ?_
  simpa only [Devm.setMach_setMach] using hstore

private def rootFinishPost
    (base : Devm) (memory : Mem) (digest : B256) (G : Nat) : Devm :=
  (base.setMach
    ⟨[], memory.write 0 digest.toBytes, G⟩).withOutput digest.toBytes

private theorem rootFinishReturn_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {digest : B256} {G : Nat}
    (hsize : memory.size = 672)
    (hread : Bytes.toB256 (memory.read 640 32).1 = digest) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 16⟩)
      (loadWord nodeWord +++ mstoreAt 0 +++
        returnMemoryRange 0 32)
      (rootFinishPost base memory digest G) := by
  let Mret := memory.write 0 digest.toBytes
  have h0 : (0 : B256).toNat = 0 := by decide +kernel
  have h32 : (32 : B256).toNat = 32 := by decide +kernel
  have h640 : (640 : B256).toNat = 640 := by decide +kernel
  have hmod : memory.size % 32 = 0 := by
    rw [hsize]
  have hreadMem : (memory.read 640 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hmod
    · rw [hsize]
  have hsizeRet : Mret.size = 672 := by
    dsimp only [Mret]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, hsize]
      omega), hsize]
  simp only [loadWord, mstoreAt, returnMemoryRange, pushList, prepend]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 640) (c := 3)
      (G := G + 13)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mload_of
      (i := 640) (v := digest) (s := [])
      (c := 3) (G := G + 10) (M := memory)
      rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by
          rw [h640, hsize])]
        decide)
      (by simpa only [Devm.memory_setMach, h640] using hread)
      (by simpa only [Devm.memory_setMach, h640] using hreadMem)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 0) (c := 2)
      (G := G + 8)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_mstore_of
      (i := 0) (v := digest) (s := [])
      (G := G + 5) (e := 0) (M := Mret)
      rfl
      (Devm.extCost_zero_of_le hmod (by
        rw [h0, hsize]
        omega))
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by rfl)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 32) (c := 3)
      (G := G + 2)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiled.next
    (Ninst.runCompiled_pushB256 (w := 0) (c := 2)
      (G := G)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  let retPre := base.setMach
    ⟨[(0 : B256), (32 : B256)], Mret, G⟩
  have hext : retPre.extCost [⟨(0 : Nat), (32 : Nat)⟩] = 0 := by
    apply Devm.extCost_zero_of_le
    · rw [hsizeRet]
    · rw [hsizeRet]
      omega
  have hretRead :
      (retPre.setMach ⟨[], retPre.memory, G⟩).memRead 0 32 =
        ⟨digest.toBytes, base.setMach ⟨[], Mret, G⟩⟩ := by
    apply Prod.ext
    · change (Mret.read 0 32).1 = digest.toBytes
      simpa only [B256.length_toBytes] using
        (Mem.read_write_zero memory
          (ys := digest.toBytes)
          (by
            intro hnil
            have := B256.length_toBytes digest
            rw [hnil] at this
            simp at this))
    · change
        base.setMach ⟨[], (Mret.read 0 32).2, G⟩ =
          base.setMach ⟨[], Mret, G⟩
      rw [Mem.read_snd_eq_self
        (memExtSize_of_le (by rw [hsizeRet])
          (by rw [hsizeRet]; omega))]
  change Func.RunCompiled fs sevm retPre (.last .ret)
    (rootFinishPost base memory digest G)
  simpa only [rootFinishPost, Mret] using
    (Func.runCompiled_ret_of
      (fs := fs) (sevm := sevm) (devm := retPre)
      (i := (0 : B256)) (sz := (32 : B256)) (s := [])
      (out := digest.toBytes)
      (d' := base.setMach ⟨[], Mret, G⟩)
      (G := G) (e := 0)
      rfl
      (by simpa only [h0, h32] using hext)
      (by simp only [retPre, Devm.gasLeft_setMach, Nat.add_zero])
      (by simpa only [retPre, Devm.memory_setMach, h0, h32] using
        hretRead))

private theorem rootFinishShaReturn_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount node : B256} {G : Nat}
    (carrier : RootFinishMemoryCarrier memory oldCount node)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + 237 < 2 ^ 256) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], memory, G + 253⟩)
        (sha64 0 nodeWord
          (loadWord nodeWord +++ mstoreAt 0 +++
            returnMemoryRange 0 32))
        post ∧
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.output =
        (mixIn Bytes.sha256 node oldCount.toNat).toBytes ∧
      Bytes.toB256 post.output =
        mixIn Bytes.sha256 node oldCount.toNat ∧
      post.returnData =
        (mixIn Bytes.sha256 node oldCount.toNat).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys = base.accessedStorageKeys ∧
      post.logs = base.logs ∧
      post.error = base.error := by
  let digest := mixIn Bytes.sha256 node oldCount.toNat
  let shaBase := base.setMach ⟨[], memory, G + 253⟩
  have hzero : ((0 : B256) * 32).toNat = 0 := by decide +kernel
  have hnode : (nodeWord * 32).toNat = 640 := by decide +kernel
  have hcovered : memExtsSize shaBase.memory.size
      [⟨((0 : B256) * 32).toNat, 64⟩,
        ⟨(nodeWord * 32).toNat, 32⟩] = shaBase.memory.size := by
    rw [hzero, hnode]
    change memExtsSize memory.size [⟨0, 64⟩, ⟨640, 32⟩] = memory.size
    rw [carrier.size_eq]
    decide +kernel
  obtain ⟨callPost, _hstack, hmemory, _hgas, hreturnData,
      hstorage, hcode, haddresses, hkeys,
      hlogs, _houtput, herror, _htransfer, hlift⟩ :=
    sha64_success_prefix_runCompiledTo
      (fs := fs) (sevm := sevm) (base := shaBase)
      (inputWord := 0) (outputWord := nodeWord)
      (stack := []) (success :=
        loadWord nodeWord +++ mstoreAt 0 +++ returnMemoryRange 0 32)
      (K := G + 16) hcovered
      (by simpa only [shaBase, Devm.getCode_setMach] using hnodeleg)
      (by change (2 : Adr) ∈ base.accessedAddresses; exact hwarm)
      hpre hdepth (by omega)
      (by simp only [List.length_nil]; omega)
  have hmemory' : callPost.memory = memory.write 640 digest.toBytes := by
    simpa only [shaBase, Devm.memory_setMach, hzero, hnode,
      carrier.shaInput, digest, mixIn] using hmemory
  have hreturnData' : callPost.returnData = digest.toBytes := by
    simpa only [shaBase, Devm.memory_setMach, hzero,
      carrier.shaInput, digest, mixIn] using hreturnData
  have hsizeCall : callPost.memory.size = 672 := by
    rw [hmemory']
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, carrier.size_eq]), carrier.size_eq]
  have hwriteReads :
      Mem.Reads (memory.write 640 digest.toBytes)
        (Bytes.writeAt carrier.image 640 digest.toBytes) :=
    Mem.Reads.write carrier.wf carrier.reads 640 digest.toBytes
  have hreadBytes :
      ((memory.write 640 digest.toBytes).read 640 32).1 =
        digest.toBytes := by
    rw [Mem.Reads.read hwriteReads]
    simpa only [B256.length_toBytes] using
      (Bytes.sliceD_writeAt carrier.image digest.toBytes 640)
  have hreadCall :
      Bytes.toB256 (callPost.memory.read 640 32).1 = digest := by
    rw [hmemory', hreadBytes, B256.toB256_toBytes]
  let post := rootFinishPost callPost callPost.memory digest G
  have htail : Func.RunCompiled fs sevm
      (callPost.setMach ⟨[], callPost.memory, G + 16⟩)
      (loadWord nodeWord +++ mstoreAt 0 +++
        returnMemoryRange 0 32) post :=
    rootFinishReturn_runCompiled hsizeCall hreadCall
  have hwholeTo : Func.RunCompiledTo fs sevm
      (shaBase.setMach ⟨[], shaBase.memory,
        G + 16 + sha64SuccessCost 0 nodeWord⟩)
      (sha64 0 nodeWord
        (loadWord nodeWord +++ mstoreAt 0 +++ returnMemoryRange 0 32))
      (.ok post) :=
    hlift (Func.RunCompiledTo.of_runCompiled htail)
  have hwhole : Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 253⟩)
      (sha64 0 nodeWord
        (loadWord nodeWord +++ mstoreAt 0 +++ returnMemoryRange 0 32))
      post := by
    have hrun := Func.RunCompiled.of_runCompiledTo_ok hwholeTo
    simpa only [shaBase, Devm.setMach_setMach,
      Devm.memory_setMach, sha64SuccessCost_zero_node] using hrun
  refine ⟨post, hwhole, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · change Bytes.toB256 digest.toBytes = digest
    exact B256.toB256_toBytes digest
  constructor
  · change callPost.returnData = digest.toBytes
    exact hreturnData'
  constructor
  · intro a
    calc
      Devm.getStor post a = Devm.getStor callPost a := rfl
      _ = Devm.getStor shaBase a := hstorage a
      _ = Devm.getStor base a := rfl
  constructor
  · intro a
    calc
      post.getCode a = callPost.getCode a := rfl
      _ = shaBase.getCode a := hcode a
      _ = base.getCode a := rfl
  constructor
  · calc
      post.accessedAddresses = callPost.accessedAddresses := rfl
      _ = shaBase.accessedAddresses := haddresses
      _ = base.accessedAddresses := rfl
  constructor
  · calc
      post.accessedStorageKeys = callPost.accessedStorageKeys := rfl
      _ = shaBase.accessedStorageKeys := hkeys
      _ = base.accessedStorageKeys := rfl
  constructor
  · calc
      post.logs = callPost.logs := rfl
      _ = shaBase.logs := hlogs
      _ = base.logs := rfl
  · calc
      post.error = callPost.error := rfl
      _ = shaBase.error := herror
      _ = base.error := rfl

/-- Complete successful finishing arm for the root fold.  The staging prefix
costs 138 gas, the warm successful SHA wrapper 237 gas, and the final
MLOAD/MSTORE/RETURN suffix 16 gas. -/
theorem rootFinish_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256} {G : Nat}
    (hmem : RootMemoryCarrier memory oldCount shiftedSize node)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : G + 237 < 2 ^ 256) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[height], memory, G + 391⟩)
        rootFinish post ∧
      post.stack = [] ∧
      post.gasLeft = G ∧
      post.output =
        (mixIn Bytes.sha256 node oldCount.toNat).toBytes ∧
      Bytes.toB256 post.output =
        mixIn Bytes.sha256 node oldCount.toNat ∧
      post.returnData =
        (mixIn Bytes.sha256 node oldCount.toNat).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧
      (∀ a, post.getCode a = base.getCode a) ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys = base.accessedStorageKeys ∧
      post.logs = base.logs ∧
      post.error = base.error := by
  let carrier := hmem.stageFinish
  obtain ⟨post, hsha, hfacts⟩ :=
    rootFinishShaReturn_runCompiled
      (fs := fs) (sevm := sevm) (base := base)
      (G := G) carrier hnodeleg hwarm hpre hdepth hbound
  have hrun0 := rootFinishPrefix_runCompiled
    (fs := fs) (sevm := sevm) (base := base)
    (height := height) (G := G + 253) hmem hsha
  have hrun : Func.RunCompiled fs sevm
      (base.setMach ⟨[height], memory, G + 391⟩)
      rootFinish post := by
    simpa only [rootFinish,
      show G + 253 + 138 = G + 391 by omega] using hrun0
  exact ⟨post, hrun, hfacts⟩

end Blanc.BeaconDeposit
