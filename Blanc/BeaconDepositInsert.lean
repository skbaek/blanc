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

/-- Select and stage one dead insertion-loop iteration. -/
theorem insertionLoopDead_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height left : B256}
    {stack : List B256} {K : Nat} {ex : Execution}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hbit : ((1 : B256) &&& shiftedSize) = 0)
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
          K + 51 + sloadCost sevm base (branchBase + height)⟩)
      insertionLoop ex := by
  let C := sloadCost sevm base (branchBase + height)
  have harm : Func.RunCompiledTo fs sevm
      (base.setMach ⟨height :: stack, memory, K + 26 + C⟩)
      insertionDead ex :=
    insertionDeadStage_runCompiledTo hmem hval hroom htail
  have hdispatch :=
    insertionLoopDead_dispatch_runCompiledTo
      (K := K + 26 + C) hmem hbit hroom harm
  have hgas : K + 26 + C + 25 = K + 51 + C := by omega
  rw [hgas] at hdispatch
  simpa only [C] using hdispatch

/-- Shift word 19, increment the insertion height, and re-enter the insertion
loop in exactly 36 gas. -/
theorem insertionContinuation_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount size node height : B256}
    {K : Nat} {ex : Execution}
    (hmem : InsertionMemoryCarrier memory oldCount size node)
    (hloop : fs[insertionLoopSlot]? = some insertionLoop)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[height + 1], memory.write 608 (size >>> 1).toBytes, K⟩)
      insertionLoop ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[height], memory, K + 36⟩)
      insertionContinuation ex := by
  have hoff : (shiftedSizeWord * 32).toNat = 608 := by
    decide +kernel
  have hpushOff :
      pushCost (shiftedSizeWord * 32).toBytes.sig = gVerylow := by
    decide +kernel
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hsize : 640 ≤ memory.size := by
    rw [hmem.size_eq]
    omega
  have hread : Bytes.toB256 (memory.read 608 32).1 = size :=
    hmem.readShiftedSize
  unfold insertionContinuation loadWord mstoreAt
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

/-- Run the shared SHA-256 and insertion-continuation tail from a staged pair.

The continuation hypothesis begins at the next insertion-loop entry.  The
exposed memory carrier records the digest in word 20 before word 19 is shifted.
-/
theorem insertionShaTail_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {oldCount size left right height : B256} {K : Nat}
    (pair : InsertionPairMemoryCarrier
      base.memory oldCount size left right)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 269 < 2 ^ 256)
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop : fs[insertionLoopSlot]? = some insertionLoop) :
    ∃ callPost,
      callPost.stack = 1 :: [height] ∧
      callPost.memory = base.memory.write 640
        (hashPair Bytes.sha256 left right).toBytes ∧
      Nonempty (InsertionMemoryCarrier callPost.memory oldCount size
        (hashPair Bytes.sha256 left right)) ∧
      callPost.gasLeft = K + 85 ∧
      callPost.returnData = (hashPair Bytes.sha256 left right).toBytes ∧
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
          insertionLoop ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨[height], base.memory, K + 285⟩)
          (sha64 0 nodeWord (.call insertionContinuationSlot)) ex := by
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
      (stack := [height]) (success := .call insertionContinuationSlot)
      (K := K + 48)
      hcovered hnodeleg hwarm hpre hdepth (by omega)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hmemory' :
      callPost.memory = base.memory.write 640
        (hashPair Bytes.sha256 left right).toBytes := by
    simpa only [hzero, hnode, pair.shaInput, hashPair] using hmemory
  have hreturn' :
      callPost.returnData = (hashPair Bytes.sha256 left right).toBytes := by
    simpa only [hzero, pair.shaInput, hashPair] using hreturn
  have hgas' : callPost.gasLeft = K + 85 := by
    omega
  have hcarrierBase := pair.finishHash
  have hcarrier : InsertionMemoryCarrier callPost.memory oldCount size
      (hashPair Bytes.sha256 left right) := by
    rw [hmemory']
    exact hcarrierBase
  refine ⟨callPost, hstack, hmemory', ⟨hcarrier⟩, hgas', hreturn',
    hstorage, hcode, haddresses, hkeys,
    hlogs, houtput, herror, ?_⟩
  intro ex htail
  have hinsertion : Func.RunCompiledTo fs sevm
      (callPost.setMach
        ⟨[height], callPost.memory, K + 36⟩)
      insertionContinuation ex :=
    insertionContinuation_runCompiledTo
      hcarrier hinsertionLoop htail
  have hsuccess : Func.RunCompiledTo fs sevm
      (callPost.setMach
        ⟨[height], callPost.memory, K + 48⟩)
      (.call insertionContinuationSlot) ex := by
    exact Func.runCompiledTo_call' (G := K + 36) hinsertionContinuation
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega)
      (by simp only [Devm.gasLeft_setMach, gVerylow, gMid, gJumpdest])
      (by
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach] using hinsertion)
  have hwhole := hlift hsuccess
  simpa only [sha64SuccessCost_zero_node] using hwhole

/-- Store the accumulated node at the first live branch and stop.  The fixed
work costs 20 gas in addition to the selected warm/cold `SSTORE` charge. -/
theorem insertionLive_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {K : Nat}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hsentry : gCallStipend <
      K + 2 + sstoreCost sevm base (branchBase + height) node)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[height], memory,
          K + 20 + sstoreCost sevm base (branchBase + height) node⟩)
      insertionLive
      (.ok ((afterSstore sevm base (branchBase + height) node).setMach
        ⟨[], memory, K⟩)) := by
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hnodeRead : Bytes.toB256 (memory.read 640 32).1 = node :=
    hmem.readNode
  have hnodeMem : (memory.read 640 32).2 = memory := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · exact hmod
    · rw [hmem.size_eq]
      omega
  simp only [insertionLive, loadWord, prepend,
    show (nodeWord * 32 : B256) = 640 by decide +kernel]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup (n := 0) (w := height)
      (G := K + 17 + sstoreCost sevm base (branchBase + height) node)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := branchBase) (c := 3)
      (G := K + 14 + sstoreCost sevm base (branchBase + height) node)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary (r := .add) (f := (· + ·))
      (cost := gVerylow) (x := branchBase) (y := height)
      (v := branchBase + height) (s := [height])
      (G := K + 11 + sstoreCost sevm base (branchBase + height) node)
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (w := 640) (c := 3)
      (G := K + 8 + sstoreCost sevm base (branchBase + height) node)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := 640) (v := node) (s := (branchBase + height) :: [height])
      (c := 3)
      (G := K + 5 + sstoreCost sevm base (branchBase + height) node)
      (M := memory)
      rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by
          rw [hmem.size_eq]
          decide +kernel)]
        decide)
      hnodeRead hnodeMem
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [List.length_cons, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_swap (n := 0)
      (S := (branchBase + height) :: node :: [height])
      (G := K + 2 + sstoreCost sevm base (branchBase + height) node)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_sstore_selected_setMach
      (base := base) (key := branchBase + height) (value := node)
      (stack := [height]) (memory := memory) (G := K + 2)
      hsentry hstatic) ?_
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pop (G := K) rfl
      (by simp only [Devm.gasLeft_setMach, gBase])) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  exact Func.RunCompiledTo.last rfl

/-- Dispatch to the first live branch, store the accumulated node, and stop.
The fixed work costs 46 gas in addition to the selected `SSTORE` charge. -/
theorem insertionLoopLive_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount shiftedSize node height : B256}
    {K : Nat}
    (hmem : InsertionMemoryCarrier memory oldCount shiftedSize node)
    (hbit : ((1 : B256) &&& shiftedSize) ≠ 0)
    (hsentry : gCallStipend <
      K + 2 + sstoreCost sevm base (branchBase + height) node)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[height], memory,
          K + 46 + sstoreCost sevm base (branchBase + height) node⟩)
      insertionLoop
      (.ok ((afterSstore sevm base (branchBase + height) node).setMach
        ⟨[], memory, K⟩)) := by
  let C := sstoreCost sevm base (branchBase + height) node
  have harm : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[height], memory, K + 20 + C⟩)
      insertionLive
      (.ok ((afterSstore sevm base (branchBase + height) node).setMach
        ⟨[], memory, K⟩)) :=
    insertionLive_runCompiledTo hmem hsentry hstatic
  have hdispatch :=
    insertionLoopLive_dispatch_runCompiledTo
      (K := K + 20 + C) hmem hbit
      (by simp only [List.length_nil]; omega) harm
  have hgas : K + 20 + C + 26 = K + 46 + C := by omega
  rw [hgas] at hdispatch
  simpa only [C] using hdispatch

end Blanc.BeaconDeposit
