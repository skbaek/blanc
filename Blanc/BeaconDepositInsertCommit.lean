import Blanc.BeaconDepositInsertFirstLiveRun

/-! # Beacon deposit commit-to-first-live composition -/

namespace Blanc.BeaconDeposit

open Jaune

/-- Increment the deposit count and execute the complete insertion through its
unique first-live branch store.  The result exposes the exact branch slot,
accumulated node, and post-insertion carrier. -/
theorem commitDeposit_firstLive_exists_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {oldCount node : B256}
    {stor : Stor} {keys : KeySet} {n size G : Nat}
    (hmem : InsertionStartMemoryCarrier memory oldCount node)
    (hshift : oldCount + 1 = Nat.toB256 size)
    (hstor : Devm.getStor
      (afterSstore sevm base depositCountSlot (oldCount + 1))
      sevm.currentTarget = stor)
    (hkeys :
      (afterSstore sevm base depositCountSlot
        (oldCount + 1)).accessedStorageKeys = keys)
    (hheight : n < 32)
    (hsize : size < 2 ^ 32)
    (hfirst : FirstLive size n)
    (hnodeleg : getDelegatedCodeAddress
      ((afterSstore sevm base depositCountSlot
        (oldCount + 1)).getCode 2) = none)
    (hwarm : (2 : Adr) ∈
      (afterSstore sevm base depositCountSlot
        (oldCount + 1)).accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n node)
    (hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n node) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 size node keys) < 2 ^ 256)
    (hcountSentry : gCallStipend <
      ((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n node) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 size node keys)) +
      14 + sstoreCost sevm base depositCountSlot (oldCount + 1))
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop : fs[insertionLoopSlot]? = some insertionLoop) :
    ∃ finalBase finalMemory,
      Nonempty (InsertionLoopCarrier
        (afterSstore sevm base depositCountSlot (oldCount + 1))
        finalBase finalMemory oldCount
        (insertionLoopIter sevm.currentTarget stor n
          (insertionNatState 0 size node keys))) ∧
      Func.RunCompiledTo fs sevm
        (base.setMach
          ⟨[], memory,
            ((G + 46 +
                insertionFirstLiveStoreCost sevm stor keys 0 n node) +
              insertionDeadGas sevm.currentTarget stor n
                (insertionNatState 0 size node keys)) +
            38 + sstoreCost sevm base depositCountSlot (oldCount + 1)⟩)
        commitDeposit
        (.ok ((afterSstore sevm finalBase (branchSlot n)
          (accumulatedNode Bytes.sha256 (accOfStor stor).branch
            0 n node)).setMach ⟨[], finalMemory, G⟩)) := by
  let countPost :=
    afterSstore sevm base depositCountSlot (oldCount + 1)
  let nextMemory := memory.write 608 (oldCount + 1).toBytes
  have hmem' :
      InsertionMemoryCarrier nextMemory oldCount (Nat.toB256 size) node := by
    simpa only [nextMemory, hshift] using
      hmem.writeShiftedSize (oldCount + 1)
  have carrier :
      InsertionLoopCarrier countPost countPost nextMemory oldCount
        (insertionNatState 0 size node keys) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [insertionNatState] using hmem'
    · intro a
      rfl
    · intro a
      rfl
    · rfl
    · exact hkeys
    · rfl
    · rfl
    · rfl
  obtain ⟨finalBase, finalMemory, hfinal, hrun⟩ :=
    insertionLoop_firstLive_exists_runCompiledTo
      (height := 0) (n := n) (size := size) (G := G)
      carrier hstor (by omega) hsize hfirst hnodeleg hwarm hpre hdepth
      hstatic hbranchSentry hbound hinsertionContinuation hinsertionLoop
  have hzero : Nat.toB256 0 = (0 : B256) := by decide +kernel
  have htail : Func.RunCompiledTo fs sevm
      (countPost.setMach
        ⟨[0], nextMemory,
          (G + 46 +
              insertionFirstLiveStoreCost sevm stor keys 0 n node) +
            insertionDeadGas sevm.currentTarget stor n
              (insertionNatState 0 size node keys)⟩)
      insertionLoop
      (.ok ((afterSstore sevm finalBase (branchSlot n)
        (accumulatedNode Bytes.sha256 (accOfStor stor).branch
          0 n node)).setMach ⟨[], finalMemory, G⟩)) := by
    simpa only [countPost, nextMemory, Nat.zero_add, hzero] using hrun
  have hcommit := commitDeposit_runCompiledTo
    (K :=
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n node) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0 size node keys))
    hmem hcountSentry hstatic hinsertionLoop htail
  exact ⟨finalBase, finalMemory, hfinal, hcommit⟩

end Blanc.BeaconDeposit
