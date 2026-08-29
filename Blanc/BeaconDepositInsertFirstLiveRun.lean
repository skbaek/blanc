import Blanc.BeaconDepositInsertDead
import Blanc.BeaconDepositInsertFirstLiveCost

/-! # Beacon deposit first-live compiled insertion bridge -/

namespace Blanc.BeaconDeposit

open Jaune

/-- A pure `FirstLive` witness determines the complete compiled insertion
prefix and terminal store, including its exact slot, node, and gas charge. -/
theorem insertionLoop_firstLive_exists_runCompiledTo
    {fs : List Func} {sevm : Sevm} {origin base : Devm}
    {memory : Mem} {oldCount : B256} {stor : Stor}
    {height n size G : Nat} {node : B256} {keys : KeySet}
    (carrier : InsertionLoopCarrier origin base memory oldCount
      (insertionNatState height size node keys))
    (horiginStor : Devm.getStor origin sevm.currentTarget = stor)
    (hheight : height + n < 32)
    (hsize : size < 2 ^ 32)
    (hfirst : FirstLive size n)
    (hnodeleg : getDelegatedCodeAddress (origin.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ origin.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hsentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys height n node)
    (hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys height n node) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState height size node keys) < 2 ^ 256)
    (hinsertionContinuation :
      fs[insertionContinuationSlot]? = some insertionContinuation)
    (hinsertionLoop : fs[insertionLoopSlot]? = some insertionLoop) :
    ∃ finalBase finalMemory,
      Nonempty (InsertionLoopCarrier origin finalBase finalMemory oldCount
        (insertionLoopIter sevm.currentTarget stor n
          (insertionNatState height size node keys))) ∧
      Func.RunCompiledTo fs sevm
        (base.setMach
          ⟨[Nat.toB256 height], memory,
            (G + 46 +
                insertionFirstLiveStoreCost sevm stor keys height n node) +
              insertionDeadGas sevm.currentTarget stor n
                (insertionNatState height size node keys)⟩)
        insertionLoop
        (.ok ((afterSstore sevm finalBase
          (branchSlot (height + n))
          (accumulatedNode Bytes.sha256 (accOfStor stor).branch
            height n node)).setMach
              ⟨[], finalMemory, G⟩)) := by
  have hdead :=
    insertionLoopDead_insertionNatState_of_firstLive
      sevm.currentTarget stor n height size node keys
      (by omega) hsize hfirst
  have hlive :=
    insertionLoopIter_live_of_firstLive
      sevm.currentTarget stor n height size node keys
      (by omega) hsize hfirst
  have hcost :=
    insertionStoreCost_iter_eq_firstLive
      sevm stor keys height n size node hheight hsize
  have hkey :=
    insertionLoopIter_key
      sevm.currentTarget stor n height size node keys hheight hsize
  have hnode :=
    insertionLoopIter_node
      sevm.currentTarget stor n height size node keys (by omega)
  obtain ⟨finalBase, finalMemory, hcarrier, hrun⟩ :=
    insertionLoop_deadThenLive_exists_runCompiledTo
      carrier horiginStor hdead hlive hnodeleg hwarm hpre hdepth hstatic
      (by rw [hcost]; exact hsentry)
      (by rw [hcost]; exact hbound)
      hinsertionContinuation hinsertionLoop
  refine ⟨finalBase, finalMemory, hcarrier, ?_⟩
  rw [hcost, hkey, hnode] at hrun
  simpa only [InsertionLoopState.height, insertionNatState] using hrun

end Blanc.BeaconDeposit
