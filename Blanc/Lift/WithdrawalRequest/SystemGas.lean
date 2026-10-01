import Blanc.Lift.WithdrawalRequest.SystemBookkeeping
import Blanc.Lift.Vyper
import Blanc.Lift.WithdrawalRequest.SystemMemoryGas
import Blanc.StorageAccessGas

/-! Fresh raw-system allocation, closed selected gas and uniform30M construction. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- Every metadata SSTORE retains its original/current/new-value selected cost.
There are two pointer stores only when the queue drains, then two final stores. -/
def systemFrameStoreGas (sevm : Sevm) (base : Devm) (memory : Mem) : Nat :=
  let queue := (systemQueuePost sevm base memory).base
  let pointers := systemFramePointers sevm base memory
  (if systemAdvancedHead (systemHead sevm base) (systemCount sevm base) = systemTail sevm base then
    sstoreCost sevm queue 2 0 + sstoreCost sevm (afterSstore sevm queue 2 0) 3 0
   else sstoreCost sevm queue 2 (systemAdvancedHead (systemHead sevm base) (systemCount sevm base))) +
  sstoreCost sevm (systemCountRead sevm pointers) 0 (systemNewExcess sevm pointers) +
  sstoreCost sevm (systemExcessStore sevm pointers) 1 0

theorem systemFrameStoreGas_le (sevm : Sevm) (base : Devm) (memory : Mem) :
    systemFrameStoreGas sevm base memory ≤ 88400 := by
  simp only [systemFrameStoreGas]
  have excess := sstoreCost_le sevm (systemCountRead sevm (systemFramePointers sevm base memory))
    0 (systemNewExcess sevm (systemFramePointers sevm base memory))
  have count := sstoreCost_le sevm (systemExcessStore sevm (systemFramePointers sevm base memory)) 1 0
  split
  · have head := sstoreCost_le sevm (systemQueuePost sevm base memory).base 2 0
    have tail := sstoreCost_le sevm (afterSstore sevm (systemQueuePost sevm base memory).base 2 0) 3 0
    simp only [gasColdSload, gasStorageSet] at excess count head tail
    omega
  · have head := sstoreCost_le sevm (systemQueuePost sevm base memory).base 2
      (systemAdvancedHead (systemHead sevm base) (systemCount sevm base))
    simp only [gasColdSload, gasStorageSet] at excess count head
    omega

/-- The per-entry affine instructions and every selected bookkeeping branch.
192 includes caller21, setup41, exit header23 and bookkeeping fixed107. -/
def systemFrameFixedGas (sevm : Sevm) (base : Devm) (memory : Mem) : Nat :=
  311*(systemCount sevm base).toNat + 192 +
  (if (systemDifference sevm base).toNat < 16 then 0 else 5) +
  (if systemAdvancedHead (systemHead sevm base) (systemCount sevm base) = systemTail sevm base
    then 16 else 17) +
  (if systemOldExcess sevm (systemFramePointers sevm base memory) = B256.max then 4 else 0) +
  (if (2 : B256) < systemExcessSum sevm (systemFramePointers sevm base memory) then 13 else 17)

theorem systemFrameFixedGas_le (sevm : Sevm) (base : Devm) (memory : Mem) :
    systemFrameFixedGas sevm base memory ≤ 5211 := by
  have cap := systemCount_le sevm base
  unfold systemFrameFixedGas
  by_cases capped : (systemDifference sevm base).toNat < 16
  <;> by_cases drained : systemAdvancedHead (systemHead sevm base) (systemCount sevm base) = systemTail sevm base
  <;> by_cases inhibited : systemOldExcess sevm (systemFramePointers sevm base memory) = B256.max
  <;> by_cases positive : (2 : B256) < systemExcessSum sevm (systemFramePointers sevm base memory)
  <;> simp only [capped, drained, inhibited, positive, ite_true, ite_false]
  <;> omega

/-- Tail/head setup, three reads per record, then excess/count after pointer stores.
The actual incoming bases are part of the schedule, including all key aliases. -/
def systemFrameReadSchedule (sevm : Sevm) (base : Devm) (memory : Mem) : SloadSchedule :=
  [(base,3), (afterSload sevm base 3,2)] ++
  systemLoopReadSchedule sevm (systemHead sevm base) 0 (systemCount sevm base).toNat
    (systemSetupBase sevm base) ++
  [(systemFramePointers sevm base memory,0),
   (systemExcessRead sevm (systemFramePointers sevm base memory),1)]

theorem systemFrameReadSchedule_length (sevm : Sevm) (base : Devm) (memory : Mem) :
    (systemFrameReadSchedule sevm base memory).length = 3*(systemCount sevm base).toNat+4 := by
  simp only [systemFrameReadSchedule, List.length_append, List.length_cons, List.length_nil,
    systemLoopReadSchedule_length]
  omega

/-- RETURN is already covered by actual padded allocation, including count0. -/
theorem systemFrameReturnGas_zero (sevm : Sevm) (base : Devm) (memory : Mem)
    (fresh : memory.size = 0) :
    systemReturnGas (systemQueuePost sevm base memory).memory (systemCount sevm base) = 0 := by
  unfold systemReturnGas
  rw [systemReturnSize_toNat (systemCount_le sevm base),
    systemQueuePost_size sevm base memory fresh,
    memExtSize_of_le (systemAllocatedSize_aligned _)
      (by simpa only [Nat.zero_add] using systemAllocatedSize_covers (systemCount sevm base).toNat),
    Nat.sub_self]

/-- The exact closed fresh formula retains both the cold count and selected stores. -/
def systemFrameClosedGas (sevm : Sevm) (base : Devm) (memory : Mem) : Nat :=
  systemFrameFixedGas sevm base memory +
  100*(3*(systemCount sevm base).toNat+4) +
  2000*sloadColdCount sevm (systemFrameReadSchedule sevm base memory) +
  systemFrameStoreGas sevm base memory +
  calculateMemoryGasCost (systemAllocatedSize (systemCount sevm base).toNat)

/-- Every selected charge is attributed to actual instructions, the finite
storage schedule, or the fresh padded memory allocation. -/
theorem systemFrameGas_closed (sevm : Sevm) (base : Devm) (memory : Mem)
    (fresh : memory.size = 0) :
    systemFrameGas sevm base memory = systemFrameClosedGas sevm base memory := by
  have queue := systemQueuePost_charges sevm base memory fresh
  have reads := sloadScheduleCost_eq sevm (systemFrameReadSchedule sevm base memory)
  rw [systemFrameReadSchedule_length] at reads
  simp only [systemFrameReadSchedule, sloadScheduleCost, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    gasWarmAccess, gasColdSload] at reads
  simp only [systemFrameGas, systemFrameClosedGas, systemFrameFixedGas, systemFrameStoreGas,
    systemBookkeepingGas, systemPointerGas, systemExcessReadGas, systemCountReadGas,
    systemFinalStoresGas, systemQueueGas, systemLoopGas, systemLoopHeaderGas_eq,
    systemSetupGas, systemSetupFixedGas_eq, dispatchGas, gBase, gVerylow, gHigh]
  rw [systemFrameReturnGas_zero sevm base memory fresh]
  simp only [systemLoopReadCharges, systemFrameReadSchedule, systemFramePointers] at queue reads ⊢
  by_cases capped : (systemDifference sevm base).toNat < 16
  <;> by_cases drained : systemAdvancedHead (systemHead sevm base) (systemCount sevm base) = systemTail sevm base
  <;> by_cases inhibited : systemOldExcess sevm
    (systemPointerBase sevm (systemQueuePost sevm base memory).base
      (systemHead sevm base) (systemTail sevm base) (systemCount sevm base)) = B256.max
  <;> by_cases positive : (2 : B256) < systemExcessSum sevm
    (systemPointerBase sevm (systemQueuePost sevm base memory).base
      (systemHead sevm base) (systemTail sevm base) (systemCount sevm base))
  <;> simp only [capped, drained, inhibited, positive, ite_true, ite_false]
  <;> omega

/-- The fresh canonical frame fits a uniform bound, independently of logical queue invariants. -/
theorem systemFrameGas_le (sevm : Sevm) (base : Devm) (memory : Mem)
    (fresh : memory.size = 0) : systemFrameGas sevm base memory ≤ 210000 := by
  rw [systemFrameGas_closed sevm base memory fresh]
  have fixed := systemFrameFixedGas_le sevm base memory
  have stores := systemFrameStoreGas_le sevm base memory
  have cap := systemCount_le sevm base
  have loop := sloadScheduleCost_le sevm
    (systemLoopReadSchedule sevm (systemHead sevm base) 0 (systemCount sevm base).toNat
      (systemSetupBase sevm base))
  rw [systemLoopReadSchedule_length] at loop
  have tail := Blanc.sloadCost_le sevm base 3
  have head := Blanc.sloadCost_le sevm (afterSload sevm base 3) 2
  have excess := Blanc.sloadCost_le sevm (systemFramePointers sevm base memory) 0
  have count := Blanc.sloadCost_le sevm (systemExcessRead sevm (systemFramePointers sevm base memory)) 1
  have reads := sloadScheduleCost_eq sevm (systemFrameReadSchedule sevm base memory)
  rw [systemFrameReadSchedule_length] at reads
  simp only [systemFrameReadSchedule, sloadScheduleCost, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero,
    gasWarmAccess, gasColdSload] at reads loop tail head excess count
  have allocation := systemAllocatedSize_le (systemCount sevm base).toNat cap
  have expansion := calculateMemoryGasCost_mono allocation
  change _ ≤ 119 at expansion
  simp only [systemFrameClosedGas, systemFrameReadSchedule]
  omega

/-- At30M, the exact remaining gas satisfies every shared SSTORE stipend sentry. -/
theorem systemFrameGas_stipend (sevm : Sevm) (base : Devm) (memory : Mem)
    (fresh : memory.size = 0) :
    gCallStipend < systemTransactionGas-systemFrameGas sevm base memory := by
  have bound := systemFrameGas_le sevm base memory fresh
  simp only [gCallStipend, systemTransactionGas]
  omega

/-- An actual successful raw canonical frame, with the exact30M residual and
whole halting poststate. Protocol settlement is a separate subsequent theorem. -/
theorem exec_system_frame_30M {sevm : Sevm} (base : Devm)
    (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (caller : sevm.caller = systemAddress)
    (dynamic : sevm.isStatic = false) :
    Nonempty (Exec 0 sevm (St base [] ⟨.empty,0⟩ systemTransactionGas)
      (.ok (systemFramePost sevm base ⟨.empty,0⟩
        (systemTransactionGas-systemFrameClosedGas sevm base ⟨.empty,0⟩)))) := by
  have bound := systemFrameGas_le sevm base ⟨.empty,0⟩ rfl
  have slack := systemFrameGas_stipend sevm base ⟨.empty,0⟩ rfl
  have run := exec_system_frame_exact (base := base) (memory := ⟨.empty,0⟩)
    code fork caller dynamic slack
  have cost := systemFrameGas_closed sevm base ⟨.empty,0⟩ rfl
  have available : systemTransactionGas-systemFrameGas sevm base ⟨.empty,0⟩ +
      systemFrameGas sevm base ⟨.empty,0⟩ = systemTransactionGas := by
    unfold systemTransactionGas
    omega
  rw [available, cost] at run
  exact run

end Blanc.Lift.WithdrawalRequest
