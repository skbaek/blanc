import Blanc.Lift.BuilderRequest.UserFrame
import Blanc.Lift.AmsterdamWalk

/-!
# The builder contracts' storage steps under Amsterdam

`amsterdamSteps` is what `SLOAD` and `SSTORE` do on a fork with a state-gas record, for any meter: a store
charges the reservoir and spills what the reservoir cannot cover into `gasLeft`. An ordinary transaction's
frame has an empty reservoir, since the reservoir holds only gas above the 2^24 execution budget
(`allocateEvmGas`), so in the ordinary case the whole state-gas charge comes from `gasLeft`. Prices are read
from the rule record.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

/-- Amsterdam's storage steps, under any meter: a store takes its execution gas and its spill from `gasLeft`,
and returns the spill its credit repays. -/
def amsterdamSteps (sevm : Sevm) : StorageSteps sevm where
  afterRead := afterSloadA sevm
  afterWrite := afterSstoreA A sevm
  writeCharge := sstoreTotalA A sevm
  writeRepay := sstoreRepayA A sevm

/-- Amsterdam's steps are what Amsterdam executes. -/
theorem amsterdamSteps_valid {sevm : Sevm} (hfork : sevm.benvStat.fork = .amsterdam) :
    (amsterdamSteps sevm).Valid where
  push0 := amsterdam_push0 hfork
  shifts := amsterdam_shifts hfork
  readRun := fun hroom k => rx_sloadA (amsterdam_access hfork) hroom k
  readInv := fun h => ri_sloadA (amsterdam_access hfork) h
  writeRun := fun dynamic slack k => rx_sstoreS (amsterdam_stateGas hfork) dynamic slack k
  writeInv := fun h => ri_sstoreA (amsterdam_stateGas hfork) h
  writeDynamic := fun h => ri_sstore_nonstaticA (amsterdam_stateGas hfork) h
  readState := afterSloadA_state sevm
  readLogs := afterSloadA_logs sevm
  readOutput := afterSloadA_output sevm
  writeState := afterSstoreA_state A sevm
  writeLogs := afterSstoreA_logs sevm
  writeOutput := afterSstoreA_output sevm

/-- A store's state gas on an ordinary frame, the reservoir empty and nothing spilled yet: a first set of a
zero slot takes the whole `STORAGE_SET` from `gasLeft`, on top of its execution gas. -/
theorem storageSet_le_total {sevm : Sevm} {b : Devm} {k x : B256} (empty : b.stateGas.left = 0)
    (zero : b.getStorVal sevm.currentTarget k = 0)
    (orig : b.getOrigStorVal sevm sevm.currentTarget k = 0) (hx : x ≠ 0) :
    amsterdamStateGasRules.storageSet ≤ sstoreTotalA A sevm b k x := by
  have charge : sstoreChargeA A sevm b k x = amsterdamStateGasRules.storageSet := by
    rw [sstoreChargeA, sstoreAmsterdamStateGas, orig, zero, ite_eq_left ⟨rfl, hx.symm, rfl⟩]
  have credit : sstoreCreditA A sevm b k x = 0 := by
    rw [sstoreCreditA, sstoreAmsterdamStateRefund, orig, zero, ite_eq_right (fun h => hx h.2.1.symm)]
  simp only [sstoreTotalA, sstoreSpillA, charge, credit, empty]
  omega

/-- The count bump's store after the fee path's reads, on an ordinary frame: the first set of a zero count
slot takes the whole `STORAGE_SET` from `gasLeft`. -/
theorem feeBase_storageSet_le {sevm : Sevm} {b : Devm} (slot1 : b.getStorVal sevm.currentTarget 1 = 0)
    (orig1 : b.getOrigStorVal sevm sevm.currentTarget 1 = 0) (empty : b.stateGas.left = 0) :
    amsterdamStateGasRules.storageSet ≤ (amsterdamSteps sevm).writeCharge
      ((amsterdamSteps sevm).afterRead ((amsterdamSteps sevm).feeBase b) 1) 1
      (1 + countWord sevm ((amsterdamSteps sevm).feeBase b)) := by
  have read : ∀ (d : Devm) (k k' : B256), (afterSloadA sevm d k).getStorVal sevm.currentTarget k' =
      d.getStorVal sevm.currentTarget k' := fun d k k' => afterSloadA_getStorVal sevm d k _ k'
  have origRead : ∀ (d : Devm) (k k' : B256), (afterSloadA sevm d k).getOrigStorVal sevm sevm.currentTarget k' =
      d.getOrigStorVal sevm sevm.currentTarget k' := fun d k k' => afterSloadA_getOrig sevm d k _ k'
  have count : countWord sevm (afterSloadA sevm (afterSloadA sevm b 0) 1) = 0 := by
    simp only [countWord, read, slot1]
  show amsterdamStateGasRules.storageSet ≤ sstoreTotalA A sevm
    (afterSloadA sevm (afterSloadA sevm (afterSloadA sevm b 0) 1) 1) 1
    (1 + countWord sevm (afterSloadA sevm (afterSloadA sevm b 0) 1))
  rw [count]
  refine storageSet_le_total ?_ ?_ ?_ (by decide)
  · simp only [afterSloadA_stateGas, empty]
  · simp only [read, slot1]
  · simp only [origRead, orig1]

/-- **Builder frames, under Amsterdam, under any state-gas meter.** Every successful execution of the contract's
code at a non-system caller, from an empty stack, is a submission or a fee read. `aligned` and `wf` hold of the
empty memory every frame starts with; `lengthBound` holds of any calldata a frame can carry, since
`CALLDATASIZE` is read as a word. Success already implies slot 0 is off the inhibitor. The statement stops at the
frame: no message or transaction level, no EIP-7708 transfer log, no settlement, no history. -/
theorem UserFrames.exec_user_frame_amsterdam (c : UserFrames) {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = c.code) (hfork : sevm.benvStat.fork = .amsterdam) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory) (lengthBound : sevm.data.length < 2 ^ 256)
    (caller : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    c.Frame (amsterdamSteps sevm) pre post :=
  c.frame (amsterdamSteps_valid hfork) hcode stack aligned wf lengthBound caller exec

end Blanc.Lift.BuilderRequest
