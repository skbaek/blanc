import Blanc.Lift.BuilderRequest.UserFrame
import Blanc.Lift.BuilderRequest.Exit.Jumps
import Blanc.Lift.ExactWalkOps
import Blanc.CommonProofs.MemImage
import Blanc.WordByteCodecs

/-!
# The exit runtime's submission path

The walks are over a fork's `StorageSteps`. One guard after the calldata-length branch: the value covers the fee. Then the body: bump the count, write
the caller and the first two calldata words at the tail record, emit `caller ++ calldata` as a topicless
`LOG0`, bump the tail, `STOP`. Writes are stated in order, so everything here holds even when a record key
aliases a metadata slot.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune

/-- The record's first storage key. -/
def submissionKey (tail : B256) : B256 := 4 + 3 * tail

/-- The caller's word, moved to the top of the word. -/
def sourceWord (sevm : Sevm) : B256 := sevm.caller.toB256 <<< (Bytes.toB256 [0x60]).toNat

/-- Memory holding the caller's bytes and the calldata after them. -/
def copyMemory (sevm : Sevm) (M : Mem) : Mem :=
  (M.write 0 (sourceWord sevm).toBytes).write 20 (sevm.data.sliceD 0 48 0)

/-- The emitted log: topicless, its data the 68 bytes read back from memory. -/
def submissionLog (sevm : Sevm) (M : Mem) : Log := windowLog sevm (copyMemory sevm M) 68

/-- Memory after the log's read. -/
def submissionMemory (sevm : Sevm) (M : Mem) : Mem := ((copyMemory sevm M).read 0 68).2

variable {sevm : Sevm}

namespace Steps

variable (l : StorageSteps sevm)

/-- The record's three stores, at the keys the code computes from `key`: the caller, then two calldata
words. -/
def recordStore (b : Devm) (key : B256) : Devm :=
  l.afterWrite (l.afterWrite (l.afterWrite b key sevm.caller.toB256)
    (1 + key) (Sevm.dataWord sevm 0)) (1 + (1 + key)) (Sevm.dataWord sevm 32)

/-- The state after the record. -/
def recordsWritten (b : Devm) : Devm := recordStore l (l.tailRead b) (submissionKey (l.tailWord b))

/-- The tail bump's base. -/
def logged (b : Devm) (M : Mem) : Devm := (recordsWritten l b).addLog (submissionLog sevm M)

/-- The base state of a finished submission. -/
def submissionBase (b : Devm) (M : Mem) : Devm := l.afterWrite (logged l b M) 3 (1 + l.tailWord b)

/-- `STOP` after a submission; `STOP` keeps the inherited output and error. -/
def submissionPost (b : Devm) (M : Mem) (G : Nat) : Devm :=
  St (submissionBase l b M) [] (submissionMemory sevm M) G

end Steps

/-- `STOP` after a submission under covered forks. -/
abbrev submissionPost (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) : Devm :=
  Steps.submissionPost (coveredSteps sevm) b M G

variable {l : StorageSteps sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- Success passes the guard. -/
theorem guard_inv {fee : B256} (run : SFunc.Run cert.prog sevm (St b [fee] M G) t_009e_c1 o) :
    fee.toNat ≤ sevm.value.toNat ∧ ∃ G', SFunc.Run cert.prog sevm (St b [] M G') t_00a5_c1 o := by
  have run := run.cut
  unfold t_009e_c1 at run
  winv 4
  rcases ric_branch run with ⟨flag, G', run⟩ | ⟨_, _, run⟩
  · exact ⟨toNat_ge_of_ltCheck_eq_zero flag, G', run.uncut⟩
  · exact False.elim (run.false_of_noOk rfl)

/-- The guard, forward, at its exact charge. -/
theorem guard_exact {fee : B256} (covered : fee.toNat ≤ sevm.value.toNat)
    (tail : SFunc.RunExact cert.prog sevm (St b [] M G) t_00a5_c1 o) :
    SFunc.RunExact cert.prog sevm (St b [fee] M (G + 19)) t_009e_c1 o := by
  have notLow : ¬ sevm.value < fee := by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt_of_ge covered
  have hgas : G + 19 = G + 10 + 3 + 3 + 2 + 1 := by omega
  rw [hgas]
  unfold t_009e_c1
  refine rx_dest ?_
  refine rx_callvalue (by change 1 < 1024; decide) ?_
  refine rx_lt (v := 0) ?_ (by change 0 < 1024; decide) ?_
  · simp only [B256.ltCheck, ite_eq_right notLow]
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  exact rx_branch_zero tail

/-- A successful body run is non-static and ends in exactly `submissionPost`. -/
theorem body_inv (v : l.Valid)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_00a5_c1 o) :
    sevm.isStatic = false ∧ ∃ G', o = .halted (Steps.submissionPost l b M G') := by
  have run := run.cut
  unfold t_00a5_c1 at run
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := countWord sevm b) rfl (v.readInv h)
  winv 3
  obtain ⟨_, h, run⟩ := ric_next run
  have dynamic := v.writeDynamic h
  obtain ⟨_, rfl⟩ := v.writeInv h
  change SFunc.RunCut _ _ _ (St (l.countStore b) [] M _) _ _ at run
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := l.tailWord b) rfl (v.readInv h)
  winv 7
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := v.writeInv h
  winv 5
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := v.writeInv h
  winv 5
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := v.writeInv h
  change SFunc.RunCut _ _ _ (St (Steps.recordsWritten l b) [l.tailWord b] M _) _ _ at run
  winv 2
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_shl h
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mstore h
  winv 3
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_calldatacopy h
  winv 2
  change SFunc.RunCut _ _ _ (St (Steps.recordsWritten l b) [0, Bytes.toB256 [0x44], l.tailWord b]
    (copyMemory sevm M) _) logTail _ at run
  obtain ⟨_, rfl⟩ := v.logTail_inv run
  exact ⟨dynamic, _, rfl⟩

/-- `CALLDATACOPY` of the key, after the caller's 20 bytes. -/
def copyGas (M : Mem) : Nat :=
  gVerylow + gasCopy * ceilDiv 48 32 +
    (calculateMemoryGasCost (memExtSize M.size 20 48) - calculateMemoryGasCost M.size)

/-- `MSTORE` at 0. -/
def sourceGas (M : Mem) : Nat :=
  gVerylow + (calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size)

namespace Steps

variable (l : StorageSteps sevm)

/-- The charge of the record's stores. -/
def recordWritesGas (b : Devm) (key : B256) : Nat :=
  let s0 := l.afterWrite b key sevm.caller.toB256
  let s1 := l.afterWrite s0 (1 + key) (Sevm.dataWord sevm 0)
  l.writeCharge b key sevm.caller.toB256 + l.writeCharge s0 (1 + key) (Sevm.dataWord sevm 0) +
    l.writeCharge s1 (1 + (1 + key)) (Sevm.dataWord sevm 32)

/-- What the submission body takes from `gasLeft`, on its way. -/
def bodyGas (b : Devm) (M : Mem) : Nat :=
  sloadCost sevm b 1 + l.writeCharge (l.afterRead b 1) 1 (1 + countWord sevm b) +
    sloadCost sevm (l.countStore b) 3 +
    recordWritesGas l (l.tailRead b) (submissionKey (l.tailWord b)) +
    sourceGas M + copyGas (M.write 0 (sourceWord sevm).toBytes) +
    log0Gas (copyMemory sevm M) 68 +
    l.writeCharge (logged l b M) 3 (1 + l.tailWord b) +
    98

/-- What the submission body's stores return to `gasLeft`: state gas a store credits against an earlier
spill. -/
def bodyRepay (b : Devm) (M : Mem) : Nat :=
  let key := submissionKey (l.tailWord b)
  let s0 := l.afterWrite (l.tailRead b) key sevm.caller.toB256
  let s1 := l.afterWrite s0 (1 + key) (Sevm.dataWord sevm 0)
  l.writeRepay (l.afterRead b 1) 1 (1 + countWord sevm b) +
    l.writeRepay (l.tailRead b) key sevm.caller.toB256 +
    l.writeRepay s0 (1 + key) (Sevm.dataWord sevm 0) +
    l.writeRepay s1 (1 + (1 + key)) (Sevm.dataWord sevm 32) +
    l.writeRepay (logged l b M) 3 (1 + l.tailWord b)

end Steps

/-- The submission body, forward: non-static, with more than the `SSTORE` sentry left at the end. It takes
`bodyGas` and returns `bodyRepay`. -/
theorem body_exact (v : l.Valid) (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) :
    SFunc.RunExact cert.prog sevm (St b [] M (G + Steps.bodyGas l b M)) t_00a5_c1
      (.halted (Steps.submissionPost l b M (G + Steps.bodyRepay l b M))) := by
  have hgas : G + Steps.bodyGas l b M =
      G + l.writeCharge (Steps.logged l b M) 3 (1 + l.tailWord b)
          + 3 + 3 + 3 + log0Gas (copyMemory sevm M) 68 + 2 + 3
        + copyGas (M.write 0 (sourceWord sevm).toBytes) + 3 + 2 + 3 + sourceGas M + 2 + 3 + 3 + 2
        + l.writeCharge (l.afterWrite (l.afterWrite (l.tailRead b)
            (submissionKey (l.tailWord b)) sevm.caller.toB256)
            (1 + submissionKey (l.tailWord b)) (Sevm.dataWord sevm 0))
            (1 + (1 + submissionKey (l.tailWord b))) (Sevm.dataWord sevm 32)
        + 3 + 3 + 3 + 3 + 3
        + l.writeCharge (l.afterWrite (l.tailRead b) (submissionKey (l.tailWord b))
            sevm.caller.toB256) (1 + submissionKey (l.tailWord b)) (Sevm.dataWord sevm 0)
        + 3 + 3 + 2 + 3 + 3
        + l.writeCharge (l.tailRead b) (submissionKey (l.tailWord b)) sevm.caller.toB256
        + 3 + 2 + 3 + 3 + 5 + 3 + 3 + sloadCost sevm (l.countStore b) 3 + 3
        + l.writeCharge (l.afterRead b 1) 1 (1 + countWord sevm b) + 3 + 3 + 3
        + sloadCost sevm b 1 + 3 := by
    simp only [Steps.bodyGas, Steps.recordWritesGas]
    omega
  rw [hgas]
  unfold t_00a5_c1
  refine rx_push rfl (by decide) ?_
  refine v.readRun (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by change 0 < 1024; decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine v.write_sink dynamic (by omega) fun r1 hr1 => ?_
  simp only [Nat.add_right_comm _ _ r1]
  refine rx_push rfl (by decide) ?_
  refine v.readRun (by decide) ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_mul rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_caller (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine v.write_sink dynamic (by omega) fun r2 hr2 => ?_
  simp only [Nat.add_right_comm _ _ r2]
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := v.push0) (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine v.write_sink dynamic (by omega) fun r3 hr3 => ?_
  simp only [Nat.add_right_comm _ _ r3]
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine v.write_sink dynamic (by omega) fun r4 hr4 => ?_
  simp only [Nat.add_right_comm _ _ r4]
  refine rx_caller (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_shl rfl v.shifts (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := v.push0) (by change 2 < 1024; decide) ?_
  refine rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := v.push0) (by change 2 < 1024; decide) ?_
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  refine rx_calldatacopy (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := v.push0) (by change 2 < 1024; decide) ?_
  have tail := v.logTail_exact (fs := cert.prog) (n := Bytes.toB256 [0x44]) (tail := l.tailWord b)
    (b := Steps.recordsWritten l b) (M := copyMemory sevm M) (G := G + r4 + r3 + r2 + r1) dynamic (by omega)
  have hout : G + Steps.bodyRepay l b M = G + r4 + r3 + r2 + r1 +
      l.writeRepay ((Steps.recordsWritten l b).addLog (windowLog sevm (copyMemory sevm M) (Bytes.toB256 [0x44]).toNat))
        3 (1 + l.tailWord b) := by
    have e1 : r1 = l.writeRepay (l.afterRead b 1) 1 (1 + countWord sevm b) := hr1
    have e2 : r2 = l.writeRepay (l.tailRead b) (submissionKey (l.tailWord b)) sevm.caller.toB256 := hr2
    have e3 : r3 = l.writeRepay (l.afterWrite (l.tailRead b) (submissionKey (l.tailWord b)) sevm.caller.toB256)
        (1 + submissionKey (l.tailWord b)) (Sevm.dataWord sevm 0) := hr3
    have e4 : r4 = l.writeRepay (l.afterWrite (l.afterWrite (l.tailRead b) (submissionKey (l.tailWord b))
        sevm.caller.toB256) (1 + submissionKey (l.tailWord b)) (Sevm.dataWord sevm 0))
        (1 + (1 + submissionKey (l.tailWord b))) (Sevm.dataWord sevm 32) := hr4
    have e5 : l.writeRepay ((Steps.recordsWritten l b).addLog (windowLog sevm (copyMemory sevm M)
        (Bytes.toB256 [0x44]).toNat)) 3 (1 + l.tailWord b) =
        l.writeRepay (Steps.logged l b M) 3 (1 + l.tailWord b) := rfl
    rw [e5]
    simp only [Steps.bodyRepay]
    omega
  rw [hout]
  exact tail

end Blanc.Lift.BuilderRequest.Exit
