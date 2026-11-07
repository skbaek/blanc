import Blanc.Lift.BuilderRequest.UserFrame
import Blanc.Lift.BuilderRequest.Exit.Jumps
import Blanc.Lift.ExactWalkOps
import Blanc.CommonProofs.MemImage
import Blanc.WordByteCodecs

/-!
# The exit runtime's submission path

One guard after the calldata-length branch: the value covers the fee. Then the body: bump the count, write
the caller and the first two calldata words at the tail record, emit `caller ++ calldata` as a topicless
`LOG0`, bump the tail, `STOP`. Writes are stated in order, so everything here holds even when a record key
aliases a metadata slot.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune

/-- The record's first storage key. -/
def submissionKey (tail : B256) : B256 := 4 + 3 * tail

/-- The record's three stores, at the keys the code computes from `key`: the caller, then two calldata
words. -/
def recordStore (sevm : Sevm) (b : Devm) (key : B256) : Devm :=
  afterSstore sevm (afterSstore sevm (afterSstore sevm b key sevm.caller.toB256)
    (1 + key) (Sevm.dataWord sevm 0)) (1 + (1 + key)) (Sevm.dataWord sevm 32)

/-- The caller's word, moved to the top of the word. -/
def sourceWord (sevm : Sevm) : B256 := sevm.caller.toB256 <<< (Bytes.toB256 [0x60]).toNat

/-- Memory holding the caller's bytes and the calldata after them. -/
def copyMemory (sevm : Sevm) (M : Mem) : Mem :=
  (M.write 0 (sourceWord sevm).toBytes).write 20 (sevm.data.sliceD 0 48 0)

/-- The emitted log: topicless, its data the 68 bytes read back from memory. -/
def submissionLog (sevm : Sevm) (M : Mem) : Log := windowLog sevm (copyMemory sevm M) 68

/-- Memory after the log's read. -/
def submissionMemory (sevm : Sevm) (M : Mem) : Mem := ((copyMemory sevm M).read 0 68).2

/-- The state after the record. -/
def recordsWritten (sevm : Sevm) (b : Devm) : Devm :=
  recordStore sevm (tailRead sevm b) (submissionKey (tailWord sevm b))

/-- The base state of a finished submission. -/
def submissionBase (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  afterSstore sevm ((recordsWritten sevm b).addLog (submissionLog sevm M)) 3 (1 + tailWord sevm b)

/-- `STOP` after a submission; `STOP` keeps the inherited output and error. -/
def submissionPost (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) : Devm :=
  St (submissionBase sevm b M) [] (submissionMemory sevm M) G

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

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
theorem body_inv (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_00a5_c1 o) :
    sevm.isStatic = false ∧ ∃ G', o = .halted (submissionPost sevm b M G') := by
  have run := run.cut
  unfold t_00a5_c1 at run
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := countWord sevm b) rfl (ri_sload fork h)
  winv 3
  obtain ⟨_, h, run⟩ := ric_next run
  have dynamic := ri_sstore_nonstatic fork h
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  change SFunc.RunCut _ _ _ (St (countStore sevm b) [] M _) _ _ at run
  winv 1
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := tailWord sevm b) rfl (ri_sload fork h)
  winv 7
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  winv 5
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  winv 5
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  change SFunc.RunCut _ _ _ (St (recordsWritten sevm b) [tailWord sevm b] M _) _ _ at run
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
  change SFunc.RunCut _ _ _ (St (recordsWritten sevm b) [0, Bytes.toB256 [0x44], tailWord sevm b]
    (copyMemory sevm M) _) logTail _ at run
  obtain ⟨_, rfl⟩ := logTail_inv fork run
  exact ⟨dynamic, _, rfl⟩

/-- `CALLDATACOPY` of the key, after the caller's 20 bytes. -/
def copyGas (M : Mem) : Nat :=
  gVerylow + gasCopy * ceilDiv 48 32 +
    (calculateMemoryGasCost (memExtSize M.size 20 48) - calculateMemoryGasCost M.size)

/-- `MSTORE` at 0. -/
def sourceGas (M : Mem) : Nat :=
  gVerylow + (calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size)

/-- The exact charge of the record's stores. -/
def recordWritesGas (sevm : Sevm) (b : Devm) (key : B256) : Nat :=
  let s0 := afterSstore sevm b key sevm.caller.toB256
  let s1 := afterSstore sevm s0 (1 + key) (Sevm.dataWord sevm 0)
  sstoreCost sevm b key sevm.caller.toB256 + sstoreCost sevm s0 (1 + key) (Sevm.dataWord sevm 0) +
    sstoreCost sevm s1 (1 + (1 + key)) (Sevm.dataWord sevm 32)

/-- The exact charge of the submission body. -/
def bodyGas (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  sloadCost sevm b 1 + sstoreCost sevm (afterSload sevm b 1) 1 (1 + countWord sevm b) +
    sloadCost sevm (countStore sevm b) 3 +
    recordWritesGas sevm (tailRead sevm b) (submissionKey (tailWord sevm b)) +
    sourceGas M + copyGas (M.write 0 (sourceWord sevm).toBytes) +
    log0Gas (copyMemory sevm M) 68 +
    sstoreCost sevm ((recordsWritten sevm b).addLog (submissionLog sevm M)) 3 (1 + tailWord sevm b) +
    98

/-- The submission body, forward: non-static, with more than the `SSTORE` sentry left at the end. -/
theorem body_exact (fork : CoveredFork sevm.benvStat.fork) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) :
    SFunc.RunExact cert.prog sevm (St b [] M (G + bodyGas sevm b M)) t_00a5_c1
      (.halted (submissionPost sevm b M G)) := by
  have tail := logTail_exact (fs := cert.prog) (n := Bytes.toB256 [0x44]) (tail := tailWord sevm b)
    (b := recordsWritten sevm b) (M := copyMemory sevm M) (G := G) fork dynamic slack
  have hgas : G + bodyGas sevm b M =
      G + sstoreCost sevm ((recordsWritten sevm b).addLog (submissionLog sevm M)) 3 (1 + tailWord sevm b)
          + 3 + 3 + 3 + log0Gas (copyMemory sevm M) 68 + 2 + 3
        + copyGas (M.write 0 (sourceWord sevm).toBytes) + 3 + 2 + 3 + sourceGas M + 2 + 3 + 3 + 2
        + sstoreCost sevm (afterSstore sevm (afterSstore sevm (tailRead sevm b)
            (submissionKey (tailWord sevm b)) sevm.caller.toB256)
            (1 + submissionKey (tailWord sevm b)) (Sevm.dataWord sevm 0))
            (1 + (1 + submissionKey (tailWord sevm b))) (Sevm.dataWord sevm 32)
        + 3 + 3 + 3 + 3 + 3
        + sstoreCost sevm (afterSstore sevm (tailRead sevm b) (submissionKey (tailWord sevm b))
            sevm.caller.toB256) (1 + submissionKey (tailWord sevm b)) (Sevm.dataWord sevm 0)
        + 3 + 3 + 2 + 3 + 3
        + sstoreCost sevm (tailRead sevm b) (submissionKey (tailWord sevm b)) sevm.caller.toB256
        + 3 + 2 + 3 + 3 + 5 + 3 + 3 + sloadCost sevm (countStore sevm b) 3 + 3
        + sstoreCost sevm (afterSload sevm b 1) 1 (1 + countWord sevm b) + 3 + 3 + 3
        + sloadCost sevm b 1 + 3 := by
    simp only [bodyGas, recordWritesGas]
    omega
  rw [hgas]
  unfold t_00a5_c1
  refine rx_push rfl (by decide) ?_
  refine rx_sload_sel fork (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by change 0 < 1024; decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_sstore fork (by omega) dynamic ?_
  refine rx_push rfl (by decide) ?_
  refine rx_sload_sel fork (by decide) ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_mul rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_caller (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstore fork (by omega) dynamic ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstore fork (by omega) dynamic ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine rx_sstore fork (by omega) dynamic ?_
  refine rx_caller (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_shl rfl fork.rules_shifts (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 2 < 1024; decide) ?_
  refine rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 2 < 1024; decide) ?_
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  refine rx_calldatacopy (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 2 < 1024; decide) ?_
  exact tail

end Blanc.Lift.BuilderRequest.Exit
