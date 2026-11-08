import Blanc.Lift.ConsolidationRequest.Fee
import Blanc.Lift.ExactWalkOps
import Blanc.CommonProofs.MemImage
import Blanc.WordByteCodecs

/-!
# The EIP-7251 submission path, under covered forks

After the calldata-length branch at 96 bytes: the value guard (value at least the fee), then the body:
bump the count in slot 1, read the tail in slot 3, write the caller and the three calldata words at the
four keys from `4 + 4 * tail` up, emit `caller ++ calldata` (116 bytes) as a topicless `LOG0`, bump the
tail and `STOP`. Writes are stated in the code's order, so everything here holds over any storage, even
when a record key aliases a metadata slot.
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open SystemExecution.ConsolidationRequest

/-- The record's first storage key. -/
def submissionKey (tail : B256) : B256 := 4 + 4 * tail

/-- The caller's word, moved to the top of the word. -/
def sourceWord (sevm : Sevm) : B256 := sevm.caller.toB256 <<< (Bytes.toB256 [0x60]).toNat

/-- Memory holding the caller's bytes and the calldata after them. -/
def copyMemory (sevm : Sevm) (M : Mem) : Mem :=
  (M.write 0 (sourceWord sevm).toBytes).write 20 (sevm.data.sliceD 0 96 0)

/-- The emitted log: topicless, its data the 116 bytes read back from memory. -/
def submissionLog (sevm : Sevm) (M : Mem) : Log :=
  ⟨sevm.currentTarget, [], ((copyMemory sevm M).read 0 116).1⟩

/-- Memory after the log's read. -/
def submissionMemory (sevm : Sevm) (M : Mem) : Mem := ((copyMemory sevm M).read 0 116).2

/-- The count word the path reads. -/
def countWord (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget 1

/-- After the count bump. -/
def countStore (sevm : Sevm) (b : Devm) : Devm :=
  afterSstore sevm (afterSload sevm b 1) 1 (1 + countWord sevm b)

/-- The tail word the path reads, after the count bump. -/
def tailWord (sevm : Sevm) (b : Devm) : B256 := (countStore sevm b).getStorVal sevm.currentTarget 3

/-- After reading the tail. -/
def tailRead (sevm : Sevm) (b : Devm) : Devm := afterSload sevm (countStore sevm b) 3

/-- The record's four stores, at the keys the code computes from `key`: the caller, then three calldata
words. -/
def recordStore (sevm : Sevm) (b : Devm) (key : B256) : Devm :=
  afterSstore sevm (afterSstore sevm (afterSstore sevm (afterSstore sevm b key sevm.caller.toB256)
    (1 + key) (Sevm.dataWord sevm 0)) (1 + (1 + key)) (Sevm.dataWord sevm 32))
    (1 + (1 + (1 + key))) (Sevm.dataWord sevm 64)

/-- The state after the record. -/
def recordsWritten (sevm : Sevm) (b : Devm) : Devm :=
  recordStore sevm (tailRead sevm b) (submissionKey (tailWord sevm b))

/-- The tail bump's base. -/
def logged (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  (recordsWritten sevm b).addLog (submissionLog sevm M)

/-- The base state of a finished submission. -/
def submissionBase (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  afterSstore sevm (logged sevm b M) 3 (1 + tailWord sevm b)

/-- `STOP` after a submission; `STOP` keeps the inherited output and error. -/
def submissionPost (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) : Devm :=
  St (submissionBase sevm b M) [] (submissionMemory sevm M) G

/-- `LOG0`, bump the tail, `STOP`. -/
private def logTail : SFunc :=
  (.next (.reg (.log 0)) (.next (.push [0x01] (by decide)) (.next (.reg .add)
    (.next (.push [0x03] (by decide)) (.next (.reg .sstore) (.last .stop))))))

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- The submission arm: the value guard, then the body. -/
theorem submission_arm : t_0088_c0 = RequestFee.paidTree ⟨0x01, [0x9a], by decide⟩ t_008f_c0 t_019a_c0 :=
  rfl

private theorem logTail_inv (fork : CoveredFork sevm.benvStat.fork) {fs : List SFunc} {n tail : B256}
    (run : SFunc.RunCut fs sevm [] (St b [0, n, tail] M G) logTail (.done o)) :
    ∃ G', o = .halted (St (afterSstore sevm (b.addLog ⟨sevm.currentTarget, [], (M.read 0 n.toNat).1⟩) 3
      (1 + tail)) [] (M.read 0 n.toNat).2 G') := by
  unfold logTail at run
  obtain ⟨d, h, run⟩ := ric_next run
  rcases of_run_reg h with ⟨pc, raw⟩
  simp only [Rinst.run, Rinst.runCore] at raw
  rw [show (St b [0, n, tail] M G).popToNat = .ok (0, St b [n, tail] M G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rw [show (St b [n, tail] M G).popToNat = .ok (n.toNat, St b [tail] M G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rw [show (St b [tail] M G).popN ((0 : Fin 5) : Nat) = .ok ([], St b [tail] M G) from rfl] at raw
  simp only [Except.bind_ok] at raw
  rcases Except.bind_eq_ok raw with ⟨s1, hcharge, rest⟩
  rcases Except.bind_eq_ok rest with ⟨_, -, last⟩
  cases last
  have eqGas := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas hcharge)
  have eqSt : s1 = St b [tail] M s1.gasLeft := eqGas
  rw [eqSt] at run
  simp only [St.memRead_fst, St.memRead_snd] at run
  change SFunc.RunCut _ _ _ (St (b.addLog ⟨sevm.currentTarget, [], (M.read 0 n.toNat).1⟩) [tail]
    (M.read 0 n.toNat).2 s1.gasLeft) _ _ at run
  winv 3
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  cases run with
  | last terminal =>
    change Except.ok _ = Except.ok _ at terminal
    cases terminal
    exact ⟨_, rfl⟩

/-- `LOG0` of a window, with its expansion charged. -/
def log0Gas (M : Mem) (n : Nat) : Nat :=
  gLog + gLogdata * n + gLogtopic * 0 +
    (calculateMemoryGasCost (memExtSize M.size 0 n) - calculateMemoryGasCost M.size)

private theorem logTail_exact (fork : CoveredFork sevm.benvStat.fork) {fs : List SFunc} {n tail : B256}
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) :
    SFunc.RunExact fs sevm
      (St b [0, n, tail] M
        (G + sstoreCost sevm (b.addLog ⟨sevm.currentTarget, [], (M.read 0 n.toNat).1⟩) 3 (1 + tail)
          + 3 + 3 + 3 + log0Gas M n.toNat))
      logTail
      (.halted (St (afterSstore sevm (b.addLog ⟨sevm.currentTarget, [], (M.read 0 n.toNat).1⟩) 3
        (1 + tail)) [] (M.read 0 n.toNat).2 G)) := by
  have emitted : Ninst.RunCompiled sevm
      (St b [0, n, tail] M
        (G + sstoreCost sevm (b.addLog ⟨sevm.currentTarget, [], (M.read 0 n.toNat).1⟩) 3 (1 + tail)
          + 3 + 3 + 3 + log0Gas M n.toNat)) (.reg (.log 0))
      (St (b.addLog ⟨sevm.currentTarget, [], (M.read 0 n.toNat).1⟩) [tail] (M.read 0 n.toNat).2
        (G + sstoreCost sevm (b.addLog ⟨sevm.currentTarget, [], (M.read 0 n.toNat).1⟩) 3 (1 + tail)
          + 3 + 3 + 3)) :=
    Ninst.runCompiled_log_of (n := 0) (i := 0) (sz := n) (topics := []) (s := [tail])
      rfl rfl dynamic (Devm.extCost_add_of_size rfl rfl) rfl rfl rfl
  unfold logTail
  refine .next emitted ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_sstore fork (by omega) dynamic ?_
  exact .last rfl

/-- A successful body run is non-static and ends in exactly `submissionPost`. -/
theorem body_inv (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_008f_c0 o) :
    sevm.isStatic = false ∧ ∃ G', o = .halted (submissionPost sevm b M G') := by
  have run := run.cut
  unfold t_008f_c0 at run
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
  change SFunc.RunCut _ _ _ (St (recordsWritten sevm b) [0, Bytes.toB256 [0x74], tailWord sevm b]
    (copyMemory sevm M) _) logTail _ at run
  obtain ⟨_, rfl⟩ := logTail_inv fork run
  exact ⟨dynamic, _, rfl⟩

/-- `CALLDATACOPY` of the 96 calldata bytes, after the caller's 20 bytes. -/
def copyGas (M : Mem) : Nat :=
  gVerylow + gasCopy * ceilDiv 96 32 +
    (calculateMemoryGasCost (memExtSize M.size 20 96) - calculateMemoryGasCost M.size)

/-- `MSTORE` at 0. -/
def sourceGas (M : Mem) : Nat :=
  gVerylow + (calculateMemoryGasCost (memExtSize M.size 0 32) - calculateMemoryGasCost M.size)

/-- The charge of the record's stores. -/
def recordWritesGas (sevm : Sevm) (b : Devm) (key : B256) : Nat :=
  let s0 := afterSstore sevm b key sevm.caller.toB256
  let s1 := afterSstore sevm s0 (1 + key) (Sevm.dataWord sevm 0)
  let s2 := afterSstore sevm s1 (1 + (1 + key)) (Sevm.dataWord sevm 32)
  sstoreCost sevm b key sevm.caller.toB256 + sstoreCost sevm s0 (1 + key) (Sevm.dataWord sevm 0) +
    sstoreCost sevm s1 (1 + (1 + key)) (Sevm.dataWord sevm 32) +
    sstoreCost sevm s2 (1 + (1 + (1 + key))) (Sevm.dataWord sevm 64)

/-- The fixed charge of the submission body's other instructions. -/
def bodyFixedGas : Nat := 113

/-- What the submission body takes from `gasLeft`. -/
def bodyGas (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  sloadCost sevm b 1 + sstoreCost sevm (afterSload sevm b 1) 1 (1 + countWord sevm b) +
    sloadCost sevm (countStore sevm b) 3 +
    recordWritesGas sevm (tailRead sevm b) (submissionKey (tailWord sevm b)) +
    sourceGas M + copyGas (M.write 0 (sourceWord sevm).toBytes) +
    log0Gas (copyMemory sevm M) 116 +
    sstoreCost sevm (logged sevm b M) 3 (1 + tailWord sevm b) +
    bodyFixedGas

/-- The submission body, forward: non-static, with more than the `SSTORE` sentry left at the end. -/
theorem body_exact (fork : CoveredFork sevm.benvStat.fork) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) :
    SFunc.RunExact cert.prog sevm (St b [] M (G + bodyGas sevm b M)) t_008f_c0
      (.halted (submissionPost sevm b M G)) := by
  have hgas : G + bodyGas sevm b M =
      G + sstoreCost sevm (logged sevm b M) 3 (1 + tailWord sevm b)
          + 3 + 3 + 3 + log0Gas (copyMemory sevm M) 116 + 2 + 3
        + copyGas (M.write 0 (sourceWord sevm).toBytes) + 3 + 2 + 3 + sourceGas M + 2 + 3 + 3 + 2
        + sstoreCost sevm (afterSstore sevm (afterSstore sevm (afterSstore sevm (tailRead sevm b)
            (submissionKey (tailWord sevm b)) sevm.caller.toB256)
            (1 + submissionKey (tailWord sevm b)) (Sevm.dataWord sevm 0))
            (1 + (1 + submissionKey (tailWord sevm b))) (Sevm.dataWord sevm 32))
            (1 + (1 + (1 + submissionKey (tailWord sevm b)))) (Sevm.dataWord sevm 64)
        + 3 + 3 + 3 + 3 + 3
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
    simp only [bodyGas, recordWritesGas, bodyFixedGas]
    omega
  rw [hgas]
  unfold t_008f_c0
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
  refine rx_push0 (h_push0 := CoveredFork.rules_push0 fork) (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstore fork (by omega) dynamic ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
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
  refine rx_shl rfl (CoveredFork.rules_shifts fork) (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := CoveredFork.rules_push0 fork) (by change 2 < 1024; decide) ?_
  refine rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := CoveredFork.rules_push0 fork) (by change 2 < 1024; decide) ?_
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  refine rx_calldatacopy (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := CoveredFork.rules_push0 fork) (by change 2 < 1024; decide) ?_
  exact logTail_exact fork (n := Bytes.toB256 [0x74]) (tail := tailWord sevm b)
    (b := recordsWritten sevm b) (M := copyMemory sevm M) (G := G) dynamic slack

end Blanc.Lift.ConsolidationRequest
