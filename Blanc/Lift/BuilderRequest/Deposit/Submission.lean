import Blanc.Lift.BuilderRequest.Deposit.FeeWindow
import Blanc.Lift.BuilderRequest.UserFrame
import Blanc.Lift.ExactWalkOps
import Blanc.CommonProofs.MemImage

/-!
# The deposit runtime's submission path

The three guards after the calldata-length branch, then the body: bump the count, write six calldata
words at the tail record, emit the 184 calldata bytes as a topicless `LOG0`, bump the tail, `STOP`.
Writes are stated in order, so everything here holds even when a record key aliases a metadata slot.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune

/-- The mask the guard applies to the word at calldata byte 56: its low 64 bits. By position those
are calldata bytes 80 to 87 of a 184-byte payload, read big-endian; no theorem here states that. -/
def amountMask : B256 := Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

/-- The submission's amount field, in gwei. -/
def amountGwei (sevm : Sevm) : B256 := amountMask &&& Sevm.dataWord sevm 56

/-- The amount a submission credits, in wei. -/
def creditedWei (sevm : Sevm) : Nat := (amountGwei sevm).toNat * 10 ^ 9

theorem amountGwei_lt (sevm : Sevm) : (amountGwei sevm).toNat < 2 ^ 64 := by
  have mask : amountMask.toNat = 2 ^ 64 - 1 := by decide
  rw [amountGwei, B256.toNat_and, mask, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

/-- What the submission guards accept at quoted fee `fee`, read from the bytes:

* `credited`: the amount field is at least `10^9` gwei, so at least 1 ETH is credited;
* `covered`: the call's value is at least the credited wei plus the fee.

The bytes compare `value < fee`, then `10^9 > amount`, then `value - fee < amount * 10^9`, and revert
on any of them; no word wraps, as the amount has 64 bits and the first check rules out underflow.
Surplus value is accepted and stays with the contract. -/
structure Admitted (sevm : Sevm) (fee : B256) : Prop where
  credited : 10 ^ 18 ≤ creditedWei sevm
  covered : creditedWei sevm + fee.toNat ≤ sevm.value.toNat

private theorem gwei_mul (sevm : Sevm) :
    ((Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00]) * amountGwei sevm).toNat = creditedWei sevm := by
  have small : creditedWei sevm < 2 ^ 256 := by
    have := amountGwei_lt sevm
    simp only [creditedWei]
    omega
  have gwei : (Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00]).toNat = 10 ^ 9 := by decide
  rw [B256.toNat_mul, gwei, Nat.mul_comm, Nat.lo]
  exact Nat.mod_eq_of_lt small

private theorem value_sub {sevm : Sevm} {fee : B256} (paid : fee.toNat ≤ sevm.value.toNat) :
    (sevm.value - fee).toNat = sevm.value.toNat - fee.toNat := by
  rw [B256.toNat_sub, Nat.lo, Nat.add_sub_mod_eq_sub (B256.toNat_lt sevm.value) paid]

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- Success passes all three guards. -/
theorem guards_inv {fee : B256} (run : SFunc.Run prog sevm (St b [fee] M G) t_009f_c1 o) :
    Admitted sevm fee ∧ ∃ G', SFunc.Run prog sevm (St b [] M G') t_00cd_c1 o := by
  have run := run.cut
  unfold t_009f_c1 at run
  winv 5
  rcases ric_branch run with ⟨flag, _, run⟩ | ⟨_, _, run⟩
  swap
  · exact False.elim (run.false_of_noOk rfl)
  have paid := toNat_ge_of_ltCheck_eq_zero flag
  unfold t_00a7_c1 at run
  winv 8
  rcases ric_branch run with ⟨flag, _, run⟩ | ⟨_, _, run⟩
  swap
  · exact False.elim (run.false_of_noOk rfl)
  have floor : 10 ^ 9 ≤ (amountGwei sevm).toNat := toNat_le_of_gtCheck_eq_zero flag
  unfold t_00bf_c1 at run
  winv 7
  rcases ric_branch run with ⟨flag, G', run⟩ | ⟨_, _, run⟩
  swap
  · exact False.elim (run.false_of_noOk rfl)
  have cover : (Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00] * amountGwei sevm).toNat ≤
      (sevm.value - fee).toNat := toNat_ge_of_ltCheck_eq_zero flag
  rw [gwei_mul, value_sub paid] at cover
  refine ⟨⟨?_, ?_⟩, G', run.uncut⟩
  · simp only [creditedWei]
    omega
  · omega

/-- The guards, forward, at their exact charge. -/
theorem guards_exact {fee : B256} (admitted : Admitted sevm fee)
    (tail : SFunc.RunExact prog sevm (St b [] M G) t_00cd_c1 o) :
    SFunc.RunExact prog sevm (St b [fee] M (G + 88)) t_009f_c1 o := by
  have paid : fee.toNat ≤ sevm.value.toNat := by
    have := admitted.covered
    omega
  have notLow : ¬ sevm.value < fee := by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt_of_ge paid
  have floor : 10 ^ 9 ≤ (amountGwei sevm).toNat := by
    have := admitted.credited
    simp only [creditedWei] at this
    omega
  have notFloor : ¬ amountGwei sevm < Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00] := by
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00]).toNat = 10 ^ 9 by decide]
    exact Nat.not_lt_of_ge floor
  have notCover : ¬ sevm.value - fee < Bytes.toB256 [0x3b, 0x9a, 0xca, 0x00] * amountGwei sevm := by
    rw [B256.lt_iff_toNat_lt_toNat, gwei_mul, value_sub paid]
    have := admitted.covered
    omega
  have hgas : G + 88 = G + 10 + 3 + 3 + 3 + 2 + 3 + 5 + 3
      + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 10 + 3 + 3 + 2 + 3 + 1 := by
    omega
  rw [hgas]
  unfold t_009f_c1
  refine rx_dest ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_callvalue (by change 2 < 1024; decide) ?_
  refine rx_lt (v := 0) ?_ (by change 1 < 1024; decide) ?_
  · simp only [B256.ltCheck, ite_eq_right notLow]
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_branch_zero ?_
  unfold t_00a7_c1
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_calldataload (by change 1 < 1024; decide) ?_
  refine rx_push (w := amountMask) rfl (by change 2 < 1024; decide) ?_
  refine rx_and (v := amountGwei sevm) rfl (by change 1 < 1024; decide) ?_
  refine rx_dup1 (by change 2 < 1024; decide) ?_
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  refine rx_gt (v := 0) ?_ (by change 2 < 1024; decide) ?_
  · simp only [B256.gtCheck, ite_eq_right notFloor]
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  refine rx_branch_zero ?_
  unfold t_00bf_c1
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_mul rfl (by change 1 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine rx_callvalue (by change 2 < 1024; decide) ?_
  refine rx_sub' rfl (by change 1 < 1024; decide) ?_
  refine rx_lt (v := 0) ?_ (by decide) ?_
  · simp only [B256.ltCheck, ite_eq_right notCover]
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  exact rx_branch_zero tail

/-- The record's first storage key. -/
def submissionKey (tail : B256) : B256 := 4 + 6 * tail

/-- Store the calldata word at byte `off` under `key`. -/
def wordStore (sevm : Sevm) (b : Devm) (key off : B256) : Devm :=
  afterSstore sevm b key (Sevm.dataWord sevm off)

/-- The six ordered record writes, at the keys the code computes from `key`. -/
def recordStore (sevm : Sevm) (b : Devm) (key : B256) : Devm :=
  wordStore sevm (wordStore sevm (wordStore sevm (wordStore sevm (wordStore sevm (wordStore sevm b
    key 0) (1 + key) 32) (1 + (1 + key)) 64) (1 + (1 + (1 + key))) 96)
    (1 + (1 + (1 + (1 + key)))) 128) (1 + (1 + (1 + (1 + (1 + key))))) 160

/-- Memory holding the calldata copy. -/
def copyMemory (sevm : Sevm) (M : Mem) : Mem := M.write 0 (sevm.data.sliceD 0 184 0)

/-- The emitted log: topicless, its data the 184 bytes read back from memory. -/
def submissionLog (sevm : Sevm) (M : Mem) : Log := windowLog sevm (copyMemory sevm M) 184

/-- Memory after the log's read. -/
def submissionMemory (sevm : Sevm) (M : Mem) : Mem := ((copyMemory sevm M).read 0 184).2

/-- The state after all six words. -/
def recordsWritten (sevm : Sevm) (b : Devm) : Devm :=
  recordStore sevm (tailRead sevm b) (submissionKey (tailWord sevm b))

/-- The state after the log. -/
def logged (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  (recordsWritten sevm b).addLog (submissionLog sevm M)

/-- The base state of a finished submission. -/
def submissionBase (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  afterSstore sevm (logged sevm b M) 3 (1 + tailWord sevm b)

/-- `STOP` after a submission; `STOP` keeps the inherited output and error. -/
def submissionPost (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) : Devm :=
  St (submissionBase sevm b M) [] (submissionMemory sevm M) G

/-- The charge of the record writes' `SSTORE`s. -/
def recordWritesGas (sevm : Sevm) (b : Devm) (key : B256) : Nat :=
  let s0 := wordStore sevm b key 0
  let s1 := wordStore sevm s0 (1 + key) 32
  let s2 := wordStore sevm s1 (1 + (1 + key)) 64
  let s3 := wordStore sevm s2 (1 + (1 + (1 + key))) 96
  let s4 := wordStore sevm s3 (1 + (1 + (1 + (1 + key)))) 128
  sstoreCost sevm b key (Sevm.dataWord sevm 0) +
  sstoreCost sevm s0 (1 + key) (Sevm.dataWord sevm 32) +
  sstoreCost sevm s1 (1 + (1 + key)) (Sevm.dataWord sevm 64) +
  sstoreCost sevm s2 (1 + (1 + (1 + key))) (Sevm.dataWord sevm 96) +
  sstoreCost sevm s3 (1 + (1 + (1 + (1 + key)))) (Sevm.dataWord sevm 128) +
  sstoreCost sevm s4 (1 + (1 + (1 + (1 + (1 + key))))) (Sevm.dataWord sevm 160)

/-- `CALLDATACOPY` of the payload. -/
def copyGas (M : Mem) : Nat :=
  gVerylow + gasCopy * ceilDiv 184 32 +
    (calculateMemoryGasCost (memExtSize M.size 0 184) - calculateMemoryGasCost M.size)

/-- `LOG0` of the payload. -/
def logGas (sevm : Sevm) (M : Mem) : Nat := log0Gas (copyMemory sevm M) 184

/-- The exact charge of the submission body. -/
def bodyGas (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  136 + sloadCost sevm b 1 + sstoreCost sevm (afterSload sevm b 1) 1 (1 + countWord sevm b) +
    sloadCost sevm (countStore sevm b) 3 +
    recordWritesGas sevm (tailRead sevm b) (submissionKey (tailWord sevm b)) +
    copyGas M + logGas sevm M + sstoreCost sevm (logged sevm b M) 3 (1 + tailWord sevm b)

private theorem word_inv {p : Bytes} {le : p.length ≤ 32} {off key tail : B256} {f : SFunc}
    {r : Seg} (hp : Bytes.toB256 p = off) (fork : CoveredFork sevm.benvStat.fork)
    {le1 : [(0x01 : UInt8)].length ≤ 32}
    (run : SFunc.RunCut prog sevm [] (St b [key, tail] M G)
      (.next (.push p le) (.next (.reg .calldataload) (.next (.reg (.dup 1)) (.next (.reg .sstore)
        (.next (.push [0x01] le1) (.next (.reg .add) f)))))) r) :
    ∃ G', SFunc.RunCut prog sevm [] (St (wordStore sevm b key off) [1 + key, tail] M G') f r := by
  subst hp
  winv 3
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  winv 2
  exact ⟨_, run⟩

/-- A successful body run is non-static and ends in exactly `submissionPost`. -/
theorem body_inv (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St b [] M G) t_00cd_c1 o) :
    sevm.isStatic = false ∧ ∃ G', o = .halted (submissionPost sevm b M G') := by
  have run := run.cut
  unfold t_00cd_c1 at run
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
  winv 5
  change SFunc.RunCut _ _ _
    (St (tailRead sevm b) [submissionKey (tailWord sevm b), tailWord sevm b] M _) _ _ at run
  obtain ⟨_, run⟩ := word_inv rfl fork run
  obtain ⟨_, run⟩ := word_inv rfl fork run
  obtain ⟨_, run⟩ := word_inv rfl fork run
  obtain ⟨_, run⟩ := word_inv rfl fork run
  obtain ⟨_, run⟩ := word_inv rfl fork run
  winv 3
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sstore fork h
  change SFunc.RunCut _ _ _ (St (recordsWritten sevm b) [tailWord sevm b] M _) _ _ at run
  winv 3
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_calldatacopy h
  winv 2
  change SFunc.RunCut _ _ _ (St (recordsWritten sevm b) [0, Bytes.toB256 [0xb8], tailWord sevm b]
    (copyMemory sevm M) _) logTail _ at run
  obtain ⟨_, rfl⟩ := logTail_inv fork run
  exact ⟨dynamic, _, rfl⟩

private theorem word_exact {x : UInt8} {xs : Bytes} {le : (x :: xs).length ≤ 32} {off key tail : B256}
    {f : SFunc} (hp : Bytes.toB256 (x :: xs) = off)
    (fork : CoveredFork sevm.benvStat.fork) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) {le1 : [(0x01 : UInt8)].length ≤ 32}
    (tail' : SFunc.RunExact prog sevm
      (St (wordStore sevm b key off) [1 + key, tail] M G) f o) :
    SFunc.RunExact prog sevm
      (St b [key, tail] M (G + 3 + 3 + sstoreCost sevm b key (Sevm.dataWord sevm off) + 3 + 3 + 3))
      (.next (.push (x :: xs) le) (.next (.reg .calldataload) (.next (.reg (.dup 1))
        (.next (.reg .sstore) (.next (.push [0x01] le1) (.next (.reg .add) f)))))) o := by
  refine rx_push hp (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstore fork (by omega) dynamic ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  exact rx_add' rfl (by change 1 < 1024; decide) tail'

private theorem word0_exact {key tail : B256} {f : SFunc}
    (fork : CoveredFork sevm.benvStat.fork) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) {le0 : ([] : Bytes).length ≤ 32}
    {le1 : [(0x01 : UInt8)].length ≤ 32}
    (tail' : SFunc.RunExact prog sevm
      (St (wordStore sevm b key 0) [1 + key, tail] M G) f o) :
    SFunc.RunExact prog sevm
      (St b [key, tail] M (G + 3 + 3 + sstoreCost sevm b key (Sevm.dataWord sevm 0) + 3 + 3 + 2))
      (.next (.push [] le0) (.next (.reg .calldataload) (.next (.reg (.dup 1))
        (.next (.reg .sstore) (.next (.push [0x01] le1) (.next (.reg .add) f)))))) o := by
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstore fork (by omega) dynamic ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  exact rx_add' rfl (by change 1 < 1024; decide) tail'

private def memoryTree : SFunc :=
  (.next (.push [0xb8] (by decide)) (.next (.push [] (by decide)) (.next (.push [] (by decide))
    (.next (.reg .calldatacopy) (.next (.push [0xb8] (by decide)) (.next (.push [] (by decide))
      logTail))))))

private def word5Tree : SFunc :=
  (.next (.push [0xa0] (by decide)) (.next (.reg .calldataload) (.next (.reg (.swap 0))
    (.next (.reg .sstore) memoryTree))))

private def wordTree (x : UInt8) (f : SFunc) : SFunc :=
  (.next (.push [x] (by change 1 ≤ 32; decide)) (.next (.reg .calldataload) (.next (.reg (.dup 1))
    (.next (.reg .sstore) (.next (.push [0x01] (by decide)) (.next (.reg .add) f))))))

private def wordsTree : SFunc :=
  (.next (.push [] (by decide)) (.next (.reg .calldataload) (.next (.reg (.dup 1))
    (.next (.reg .sstore) (.next (.push [0x01] (by decide)) (.next (.reg .add)
      (wordTree 0x20 (wordTree 0x40 (wordTree 0x60 (wordTree 0x80 word5Tree))))))))))

private def bodyTree : SFunc :=
  (.next (.push [0x01] (by decide)) (.next (.reg .sload) (.next (.push [0x01] (by decide))
    (.next (.reg .add) (.next (.push [0x01] (by decide)) (.next (.reg .sstore)
      (.next (.push [0x03] (by decide)) (.next (.reg .sload) (.next (.reg (.dup 0))
        (.next (.push [0x06] (by decide)) (.next (.reg .mul) (.next (.push [0x04] (by decide))
          (.next (.reg .add) wordsTree)))))))))))))

private theorem body_split : t_00cd_c1 = bodyTree := rfl

private theorem suffix_exact (fork : CoveredFork sevm.benvStat.fork)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G) :
    SFunc.RunExact prog sevm
      (St (recordsWritten sevm b) [tailWord sevm b] M
        (G + sstoreCost sevm (logged sevm b M) 3 (1 + tailWord sevm b) + 3 + 3 + 3 +
          logGas sevm M + 2 + 3 + copyGas M + 2 + 2 + 3))
      memoryTree (.halted (submissionPost sevm b M G)) := by
  unfold memoryTree
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 2 < 1024; decide) ?_
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 3 < 1024; decide) ?_
  refine rx_calldatacopy (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := fork.rules_push0) (by change 2 < 1024; decide) ?_
  exact logTail_exact (n := Bytes.toB256 [0xb8]) fork dynamic slack

private theorem word5_exact {key tail : B256} {G' : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G')
    (next : SFunc.RunExact prog sevm (St (wordStore sevm b key 160) [tail] M G') memoryTree o) :
    SFunc.RunExact prog sevm
      (St b [key, tail] M (G' + sstoreCost sevm b key (Sevm.dataWord sevm 160) + 3 + 3 + 3))
      word5Tree o := by
  unfold word5Tree
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_swap1 ?_
  exact rx_sstore fork (by omega) dynamic next

private theorem words_exact {key tail : B256} {G' : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G')
    (next : SFunc.RunExact prog sevm (St (recordStore sevm b key) [tail] M G') memoryTree o) :
    SFunc.RunExact prog sevm (St b [key, tail] M (G' + 83 + recordWritesGas sevm b key))
      wordsTree o := by
  have h5 := word5_exact (b := wordStore sevm (wordStore sevm (wordStore sevm (wordStore sevm
    (wordStore sevm b key 0) (1 + key) 32) (1 + (1 + key)) 64) (1 + (1 + (1 + key))) 96)
    (1 + (1 + (1 + (1 + key)))) 128) fork dynamic slack next
  have h4 := word_exact (x := 0x80) (xs := []) (le := by decide) (off := 128) (le1 := by decide)
    rfl fork dynamic (by omega) h5
  have h3 := word_exact (x := 0x60) (xs := []) (le := by decide) (off := 96) (le1 := by decide)
    rfl fork dynamic (by omega) h4
  have h2 := word_exact (x := 0x40) (xs := []) (le := by decide) (off := 64) (le1 := by decide)
    rfl fork dynamic (by omega) h3
  have h1 := word_exact (x := 0x20) (xs := []) (le := by decide) (off := 32) (le1 := by decide)
    rfl fork dynamic (by omega) h2
  have h0 := word0_exact (le0 := by decide) (le1 := by decide) fork dynamic (by omega) h1
  have hgas : ∀ X, X = G' + 83 + recordWritesGas sevm b key →
      SFunc.RunExact prog sevm (St b [key, tail] M X) wordsTree o →
      SFunc.RunExact prog sevm (St b [key, tail] M (G' + 83 + recordWritesGas sevm b key))
        wordsTree o := fun _ eq h => eq ▸ h
  refine hgas _ ?_ h0
  simp only [recordWritesGas]
  omega

/-- The submission body, forward: non-static, with more than the `SSTORE` sentry left at the end. -/
theorem body_exact (fork : CoveredFork sevm.benvStat.fork) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) :
    SFunc.RunExact prog sevm (St b [] M (G + bodyGas sevm b M)) t_00cd_c1
      (.halted (submissionPost sevm b M G)) := by
  have suffix := suffix_exact (b := b) (M := M) fork dynamic slack
  have words := words_exact (b := tailRead sevm b) (key := submissionKey (tailWord sevm b))
    fork dynamic (by omega) suffix
  rw [body_split]
  have hgas : G + bodyGas sevm b M =
      G + sstoreCost sevm (logged sevm b M) 3 (1 + tailWord sevm b) + 3 + 3 + 3 +
          logGas sevm M + 2 + 3 + copyGas M + 2 + 2 + 3
        + 83 + recordWritesGas sevm (tailRead sevm b) (submissionKey (tailWord sevm b))
        + 3 + 3 + 5 + 3 + 3 + sloadCost sevm (countStore sevm b) 3 + 3
        + sstoreCost sevm (afterSload sevm b 1) 1 (1 + countWord sevm b) + 3 + 3 + 3
        + sloadCost sevm b 1 + 3 := by
    simp only [bodyGas]
    omega
  rw [hgas]
  unfold bodyTree
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
  exact words

end Blanc.Lift.BuilderRequest.Deposit
