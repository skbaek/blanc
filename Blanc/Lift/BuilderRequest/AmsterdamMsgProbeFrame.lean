import Blanc.Lift.BuilderRequest.Deposit.Frames
import Blanc.Lift.BuilderRequest.AmsterdamMsgProbeSettle
import Blanc.Lift.BuilderRequest.Deposit.System

/-!
# Probe: the deposit submission frame under Amsterdam

Disposable (goal `blanc-eip8282-builder-requests-v1`, O16). The narrow frame the message probe needs:
forward only, no converse, under `Ready` with enough reservoir for all eight stores, keys distinct.
W11 owns the real statement. The fee recurrence, the guards and the dispatch are reused unchanged; only
the `SLOAD`/`SSTORE` steps move.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestSystem (dispatchGas dispatch_exact dispatchArm)
open RequestFee (feeLoopGas selected)

local notation "A" => amsterdamStateGasRules

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-! ## The shared fee path, with the read record -/

theorem inhibitor_exactA {dest : RequestFee.PushWord} {active revert : SFunc}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hp0 : sevm.benvStat.rules.op.push0 = true)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (tail : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b 0) [b.getStorVal sevm.currentTarget 0] M G) active o) :
    SFunc.RunExact fs sevm (St b [] M (G + 22 + sloadCost sevm b 0 + 2))
      (inhibitorTree dest active revert) o := by
  have hgas : G + 22 + sloadCost sevm b 0 + 2 =
      G + 10 + 3 + 3 + 3 + 3 + sloadCost sevm b 0 + 2 := by
    omega
  rw [hgas]
  unfold inhibitorTree
  refine rx_push0 (h_push0 := hp0) (by change 0 < 1024; decide) ?_
  refine rx_sloadA hacc (by change 0 < 1024; decide) ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_push (w := B256.max) (by decide) (by change 2 < 1024; decide) ?_
  refine rx_eq (v := 0) ?_ (by change 1 < 1024; decide) ?_
  · simp only [B256.eqCheck, ite_eq_right (Ne.symm off)]
  · refine rx_push rfl (by change 2 < 1024; decide) ?_
    exact rx_branch_zero tail

theorem excess_exactA {target over under : RequestFee.PushWord} {window : Nat} {fall : SFunc}
    (hacc : sevm.benvStat.rules.access = .eip2929) (entry : fs[window]? = some fall)
    {slot0 : B256}
    (tail : SFunc.RunExact fs sevm
      (St (afterSloadA sevm b 1)
        [targetExcess target.word slot0 (b.getStorVal sevm.currentTarget 1)] M G) fall o) :
    SFunc.RunExact fs sevm (St b [slot0] M (G + 35 + sloadCost sevm b 1 + 3))
      (excessTree target over under window fall) o := by
  have hgas : G + 35 + sloadCost sevm b 1 + 3 =
      G + 13 + 10 + 3 + 3 + 3 + 3 + sloadCost sevm b 1 + 3 := by
    omega
  rw [hgas]
  unfold excessTree
  refine rx_push (w := (1 : B256)) rfl (by change 1 < 1024; decide) ?_
  refine rx_sloadA hacc (by change 1 < 1024; decide) ?_
  generalize hcount : b.getStorVal sevm.currentTarget 1 = count at tail ⊢
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_gt rfl (by change 2 < 1024; decide) ?_
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  by_cases isOver : target.word < count
  · have flag : B256.gtCheck count target.word = 1 := by
      simp only [B256.gtCheck, ite_eq_left isOver]
    rw [flag]
    refine rx_branch_succ (by decide : (1 : B256) ≠ 0) ?_
    have tail' : SFunc.RunExact fs sevm
        (St (afterSloadA sevm b 1) [(count - target.word) + slot0] M G) fall o := by
      simpa only [targetExcess, ite_eq_left isOver] using tail
    have hgas' : G + 13 = G + 3 + 3 + 3 + 3 + 1 := by simp only [Nat.add_assoc]
    rw [hgas']
    refine rx_dest ?_
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    refine rx_swap1 ?_
    refine rx_sub' rfl (by change 1 < 1024; decide) ?_
    exact rx_add' rfl (by decide) tail'
  · have flag : B256.gtCheck count target.word = 0 := by
      simp only [B256.gtCheck, ite_eq_right isOver]
    rw [flag]
    refine rx_branch_zero ?_
    have tail' : SFunc.RunExact fs sevm (St (afterSloadA sevm b 1) [slot0] M G) fall o := by
      simpa only [targetExcess, ite_eq_right isOver] using tail
    have hgas' : G + 13 = G + 8 + 3 + 2 := by simp only [Nat.add_assoc]
    rw [hgas']
    refine rx_pop ?_
    refine rx_push rfl (by change 1 < 1024; decide) ?_
    exact rx_jump entry tail'

/-- `feeBase` with the read record. -/
def feeBaseA (sevm : Sevm) (b : Devm) : Devm := afterSloadA sevm (afterSloadA sevm b 0) 1

/-- `feePathGas` over the Amsterdam reads. -/
def feePathGasA (sevm : Sevm) (b : Devm) (iterations : Nat) : Nat :=
  feePathFixedGas + feeLoopGas iterations + sloadCost sevm b 0 +
    sloadCost sevm (afterSloadA sevm b 0) 1

theorem feePath_exactA (p : Shape) {revert getter submission : SFunc} {iterations : Nat}
    {finalOutput : B256}
    (hacc : sevm.benvStat.rules.access = .eip2929) (hp0 : sevm.benvStat.rules.op.push0 = true)
    (window : fs[p.window]? = some (windowOf p getter submission))
    (loop : fs[p.loopEntry]? =
      some (RequestFee.loopTree p.post p.loop p.loopEntry
        (RequestFee.postloopTree p.len p.submit getter submission)))
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess p.target.word sevm b) 17 1 17 0
      iterations finalOutput)
    (tail : SFunc.RunExact fs sevm (St (feeBaseA sevm b) [finalOutput / (17 : B256)] M G)
      (selected sevm p.len.word getter submission) o) :
    SFunc.RunExact fs sevm (St b [] M (G + feePathGasA sevm b iterations))
      (feePathTree p revert getter submission) o := by
  have read0 : (afterSloadA sevm b 0).getStorVal sevm.currentTarget 1 =
      b.getStorVal sevm.currentTarget 1 := afterSloadA_getStorVal sevm b 0 _ 1
  have hloop := fun finalCounter => (RequestFee.postloop_exact (len := p.len) (dest := p.submit)
    (w := p.len.word) (numerator := storedExcess p.target.word sevm b) (denominator := 17)
    (accumulator := 0) (output := finalOutput) (counter := finalCounter) (fs := fs) rfl
    (getter := getter) (submission := submission) tail)
  have hlooped := RequestFee.loop_exact loop hp0 wordRun hloop
  have hinit := RequestFee.init_exact hp0 hlooped
  have hwindow : SFunc.RunExact fs sevm
      (St (feeBaseA sevm b) [storedExcess p.target.word sevm b] M
        (G + 45 + feeLoopGas iterations + 19 + 3 + 3 + 1)) (windowOf p getter submission) o := by
    unfold windowOf windowTree
    refine rx_dest ?_
    refine rx_push (w := (17 : B256)) rfl (by change 1 < 1024; decide) ?_
    refine rx_swap1 ?_
    exact hinit
  have hexcess := excess_exactA (b := afterSloadA sevm b 0) (target := p.target) (over := p.over)
    (under := p.under) (slot0 := b.getStorVal sevm.currentTarget 0) hacc window (by
      rw [read0]
      exact hwindow)
  have hguard := inhibitor_exactA (dest := p.revert) (revert := revert) hacc hp0 off hexcess
  have hgas : G + feePathGasA sevm b iterations =
      G + 45 + feeLoopGas iterations + 19 + 3 + 3 + 1 + 35 + sloadCost sevm (afterSloadA sevm b 0) 1 + 3
        + 22 + sloadCost sevm b 0 + 2 := by
    simp only [feePathGasA, feePathFixedGas]
    omega
  rw [hgas]
  exact hguard

/-! ## The submission body -/

def countStoreA (sevm : Sevm) (b : Devm) : Devm :=
  afterSstoreA A sevm (afterSloadA sevm b 1) 1 (1 + countWord sevm b)

def tailWordA (sevm : Sevm) (b : Devm) : B256 := (countStoreA sevm b).getStorVal sevm.currentTarget 3

def tailReadA (sevm : Sevm) (b : Devm) : Devm := afterSloadA sevm (countStoreA sevm b) 3

def wordStoreA (sevm : Sevm) (b : Devm) (key off : B256) : Devm :=
  afterSstoreA A sevm b key (Sevm.dataWord sevm off)

def recordStoreA (sevm : Sevm) (b : Devm) (key : B256) : Devm :=
  wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm b
    key 0) (1 + key) 32) (1 + (1 + key)) 64) (1 + (1 + (1 + key))) 96)
    (1 + (1 + (1 + (1 + key)))) 128) (1 + (1 + (1 + (1 + (1 + key))))) 160

def recordsWrittenA (sevm : Sevm) (b : Devm) : Devm :=
  recordStoreA sevm (tailReadA sevm b) (submissionKey (tailWordA sevm b))

def loggedA (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  (recordsWrittenA sevm b).addLog (submissionLog sevm M)

def submissionBaseA (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  afterSstoreA A sevm (loggedA sevm b M) 3 (1 + tailWordA sevm b)

def submissionPostA (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) : Devm :=
  St (submissionBaseA sevm b M) [] (submissionMemory sevm M) G

def recordWritesGasA (sevm : Sevm) (b : Devm) (key : B256) : Nat :=
  let s0 := wordStoreA sevm b key 0
  let s1 := wordStoreA sevm s0 (1 + key) 32
  let s2 := wordStoreA sevm s1 (1 + (1 + key)) 64
  let s3 := wordStoreA sevm s2 (1 + (1 + (1 + key))) 96
  let s4 := wordStoreA sevm s3 (1 + (1 + (1 + (1 + key)))) 128
  sstoreCostA A sevm b key (Sevm.dataWord sevm 0) +
  sstoreCostA A sevm s0 (1 + key) (Sevm.dataWord sevm 32) +
  sstoreCostA A sevm s1 (1 + (1 + key)) (Sevm.dataWord sevm 64) +
  sstoreCostA A sevm s2 (1 + (1 + (1 + key))) (Sevm.dataWord sevm 96) +
  sstoreCostA A sevm s3 (1 + (1 + (1 + (1 + key)))) (Sevm.dataWord sevm 128) +
  sstoreCostA A sevm s4 (1 + (1 + (1 + (1 + (1 + key))))) (Sevm.dataWord sevm 160)

def bodyGasA (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  136 + sloadCost sevm b 1 + sstoreCostA A sevm (afterSloadA sevm b 1) 1 (1 + countWord sevm b) +
    sloadCost sevm (countStoreA sevm b) 3 +
    recordWritesGasA sevm (tailReadA sevm b) (submissionKey (tailWordA sevm b)) +
    copyGas M + logGas sevm M + sstoreCostA A sevm (loggedA sevm b M) 3 (1 + tailWordA sevm b)

/-- The eight keys, in store order. -/
def bodyKeys (key : B256) : List B256 :=
  [1, key, 1 + key, 1 + (1 + key), 1 + (1 + (1 + key)), 1 + (1 + (1 + (1 + key))),
    1 + (1 + (1 + (1 + (1 + key)))), 3]

theorem Ready.addLog {sevm : Sevm} {d : Devm} {ks : List B256} (l : Log) (r : Ready sevm d ks) :
    Ready sevm (d.addLog l) ks where
  error := r.error
  refund := r.refund
  spill := r.spill
  reservoir := r.reservoir
  clean := r.clean

private def logTreeA : SFunc :=
  (.next (.reg (.log 0)) (.next (.push [0x01] (by decide)) (.next (.reg .add)
    (.next (.push [0x03] (by decide)) (.next (.reg .sstore) (.last .stop))))))

private def memoryTreeA : SFunc :=
  (.next (.push [0xb8] (by decide)) (.next (.push [] (by decide)) (.next (.push [] (by decide))
    (.next (.reg .calldatacopy) (.next (.push [0xb8] (by decide)) (.next (.push [] (by decide))
      logTreeA))))))

private def word5TreeA : SFunc :=
  (.next (.push [0xa0] (by decide)) (.next (.reg .calldataload) (.next (.reg (.swap 0))
    (.next (.reg .sstore) memoryTreeA))))

private def wordTreeA (x : UInt8) (f : SFunc) : SFunc :=
  (.next (.push [x] (by change 1 ≤ 32; decide)) (.next (.reg .calldataload) (.next (.reg (.dup 1))
    (.next (.reg .sstore) (.next (.push [0x01] (by decide)) (.next (.reg .add) f))))))

private def wordsTreeA : SFunc :=
  (.next (.push [] (by decide)) (.next (.reg .calldataload) (.next (.reg (.dup 1))
    (.next (.reg .sstore) (.next (.push [0x01] (by decide)) (.next (.reg .add)
      (wordTreeA 0x20 (wordTreeA 0x40 (wordTreeA 0x60 (wordTreeA 0x80 word5TreeA))))))))))

private def bodyTreeA : SFunc :=
  (.next (.push [0x01] (by decide)) (.next (.reg .sload) (.next (.push [0x01] (by decide))
    (.next (.reg .add) (.next (.push [0x01] (by decide)) (.next (.reg .sstore)
      (.next (.push [0x03] (by decide)) (.next (.reg .sload) (.next (.reg (.dup 0))
        (.next (.push [0x06] (by decide)) (.next (.reg .mul) (.next (.push [0x04] (by decide))
          (.next (.reg .add) wordsTreeA)))))))))))))

private theorem body_splitA : t_00cd_c1 = bodyTreeA := rfl

section body

variable (hsg : sevm.benvStat.rules.stateGas = some A) (dynamic : sevm.isStatic = false)
  (hacc : sevm.benvStat.rules.access = .eip2929) (hp0 : sevm.benvStat.rules.op.push0 = true)
include hsg dynamic

private theorem log_exactA {tail : B256} (r : Ready sevm b [3]) (slack : gCallStipend < G)
    {le1 : [(0x01 : UInt8)].length ≤ 32} {le3 : [(0x03 : UInt8)].length ≤ 32} :
    SFunc.RunExact prog sevm
      (St b [0, 184, tail] (copyMemory sevm M)
        (G + sstoreCostA A sevm (b.addLog (submissionLog sevm M)) 3 (1 + tail) + 3 + 3 + 3 +
          logGas sevm M))
      (.next (.reg (.log 0)) (.next (.push [0x01] le1) (.next (.reg .add)
        (.next (.push [0x03] le3) (.next (.reg .sstore) (.last .stop))))))
      (.halted (St (afterSstoreA A sevm (b.addLog (submissionLog sevm M)) 3 (1 + tail)) []
        (submissionMemory sevm M) G)) := by
  have emitted : Ninst.RunCompiled sevm
      (St b [0, 184, tail] (copyMemory sevm M)
        (G + sstoreCostA A sevm (b.addLog (submissionLog sevm M)) 3 (1 + tail) + 3 + 3 + 3 +
          logGas sevm M)) (.reg (.log 0))
      (St (b.addLog (submissionLog sevm M)) [tail] (submissionMemory sevm M)
        (G + sstoreCostA A sevm (b.addLog (submissionLog sevm M)) 3 (1 + tail) + 3 + 3 + 3)) :=
    Ninst.runCompiled_log_of (n := 0) (i := 0) (sz := 184) (topics := []) (s := [tail])
      rfl rfl dynamic (Devm.extCost_add_of_size rfl rfl) rfl rfl rfl
  refine .next emitted ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_sstoreR hsg dynamic (Ready.addLog _ r) (by omega) ?_
  exact .last rfl

private theorem suffix_exactA (hp0 : sevm.benvStat.rules.op.push0 = true) (r : Ready sevm (recordsWrittenA sevm b) [3])
    (slack : gCallStipend < G) :
    SFunc.RunExact prog sevm
      (St (recordsWrittenA sevm b) [tailWordA sevm b] M
        (G + sstoreCostA A sevm (loggedA sevm b M) 3 (1 + tailWordA sevm b) + 3 + 3 + 3 +
          logGas sevm M + 2 + 3 + copyGas M + 2 + 2 + 3))
      memoryTreeA (.halted (submissionPostA sevm b M G)) := by
  unfold memoryTreeA
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := hp0) (by change 2 < 1024; decide) ?_
  refine rx_push0 (h_push0 := hp0) (by change 3 < 1024; decide) ?_
  refine rx_calldatacopy (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := hp0) (by change 2 < 1024; decide) ?_
  exact log_exactA hsg dynamic r slack

private theorem word_exactA {x : UInt8} {xs : Bytes} {le : (x :: xs).length ≤ 32} {off key tail : B256}
    {f : SFunc} {ks : List B256} (hp : Bytes.toB256 (x :: xs) = off)
    (r : Ready sevm b (key :: ks)) (slack : gCallStipend < G) {le1 : [(0x01 : UInt8)].length ≤ 32}
    (tail' : SFunc.RunExact prog sevm
      (St (wordStoreA sevm b key off) [1 + key, tail] M G) f o) :
    SFunc.RunExact prog sevm
      (St b [key, tail] M (G + 3 + 3 + sstoreCostA A sevm b key (Sevm.dataWord sevm off) + 3 + 3 + 3))
      (.next (.push (x :: xs) le) (.next (.reg .calldataload) (.next (.reg (.dup 1))
        (.next (.reg .sstore) (.next (.push [0x01] le1) (.next (.reg .add) f)))))) o := by
  refine rx_push hp (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstoreR hsg dynamic r (by omega) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  exact rx_add' rfl (by change 1 < 1024; decide) tail'

private theorem word0_exactA {key tail : B256} {f : SFunc} {ks : List B256}
    (hp0 : sevm.benvStat.rules.op.push0 = true)
    (r : Ready sevm b (key :: ks)) (slack : gCallStipend < G) {le0 : ([] : Bytes).length ≤ 32}
    {le1 : [(0x01 : UInt8)].length ≤ 32}
    (tail' : SFunc.RunExact prog sevm
      (St (wordStoreA sevm b key 0) [1 + key, tail] M G) f o) :
    SFunc.RunExact prog sevm
      (St b [key, tail] M (G + 3 + 3 + sstoreCostA A sevm b key (Sevm.dataWord sevm 0) + 3 + 3 + 2))
      (.next (.push [] le0) (.next (.reg .calldataload) (.next (.reg (.dup 1))
        (.next (.reg .sstore) (.next (.push [0x01] le1) (.next (.reg .add) f)))))) o := by
  refine rx_push0 (h_push0 := hp0) (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstoreR hsg dynamic r (by omega) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  exact rx_add' rfl (by change 1 < 1024; decide) tail'

/-- The submission body under Amsterdam. -/
theorem body_exactA (hacc : sevm.benvStat.rules.access = .eip2929)
    (hp0 : sevm.benvStat.rules.op.push0 = true) (slack : gCallStipend < G)
    (r : Ready sevm b (bodyKeys (submissionKey (tailWordA sevm b))))
    (nodup : (bodyKeys (submissionKey (tailWordA sevm b))).Nodup) :
    SFunc.RunExact prog sevm (St b [] M (G + bodyGasA sevm b M)) t_00cd_c1
      (.halted (submissionPostA sevm b M G)) := by
  generalize hK : submissionKey (tailWordA sevm b) = K at r nodup
  simp only [bodyKeys] at r nodup
  have n0 := List.nodup_cons.mp nodup
  have n1 := List.nodup_cons.mp n0.2
  have n2 := List.nodup_cons.mp n1.2
  have n3 := List.nodup_cons.mp n2.2
  have n4 := List.nodup_cons.mp n3.2
  have n5 := List.nodup_cons.mp n4.2
  have n6 := List.nodup_cons.mp n5.2
  have rc := Ready.sstore (r.sload 1) n0.1 (1 + countWord sevm b)
  have rt : Ready sevm (tailReadA sevm b) _ := rc.sload 3
  have r0 : Ready sevm (wordStoreA sevm (tailReadA sevm b) K 0) _ := Ready.sstore rt n1.1 (Sevm.dataWord sevm 0)
  have r1 : Ready sevm (wordStoreA sevm (wordStoreA sevm (tailReadA sevm b) K 0) (1 + K) 32) _ := Ready.sstore r0 n2.1 (Sevm.dataWord sevm 32)
  have r2 : Ready sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (tailReadA sevm b) K 0) (1 + K) 32) (1 + (1 + K)) 64) _ := Ready.sstore r1 n3.1 (Sevm.dataWord sevm 64)
  have r3 : Ready sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (tailReadA sevm b) K 0) (1 + K) 32) (1 + (1 + K)) 64) (1 + (1 + (1 + K))) 96) _ := Ready.sstore r2 n4.1 (Sevm.dataWord sevm 96)
  have r4 : Ready sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (tailReadA sevm b) K 0) (1 + K) 32) (1 + (1 + K)) 64) (1 + (1 + (1 + K))) 96) (1 + (1 + (1 + (1 + K)))) 128) _ := Ready.sstore r3 n5.1 (Sevm.dataWord sevm 128)
  have r5 := Ready.sstore r4 n6.1 (Sevm.dataWord sevm 160)
  have rw' : Ready sevm (recordsWrittenA sevm b) [3] := by
    unfold recordsWrittenA recordStoreA wordStoreA
    rw [hK]
    exact r5
  have suffix := suffix_exactA (b := b) (M := M) hsg dynamic hp0 rw' slack
  have h5 : SFunc.RunExact prog sevm
      (St (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm
        (tailReadA sevm b) K 0) (1 + K) 32) (1 + (1 + K)) 64) (1 + (1 + (1 + K))) 96)
          (1 + (1 + (1 + (1 + K)))) 128) [1 + (1 + (1 + (1 + (1 + K)))), tailWordA sevm b] M
        (G + sstoreCostA A sevm (loggedA sevm b M) 3 (1 + tailWordA sevm b) + 3 + 3 + 3 +
          logGas sevm M + 2 + 3 + copyGas M + 2 + 2 + 3 +
          sstoreCostA A sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm
            (wordStoreA sevm (tailReadA sevm b) K 0) (1 + K) 32) (1 + (1 + K)) 64)
              (1 + (1 + (1 + K))) 96) (1 + (1 + (1 + (1 + K)))) 128)
            (1 + (1 + (1 + (1 + (1 + K))))) (Sevm.dataWord sevm 160) + 3 + 3 + 3))
      word5TreeA (.halted (submissionPostA sevm b M G)) := by
    unfold word5TreeA
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    refine rx_calldataload (by change 2 < 1024; decide) ?_
    refine rx_swap1 ?_
    refine rx_sstoreR hsg dynamic r4 (by omega) ?_
    have e : recordsWrittenA sevm b = afterSstoreA A sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm (wordStoreA sevm
        (wordStoreA sevm (tailReadA sevm b) K 0) (1 + K) 32) (1 + (1 + K)) 64)
          (1 + (1 + (1 + K))) 96) (1 + (1 + (1 + (1 + K)))) 128)
          (1 + (1 + (1 + (1 + (1 + K))))) (Sevm.dataWord sevm 160) := by
      unfold recordsWrittenA recordStoreA
      rw [hK]
      rfl
    rw [show Bytes.toB256 [160] = (160 : B256) by decide, ← e]
    exact suffix
  have h4 := word_exactA (x := 0x80) (xs := []) (le := by decide) (off := 128) (le1 := by decide)
    (f := word5TreeA) hsg dynamic rfl r3 (by omega) h5
  have h3 := word_exactA (x := 0x60) (xs := []) (le := by decide) (off := 96) (le1 := by decide)
    hsg dynamic rfl r2 (by omega) h4
  have h2 := word_exactA (x := 0x40) (xs := []) (le := by decide) (off := 64) (le1 := by decide)
    hsg dynamic rfl r1 (by omega) h3
  have h1 := word_exactA (x := 0x20) (xs := []) (le := by decide) (off := 32) (le1 := by decide)
    hsg dynamic rfl r0 (by omega) h2
  have hgasBody : G + bodyGasA sevm b M =
      (G + sstoreCostA A sevm (loggedA sevm b M) 3 (1 + tailWordA sevm b) + 3 + 3 + 3 +
          logGas sevm M + 2 + 3 + copyGas M + 2 + 2 + 3 +
          recordWritesGasA sevm (tailReadA sevm b) K + 83)
        + 3 + 3 + 5 + 3 + 3 + sloadCost sevm (countStoreA sevm b) 3 + 3
        + sstoreCostA A sevm (afterSloadA sevm b 1) 1 (1 + countWord sevm b) + 3 + 3 + 3
        + sloadCost sevm b 1 + 3 := by
    simp only [bodyGasA, hK]
    omega
  rw [body_splitA, hgasBody]
  unfold bodyTreeA
  refine rx_push rfl (by decide) ?_
  refine rx_sloadV hacc (by decide) (v := countWord sevm b) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by change 0 < 1024; decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_sstoreR hsg dynamic (r.sload 1) (by omega) ?_
  refine rx_push rfl (by decide) ?_
  refine rx_sloadV hacc (by decide) (v := tailWordA sevm b) rfl ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_mul rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  change SFunc.RunExact prog sevm
    (St (tailReadA sevm b) [submissionKey (tailWordA sevm b), tailWordA sevm b] M _) wordsTreeA _
  rw [hK]
  have hg0 : ∀ X, X = (G + sstoreCostA A sevm (loggedA sevm b M) 3 (1 + tailWordA sevm b) + 3 + 3 + 3 +
          logGas sevm M + 2 + 3 + copyGas M + 2 + 2 + 3 +
          recordWritesGasA sevm (tailReadA sevm b) K + 83) →
      SFunc.RunExact prog sevm (St (tailReadA sevm b) [K, tailWordA sevm b] M X) wordsTreeA
        (.halted (submissionPostA sevm b M G)) →
      SFunc.RunExact prog sevm (St (tailReadA sevm b) [K, tailWordA sevm b] M
        (G + sstoreCostA A sevm (loggedA sevm b M) 3 (1 + tailWordA sevm b) + 3 + 3 + 3 +
          logGas sevm M + 2 + 3 + copyGas M + 2 + 2 + 3 +
          recordWritesGasA sevm (tailReadA sevm b) K + 83)) wordsTreeA
        (.halted (submissionPostA sevm b M G)) := fun _ e h => e ▸ h
  have h0 := word0_exactA (le0 := by decide) (le1 := by decide) hsg dynamic hp0 rt (by omega) h1
  refine hg0 _ ?_ h0
  simp only [recordWritesGasA]
  omega

end body

/-! ## The bytes -/

theorem progNoExec_deposit : ProgNoExec cert.prog := progNoExec_of_all (by decide +kernel)

/-- The charge of a submission from the frame's start. -/
def submissionGasA (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  bodyGasA sevm (feeBaseA sevm b) M + 88 + feePathGasA sevm b iterations + dispatchGas

/-- **A deposit submission's frame under Amsterdam, forward.** -/
theorem exec_submission_exactA {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (hfork : sevm.benvStat.fork = .amsterdam)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 184)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput)
    (admitted : Admitted sevm (finalOutput / (17 : B256)))
    (r : Ready sevm (feeBaseA sevm b) (bodyKeys (submissionKey (tailWordA sevm (feeBaseA sevm b)))))
    (nodup : (bodyKeys (submissionKey (tailWordA sevm (feeBaseA sevm b)))).Nodup) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGasA sevm b M iterations))
      (.ok (submissionPostA sevm (feeBaseA sevm b) M G))) := by
  have hsg := Blanc.amsterdam_stateGas hfork
  have hacc := Blanc.amsterdam_access hfork
  have hp0 := Blanc.amsterdam_push0 hfork
  have word : sevm.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  have body := guards_exact admitted (body_exactA (b := feeBaseA sevm b) (M := M) hsg dynamic hacc hp0
    slack r nodup)
  have path := feePath_exactA userPath.shape (revert := userPath.revert)
    (getter := userPath.getter) (submission := t_009f_c1) hacc hp0 userPath.window userPath.loop off
    wordRun (by
      rw [RequestFee.selected, ite_eq_left word]
      exact body)
  have hgas : G + submissionGasA sevm b M iterations =
      (G + bodyGasA sevm (feeBaseA sevm b) M + 88 + feePathGasA sevm b iterations) + dispatchGas := by
    simp only [submissionGasA, Nat.add_assoc]
  rw [hgas]
  apply lift_exact_noExec userPath.check userPath.jumps hcode progNoExec_deposit
  refine ⟨_, userPath.root, dispatch_exact ?_⟩
  simp only [dispatchArm, ite_eq_right caller]
  exact path

end Blanc.Lift.BuilderRequest.Deposit
