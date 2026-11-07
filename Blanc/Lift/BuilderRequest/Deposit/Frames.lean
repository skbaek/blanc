import Blanc.Lift.BuilderRequest.Deposit.Submission
import Blanc.Lift.BuilderRequest.QueueLayout

/-!
# The deposit contract's user frames, under covered forks

Every successful non-system frame at the deposit code is exactly a submission or a fee read, each
with its exact storage, logs and return bytes, and each of those has a converse constructing the
execution. These are statements about one frame over any storage. They say nothing about which
storage is reachable, or about any history, and nothing here is stated for Amsterdam.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune

/-- The storage a submission leaves, in the code's write order, so it stays exact when a record key
aliases a metadata slot: the count in slot 1 is bumped, six calldata words go to the six keys from
`4 + 6 * tail` up, and the tail in slot 3 is bumped. Slot 0 and slot 2 are not written. -/
def submittedStorage (sevm : Sevm) (s : Stor) : Stor :=
  let tail := s.get 3
  let key := recordKey tail
  ((((((((s.set 1 (1 + s.get 1)).set key (Sevm.dataWord sevm 0)).set (1 + key)
    (Sevm.dataWord sevm 32)).set (1 + (1 + key)) (Sevm.dataWord sevm 64)).set (1 + (1 + (1 + key)))
    (Sevm.dataWord sevm 96)).set (1 + (1 + (1 + (1 + key)))) (Sevm.dataWord sevm 128)).set
    (1 + (1 + (1 + (1 + (1 + key))))) (Sevm.dataWord sevm 160)).set 3 (1 + tail))

/-- The record the code writes at tail `n` is the queue's record `n`, at width 6. -/
theorem recordKey_queueSlot (n : Nat) : recordKey n.toB256 = queueSlot 6 n 0 :=
  record_key 6 n

/-- What a successful submission does, for the fee recurrence's iteration count and final output. -/
structure Submitted (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) :
    Prop where
  /-- The frame is not static. -/
  dynamic : sevm.isStatic = false
  /-- The calldata is exactly 184 bytes. -/
  length : sevm.data.length = 184
  /-- Slot 0 is not the inhibitor. -/
  active : pre.getStorVal sevm.currentTarget 0 ≠ B256.max
  /-- The word recurrence ran on `slot0 + max(0, count - 8)`. -/
  quote : WordFakeExponential.Run (storedExcess 8 sevm pre) 17 1 17 0 iterations finalOutput
  /-- At least 1 ETH credited, and value covering the credit plus the quoted fee. -/
  admitted : Admitted sevm (finalOutput / (17 : B256))
  /-- The contract's storage is exactly `submittedStorage`. -/
  storage : post.getStor sevm.currentTarget =
    submittedStorage sevm (pre.getStor sevm.currentTarget)
  /-- No other account's storage changed. -/
  otherStorage : ∀ address, address ≠ sevm.currentTarget →
    post.getStor address = pre.getStor address
  /-- No balance changed within the frame's code. -/
  balance : ∀ address, post.getBal address = pre.getBal address
  /-- One topicless log is appended, its data the calldata. -/
  logs : post.logs = pre.logs ++ [⟨sevm.currentTarget, [], sevm.data⟩]
  /-- `STOP` returns nothing of its own: the output is the one the frame started with. -/
  output : post.output = pre.output
  /-- The whole post state, including warmed keys, refunds and memory. -/
  state : ∃ gas, post = submissionPost sevm (feeBase sevm pre) pre.memory gas

/-- **Deposit frames.** A successful non-system frame at the deposit code. -/
inductive UserFrame (sevm : Sevm) (pre post : Devm) : Prop where
  /-- A submission. -/
  | submission (iterations : Nat) (finalOutput : B256)
      (effect : Submitted sevm pre post iterations finalOutput)
  /-- A fee read: empty calldata. -/
  | feeRead (iterations : Nat) (finalOutput : B256) (empty : sevm.data = [])
      (effect : UserPath.FeeRead 8 sevm pre post iterations finalOutput)

variable {sevm : Sevm} {pre post b : Devm} {M : Mem} {G : Nat}

private theorem read_feeBase (key : B256) (a : Adr) (s : Devm) :
    (feeBase sevm s).getStorVal a key = s.getStorVal a key := by
  rw [feeBase, afterSload_getStorVal, afterSload_getStorVal]

private theorem countWord_feeBase (s : Devm) :
    countWord sevm (feeBase sevm s) = s.getStorVal sevm.currentTarget 1 :=
  read_feeBase 1 _ s

private theorem tailWord_eq (s : Devm) :
    tailWord sevm s = s.getStorVal sevm.currentTarget 3 := by
  change (Devm.getStor (countStore sevm s) sevm.currentTarget).get 3 =
    (Devm.getStor s sevm.currentTarget).get 3
  rw [countStore, afterSstore_getStor_self, afterSload_getStor,
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3)]

private theorem wordStore_getStor (s : Devm) (key off : B256) :
    (wordStore sevm s key off).getStor sevm.currentTarget =
      (s.getStor sevm.currentTarget).set key (Sevm.dataWord sevm off) :=
  afterSstore_getStor_self sevm s key _

private theorem wordStore_other (s : Devm) (key off : B256) {a : Adr}
    (other : a ≠ sevm.currentTarget) :
    (wordStore sevm s key off).getStor a = s.getStor a :=
  afterSstore_getStor_ne sevm s key _ a other.symm

private theorem wordStore_logs (s : Devm) (key off : B256) :
    (wordStore sevm s key off).logs = s.logs := afterSstore_logs sevm s key _

private theorem wordStore_output (s : Devm) (key off : B256) :
    (wordStore sevm s key off).output = s.output := afterSstore_output sevm s key _

private theorem wordStore_getBal (s : Devm) (key off : B256) (a : Adr) :
    (wordStore sevm s key off).getBal a = s.getBal a := afterSstore_getBal a

private theorem recordsWritten_getStor (s : Devm) :
    (recordsWritten sevm s).getStor sevm.currentTarget =
      let tail := tailWord sevm s
      let key := recordKey tail
      (((((((s.getStor sevm.currentTarget).set 1 (1 + countWord sevm s)).set key
        (Sevm.dataWord sevm 0)).set (1 + key) (Sevm.dataWord sevm 32)).set (1 + (1 + key))
        (Sevm.dataWord sevm 64)).set (1 + (1 + (1 + key))) (Sevm.dataWord sevm 96)).set
        (1 + (1 + (1 + (1 + key)))) (Sevm.dataWord sevm 128)).set
        (1 + (1 + (1 + (1 + (1 + key))))) (Sevm.dataWord sevm 160) := by
  simp only [recordsWritten, recordStore, wordStore_getStor, tailRead, afterSload_getStor,
    countStore, afterSstore_getStor_self]

private theorem stop_projections (B : Devm) (S : List B256) (M' : Mem) (G' : Nat) (a : Adr) :
    (St B S M' G').getStor a = B.getStor a ∧ (St B S M' G').getBal a = B.getBal a ∧
      (St B S M' G').logs = B.logs ∧ (St B S M' G').output = B.output :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem addLog_getBal (w : Devm) (l : Log) (a : Adr) :
    (w.addLog l).getBal a = w.getBal a := rfl

private theorem addLog_output (w : Devm) (l : Log) : (w.addLog l).output = w.output := rfl

private theorem afterSload_getBal (w : Devm) (k : B256) (a : Adr) :
    (afterSload sevm w k).getBal a = w.getBal a := by
  simp only [Devm.getBal, afterSload_getAcct]

/-- The log reads back exactly the 184 bytes the frame was called with. -/
theorem submissionLog_eq (hlen : sevm.data.length = 184) (wf : Mem.Wf M) :
    submissionLog sevm M = ⟨sevm.currentTarget, [], sevm.data⟩ := by
  have copied : sevm.data.sliceD 0 184 0 = sevm.data := by
    rw [List.sliceD, List.drop_zero]
    exact List.takeD_eq_self 0 hlen.symm
  have reads := (Mem.reads_data M).write wf 0 (sevm.data.sliceD 0 184 0)
  have image := reads.read 0 184
  change ((copyMemory sevm M).read 0 184).1 =
    (Bytes.writeAt M.data.toList 0 (sevm.data.sliceD 0 184 0)).sliceD 0 184 0 at image
  rw [copied] at image
  have written : (Bytes.writeAt M.data.toList 0 sevm.data).sliceD 0 184 0 = sevm.data := by
    have whole := Bytes.sliceD_writeAt M.data.toList sevm.data 0
    rwa [hlen] at whole
  rw [written] at image
  rw [submissionLog, image]

/-- The observable effects of `submissionPost`. -/
theorem submissionPost_effects (hlen : sevm.data.length = 184) (wf : Mem.Wf M) (gas : Nat) :
    (submissionPost sevm (feeBase sevm b) M gas).getStor sevm.currentTarget =
      submittedStorage sevm (b.getStor sevm.currentTarget) ∧
    (∀ a, a ≠ sevm.currentTarget →
      (submissionPost sevm (feeBase sevm b) M gas).getStor a = b.getStor a) ∧
    (∀ a, (submissionPost sevm (feeBase sevm b) M gas).getBal a = b.getBal a) ∧
    (submissionPost sevm (feeBase sevm b) M gas).logs =
      b.logs ++ [⟨sevm.currentTarget, [], sevm.data⟩] ∧
    (submissionPost sevm (feeBase sevm b) M gas).output = b.output := by
  have facts := fun a => stop_projections (submissionBase sevm (feeBase sevm b) M) []
    (submissionMemory sevm M) gas a
  have base := read_feeBase (sevm := sevm) (s := b)
  unfold submissionPost
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (facts _).1.trans ?_
    rw [submissionBase, afterSstore_getStor_self, logged, Devm.addLog_getStor,
      recordsWritten_getStor, tailWord_eq, countWord_feeBase, base]
    simp only [submittedStorage, feeBase, afterSload_getStor]
    rfl
  · intro a other
    refine (facts a).1.trans ?_
    simp only [submissionBase, logged, recordsWritten, recordStore, tailRead, countStore, feeBase,
      afterSstore_getStor_ne _ _ _ _ _ other.symm, wordStore_other _ _ _ other, afterSload_getStor,
      Devm.addLog_getStor]
  · intro a
    refine (facts a).2.1.trans ?_
    simp only [submissionBase, logged, addLog_getBal, recordsWritten, recordStore, tailRead,
      countStore, feeBase, afterSstore_getBal, wordStore_getBal, afterSload_getBal]
  · refine (facts sevm.currentTarget).2.2.1.trans ?_
    rw [submissionBase, afterSstore_logs, logged, Devm.addLog_logs, submissionLog_eq hlen wf]
    simp only [recordsWritten, recordStore, wordStore_logs, tailRead, afterSload_logs, countStore,
      afterSstore_logs, feeBase]
  · refine (facts sevm.currentTarget).2.2.2.trans ?_
    simp only [submissionBase, logged, addLog_output, afterSstore_output, recordsWritten, recordStore,
      wordStore_output, tailRead, afterSload_output, countStore, feeBase]

/-- **Deposit frames.** Every successful execution of the deposit code at a non-system caller, from
an empty stack, is a submission or a fee read. `aligned` and `wf` hold of the empty memory every
frame starts with; `lengthBound` holds of any calldata a frame can carry, since `CALLDATASIZE` is
read as a word. `exec_submission_exact` and `exec_fee_read_exact` are the converses. -/
theorem exec_user_frame (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) : UserFrame sevm pre post := by
  obtain ⟨_, run⟩ := UserPath.exec_user (k := userPath) hcode fork stack caller exec
  obtain ⟨active, iterations, finalOutput, wordRun, G0, run⟩ :=
    feePath_inv userPath.shape fork userPath.revert_noOk userPath.window userPath.loop run
  by_cases hlen : sevm.data.length.toB256 = 184
  · have literal : sevm.data.length = 184 := by
      have values := congrArg B256.toNat hlen
      rwa [B256.toNat_toB256_of_lt lengthBound] at values
    have hword : sevm.data.length.toB256 = userPath.shape.len.word := hlen
    have run' : SFunc.Run prog sevm (St (feeBase sevm pre) [finalOutput / (17 : B256)] pre.memory G0)
        t_009f_c1 (.halted post) := by
      rw [RequestFee.selected, ite_eq_left hword] at run
      exact run
    obtain ⟨admitted, _, run⟩ := guards_inv run'
    obtain ⟨dynamic, gas, state⟩ := body_inv fork run
    have state := Outcome.halted.inj state
    subst state
    obtain ⟨storage, other, balance, logs, output⟩ :=
      submissionPost_effects (b := pre) (M := pre.memory) literal wf gas
    exact .submission iterations finalOutput ⟨dynamic, literal, active, wordRun, admitted, storage,
      other, balance, logs, output, gas, rfl⟩
  · have hword : sevm.data.length.toB256 ≠ userPath.shape.len.word := hlen
    have run' : SFunc.Run userPath.cert.prog sevm
        (St (feeBase sevm pre) [finalOutput / (17 : B256)] pre.memory G0)
        userPath.getter (.halted post) := by
      rw [RequestFee.selected, ite_eq_right hword] at run
      exact run
    obtain ⟨empty, _, _⟩ := RequestFee.guard_inv userPath.getterRevert_noOk run'
    have literal : sevm.data = [] := by
      have values := congrArg B256.toNat empty
      rw [B256.toNat_toB256_of_lt lengthBound] at values
      exact List.eq_nil_of_length_eq_zero values
    obtain ⟨iterations', finalOutput', read⟩ := UserPath.exec_fee_read (k := userPath) hcode fork
      stack aligned wf caller literal exec
    exact .feeRead iterations' finalOutput' literal read

/-- **Deposit fee read.** A successful empty-calldata execution at a non-system caller carries no
value, changes no storage, balance or log, and returns the word recurrence's quotient on
`slot0 + max(0, count - 8)`. -/
theorem exec_fee_read (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations finalOutput, UserPath.FeeRead 8 sevm pre post iterations finalOutput :=
  UserPath.exec_fee_read (k := userPath) hcode fork stack aligned wf caller empty exec

/-- The charge of a submission, from the frame's start. -/
def submissionGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  bodyGas sevm (feeBase sevm b) M + 88 + feePathGas sevm b iterations + dispatchGas

/-- **Submission, forward.** 184 bytes of calldata in a non-static frame, slot 0 off the inhibitor,
and the guards' `Admitted` give a successful execution at the exact charge, leaving `slack` over the
`SSTORE` sentry. -/
theorem exec_submission_exact {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 184)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput)
    (admitted : Admitted sevm (finalOutput / (17 : B256))) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGas sevm b M iterations))
      (.ok (submissionPost sevm (feeBase sevm b) M G))) := by
  have word : sevm.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  have body := guards_exact admitted (body_exact (b := feeBase sevm b) (M := M) fork dynamic slack)
  have path := feePath_exact userPath.shape (revert := userPath.revert)
    (getter := userPath.getter) (submission := t_009f_c1) fork userPath.window userPath.loop off
    wordRun (by
      rw [RequestFee.selected, ite_eq_left word]
      exact body)
  have hgas : G + submissionGas sevm b M iterations =
      (G + bodyGas sevm (feeBase sevm b) M + 88 + feePathGas sevm b iterations) + dispatchGas := by
    simp only [submissionGas, Nat.add_assoc]
  rw [hgas]
  exact UserPath.exec_of_user (k := userPath) hcode fork caller path

/-- **Deposit fee read, forward.** Empty calldata, no value and slot 0 off the inhibitor give a
successful execution at the exact charge, returning the word recurrence's quotient on
`slot0 + max(0, count - 8)`. -/
theorem exec_fee_read_exact {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M iterations))
      (.ok (RequestFee.feeGetterPost (feeBase sevm b) M (finalOutput / (17 : B256)) G))) :=
  UserPath.exec_fee_read_exact (k := userPath) hcode fork aligned caller empty zero off wordRun

/-- At excess 0 the fee recurrence takes one step and quotes 1 wei. -/
theorem quote_zero_excess : WordFakeExponential.Run 0 17 1 17 0 1 17 := by
  have next : WordFakeExponential.nextAccumulator 0 17 1 17 = 0 := by decide
  have sum : (0 : B256) + 17 = 17 := by decide
  refine .step (by decide) ?_
  rw [next, sum]
  exact .stop _ _

/-- The `Admitted` premise can be met: all-ones calldata credits `(2^64 - 1) * 10^9` wei, and a
value above that by the fee of 1 covers it. -/
theorem admitted_witness (data : sevm.data = List.replicate 184 0xff)
    (value : (2 ^ 64 - 1) * 10 ^ 9 + 1 ≤ sevm.value.toNat) : Admitted sevm 1 := by
  have amount : amountGwei sevm = amountMask := by
    rw [amountGwei, Sevm.dataWord, data]
    decide
  have credit : creditedWei sevm = (2 ^ 64 - 1) * 10 ^ 9 := by
    rw [creditedWei, amount]
    rfl
  refine ⟨?_, ?_⟩
  · rw [credit]
    decide
  · rw [credit]
    exact value

/-- **The submission's premises can all be met together.** On storage whose slots 0 and 1 are zero,
as at deployment, all-ones calldata with enough value in a non-static frame runs to `STOP`. -/
theorem exec_submission_witness (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (data : sevm.data = List.replicate 184 0xff)
    (value : (2 ^ 64 - 1) * 10 ^ 9 + 1 ≤ sevm.value.toNat) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) (slot0 : b.getStorVal sevm.currentTarget 0 = 0)
    (slot1 : b.getStorVal sevm.currentTarget 1 = 0) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGas sevm b M 1))
      (.ok (submissionPost sevm (feeBase sevm b) M G))) := by
  have excess : storedExcess 8 sevm b = 0 := by
    rw [storedExcess, slot0, slot1]
    decide
  have fee : (17 : B256) / (17 : B256) = 1 := by decide
  refine exec_submission_exact (finalOutput := 17) hcode fork caller (by rw [data]; rfl) dynamic
    slack (by rw [slot0]; decide) (by rw [excess]; exact quote_zero_excess) ?_
  rw [fee]
  exact admitted_witness data value

end Blanc.Lift.BuilderRequest.Deposit
