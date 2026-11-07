import Blanc.Lift.BuilderRequest.Deposit.Submission
import Blanc.Lift.BuilderRequest.QueueLayout

/-!
# The deposit contract's user frames, under covered forks

Every successful non-system frame at the deposit code is exactly a submission or a fee read, each
with its exact storage, logs and return bytes, and each of those has a converse constructing the
execution. These are statements about one frame over any storage, each an instance of a statement on a fork's
`StorageSteps` that `Deposit.SubmissionAmsterdam` instantiates too. They say nothing about which
storage is reachable, or about any history.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestSystem (dispatchGas)

/-- The storage a submission leaves, in the code's write order, so it stays exact when a record key
aliases a metadata slot: the count in slot 1 is bumped, six calldata words go to the six keys from
`4 + 6 * tail` up, and the tail in slot 3 is bumped. Slot 0 and slot 2 are not written. -/
def submittedStorage (sevm : Sevm) (s : Stor) : Stor :=
  let tail := s.get 3
  let key := submissionKey tail
  ((((((((s.set 1 (1 + s.get 1)).set key (Sevm.dataWord sevm 0)).set (1 + key)
    (Sevm.dataWord sevm 32)).set (1 + (1 + key)) (Sevm.dataWord sevm 64)).set (1 + (1 + (1 + key)))
    (Sevm.dataWord sevm 96)).set (1 + (1 + (1 + (1 + key)))) (Sevm.dataWord sevm 128)).set
    (1 + (1 + (1 + (1 + (1 + key))))) (Sevm.dataWord sevm 160)).set 3 (1 + tail))

/-- The record the code writes at tail `n` is the queue's record `n`, at width 6. -/
theorem submissionKey_queueSlot (n : Nat) : submissionKey n.toB256 = queueSlot 6 n 0 :=
  record_key 6 n

variable {sevm : Sevm}

/-- What a submission's frame does to the world and its log, from the base it starts on. -/
structure SubmissionEffects (sevm : Sevm) (pre post : Devm) : Prop where
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

/-- What a successful submission does on a fork's steps, for the fee recurrence's iteration count and final
output. -/
structure SubmittedOn (l : StorageSteps sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) :
    Prop extends SubmissionEffects sevm pre post where
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
  /-- The whole post state, including warmed keys, refunds and memory. -/
  state : ∃ gas, post = Steps.submissionPost l (l.feeBase pre) pre.memory gas

/-- A successful non-system frame at the deposit code, on a fork's steps. -/
inductive UserFrameOn (l : StorageSteps sevm) (pre post : Devm) : Prop where
  /-- A submission. -/
  | submission (iterations : Nat) (finalOutput : B256)
      (effect : SubmittedOn l pre post iterations finalOutput)
  /-- A fee read: empty calldata. -/
  | feeRead (iterations : Nat) (finalOutput : B256) (empty : sevm.data = [])
      (effect : UserPath.FeeReadOn l 8 pre post iterations finalOutput)

/-- What a successful submission does under covered forks. -/
abbrev Submitted (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) : Prop :=
  SubmittedOn (coveredSteps sevm) pre post iterations finalOutput

/-- **Deposit frames.** A successful non-system frame at the deposit code under covered forks. -/
abbrev UserFrame (sevm : Sevm) (pre post : Devm) : Prop := UserFrameOn (coveredSteps sevm) pre post

variable {l : StorageSteps sevm} {pre post b : Devm} {M : Mem} {G : Nat}

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
  rw [submissionLog, windowLog, image]

/-- The world's post state of a submission, from the base's state. -/
theorem submissionBase_state (v : l.Valid) :
    (Steps.submissionBase l (l.feeBase b) M).state =
      let tail := (b.state.getStor sevm.currentTarget).get 3
      let key := submissionKey tail
      let a := sevm.currentTarget
      ((((((((b.state.setStorVal a 1 (1 + (b.state.getStor a).get 1)).setStorVal a key
        (Sevm.dataWord sevm 0)).setStorVal a (1 + key) (Sevm.dataWord sevm 32)).setStorVal a (1 + (1 + key))
        (Sevm.dataWord sevm 64)).setStorVal a (1 + (1 + (1 + key))) (Sevm.dataWord sevm 96)).setStorVal a
        (1 + (1 + (1 + (1 + key)))) (Sevm.dataWord sevm 128)).setStorVal a
        (1 + (1 + (1 + (1 + (1 + key))))) (Sevm.dataWord sevm 160)).setStorVal a 3 (1 + tail)) := by
  have hbase := v.state_feeBase b
  have hc : countWord sevm (l.feeBase b) = (b.state.getStor sevm.currentTarget).get 1 :=
    v.read_feeBase 1 _ b
  have ht : l.tailWord (l.feeBase b) = (b.state.getStor sevm.currentTarget).get 3 :=
    (v.tailWord_eq _).trans (v.read_feeBase 3 _ b)
  have hcs : (l.countStore (l.feeBase b)).state =
      b.state.setStorVal sevm.currentTarget 1 (1 + (b.state.getStor sevm.currentTarget).get 1) := by
    rw [v.countStore_state, hbase]
    have h1 : (l.feeBase b).getStorVal sevm.currentTarget 1 = (b.state.getStor sevm.currentTarget).get 1 := hc
    rw [h1]
  show (l.afterWrite _ 3 _).state = _
  rw [v.writeState, ht]
  show State.setStorVal (Steps.recordsWritten l (l.feeBase b)).state _ _ _ = _
  simp only [Steps.recordsWritten, Steps.recordStore, Steps.wordStore, v.writeState, StorageSteps.tailRead,
    v.readState, hcs, ht]

/-- **What a submission's frame does**, on a fork's steps: the same storage, log and balances on every
fork. -/
theorem submissionPost_effects (v : l.Valid) (hlen : sevm.data.length = 184) (wf : Mem.Wf M) (gas : Nat) :
    SubmissionEffects sevm b (Steps.submissionPost l (l.feeBase b) M gas) := by
  have hstate := submissionBase_state (b := b) (M := M) v
  have stor : ∀ x, (Steps.submissionPost l (l.feeBase b) M gas).getStor x =
      (Steps.submissionBase l (l.feeBase b) M).state.getStor x := fun _ => rfl
  have bal : ∀ x, (Steps.submissionPost l (l.feeBase b) M gas).getBal x =
      ((Steps.submissionBase l (l.feeBase b) M).state.get x).bal := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [stor, hstate]
    show _ = submittedStorage sevm (b.state.getStor sevm.currentTarget)
    simp only [State.getStor_setStorVal_self, submittedStorage]
  · intro a hne
    rw [stor, hstate]
    show _ = b.state.getStor a
    simp only [State.getStor_setStorVal_other _ _ _ hne.symm]
  · intro a
    rw [bal, hstate]
    show _ = (b.state.get a).bal
    simp only [State.bal_setStorVal]
  · show (Steps.submissionBase l (l.feeBase b) M).logs = b.logs ++ _
    rw [Steps.submissionBase, v.writeLogs, Steps.logged, Devm.addLog_logs, submissionLog_eq hlen wf]
    simp only [Steps.recordsWritten, Steps.recordStore, Steps.wordStore, v.writeLogs, StorageSteps.tailRead,
      v.readLogs, StorageSteps.countStore, StorageSteps.feeBase]
  · show (Steps.submissionBase l (l.feeBase b) M).output = b.output
    simp only [Steps.submissionBase, Steps.logged, v.writeOutput, addLog_output, Steps.recordsWritten,
      Steps.recordStore, Steps.wordStore, StorageSteps.tailRead, v.readOutput, StorageSteps.countStore,
      StorageSteps.feeBase]

/-- Every successful execution of the deposit code at a non-system caller, from an empty stack, on a fork's
steps, is a submission or a fee read. -/
theorem exec_user_frame_on (v : l.Valid) (hcode : sevm.code = code)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) : UserFrameOn l pre post := by
  rcases UserPath.exec_user_cases (k := userPath) v hcode stack aligned wf lengthBound caller exec with
    ⟨active, literal, iterations, finalOutput, wordRun, _, run⟩ | ⟨empty, iterations, finalOutput, read⟩
  · have literal : sevm.data.length = 184 := literal
    obtain ⟨admitted, _, run⟩ := guards_inv run
    obtain ⟨dynamic, gas, state⟩ := body_inv v run
    have state := Outcome.halted.inj state
    subst state
    exact .submission iterations finalOutput
      ⟨submissionPost_effects v literal wf gas, dynamic, literal, active, wordRun, admitted, gas, rfl⟩
  · exact .feeRead iterations finalOutput empty read

/-- The deposit contract's user frames. -/
def frames : UserFrames where
  code := code
  Frame := UserFrameOn
  frame := exec_user_frame_on

/-- **Deposit frames.** `UserFrames.exec_user_frame` at the deposit code: every successful execution at a
non-system caller, from an empty stack, under covered forks, is a `UserFrame`. -/
abbrev exec_user_frame := @UserFrames.exec_user_frame frames

/-- **Deposit fee read.** A successful empty-calldata execution at a non-system caller carries no
value, changes no storage, balance or log, and returns the word recurrence's quotient on
`slot0 + max(0, count - 8)`. -/
theorem exec_fee_read (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations finalOutput, UserPath.FeeRead 8 sevm pre post iterations finalOutput :=
  UserPath.exec_fee_read (k := userPath) (coveredSteps_valid fork) hcode stack aligned wf caller empty exec

/-- What a submission takes from `gasLeft`, from the frame's start, on a fork's steps. -/
def submissionGasOn (l : StorageSteps sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  Steps.bodyGas l (l.feeBase b) M + 88 + l.feePathGas b iterations + dispatchGas

/-- The charge of a submission, from the frame's start, under covered forks. -/
def submissionGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  submissionGasOn (coveredSteps sevm) b M iterations

/-- **Submission, forward**, on a fork's steps. 184 bytes of calldata in a non-static frame, slot 0 off the
inhibitor, and the guards' `Admitted` give a successful execution, taking `submissionGasOn` from `gasLeft` and
returning `bodyRepay`, leaving `slack` over the `SSTORE` sentry. -/
theorem exec_submission_on {iterations : Nat} {finalOutput : B256} (v : l.Valid)
    (hcode : sevm.code = code) (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 184)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 8 sevm b) 17 1 17 0 iterations finalOutput)
    (admitted : Admitted sevm (finalOutput / (17 : B256))) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGasOn l b M iterations))
      (.ok (Steps.submissionPost l (l.feeBase b) M (G + Steps.bodyRepay l (l.feeBase b) M)))) := by
  have word : sevm.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  have body := guards_exact admitted (body_exact (b := l.feeBase b) (M := M) v dynamic slack)
  have path := feePath_exact userPath.shape v (revert := userPath.revert)
    (getter := userPath.getter) (submission := t_009f_c1) userPath.window userPath.loop off
    wordRun (by
      rw [RequestFee.selected, ite_eq_left word]
      exact body)
  have hgas : G + submissionGasOn l b M iterations =
      (G + Steps.bodyGas l (l.feeBase b) M + 88 + l.feePathGas b iterations) + dispatchGas := by
    simp only [submissionGasOn, Nat.add_assoc]
  rw [hgas]
  exact UserPath.exec_of_user (k := userPath) hcode caller path

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
      (.ok (submissionPost sevm (feeBase sevm b) M G))) :=
  exec_submission_on (l := coveredSteps sevm) (M := M) (coveredSteps_valid fork) hcode caller hlen dynamic slack
    off wordRun admitted

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
  UserPath.exec_fee_read_exact (k := userPath) (coveredSteps_valid fork) hcode aligned caller empty zero off wordRun

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
