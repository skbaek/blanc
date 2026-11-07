import Blanc.Lift.BuilderRequest.Exit.Submission
import Blanc.Lift.BuilderRequest.QueueLayout

/-!
# The exit contract's user frames, under covered forks

While slot 0 holds the inhibitor, no user call at the exit code succeeds. With slot 0 off the inhibitor,
every successful non-system frame is exactly a submission or a fee read, each with its exact storage, logs
and return bytes, and each of those has a converse constructing the execution. Each is an instance of a statement on a fork's
`StorageSteps`, which `Exit.SubmissionAmsterdam` instantiates too. These are statements about
one frame over any storage, not a claim that such storage is reachable: under covered forks the exit
contract never leaves inhibition on mainnet. They do not cover message or transaction level.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune

/-- The exit runtime's user path. -/
def userPath : UserPath where
  code := code
  cert := cert
  check := cert_check
  jumps := jumps_ok
  noExec := progNoExec_of_all (by decide +kernel)
  shape :=
    { revert := ⟨0x01, [0xc6], by decide⟩
      target := ⟨0x02, [], by decide⟩
      over := ⟨0x51, [], by decide⟩
      under := ⟨0x57, [], by decide⟩
      window := 1
      post := ⟨0x7e, [], by decide⟩
      loop := ⟨0x63, [], by decide⟩
      loopEntry := 6
      len := ⟨0x30, [], by decide⟩
      submit := ⟨0x9e, [], by decide⟩ }
  systemDest := ⟨0xe1, [], by decide⟩
  system := t_00e1_c0
  revert := t_01c6_c0
  getterDest := ⟨0x01, [0xc6], by decide⟩
  getterRevert := t_01c6_c1
  submission := t_009e_c1
  root := rfl
  window := rfl
  loop := rfl
  revert_noOk := rfl
  getterRevert_noOk := rfl
  len_ne := by decide

variable {sevm : Sevm} {pre post : Devm}

/-- While slot 0 holds the inhibitor, no execution of the exit code at a non-system caller from an
empty stack succeeds. -/
theorem exec_user_inhibited_no_ok (hcode : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre (.ok post)) : False :=
  UserPath.exec_inhibited_no_ok (k := userPath) (coveredSteps_valid fork) hcode stack caller inhibited exec

/-- **Exit rejection.** While slot 0 holds the inhibitor, every execution of the exit code at a
non-system caller from an empty stack ends in failure, for any calldata, value and memory. The only
success-free way out of the code's path is its `REVERT` or running out of gas first; this statement
does not say which, and it constructs no `REVERT`. -/
theorem exec_user_inhibited_fails {outcome : Execution} (hcode : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = [])
    (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max)
    (exec : Exec 0 sevm pre outcome) : ∃ failure, outcome = .error failure := by
  cases outcome with
  | ok post => exact (exec_user_inhibited_no_ok hcode fork stack caller inhibited exec).elim
  | error failure => exact ⟨failure, rfl⟩

/-- **Exit fee read.** With slot 0 off the inhibitor, a successful empty-calldata execution at a
non-system caller carries no value, changes no storage, balance or log, and returns the word
recurrence's quotient on `slot0 + max(0, count - 2)`. `aligned` and `wf` hold of the empty memory
every frame starts with. -/
theorem exec_fee_read (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    ∃ iterations finalOutput, UserPath.FeeRead 2 sevm pre post iterations finalOutput :=
  UserPath.exec_fee_read (k := userPath) (coveredSteps_valid fork) hcode stack aligned wf caller empty exec

/-- The exit fee read, forward: such a read exists at the exact charge whenever slot 0 is off the
inhibitor, so `exec_fee_read`'s premises can be met. -/
theorem exec_fee_read_exact {b : Devm} {M : Mem} {G iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + UserPath.feeReadGas sevm b M iterations))
      (.ok (RequestFee.feeGetterPost (feeBase sevm b) M (finalOutput / (17 : B256)) G))) :=
  UserPath.exec_fee_read_exact (k := userPath) (coveredSteps_valid fork) hcode aligned caller empty zero off wordRun

/-! ## Submissions -/

/-- The storage a submission leaves, in the code's write order, so it stays exact when a record key
aliases a metadata slot: the count in slot 1 is bumped, the caller and two calldata words go to the three
keys from `4 + 3 * tail` up, and the tail in slot 3 is bumped. Slot 0 and slot 2 are not written. -/
def submittedStorage (sevm : Sevm) (s : Stor) : Stor :=
  let tail := s.get 3
  let key := submissionKey tail
  ((((s.set 1 (1 + s.get 1)).set key sevm.caller.toB256).set (1 + key) (Sevm.dataWord sevm 0)).set
    (1 + (1 + key)) (Sevm.dataWord sevm 32)).set 3 (1 + tail)

/-- What a submission's frame does to the world and its log, from the base it starts on. -/
structure SubmissionEffects (sevm : Sevm) (pre post : Devm) : Prop where
  /-- The contract's storage is exactly `submittedStorage`; `submittedStorage_record` reads its record. -/
  storage : post.getStor sevm.currentTarget = submittedStorage sevm (pre.getStor sevm.currentTarget)
  /-- No other account's storage changed. -/
  otherStorage : ∀ address, address ≠ sevm.currentTarget → post.getStor address = pre.getStor address
  /-- No balance changed within the frame's code. The value moves before the frame, at message level: see `message_ok` and `transaction_ok`. -/
  balance : ∀ address, post.getBal address = pre.getBal address
  /-- One topicless log is appended, its data the caller's 20 bytes and the calldata. -/
  logs : post.logs = pre.logs ++ [⟨sevm.currentTarget, [], sevm.caller.toBytes ++ sevm.data⟩]
  /-- `STOP` returns nothing of its own: the output is the one the frame started with. -/
  output : post.output = pre.output

/-- What a successful submission does on a fork's steps, for the fee recurrence's iteration count and final
output. -/
structure SubmittedOn (l : StorageSteps sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) :
    Prop extends SubmissionEffects sevm pre post where
  /-- The frame is not static. -/
  dynamic : sevm.isStatic = false
  /-- The calldata is exactly 48 bytes. -/
  length : sevm.data.length = 48
  /-- Slot 0 is not the inhibitor. -/
  active : pre.getStorVal sevm.currentTarget 0 ≠ B256.max
  /-- The word recurrence ran on `slot0 + max(0, count - 2)`. -/
  quote : WordFakeExponential.Run (storedExcess 2 sevm pre) 17 1 17 0 iterations finalOutput
  /-- The value covers the quoted fee. Surplus value is accepted and stays with the contract. -/
  covered : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat
  /-- The whole post state, including warmed keys, refunds and memory. -/
  state : ∃ gas, post = Steps.submissionPost l (l.feeBase pre) pre.memory gas

/-- A successful non-system frame at the exit code, on a fork's steps. -/
inductive UserFrameOn (l : StorageSteps sevm) (pre post : Devm) : Prop where
  /-- A submission. -/
  | submission (iterations : Nat) (finalOutput : B256)
      (effect : SubmittedOn l pre post iterations finalOutput)
  /-- A fee read: empty calldata. -/
  | feeRead (iterations : Nat) (finalOutput : B256) (empty : sevm.data = [])
      (effect : UserPath.FeeReadOn l 2 pre post iterations finalOutput)

/-- What a successful submission does under covered forks. -/
abbrev Submitted (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) : Prop :=
  SubmittedOn (coveredSteps sevm) pre post iterations finalOutput

/-- **Exit frames.** A successful non-system frame at the exit code under covered forks. -/
abbrev UserFrame (sevm : Sevm) (pre post : Devm) : Prop := UserFrameOn (coveredSteps sevm) pre post

/-- On a tail with its slots below the word modulus, the record a submission leaves: **the source is
exactly the caller**, and the two words after it are the calldata's. -/
theorem submittedStorage_record (sevm : Sevm) {s : Stor} {t : Nat} (ht : s.get 3 = t.toB256)
    (hb : queueBase 3 t + 3 ≤ 2 ^ 256) :
    (submittedStorage sevm s).get (queueSlot 3 t 0) = sevm.caller.toB256 ∧
      (submittedStorage sevm s).get (queueSlot 3 t 1) = Sevm.dataWord sevm 0 ∧
      (submittedStorage sevm s).get (queueSlot 3 t 2) = Sevm.dataWord sevm 32 := by
  have key : submissionKey (s.get 3) = queueSlot 3 t 0 := by
    rw [ht]
    exact record_key 3 t
  have k1 : (1 : B256) + queueSlot 3 t 0 = queueSlot 3 t 1 := by
    rw [show (1 : B256) = Nat.toB256 1 by decide]
    exact record_key_add 3 t 0 1
  have k2 : (1 : B256) + queueSlot 3 t 1 = queueSlot 3 t 2 := by
    rw [show (1 : B256) = Nat.toB256 1 by decide]
    exact record_key_add 3 t 1 1
  have val : ∀ j, j < 3 → (queueSlot 3 t j).toNat = 4 + 3 * t + j := fun j hj => by
    unfold queueSlot queueBase at *
    rw [B256.toNat_toB256_of_lt (by omega)]
  have ne : ∀ i j, i < 3 → j < 3 → i ≠ j → queueSlot 3 t i ≠ queueSlot 3 t j := fun i j hi hj hij e => by
    have := congrArg B256.toNat e
    rw [val i hi, val j hj] at this
    omega
  have three : ∀ j, j < 3 → (3 : B256) ≠ queueSlot 3 t j := fun j hj e => by
    have := congrArg B256.toNat e
    rw [val j hj, show (3 : B256).toNat = 3 by decide] at this
    omega
  have n01 := ne 0 1 (by omega) (by omega) (by omega)
  have n02 := ne 0 2 (by omega) (by omega) (by omega)
  have n12 := ne 1 2 (by omega) (by omega) (by omega)
  simp only [submittedStorage]
  rw [key, k1, k2]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Stor.get_set_ite, ite_eq_right (three 0 (by omega)), ite_eq_right n02.symm,
      ite_eq_right n01.symm, ite_true]
  · simp only [Stor.get_set_ite, ite_eq_right (three 1 (by omega)), ite_eq_right n12.symm, ite_true]
  · simp only [Stor.get_set_ite, ite_eq_right (three 2 (by omega)), ite_true]

/-- The log reads back the caller's bytes and exactly the 48 bytes the frame was called with. -/
theorem submissionLog_eq {sevm : Sevm} {M : Mem} (hlen : sevm.data.length = 48) (wf : Mem.Wf M) :
    submissionLog sevm M = ⟨sevm.currentTarget, [], sevm.caller.toBytes ++ sevm.data⟩ := by
  have copied : sevm.data.sliceD 0 48 0 = sevm.data := by
    rw [List.sliceD, List.drop_zero]
    exact List.takeD_eq_self 0 hlen.symm
  have reads := ((Mem.reads_data M).write wf 0 (sourceWord sevm).toBytes).write
    (Mem.Wf.write wf _ _) 20 (sevm.data.sliceD 0 48 0)
  have image := reads.read 0 68
  change ((copyMemory sevm M).read 0 68).1 = _ at image
  rw [copied] at image
  have source : (sourceWord sevm).toBytes.sliceD 0 20 0 = sevm.caller.toBytes := by
    unfold List.sliceD sourceWord
    rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega),
      show (Bytes.toB256 [0x60]).toNat = 96 by decide, WordByteCodecs.shift96_take20_toAdr_bytes,
      toAdr_toB256]
  have whole : (Bytes.writeAt (Bytes.writeAt M.data.toList 0 (sourceWord sevm).toBytes) 20 sevm.data).sliceD
      0 68 0 = sevm.caller.toBytes ++ sevm.data := by
    rw [show (68 : Nat) = 20 + 48 by rfl, List.sliceD_split, Nat.zero_add]
    have tail := Bytes.sliceD_writeAt (Bytes.writeAt M.data.toList 0 (sourceWord sevm).toBytes) sevm.data 20
    rw [hlen] at tail
    rw [tail, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega), source]
  rw [whole] at image
  rw [submissionLog, windowLog, image]

/-- The world's post state of a submission, from the base's state. -/
theorem submissionBase_state {l : StorageSteps sevm} {b : Devm} {M : Mem} (v : l.Valid) :
    (Steps.submissionBase l (l.feeBase b) M).state =
      let tail := (b.state.getStor sevm.currentTarget).get 3
      let key := submissionKey tail
      let a := sevm.currentTarget
      ((((b.state.setStorVal a 1 (1 + (b.state.getStor a).get 1)).setStorVal a key
        sevm.caller.toB256).setStorVal a (1 + key) (Sevm.dataWord sevm 0)).setStorVal a (1 + (1 + key))
        (Sevm.dataWord sevm 32)).setStorVal a 3 (1 + tail) := by
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
  simp only [Steps.recordsWritten, Steps.recordStore, v.writeState, StorageSteps.tailRead, v.readState, hcs, ht]

/-- **What a submission's frame does**, on a fork's steps: the same storage, log and balances on every
fork. -/
theorem submissionPost_effects {l : StorageSteps sevm} {b : Devm} {M : Mem} (v : l.Valid)
    (hlen : sevm.data.length = 48) (wf : Mem.Wf M) (gas : Nat) :
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
    simp only [Steps.recordsWritten, Steps.recordStore, v.writeLogs, StorageSteps.tailRead, v.readLogs,
      StorageSteps.countStore, StorageSteps.feeBase]
  · show (Steps.submissionBase l (l.feeBase b) M).output = b.output
    simp only [Steps.submissionBase, Steps.logged, v.writeOutput, addLog_output, Steps.recordsWritten,
      Steps.recordStore, StorageSteps.tailRead, v.readOutput, StorageSteps.countStore, StorageSteps.feeBase]

/-- Every successful execution of the exit code at a non-system caller, from an empty stack, on a fork's
steps, is a submission or a fee read. -/
theorem exec_user_frame_on {l : StorageSteps sevm} (v : l.Valid) (hcode : sevm.code = code)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) : UserFrameOn l pre post := by
  rcases UserPath.exec_user_cases (k := userPath) v hcode stack aligned wf lengthBound caller exec with
    ⟨active, literal, iterations, finalOutput, wordRun, _, run⟩ | ⟨empty, iterations, finalOutput, read⟩
  · have literal : sevm.data.length = 48 := literal
    obtain ⟨cov, _, run⟩ := guard_inv run
    obtain ⟨dynamic, gas, state⟩ := body_inv v run
    have state := Outcome.halted.inj state
    subst state
    exact .submission iterations finalOutput
      ⟨submissionPost_effects v literal wf gas, dynamic, literal, active, wordRun, cov, gas, rfl⟩
  · exact .feeRead iterations finalOutput empty read

/-- The exit contract's user frames. -/
def frames : UserFrames where
  code := code
  Frame := UserFrameOn
  frame := exec_user_frame_on

/-- **Exit frames.** `UserFrames.exec_user_frame` at the exit code: every successful execution at a
non-system caller, from an empty stack, under covered forks, is a `UserFrame`. -/
abbrev exec_user_frame := @UserFrames.exec_user_frame frames

/-- What a submission takes from `gasLeft`, from the frame's start, on a fork's steps. -/
def submissionGasOn (l : StorageSteps sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  Steps.bodyGas l (l.feeBase b) M + 19 + l.feePathGas b iterations + RequestSystem.dispatchGas

/-- The charge of a submission, from the frame's start, under covered forks. -/
def submissionGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  submissionGasOn (coveredSteps sevm) b M iterations

variable {b : Devm} {M : Mem} {G : Nat}

/-- **Submission, forward**, on a fork's steps. 48 bytes of calldata in a non-static frame, slot 0 off the
inhibitor and value covering the fee give a successful execution, taking `submissionGasOn` from `gasLeft`
and returning `bodyRepay`, leaving `slack` over the `SSTORE` sentry. -/
theorem exec_submission_on {l : StorageSteps sevm} {iterations : Nat} {finalOutput : B256} (v : l.Valid)
    (hcode : sevm.code = code) (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 48)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput)
    (cov : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGasOn l b M iterations))
      (.ok (Steps.submissionPost l (l.feeBase b) M (G + Steps.bodyRepay l (l.feeBase b) M)))) := by
  have word : sevm.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  have body := guard_exact cov (body_exact (b := l.feeBase b) (M := M) v dynamic slack)
  have path := feePath_exact userPath.shape v (revert := userPath.revert)
    (getter := userPath.getter) (submission := t_009e_c1) userPath.window userPath.loop off
    wordRun (by
      rw [RequestFee.selected, ite_eq_left word]
      exact body)
  have hgas : G + submissionGasOn l b M iterations =
      (G + Steps.bodyGas l (l.feeBase b) M + 19 + l.feePathGas b iterations) +
        RequestSystem.dispatchGas := by
    simp only [submissionGasOn, Nat.add_assoc]
  rw [hgas]
  exact UserPath.exec_of_user (k := userPath) hcode caller path

/-- **Submission, forward.** 48 bytes of calldata in a non-static frame, slot 0 off the inhibitor and value
covering the fee give a successful execution at the exact charge, leaving `slack` over the `SSTORE` sentry. -/
theorem exec_submission_exact {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 48)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput)
    (cov : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGas sevm b M iterations))
      (.ok (submissionPost sevm (feeBase sevm b) M G))) :=
  exec_submission_on (l := coveredSteps sevm) (M := M) (coveredSteps_valid fork) hcode caller hlen dynamic slack off
    wordRun cov

/-- **The submission's premises can all be met together.** On storage whose slots 0 and 1 are zero, any 48
bytes of calldata and a value of at least 1 wei in a non-static frame run to `STOP`. -/
theorem exec_submission_witness (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 48)
    (value : 1 ≤ sevm.value.toNat) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) (slot0 : b.getStorVal sevm.currentTarget 0 = 0)
    (slot1 : b.getStorVal sevm.currentTarget 1 = 0) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGas sevm b M 1))
      (.ok (submissionPost sevm (feeBase sevm b) M G))) := by
  have excess : storedExcess 2 sevm b = 0 := by
    rw [storedExcess, slot0, slot1]
    decide
  have fee : ((17 : B256) / (17 : B256)).toNat = 1 := by decide
  refine exec_submission_exact (finalOutput := 17) hcode fork caller hlen dynamic slack
    (by rw [slot0]; decide) (by rw [excess]; exact quote_zero_excess) ?_
  rw [fee]
  exact value

end Blanc.Lift.BuilderRequest.Exit
