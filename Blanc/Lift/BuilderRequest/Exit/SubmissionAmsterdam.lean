import Blanc.Lift.BuilderRequest.Exit.Frames
import Blanc.Lift.BuilderRequest.Exit.System
import Blanc.Lift.BuilderRequest.UserFrameAmsterdam
import Blanc.Lift.RequestSystem.Call

/-!
# The exit runtime's user frames, under Amsterdam: the forward direction

Under Amsterdam the exit contract can leave inhibition (`Exit.activation_unlocks`), so these are the frames
that can happen. `exec_submission_amsterdam` and `exec_fee_read_amsterdam` construct the execution from the
frame's premises, at their exact regular-gas charge, with the same record, log and storage as the covered
forks' `Exit.Submitted`.

**Not here: the inverse**, that every successful frame is one of these. `lift_sound` assumes
`rules.stateGas = none`, which Amsterdam does not meet. So this module does not state "every successful
frame". It stops at the frame: no message or transaction level, no EIP-7708 transfer log (the frame does not
emit it), no settlement, no history.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestSystem (dispatchGas dispatchArm dispatch_exact bal_setStorVal getStor_setStorVal_other)

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

/-- The record's three stores. -/
def recordStoreA (sevm : Sevm) (b : Devm) (key : B256) : Devm :=
  afterSstoreA A sevm (afterSstoreA A sevm (afterSstoreA A sevm b key sevm.caller.toB256)
    (1 + key) (Sevm.dataWord sevm 0)) (1 + (1 + key)) (Sevm.dataWord sevm 32)

/-- The state after the record. -/
def recordsWrittenA (sevm : Sevm) (b : Devm) : Devm :=
  recordStoreA sevm (tailReadA sevm b) (submissionKey (tailWordA sevm b))

/-- The base state of a finished submission. -/
def submissionBaseA (sevm : Sevm) (b : Devm) (M : Mem) : Devm :=
  afterSstoreA A sevm ((recordsWrittenA sevm b).addLog (submissionLog sevm M)) 3 (1 + tailWordA sevm b)

/-- `STOP` after a submission. -/
def submissionPostA (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) : Devm :=
  St (submissionBaseA sevm b M) [] (submissionMemory sevm M) G

/-- The exact regular-gas charge of the record's stores. -/
def recordWritesGasA (sevm : Sevm) (b : Devm) (key : B256) : Nat :=
  let s0 := afterSstoreA A sevm b key sevm.caller.toB256
  let s1 := afterSstoreA A sevm s0 (1 + key) (Sevm.dataWord sevm 0)
  sstoreCostA A sevm b key sevm.caller.toB256 + sstoreCostA A sevm s0 (1 + key) (Sevm.dataWord sevm 0) +
    sstoreCostA A sevm s1 (1 + (1 + key)) (Sevm.dataWord sevm 32)

/-- The exact regular-gas charge of the submission body. State gas is drawn from the reservoir. -/
def bodyGasA (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  sloadCost sevm b 1 + sstoreCostA A sevm (afterSloadA sevm b 1) 1 (1 + countWord sevm b) +
    sloadCost sevm (countStoreA sevm b) 3 +
    recordWritesGasA sevm (tailReadA sevm b) (submissionKey (tailWordA sevm b)) +
    sourceGas M + copyGas (M.write 0 (sourceWord sevm).toBytes) +
    log0Gas (copyMemory sevm M) 68 +
    sstoreCostA A sevm ((recordsWrittenA sevm b).addLog (submissionLog sevm M)) 3 (1 + tailWordA sevm b) +
    98

/-- The submission body, forward, under Amsterdam: non-static, with room in the reservoir for its five stores
and more than the `SSTORE` sentry left at the end. -/
theorem body_exactA (hfork : sevm.benvStat.fork = .amsterdam) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) (r : Room b 5) :
    SFunc.RunExact cert.prog sevm (St b [] M (G + bodyGasA sevm b M)) t_00a5_c1
      (.halted (submissionPostA sevm b M G)) := by
  have hacc := amsterdam_access (s := sevm.benvStat) hfork
  have hpush0 := amsterdam_push0 (s := sevm.benvStat) hfork
  have hsh := amsterdam_shifts (s := sevm.benvStat) hfork
  have r1 : Room (countStoreA sevm b) 4 := (r.sload 1).sstore _ _
  have r2 : Room (tailReadA sevm b) 4 := r1.sload 3
  have r3 := r2.sstore (sevm := sevm) (submissionKey (tailWordA sevm b)) sevm.caller.toB256
  have r4 := r3.sstore (sevm := sevm) (1 + submissionKey (tailWordA sevm b)) (Sevm.dataWord sevm 0)
  have r5 := r4.sstore (sevm := sevm) (1 + (1 + submissionKey (tailWordA sevm b))) (Sevm.dataWord sevm 32)
  have tail := logTail_exactA (fs := cert.prog) (n := Bytes.toB256 [0x44]) (tail := tailWordA sevm b)
    (b := recordsWrittenA sevm b) (M := copyMemory sevm M) (G := G) hfork dynamic slack r5
  have hgas : G + bodyGasA sevm b M =
      G + sstoreCostA A sevm ((recordsWrittenA sevm b).addLog (submissionLog sevm M)) 3 (1 + tailWordA sevm b)
          + 3 + 3 + 3 + log0Gas (copyMemory sevm M) 68 + 2 + 3
        + copyGas (M.write 0 (sourceWord sevm).toBytes) + 3 + 2 + 3 + sourceGas M + 2 + 3 + 3 + 2
        + sstoreCostA A sevm (afterSstoreA A sevm (afterSstoreA A sevm (tailReadA sevm b)
            (submissionKey (tailWordA sevm b)) sevm.caller.toB256)
            (1 + submissionKey (tailWordA sevm b)) (Sevm.dataWord sevm 0))
            (1 + (1 + submissionKey (tailWordA sevm b))) (Sevm.dataWord sevm 32)
        + 3 + 3 + 3 + 3 + 3
        + sstoreCostA A sevm (afterSstoreA A sevm (tailReadA sevm b) (submissionKey (tailWordA sevm b))
            sevm.caller.toB256) (1 + submissionKey (tailWordA sevm b)) (Sevm.dataWord sevm 0)
        + 3 + 3 + 2 + 3 + 3
        + sstoreCostA A sevm (tailReadA sevm b) (submissionKey (tailWordA sevm b)) sevm.caller.toB256
        + 3 + 2 + 3 + 3 + 5 + 3 + 3 + sloadCost sevm (countStoreA sevm b) 3 + 3
        + sstoreCostA A sevm (afterSloadA sevm b 1) 1 (1 + countWord sevm b) + 3 + 3 + 3
        + sloadCost sevm b 1 + 3 := by
    simp only [bodyGasA, recordWritesGasA]
    omega
  rw [hgas]
  unfold t_00a5_c1
  refine rx_push rfl (by decide) ?_
  refine rx_sloadA hacc (by decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by change 0 < 1024; decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_sstoreRoom (n := 4) hfork dynamic (r.sload 1) (by omega) ?_
  refine rx_push rfl (by decide) ?_
  refine rx_sloadA hacc (by decide) ?_
  refine rx_dup1 (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_mul rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_caller (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstoreRoom (n := 3) hfork dynamic r2 (by omega) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := hpush0) (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_dup2 (by change 3 < 1024; decide) ?_
  refine rx_sstoreRoom (n := 2) hfork dynamic r3 (by omega) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_add' rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_calldataload (by change 2 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine rx_sstoreRoom (n := 1) hfork dynamic r4 (by omega) ?_
  refine rx_caller (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  refine rx_shl rfl hsh (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := hpush0) (by change 2 < 1024; decide) ?_
  refine rx_mstore (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := hpush0) (by change 2 < 1024; decide) ?_
  refine rx_push rfl (by change 3 < 1024; decide) ?_
  refine rx_calldatacopy (Devm.extCost_add_of_size rfl rfl) rfl ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_push0 (h_push0 := hpush0) (by change 2 < 1024; decide) ?_
  exact tail

/-- An exact user arm at a non-system caller is an execution of the exit bytes, under Amsterdam. -/
theorem exec_of_userA {post : Devm} (hcode : sevm.code = code) (caller : sevm.caller ≠ systemAddress)
    (tail : SFunc.RunExact userPath.cert.prog sevm (St b [] M G) userPath.user (.halted post)) :
    Nonempty (Exec 0 sevm (St b [] M (G + dispatchGas)) (.ok post)) := by
  apply lift_exact_noExec userPath.check userPath.jumps hcode sysPath.noExec
  refine ⟨_, userPath.root, dispatch_exact ?_⟩
  simpa only [dispatchArm, ite_eq_right caller] using tail

/-- The fee path's base after its reads, under Amsterdam. -/
abbrev feeBaseA (sevm : Sevm) (hfork : sevm.benvStat.fork = .amsterdam) (b : Devm) : Devm :=
  (amsterdamLane hfork).feeBase b

/-- The charge of a submission under Amsterdam, from the frame's start: regular gas, state gas excluded. -/
def submissionGasA (sevm : Sevm) (hfork : sevm.benvStat.fork = .amsterdam) (b : Devm) (M : Mem)
    (iterations : Nat) : Nat :=
  bodyGasA sevm (feeBaseA sevm hfork b) M + 19 + (amsterdamLane hfork).feePathGas b iterations + dispatchGas

/-- **Exit submission, forward, under Amsterdam.** 48 bytes of calldata in a non-static frame at a non-system
caller, slot 0 off the inhibitor, value covering the quoted fee, and room in the state-gas reservoir for the
five stores give a successful execution at the exact regular-gas charge, leaving `slack` over the `SSTORE`
sentry. A frame without that room may spill into regular gas; this does not cover it. -/
theorem exec_submission_amsterdam {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (hfork : sevm.benvStat.fork = .amsterdam)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 48)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput)
    (cov : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) (room : Room b 5) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGasA sevm hfork b M iterations))
      (.ok (submissionPostA sevm (feeBaseA sevm hfork b) M G))) := by
  have word : sevm.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  have body := guard_exact cov (body_exactA (b := feeBaseA sevm hfork b) (M := M) hfork dynamic slack
    ((room.sload (sevm := sevm) 0).sload (sevm := sevm) 1))
  have path := SloadLane.feePath_exact userPath.shape (amsterdamLane hfork) (revert := userPath.revert)
    (getter := userPath.getter) (submission := t_009e_c1) userPath.window userPath.loop off
    wordRun (by
      rw [RequestFee.selected, ite_eq_left word]
      exact body)
  have hgas : G + submissionGasA sevm hfork b M iterations =
      (G + bodyGasA sevm (feeBaseA sevm hfork b) M + 19 + (amsterdamLane hfork).feePathGas b iterations) +
        dispatchGas := by
    simp only [submissionGasA, Nat.add_assoc]
  rw [hgas]
  exact exec_of_userA hcode caller path

/-! ## What the frame does -/

/-- What a submission's frame does, from the base it starts on. -/
structure SubmissionEffects (sevm : Sevm) (pre post : Devm) : Prop where
  /-- The contract's storage is exactly `submittedStorage`; `submittedStorage_record` reads its record. -/
  storage : post.getStor sevm.currentTarget = submittedStorage sevm (pre.getStor sevm.currentTarget)
  /-- No other account's storage changed. -/
  otherStorage : ∀ address, address ≠ sevm.currentTarget → post.getStor address = pre.getStor address
  /-- No balance changed within the frame's code. -/
  balance : ∀ address, post.getBal address = pre.getBal address
  /-- One topicless log is appended, its data the caller's 20 bytes and the calldata. -/
  logs : post.logs = pre.logs ++ [⟨sevm.currentTarget, [], sevm.caller.toBytes ++ sevm.data⟩]
  /-- `STOP` returns nothing of its own. -/
  output : post.output = pre.output

/-- The world's post state of a submission, from the bases' states. -/
theorem submissionBaseA_state (hfork : sevm.benvStat.fork = .amsterdam) :
    (submissionBaseA sevm (feeBaseA sevm hfork b) M).state =
      let tail := (b.state.getStor sevm.currentTarget).get 3
      let key := submissionKey tail
      let a := sevm.currentTarget
      ((((((b.state.setStorVal a 1 (1 + (b.state.getStor a).get 1)).setStorVal a key
        sevm.caller.toB256).setStorVal a (1 + key) (Sevm.dataWord sevm 0)).setStorVal a (1 + (1 + key))
        (Sevm.dataWord sevm 32))).setStorVal a 3 (1 + tail)) := by
  have hbase : (feeBaseA sevm hfork b).state = b.state := by
    show (afterSloadA sevm (afterSloadA sevm b 0) 1).state = _
    rw [afterSloadA_state, afterSloadA_state]
  have hc : countWord sevm (feeBaseA sevm hfork b) = (b.state.getStor sevm.currentTarget).get 1 := by
    show ((feeBaseA sevm hfork b).state.getStor sevm.currentTarget).get 1 = _
    rw [hbase]
  have hcs : (countStoreA sevm (feeBaseA sevm hfork b)).state =
      b.state.setStorVal sevm.currentTarget 1 (1 + (b.state.getStor sevm.currentTarget).get 1) := by
    simp only [countStoreA, afterSstoreA_state, afterSloadA_state, hbase, hc]
  have ht : tailWordA sevm (feeBaseA sevm hfork b) = (b.state.getStor sevm.currentTarget).get 3 := by
    show ((countStoreA sevm (feeBaseA sevm hfork b)).state.getStor sevm.currentTarget).get 3 = _
    rw [hcs, State.getStor_setStorVal_self, Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3)]
  show (afterSstoreA A sevm _ 3 _).state = _
  rw [afterSstoreA_state, ht]
  show State.setStorVal (recordsWrittenA sevm (feeBaseA sevm hfork b)).state _ _ _ = _
  simp only [recordsWrittenA, recordStoreA, afterSstoreA_state, tailReadA, afterSloadA_state, hcs, ht]

/-- **What the Amsterdam frame does**: the same storage, log and balances as the covered forks' `Submitted`. -/
theorem submissionPostA_effects (hfork : sevm.benvStat.fork = .amsterdam) (hlen : sevm.data.length = 48)
    (wf : Mem.Wf M) (gas : Nat) :
    SubmissionEffects sevm b (submissionPostA sevm (feeBaseA sevm hfork b) M gas) := by
  have hstate := submissionBaseA_state (sevm := sevm) (b := b) (M := M) hfork
  have hs : (submissionPostA sevm (feeBaseA sevm hfork b) M gas).state =
      (submissionBaseA sevm (feeBaseA sevm hfork b) M).state := rfl
  have stor : ∀ x, (submissionPostA sevm (feeBaseA sevm hfork b) M gas).getStor x =
      (submissionBaseA sevm (feeBaseA sevm hfork b) M).state.getStor x := fun _ => rfl
  have bal : ∀ x, (submissionPostA sevm (feeBaseA sevm hfork b) M gas).getBal x =
      ((submissionBaseA sevm (feeBaseA sevm hfork b) M).state.get x).bal := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [stor, hstate]
    show _ = submittedStorage sevm (b.state.getStor sevm.currentTarget)
    simp only [State.getStor_setStorVal_self, submittedStorage]
  · intro a hne
    rw [stor, hstate]
    show _ = b.state.getStor a
    simp only [getStor_setStorVal_other _ _ _ hne.symm]
  · intro a
    rw [bal, hstate]
    show _ = (b.state.get a).bal
    simp only [bal_setStorVal]
  · show (submissionBaseA sevm (feeBaseA sevm hfork b) M).logs = b.logs ++ _
    rw [submissionBaseA, afterSstoreA_logs, Devm.addLog_logs, submissionLog_eq hlen wf]
    simp only [recordsWrittenA, recordStoreA, afterSstoreA_logs, tailReadA, afterSloadA_logs, countStoreA,
      feeBaseA, SloadLane.feeBase, amsterdamLane]
  · show (submissionBaseA sevm (feeBaseA sevm hfork b) M).output = b.output
    simp only [submissionBaseA, afterSstoreA_output, addLog_output, recordsWrittenA, recordStoreA, tailReadA,
      afterSloadA_output, countStoreA, feeBaseA, SloadLane.feeBase, amsterdamLane]

/-- **The Amsterdam submission's premises can all be met together.** On storage whose slots 0 and 1 are zero,
any 48 bytes of calldata, a value of at least 1 wei in a non-static frame, and room in the reservoir run to
`STOP`, with the stated effects. -/
theorem exec_submission_witness_amsterdam (hcode : sevm.code = code)
    (hfork : sevm.benvStat.fork = .amsterdam) (caller : sevm.caller ≠ systemAddress)
    (hlen : sevm.data.length = 48) (value : 1 ≤ sevm.value.toNat) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) (slot0 : b.getStorVal sevm.currentTarget 0 = 0)
    (slot1 : b.getStorVal sevm.currentTarget 1 = 0) (room : Room b 5) (wf : Mem.Wf M) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] M (G + submissionGasA sevm hfork b M 1)) (.ok post)) ∧
      SubmissionEffects sevm b post := by
  have excess : storedExcess 2 sevm b = 0 := by
    rw [storedExcess, slot0, slot1]
    decide
  have fee : ((17 : B256) / (17 : B256)).toNat = 1 := by decide
  refine ⟨_, exec_submission_amsterdam (finalOutput := 17) hcode hfork caller hlen dynamic slack
    (by rw [slot0]; decide) (by rw [excess]; exact quote_zero_excess) (by rw [fee]; exact value) room,
    submissionPostA_effects hfork hlen wf G⟩

/-- **Exit fee read, forward, under Amsterdam.** Empty calldata, no value and slot 0 off the inhibitor at a
non-system caller give a successful execution at the exact charge, returning the word recurrence's quotient
and changing no storage or balance. -/
theorem exec_fee_read_amsterdam {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (hfork : sevm.benvStat.fork = .amsterdam)
    (aligned : M.size % 32 = 0) (wf : Mem.Wf M) (caller : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess 2 sevm b) 17 1 17 0 iterations finalOutput) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] M
        (G + RequestFee.feeGetterGas M + 30 + (amsterdamLane hfork).feePathGas b iterations + dispatchGas))
        (.ok post)) ∧
      post.output = (finalOutput / (17 : B256)).toBytes ∧
      (∀ a, post.getStor a = b.getStor a) ∧ (∀ a, post.getBal a = b.getBal a) ∧ post.logs = b.logs := by
  have hlen : sevm.data.length.toB256 ≠ userPath.shape.len.word := by
    rw [empty]
    exact userPath.len_ne.symm
  have hempty : sevm.data.length.toB256 = 0 := by rw [empty]; rfl
  have body := RequestFee.guard_exact (dest := userPath.getterDest) (revert := userPath.getterRevert)
    (fs := userPath.cert.prog) hempty zero
    (RequestFee.return_exact (b := feeBaseA sevm hfork b) (M := M) (G := G)
      (fee := finalOutput / (17 : B256)) (amsterdam_push0 hfork) aligned)
  have path := SloadLane.feePath_exact userPath.shape (amsterdamLane hfork) (revert := userPath.revert)
    (submission := userPath.submission) userPath.window userPath.loop off wordRun
    (by simpa only [RequestFee.selected, ite_eq_right hlen] using body)
  have facts := RequestFee.feeGetterPost_facts (feeBaseA sevm hfork b) M (finalOutput / (17 : B256)) G wf aligned
  have hbase : (feeBaseA sevm hfork b).state = b.state := by
    show (afterSloadA sevm (afterSloadA sevm b 0) 1).state = _
    rw [afterSloadA_state, afterSloadA_state]
  refine ⟨_, exec_of_userA hcode caller path, facts.1, ?_, ?_, ?_⟩
  · intro a
    have h := congrArg (fun world : World => (world.state.get a).stor) facts.2.1
    exact h.trans (congrArg (fun σ : State => (σ.get a).stor) hbase)
  · intro a
    have h := congrArg (fun world : World => (world.state.get a).bal) facts.2.1
    exact h.trans (congrArg (fun σ : State => (σ.get a).bal) hbase)
  · have h := congrArg Meta.logs facts.2.2.1
    refine h.trans ?_
    show (feeBaseA sevm hfork b).logs = b.logs
    simp only [feeBaseA, SloadLane.feeBase, amsterdamLane, afterSloadA_logs]

end Blanc.Lift.BuilderRequest.Exit
