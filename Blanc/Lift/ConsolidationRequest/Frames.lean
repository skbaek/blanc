import Blanc.Lift.ConsolidationRequest.Submission
import Blanc.SystemCallForward

/-!
# The EIP-7251 user frames, under covered forks

Every successful fresh frame at the consolidation code from a caller other than `SYSTEM_ADDRESS` is
exactly one of two:

* a **fee read**: empty calldata and zero value, slot 0 off the inhibitor, returning the word fee of
  slot 0, with no storage, balance or log change (`RequestFee.PlainUserPath.FeeRead`);
* a **submission**: 96 bytes of calldata in a non-static frame, slot 0 off the inhibitor, value at least the
  word fee, whose effect is the count bumped, the record (caller, calldata words 0 to 2) written at the four
  keys from `4 + 4 * tail`, the tail bumped, and one topicless `LOG0` of the 116 bytes `caller ++ calldata`.

Every other fresh user entry has no successful execution: any other calldata length, a fee read carrying
value, a static or underpaying submission, and any user call while slot 0 holds the inhibitor. Each
success has a converse constructing the execution at its exact charge.

"Fresh" is the frame's empty stack, and memory that is word aligned and well formed, as the empty memory
every frame starts with is. These are statements about one frame over any storage, not a claim that such
storage is reachable, and they do not cover message or transaction level. The record's slots are read back
on represented storage only: with the tail below `2 ^ 253`, no record slot aliases slots 0 to 3; the
storage itself (`submittedStorage`) is exact on any storage.
-/

namespace Blanc.Lift.ConsolidationRequest

open Jaune
open SystemExecution.ConsolidationRequest
open RequestFee (PlainUserPath)

/-- The storage a submission leaves, in the code's write order, so it stays exact when a record key aliases
a metadata slot: the count in slot 1 is bumped, the caller and three calldata words go to the four keys from
`4 + 4 * tail` up, and the tail in slot 3 is bumped. Slot 0 and slot 2 are not written. -/
def submittedStorage (sevm : Sevm) (s : Stor) : Stor :=
  let tail := s.get 3
  let key := submissionKey tail
  (((((s.set 1 (1 + s.get 1)).set key sevm.caller.toB256).set (1 + key) (Sevm.dataWord sevm 0)).set
    (1 + (1 + key)) (Sevm.dataWord sevm 32)).set (1 + (1 + (1 + key))) (Sevm.dataWord sevm 64)).set
    3 (1 + tail)

/-- What a submission's frame does to the world and its log, from the state it starts on. -/
structure SubmissionEffects (sevm : Sevm) (pre post : Devm) : Prop where
  /-- The contract's storage is exactly `submittedStorage`; `submittedStorage_record` reads it. -/
  storage : post.getStor sevm.currentTarget = submittedStorage sevm (pre.getStor sevm.currentTarget)
  /-- No other account's storage changed. -/
  otherStorage : ∀ address, address ≠ sevm.currentTarget → post.getStor address = pre.getStor address
  /-- No balance changed within the frame's code. The value moves before the frame, at message level. -/
  balance : ∀ address, post.getBal address = pre.getBal address
  /-- One topicless log is appended, its data the caller's 20 bytes and the 96 calldata bytes. -/
  logs : post.logs = pre.logs ++ [⟨sevm.currentTarget, [], sevm.caller.toBytes ++ sevm.data⟩]
  /-- `STOP` returns nothing of its own: the output is the one the frame started with. -/
  output : post.output = pre.output

/-- What a successful submission does, for the fee recurrence's iteration count and final output. -/
structure Submitted (sevm : Sevm) (pre post : Devm) (iterations : Nat) (finalOutput : B256) : Prop
    extends SubmissionEffects sevm pre post where
  /-- The frame is not static. -/
  dynamic : sevm.isStatic = false
  /-- The calldata is exactly 96 bytes. -/
  length : sevm.data.length = 96
  /-- Slot 0 is not the inhibitor. -/
  active : pre.getStorVal sevm.currentTarget 0 ≠ B256.max
  /-- The word recurrence ran on slot 0 as stored. -/
  quote : WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput
  /-- The value covers the quoted fee. Surplus value is accepted and stays with the contract. -/
  covered : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat
  /-- The whole post state, including warmed keys, refunds and memory. -/
  state : ∃ gas, post = submissionPost sevm (afterSload sevm pre 0) pre.memory gas

/-- **EIP-7251 frames.** A successful non-system frame at the consolidation code under covered forks. -/
inductive UserFrame (sevm : Sevm) (pre post : Devm) : Prop where
  /-- A submission. -/
  | submission (iterations : Nat) (finalOutput : B256)
      (effect : Submitted sevm pre post iterations finalOutput)
  /-- A fee read: empty calldata. -/
  | feeRead (iterations : Nat) (finalOutput : B256) (empty : sevm.data = [])
      (effect : PlainUserPath.FeeRead sevm pre post iterations finalOutput)

private theorem addLog_output (w : Devm) (l : Log) : (w.addLog l).output = w.output := rfl

private theorem addLog_state (w : Devm) (l : Log) : (w.addLog l).state = w.state := rfl

private theorem countStore_state (sevm : Sevm) (b : Devm) :
    (countStore sevm b).state =
      b.state.setStorVal sevm.currentTarget 1 (1 + b.getStorVal sevm.currentTarget 1) := by
  rw [countStore, afterSstore_state, RequestFee.afterSload_state]
  rfl

private theorem tailWord_eq (sevm : Sevm) (b : Devm) :
    tailWord sevm b = b.getStorVal sevm.currentTarget 3 := by
  show ((countStore sevm b).state.getStor sevm.currentTarget).get 3 =
    (b.state.getStor sevm.currentTarget).get 3
  rw [countStore_state, State.getStor_setStorVal_self, Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3)]

/-- The log reads back the caller's bytes and exactly the 96 bytes the frame was called with. -/
theorem submissionLog_eq {sevm : Sevm} {M : Mem} (hlen : sevm.data.length = 96) (wf : Mem.Wf M) :
    submissionLog sevm M = ⟨sevm.currentTarget, [], sevm.caller.toBytes ++ sevm.data⟩ := by
  have copied : sevm.data.sliceD 0 96 0 = sevm.data := by
    rw [List.sliceD, List.drop_zero]
    exact List.takeD_eq_self 0 hlen.symm
  have reads := ((Mem.reads_data M).write wf 0 (sourceWord sevm).toBytes).write
    (Mem.Wf.write wf _ _) 20 (sevm.data.sliceD 0 96 0)
  have image := reads.read 0 116
  change ((copyMemory sevm M).read 0 116).1 = _ at image
  rw [copied] at image
  have source : (sourceWord sevm).toBytes.sliceD 0 20 0 = sevm.caller.toBytes := by
    unfold List.sliceD sourceWord
    rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega),
      show (Bytes.toB256 [0x60]).toNat = 96 by decide, WordByteCodecs.shift96_take20_toAdr_bytes,
      toAdr_toB256]
  have whole : (Bytes.writeAt (Bytes.writeAt M.data.toList 0 (sourceWord sevm).toBytes) 20 sevm.data).sliceD
      0 116 0 = sevm.caller.toBytes ++ sevm.data := by
    rw [show (116 : Nat) = 20 + 96 by rfl, List.sliceD_split, Nat.zero_add]
    have tail := Bytes.sliceD_writeAt (Bytes.writeAt M.data.toList 0 (sourceWord sevm).toBytes) sevm.data 20
    rw [hlen] at tail
    rw [tail, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (by omega) (by rw [B256.length_toBytes]; omega), source]
  rw [whole] at image
  rw [submissionLog, image]

/-- The world's state after a submission, from the frame's starting state. -/
theorem submissionBase_state {sevm : Sevm} {b : Devm} {M : Mem} :
    (submissionBase sevm (afterSload sevm b 0) M).state =
      let tail := (b.state.getStor sevm.currentTarget).get 3
      let key := submissionKey tail
      let a := sevm.currentTarget
      (((((b.state.setStorVal a 1 (1 + (b.state.getStor a).get 1)).setStorVal a key
        sevm.caller.toB256).setStorVal a (1 + key) (Sevm.dataWord sevm 0)).setStorVal a (1 + (1 + key))
        (Sevm.dataWord sevm 32)).setStorVal a (1 + (1 + (1 + key))) (Sevm.dataWord sevm 64)).setStorVal a 3
        (1 + tail) := by
  have hc : (afterSload sevm b 0).getStorVal sevm.currentTarget 1 =
      (b.state.getStor sevm.currentTarget).get 1 := afterSload_getStorVal sevm b 0 _ 1
  have ht : tailWord sevm (afterSload sevm b 0) = (b.state.getStor sevm.currentTarget).get 3 :=
    (tailWord_eq sevm _).trans (afterSload_getStorVal sevm b 0 _ 3)
  have hcs : (countStore sevm (afterSload sevm b 0)).state =
      b.state.setStorVal sevm.currentTarget 1 (1 + (b.state.getStor sevm.currentTarget).get 1) := by
    rw [countStore_state, RequestFee.afterSload_state, hc]
  rw [submissionBase, afterSstore_state, ht, logged, addLog_state, recordsWritten, recordStore,
    afterSstore_state, afterSstore_state, afterSstore_state, afterSstore_state, tailRead,
    RequestFee.afterSload_state, hcs, ht]

/-- **What a submission's frame does**: its storage, other accounts, balances, log and output. -/
theorem submissionPost_effects {sevm : Sevm} {b : Devm} {M : Mem} (hlen : sevm.data.length = 96)
    (wf : Mem.Wf M) (gas : Nat) :
    SubmissionEffects sevm b (submissionPost sevm (afterSload sevm b 0) M gas) := by
  have hstate := submissionBase_state (sevm := sevm) (b := b) (M := M)
  have stor : ∀ x, (submissionPost sevm (afterSload sevm b 0) M gas).getStor x =
      (submissionBase sevm (afterSload sevm b 0) M).state.getStor x := by
    intro x
    unfold submissionPost
    generalize submissionBase sevm (afterSload sevm b 0) M = B
    rfl
  have bal : ∀ x, (submissionPost sevm (afterSload sevm b 0) M gas).getBal x =
      ((submissionBase sevm (afterSload sevm b 0) M).state.get x).bal := by
    intro x
    unfold submissionPost
    generalize submissionBase sevm (afterSload sevm b 0) M = B
    rfl
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
  · have logs : (submissionPost sevm (afterSload sevm b 0) M gas).logs =
        (submissionBase sevm (afterSload sevm b 0) M).logs := by
      unfold submissionPost
      generalize submissionBase sevm (afterSload sevm b 0) M = B
      rfl
    rw [logs, submissionBase, afterSstore_logs, logged, Devm.addLog_logs, submissionLog_eq hlen wf]
    simp only [recordsWritten, recordStore, afterSstore_logs, tailRead, afterSload_logs, countStore]
  · have output : (submissionPost sevm (afterSload sevm b 0) M gas).output =
        (submissionBase sevm (afterSload sevm b 0) M).output := by
      unfold submissionPost
      generalize submissionBase sevm (afterSload sevm b 0) M = B
      rfl
    rw [output]
    simp only [submissionBase, logged, afterSstore_output, addLog_output, recordsWritten, recordStore,
      tailRead, afterSload_output, countStore]

variable {sevm : Sevm} {pre post : Devm}

/-- **EIP-7251 frames.** Every successful execution of the consolidation code at a non-system caller, from
an empty stack, under covered forks, is a submission or a fee read. `aligned` and `wf` hold of the empty
memory every frame starts with; `lengthBound` holds of any calldata a frame can carry, since
`CALLDATASIZE` is read as a word. -/
theorem exec_user_frame (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress)
    (exec : Exec 0 sevm pre (.ok post)) : UserFrame sevm pre post := by
  rcases PlainUserPath.exec_user_cases (k := userPath) fork hcode stack aligned wf lengthBound caller exec with
    ⟨active, literal, iterations, finalOutput, wordRun, _, run⟩ | ⟨empty, iterations, finalOutput, read⟩
  · have literal : sevm.data.length = 96 := literal
    have run : SFunc.Run cert.prog sevm _
        (RequestFee.paidTree ⟨0x01, [0x9a], by decide⟩ t_008f_c0 t_019a_c0) _ := run
    obtain ⟨cov, _, run⟩ := RequestFee.paid_inv rfl run
    obtain ⟨dynamic, gas, state⟩ := body_inv fork run
    have state := Outcome.halted.inj state
    subst state
    exact .submission iterations finalOutput
      ⟨submissionPost_effects literal wf gas, dynamic, literal, active, wordRun, cov, gas, rfl⟩
  · exact .feeRead iterations finalOutput empty read

/-! ## Every other user entry fails -/

/-- **No other length.** A successful user frame has empty or 96-byte calldata. -/
theorem UserFrame.length (frame : UserFrame sevm pre post) :
    sevm.data.length = 0 ∨ sevm.data.length = 96 := by
  cases frame with
  | submission _ _ effect => exact .inr effect.length
  | feeRead _ _ empty _ => exact .inl (by rw [empty]; rfl)

/-- Fresh-frame premises, bundled: the code, a covered fork, an empty stack, aligned and well-formed
memory, calldata a word can measure, and a caller other than `SYSTEM_ADDRESS`. -/
structure Fresh (sevm : Sevm) (pre : Devm) : Prop where
  hcode : sevm.code = code
  fork : CoveredFork sevm.benvStat.fork
  stack : pre.stack = []
  aligned : pre.memory.size % 32 = 0
  wf : Mem.Wf pre.memory
  lengthBound : sevm.data.length < 2 ^ 256
  caller : sevm.caller ≠ systemAddress

theorem Fresh.frame (fresh : Fresh sevm pre) (exec : Exec 0 sevm pre (.ok post)) : UserFrame sevm pre post :=
  exec_user_frame fresh.hcode fresh.fork fresh.stack fresh.aligned fresh.wf fresh.lengthBound fresh.caller exec

/-- **Other input lengths fail.** A fresh user call whose calldata is neither empty nor 96 bytes has no
successful execution. -/
theorem exec_other_length_no_ok (fresh : Fresh sevm pre)
    (other : sevm.data.length ≠ 0 ∧ sevm.data.length ≠ 96) (exec : Exec 0 sevm pre (.ok post)) : False := by
  rcases (fresh.frame exec).length with h | h
  · exact other.1 h
  · exact other.2 h

/-- **A fee read with value fails.** A fresh user call with empty calldata and nonzero value has no
successful execution. -/
theorem exec_fee_read_value_no_ok (fresh : Fresh sevm pre) (empty : sevm.data = [])
    (value : sevm.value ≠ 0) (exec : Exec 0 sevm pre (.ok post)) : False := by
  cases fresh.frame exec with
  | submission _ _ effect =>
    have := effect.length
    rw [empty] at this
    exact absurd this (by decide)
  | feeRead _ _ _ effect => exact value effect.value

/-- **A static submission fails.** A fresh static user call with 96 bytes of calldata has no successful
execution. -/
theorem exec_static_submission_no_ok (fresh : Fresh sevm pre) (hlen : sevm.data.length = 96)
    (static : sevm.isStatic = true) (exec : Exec 0 sevm pre (.ok post)) : False := by
  cases fresh.frame exec with
  | submission _ _ effect =>
    rw [effect.dynamic] at static
    exact Bool.false_ne_true static
  | feeRead _ _ empty _ =>
    rw [empty] at hlen
    exact absurd hlen (by decide)

/-- **An underpaying submission fails.** A fresh user call with 96 bytes of calldata whose value is below
the word fee quoted on slot 0 has no successful execution. -/
theorem exec_underpaid_submission_no_ok {iterations : Nat} {finalOutput : B256}
    (fresh : Fresh sevm pre) (hlen : sevm.data.length = 96)
    (quote : WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput)
    (low : sevm.value.toNat < (finalOutput / (17 : B256)).toNat)
    (exec : Exec 0 sevm pre (.ok post)) : False := by
  cases fresh.frame exec with
  | submission _ _ effect =>
    obtain ⟨-, rfl⟩ := effect.quote.deterministic quote
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le low effect.covered)
  | feeRead _ _ empty _ =>
    rw [empty] at hlen
    exact absurd hlen (by decide)

/-- **Inhibited user calls fail.** While slot 0 holds the inhibitor, no fresh user call succeeds. -/
theorem exec_inhibited_no_ok (fresh : Fresh sevm pre)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max) (exec : Exec 0 sevm pre (.ok post)) :
    False :=
  exec_user_inhibited_no_ok fresh.hcode fresh.fork fresh.stack fresh.caller inhibited exec

/-! ## Submissions, forward -/

/-- The charge of a submission, from the frame's start. -/
def submissionGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  bodyGas sevm (afterSload sevm b 0) M + RequestFee.paidGas + RequestFee.plainPathGas sevm b iterations +
    RequestSystem.dispatchGas

variable {b : Devm} {M : Mem} {G : Nat}

/-- **Submission, forward.** 96 bytes of calldata in a non-static frame, slot 0 off the inhibitor and value
covering the word fee give a successful execution at the exact charge, leaving `slack` over the `SSTORE`
sentry. -/
theorem exec_submission_exact {iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 96)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (off : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput)
    (cov : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGas sevm b M iterations))
      (.ok (submissionPost sevm (afterSload sevm b 0) M G))) := by
  have word : sevm.data.length.toB256 = userPath.shape.len.word := by rw [hlen]; rfl
  have body := RequestFee.paid_exact (fs := cert.prog) (dest := ⟨0x01, [0x9a], by decide⟩)
    (revert := t_019a_c0) cov (body_exact (b := afterSload sevm b 0) (M := M) fork dynamic slack)
  have path := RequestFee.plainPath_exact fork (p := userPath.shape) (revert := userPath.revert)
    (getter := userPath.getter) (submission := t_0088_c0) userPath.loop off wordRun (by
      rw [RequestFee.selected, ite_eq_left word]
      exact body)
  have hgas : G + submissionGas sevm b M iterations =
      (G + bodyGas sevm (afterSload sevm b 0) M + RequestFee.paidGas + RequestFee.plainPathGas sevm b iterations) +
        RequestSystem.dispatchGas := by
    simp only [submissionGas, Nat.add_assoc]
  rw [hgas]
  exact PlainUserPath.exec_of_user (k := userPath) hcode caller path

/-- **The submission's premises can all be met together.** On storage whose slot 0 is zero, any 96 bytes of
calldata and a value of at least 1 wei in a non-static frame run to `STOP`. -/
theorem exec_submission_witness (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (caller : sevm.caller ≠ systemAddress) (hlen : sevm.data.length = 96)
    (value : 1 ≤ sevm.value.toNat) (dynamic : sevm.isStatic = false)
    (slack : gCallStipend < G) (slot0 : b.getStorVal sevm.currentTarget 0 = 0) :
    Nonempty (Exec 0 sevm (St b [] M (G + submissionGas sevm b M 1))
      (.ok (submissionPost sevm (afterSload sevm b 0) M G))) := by
  have fee : ((17 : B256) / (17 : B256)).toNat = 1 := by decide
  refine exec_submission_exact (finalOutput := 17) hcode fork caller hlen dynamic slack
    (by rw [slot0]; decide) (by rw [slot0]; exact RequestFee.word_run_zero) ?_
  rw [fee]
  exact value

/-! ## The record, on represented storage -/

/-- **The record a submission leaves**, on storage whose tail is below `2 ^ 253`, so that no record slot
aliases slots 0 to 3: the caller and calldata words 0, 1, 2 at slots `4 + 4 * tail` to `+ 3`, the count and
the tail bumped by one, slots 0 and 2 kept. -/
theorem submittedStorage_record (sevm : Sevm) {s : Stor} (room : (s.get 3).toNat < 2 ^ 253) :
    (submittedStorage sevm s).get (4 + 4 * (s.get 3).toNat).toB256 = sevm.caller.toB256 ∧
    (submittedStorage sevm s).get (4 + 4 * (s.get 3).toNat + 1).toB256 = Sevm.dataWord sevm 0 ∧
    (submittedStorage sevm s).get (4 + 4 * (s.get 3).toNat + 2).toB256 = Sevm.dataWord sevm 32 ∧
    (submittedStorage sevm s).get (4 + 4 * (s.get 3).toNat + 3).toB256 = Sevm.dataWord sevm 64 ∧
    (submittedStorage sevm s).get 0 = s.get 0 ∧
    (submittedStorage sevm s).get 1 = 1 + s.get 1 ∧
    (submittedStorage sevm s).get 2 = s.get 2 ∧
    (submittedStorage sevm s).get 3 = 1 + s.get 3 := by
  generalize ht : (s.get 3).toNat = t at room
  have tail : s.get 3 = t.toB256 := by rw [← ht, toB256_toNat]
  have key0 : submissionKey (s.get 3) = (4 + 4 * t).toB256 := by
    rw [tail, submissionKey, show (4 : B256) = Nat.toB256 4 by decide]
    apply B256.toNat_inj
    rw [B256.toNat_toB256_of_lt (by omega), B256.toNat_add, B256.toNat_mul, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt (by omega)]
    simp only [Nat.lo]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have step : ∀ n, (1 : B256) + n.toB256 = (n + 1).toB256 := fun n => by
    rw [show (1 : B256) = Nat.toB256 1 by decide, Nat.toB256_add_toB256, Nat.add_comm]
  have nk : ∀ a b : Nat, a < 2 ^ 256 → b < 2 ^ 256 → a ≠ b → a.toB256 ≠ b.toB256 :=
    fun a b ha hb hab e => hab (by
      have := congrArg B256.toNat e
      rwa [B256.toNat_toB256_of_lt ha, B256.toNat_toB256_of_lt hb] at this)
  have c0 : (0 : B256) = Nat.toB256 0 := by decide
  have c1 : (1 : B256) = Nat.toB256 1 := by decide
  have c2 : (2 : B256) = Nat.toB256 2 := by decide
  have c3 : (3 : B256) = Nat.toB256 3 := by decide
  unfold submittedStorage
  simp only []
  rw [key0, step, step, step, show 4 + 4 * t + 1 + 1 = 4 + 4 * t + 2 by omega,
    show 4 + 4 * t + 2 + 1 = 4 + 4 * t + 3 by omega]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Stor.get_set_ne _ (by rw [c3]; exact nk 3 (4 + 4 * t) (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by exact nk (4 + 4 * t + 3) (4 + 4 * t) (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by exact nk (4 + 4 * t + 2) (4 + 4 * t) (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by exact nk (4 + 4 * t + 1) (4 + 4 * t) (by omega) (by omega) (by omega)),
      Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by rw [c3]; exact nk 3 (4 + 4 * t + 1) (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by exact nk (4 + 4 * t + 3) (4 + 4 * t + 1) (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by exact nk (4 + 4 * t + 2) (4 + 4 * t + 1) (by omega) (by omega) (by omega)),
      Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by rw [c3]; exact nk 3 (4 + 4 * t + 2) (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by exact nk (4 + 4 * t + 3) (4 + 4 * t + 2) (by omega) (by omega) (by omega)),
      Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by rw [c3]; exact nk 3 (4 + 4 * t + 3) (by omega) (by omega) (by omega)),
      Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by rw [c3, c0]; exact nk 3 0 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c0]; exact nk (4 + 4 * t + 3) 0 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c0]; exact nk (4 + 4 * t + 2) 0 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c0]; exact nk (4 + 4 * t + 1) 0 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c0]; exact nk (4 + 4 * t) 0 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c1, c0]; exact nk 1 0 (by omega) (by omega) (by omega))]
  · rw [Stor.get_set_ne _ (by rw [c3, c1]; exact nk 3 1 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c1]; exact nk (4 + 4 * t + 3) 1 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c1]; exact nk (4 + 4 * t + 2) 1 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c1]; exact nk (4 + 4 * t + 1) 1 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c1]; exact nk (4 + 4 * t) 1 (by omega) (by omega) (by omega)),
      Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by rw [c3, c2]; exact nk 3 2 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c2]; exact nk (4 + 4 * t + 3) 2 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c2]; exact nk (4 + 4 * t + 2) 2 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c2]; exact nk (4 + 4 * t + 1) 2 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c2]; exact nk (4 + 4 * t) 2 (by omega) (by omega) (by omega)),
      Stor.get_set_ne _ (by rw [c1, c2]; exact nk 1 2 (by omega) (by omega) (by omega))]
  · rw [Stor.get_set_self]


end Blanc.Lift.ConsolidationRequest
