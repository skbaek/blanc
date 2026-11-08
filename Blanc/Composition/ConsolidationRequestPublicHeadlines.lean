import Blanc.Composition.ConsolidationRequestPublicObservers
import Blanc.Lift.ConsolidationRequest.System
import Blanc.Lift.ConsolidationRequest.SystemFrame
import Blanc.Lift.ConsolidationRequest.Fee
import Blanc.Lift.ConsolidationRequest.Frames
import Blanc.Lift.ConsolidationRequest.Submission
import Blanc.Lift.RequestFee.Plain
import Blanc.Lift.RequestFee.Window
import Blanc.Lift.RequestSystem.Dispatch
import Blanc.Lift.RequestQueue.Model

/-!
# EIP-7251 public headlines C1, C2, C3, C5

Featured C1 (system call), C2 (what succeeds), C3 (fee against the EIP) and C5 (submission queued
and live), over the observers in `ConsolidationRequestPublicObservers`. Each
headline is a thin wrapper over the proved unit theorems in
`Lift/ConsolidationRequest/`; every definition and theorem has a one-sentence
docstring. C1b (`system_call_bookkept`, ordinary, unfeatured) takes the tail
below `2 ^ 253`: a record occupies four slots from `4 + 4q`, computed in words,
so a larger tail lets a record key wrap onto slots 0 to 3. C2 (`exec_succeeded`)
classifies every successful fresh frame; its dequeue arm reads the output as
queue entries only with head ≤ tail, since the bytes subtract the pointers in
words (head > tail drains wrapped positions, where the stored queue is empty).
`ConsolidationRequestPublicHistory.history_pointers` derives head ≤ tail, and
the tail at most the number of submissions, from C4's premises.
-/

namespace Blanc.Composition.ConsolidationRequestPublic

open Jaune Blanc

/-! ## C1: the system call -/

/-- The checked EIP-7251 system call returns without error and uses at most 114,177 gas. The subtraction is of
naturals; `system_call_ok` also shows the call ends with at most the 30,000,000 it started with, so it is exact. -/
def SystemCallOk (benv : Benv) : Prop :=
  ∃ post out, processCheckedSystemTransaction benv addr [] = .ok (post, out) ∧
    systemTransactionGas - out.gasLeft ≤ 114177

/-- **C1. EIP-7251 system call.** On a covered fork with the canonical code installed, whatever storage holds,
the checked system call succeeds and uses at most 114,177 gas. -/
theorem system_call_succeeds {benv : Benv} (fork : CoveredFork benv.stat.fork)
    (installed : benv.state.getCode addr = code) :
    SystemCallOk benv := by
  obtain ⟨out, hcall, -, hgas, -⟩ := Lift.ConsolidationRequest.system_call_ok fork installed
  obtain ⟨-, hbound⟩ := hgas
  exact ⟨_, out, hcall, hbound⟩

/-- The EIP's next excess: the stored excess (inhibitor read as 0) plus the count, less the target 1, floored at 0. -/
def excessAfter (e n : Nat) : Nat := (if e = 2 ^ 256 - 1 then 0 else e) + n - 1

/-- One system call's bookkeeping from `pre` to `post`, reading the four words as numbers. -/
structure Bookkept (pre post : State) (out : Bytes) : Prop where
  /-- The new excess is `max(0, e + count − 1)`. -/
  excess : (word post 0).toNat = excessAfter (word pre 0).toNat (word pre 1).toNat
  /-- The count resets. -/
  count : word post 1 = 0
  /-- The first `min(2, queue)` entries leave. -/
  queue : remainingQueue post = (remainingQueue pre).drop 2
  /-- When the queue empties, both pointers reset to 0. -/
  reset : (word pre 3).toNat - (word pre 2).toNat ≤ 2 → word post 2 = 0 ∧ word post 3 = 0
  /-- No slot of the predeploy beyond the four words changes. -/
  others : ∀ k : B256, 3 < k.toNat → word post k = word pre k
  /-- The call returns exactly the entries that left, 116 bytes each. -/
  output : out = ((remainingQueue pre).take 2).flatten

/-- One returned record, read from queue position `h + i`, is the stored queue's entry there. -/
theorem recordBytes_queueRecord (s : B256 → B256) (h i : Nat) :
    Lift.ConsolidationRequest.recordBytes s h.toB256 i.toB256 = queueRecord s (h + i) := by
  have ha : ∀ x : B256, (x <<< 96).toBytes.sliceD 0 20 0 = x.toAdr.toBytes := fun x => by
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega),
      WordByteCodecs.shift96_take20_toAdr_bytes]
  have hk : ∀ r : Nat, r.toB256 + (4 + 4 * (h + i)).toB256 = (4 + 4 * (h + i) + r).toB256 := fun r => by
    rw [Nat.toB256_add_toB256, Nat.add_comm]
  unfold Lift.ConsolidationRequest.recordBytes queueRecord
  rw [Lift.ConsolidationRequest.recordKey_toB256, ha, show (1 : B256) = Nat.toB256 1 by decide,
    show (2 : B256) = Nat.toB256 2 by decide, show (3 : B256) = Nat.toB256 3 by decide, hk, hk, hk]

/-- The first two entries of the stored queue, read as the records a call returns from queue position `h`. -/
theorem take_two_eq (s : B256 → B256) {h t : Nat} (h2 : s 2 = h.toB256) (h3 : s 3 = t.toB256) (ordered : h ≤ t)
    (t_lt : t < 2 ^ 256) :
    ((storedQueue s).take 2).flatten = (List.range (Lift.ConsolidationRequest.taken (t - h))).flatMap
      fun i => Lift.ConsolidationRequest.recordBytes s h.toB256 i.toB256 := by
  unfold storedQueue Lift.ConsolidationRequest.taken
  rw [h2, h3, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt t_lt, ← List.map_take, List.take_range,
    ← List.flatMap_def]
  exact List.flatMap_congr fun i _ => (recordBytes_queueRecord s h i).symm

/-- **C1b. Bookkeeping.** On a covered fork with the canonical code installed, head ≤ tail with the tail below
`2 ^ 253` (four slots per record: no record key wraps onto slots 0 to 3), and no word wrap in `excess + count`, the
call does the EIP's bookkeeping. On a kept history from the checkpoint, `history_pointers` gives head ≤ tail and the
tail at most the number of submissions, so `room` holds while fewer than `2 ^ 253` have been made. -/
theorem system_call_bookkept {benv : Benv} (fork : CoveredFork benv.stat.fork) (installed : installed benv.state)
    (ordered : (word benv.state 2).toNat ≤ (word benv.state 3).toNat)
    (room : (word benv.state 3).toNat < 2 ^ 253)
    (noWrap : (if word benv.state 0 = B256.max then 0 else (word benv.state 0).toNat) +
      (word benv.state 1).toNat < 2 ^ 256) :
    ∃ post out, processCheckedSystemTransaction benv addr [] = .ok (post, out) ∧
      Bookkept benv.state post out.returnData := by
  generalize he : (word benv.state 0).toNat = e at noWrap
  generalize hn : (word benv.state 1).toNat = n at noWrap
  generalize hh : (word benv.state 2).toNat = h at ordered
  generalize ht : (word benv.state 3).toNat = t at ordered room
  have hmax : (B256.max).toNat = 2 ^ 256 - 1 := by decide
  have noWrap' : (if e = 2 ^ 256 - 1 then 0 else e) + n < 2 ^ 256 := by
    by_cases hm : word benv.state 0 = B256.max
    · rw [ite_eq_left hm] at noWrap
      rw [ite_eq_left (by rw [← he, hm, hmax])]
      exact noWrap
    · rw [ite_eq_right hm] at noWrap
      rw [ite_eq_right fun (heq : e = 2 ^ 256 - 1) => hm (B256.toNat_inj _ _ (by rw [he, heq, hmax]))]
      exact noWrap
  obtain ⟨σ, out, hcall, -, -, h0, h1, h2, h3, hothers, hret⟩ :=
    Lift.ConsolidationRequest.system_call_storage fork installed (e := e) (n := n) (h := h) (t := t)
      (by rw [← he]; exact (toB256_toNat _).symm) (by rw [← hn]; exact (toB256_toNat _).symm)
      (by rw [← hh]; exact (toB256_toNat _).symm) (by rw [← ht]; exact (toB256_toNat _).symm)
      (by rw [← he]; exact B256.toNat_lt _) ordered (by omega) noWrap'
  have rd2 : word benv.state 2 = h.toB256 := by rw [← hh, toB256_toNat]
  have rd3 : word benv.state 3 = t.toB256 := by rw [← ht, toB256_toNat]
  refine ⟨σ, out, hcall, ⟨?_, h1, ?_, ?_, hothers, ?_⟩⟩
  · show (Lift.RequestSystem.storOf σ addr 0).toNat = _
    rw [h0, he, hn, B256.toNat_toB256_of_lt (by unfold Lift.ConsolidationRequest.excessAfter; omega)]
    rfl
  · have keep : ∀ k, k < t → queueRecord (Lift.RequestSystem.storOf σ addr) k =
        queueRecord (Lift.RequestSystem.storOf benv.state addr) k := by
      intro k hk
      have hr : ∀ r, r < 4 → Lift.RequestSystem.storOf σ addr (4 + 4 * k + r).toB256 =
          Lift.RequestSystem.storOf benv.state addr (4 + 4 * k + r).toB256 := fun r hr =>
        hothers _ (by rw [B256.toNat_toB256_of_lt (by omega)]; omega)
      unfold queueRecord
      rw [show 4 + 4 * k = 4 + 4 * k + 0 from rfl, hr 0 (by omega), hr 1 (by omega), hr 2 (by omega),
        hr 3 (by omega)]
    show storedQueue (Lift.RequestSystem.storOf σ addr) = (storedQueue (Lift.RequestSystem.storOf benv.state addr)).drop 2
    unfold storedQueue
    rw [h2, h3]
    show _ = ((List.range ((word benv.state 3).toNat - (word benv.state 2).toNat)).map _).drop 2
    rw [hh, ht]
    by_cases le : t - h ≤ 2
    · rw [ite_eq_left le, ite_eq_left le, show (Nat.toB256 0).toNat = 0 from rfl, Nat.sub_self, List.range_zero,
        List.map_nil, List.drop_eq_nil_of_le (by rw [List.length_map, List.length_range]; omega)]
    · rw [ite_eq_right le, ite_eq_right le, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt (by omega)]
      apply List.ext_getElem
      · simp only [List.length_map, List.length_range, List.length_drop]
        omega
      · intro j h1' h2'
        simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
        have hh' : (Lift.RequestSystem.storOf benv.state addr 2).toNat = h := hh
        rw [keep _ (by simp only [List.length_map, List.length_range] at h1'; omega), hh']
        exact congrArg _ (by omega)
  · intro le
    rw [hh, ht] at le
    exact ⟨h2.trans (by rw [ite_eq_left le]; rfl), h3.trans (by rw [ite_eq_left le]; rfl)⟩
  · rw [hret]
    exact (take_two_eq _ (by rw [← hh, toB256_toNat]; rfl) (by rw [← ht, toB256_toNat]; rfl) ordered
      (by omega)).symm

/-! ## C3: the fee against the EIP -/

/-- **C3a. Fee bound.** The fee the bytes quote never exceeds the EIP's `fake_exponential(1, excess, 17)`. -/
theorem fee_le_spec (excess : B256) : quotedFee excess ≤ SpecFee excess := by
  have hrun := Classical.choose_spec
    (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists
  exact Lift.ConsolidationRequest.fee_le_spec hrun

/-- **C3b. Exact fee through excess 2892.** -/
theorem fee_eq_spec_of_le {excess : B256} (le : excess.toNat ≤ 2892) :
    quotedFee excess = SpecFee excess := by
  have hrun := Classical.choose_spec
    (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists
  exact Lift.ConsolidationRequest.fee_eq_spec_of_le le hrun

/-- **C3c. Finding: at excess 2893 the bytes quote less than the EIP's fee.** The fee loop's accumulator wraps a
word there. The window is the EIP-7002 runtime's but for one jump-target byte (`fee_window_bytes_eq`); EIP-7002's
`fee_guarantee_refuted` shows such an excess reached by a configured history. -/
theorem fee_lt_spec_2893 {excess : B256} (at2893 : excess.toNat = 2893) :
    quotedFee excess < SpecFee excess := by
  have hrun := Classical.choose_spec
    (Blanc.WordFakeExponential.run_exists_unique excess 17 1 17 0).exists
  exact Nat.lt_of_le_of_ne (Lift.ConsolidationRequest.fee_le_spec hrun)
    (Lift.ConsolidationRequest.fee_ne_spec_2893 at2893 hrun)

/-- The 87 fee-window bytes (pc 0x1a to 0x70 inclusive) of the EIP-7251 and EIP-7002 runtimes agree at every
index but 41 (pc 0x43), the low byte of the revert target: `0x9a` against `0xf4`. -/
theorem fee_window_bytes_eq :
    (∀ (i : Nat), i < 87 → i ≠ 41 →
      ((Blanc.consolidationRequestCode.toList.drop 26).take 87)[i]? =
        ((Blanc.withdrawalRequestCode.toList.drop 26).take 87)[i]?) ∧
    ((Blanc.consolidationRequestCode.toList.drop 26).take 87)[41]? = some 0x9a ∧
    ((Blanc.withdrawalRequestCode.toList.drop 26).take 87)[41]? = some 0xf4 := by
  decide +kernel

/-! ## C2: what succeeds -/

/-- A fresh entry: empty stack, word-aligned well-formed memory, calldata a word can measure. Every frame Jaune
opens starts with an empty stack and memory (`Blanc.Exec.FreshEntry`, `Frame.enter_run_fresh`), so it is one given
its calldata length (`FreshEntry.of_exec`). -/
structure FreshEntry (sevm : Sevm) (pre : Devm) : Prop where
  /-- The stack is empty. -/
  stack : pre.stack = []
  /-- Memory size is word aligned. -/
  aligned : pre.memory.size % 32 = 0
  /-- Memory is well formed. -/
  wf : Mem.Wf pre.memory
  /-- Calldata fits in a word. -/
  lengthBound : sevm.data.length < 2 ^ 256

/-- A frame Jaune opens, with calldata a word can measure, is a fresh entry. -/
theorem FreshEntry.of_exec {sevm : Sevm} {pre : Devm} (entry : Exec.FreshEntry sevm pre)
    (lengthBound : sevm.data.length < 2 ^ 256) : FreshEntry sevm pre :=
  ⟨entry.1, by rw [entry.2]; rfl, by rw [entry.2]; exact Mem.wf_empty, lengthBound⟩

/-- The one log a submission emits: topicless, its 116 record bytes. -/
def submissionLog (sevm : Sevm) : Log := ⟨addr, [], sevm.caller.toBytes ++ sevm.data⟩

/-- Every successful fresh frame at EIP-7251 is one of these three: the dequeue with its exact state and, for
head ≤ tail, its return bytes; the submission and the fee read with their storage, logs and output. -/
inductive Succeeded (sevm : Sevm) (pre post : Devm) : Prop
  /-- **Dequeue.** The system caller: storage updated as the system call defines; with head ≤ tail, the first two
  queued entries returned. -/
  | dequeue (caller : sevm.caller = systemAddress)
      (storage : post.state = Lift.RequestSystem.sysState
        Lift.SystemExecution.ConsolidationRequest.Amsterdam.sysShape pre.state addr)
      (output : (pre.getStorVal addr 2).toNat ≤ (pre.getStorVal addr 3).toNat →
        post.output = ((storedQueue (pre.getStor addr).get).take 2).flatten)
  /-- **Submission.** 96 bytes from a user in a non-static frame, slot 0 off the inhibitor, value at least the quoted
  fee: the record is stored at the tail and logged; no other storage changes; the output is unchanged. -/
  | submission (caller : sevm.caller ≠ systemAddress) (length : sevm.data.length = 96)
      (dynamic : sevm.isStatic = false) (active : pre.getStorVal addr 0 ≠ B256.max)
      (paid : quotedFee (pre.getStorVal addr 0) ≤ sevm.value.toNat)
      (storage : post.getStor addr = Lift.ConsolidationRequest.submittedStorage sevm (pre.getStor addr))
      (others : ∀ a, a ≠ addr → post.getStor a = pre.getStor a)
      (logs : post.logs = pre.logs ++ [submissionLog sevm]) (output : post.output = pre.output)
  /-- **Fee read.** Empty calldata and no value from a user, slot 0 off the inhibitor: returns the quoted fee as one
  word; storage and logs are unchanged. -/
  | feeRead (caller : sevm.caller ≠ systemAddress) (empty : sevm.data = []) (value : sevm.value = 0)
      (active : pre.getStorVal addr 0 ≠ B256.max)
      (output : post.output = (quotedFee (pre.getStorVal addr 0)).toB256.toBytes)
      (storage : ∀ a, post.getStor a = pre.getStor a) (logs : post.logs = pre.logs)

/-- The fee loop's unique run is the run a frame took. -/
private theorem quote_choose {e : B256} {n : Nat} {w : B256} (run : WordFakeExponential.Run e 17 1 17 0 n w) :
    Classical.choose (Blanc.WordFakeExponential.run_exists_unique e 17 1 17 0).exists = (n, w) :=
  (Blanc.WordFakeExponential.run_exists_unique e 17 1 17 0).unique
    (Classical.choose_spec (Blanc.WordFakeExponential.run_exists_unique e 17 1 17 0).exists) run

/-- The quoted fee is the quotient a frame's fee loop left. -/
theorem quotedFee_of_run {e : B256} {n : Nat} {w : B256} (run : WordFakeExponential.Run e 17 1 17 0 n w) :
    quotedFee e = (w / (17 : B256)).toNat := by
  unfold quotedFee
  rw [quote_choose run]

/-- **What the call returns, as queue entries.** With head ≤ tail, the drained records are the first two
entries of the stored queue (fewer if the queue is shorter). -/
theorem drained_eq_queue (s : B256 → B256) (ordered : (s 2).toNat ≤ (s 3).toNat) :
    Lift.ConsolidationRequest.drained s = ((storedQueue s).take 2).flatten := by
  have h2 : s 2 = (s 2).toNat.toB256 := (toB256_toNat _).symm
  have h3 : s 3 = (s 3).toNat.toB256 := (toB256_toNat _).symm
  have hc : Lift.RequestSystem.drainCount Lift.SystemExecution.ConsolidationRequest.Amsterdam.sysShape.cap.word
      (s 2) (s 3) = (Lift.ConsolidationRequest.taken ((s 3).toNat - (s 2).toNat)).toB256 := by
    have := Lift.ConsolidationRequest.drainCount_nat (h := (s 2).toNat) (t := (s 3).toNat) ordered
      (B256.toNat_lt _)
    rwa [toB256_toNat, toB256_toNat] at this
  rw [take_two_eq s h2 h3 ordered (B256.toNat_lt _)]
  unfold Lift.ConsolidationRequest.drained Lift.RequestSystem.SysOutput.drained
  rw [hc, B256.toNat_toB256_of_lt (by unfold Lift.ConsolidationRequest.taken; omega), ← h2]
  rfl

/-- **C2. What succeeds at EIP-7251.** On a covered fork, every successful fresh frame at the predeploy running its
code is a dequeue, a submission or a fee read, with the stated effect; so no other entry succeeds. -/
theorem exec_succeeded {sevm : Sevm} {pre post : Devm} (target : sevm.currentTarget = addr)
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork) (fresh : FreshEntry sevm pre)
    (exec : Exec 0 sevm pre (.ok post)) :
    Succeeded sevm pre post := by
  by_cases caller : sevm.caller = systemAddress
  · obtain ⟨-, hstate, hout⟩ :=
      Lift.ConsolidationRequest.exec_system_frame hcode fork fresh.stack fresh.wf caller exec
    refine .dequeue caller (by rw [hstate, target]) fun ordered => ?_
    rw [hout, target]
    exact drained_eq_queue _ ordered
  · rcases Lift.ConsolidationRequest.exec_user_frame hcode fork fresh.stack fresh.aligned fresh.wf
      fresh.lengthBound caller exec with ⟨i, w, law⟩ | ⟨i, w, empty, read⟩
    · have quote := law.quote
      rw [target] at quote
      refine .submission caller law.length law.dynamic (by rw [← target]; exact law.active)
        (by rw [quotedFee_of_run quote]; exact law.covered) (by rw [← target]; exact law.storage)
        (fun a ha => law.otherStorage a (by rw [target]; exact ha))
        (by rw [law.logs, target]; rfl) law.output
    · have quote := read.quote
      rw [target] at quote
      refine .feeRead caller empty read.value (by rw [← target]; exact read.active) ?_ read.storage read.logs
      rw [quotedFee_of_run quote, toB256_toNat]
      exact read.output

/-! ## C5: a submission works -/

/-- A successful 96-byte user submission appends exactly its record to the stored queue. -/
def SubmissionQueued (sevm : Sevm) (pre post : Devm) : Prop :=
  storedQueue (post.getStor addr).get = storedQueue (pre.getStor addr).get ++ [sevm.caller.toBytes ++ sevm.data]

/-- One stored-queue entry agrees when every record slot agrees. -/
private theorem queued_entry (preS postS : Stor) (h t x : Nat)
    (preserved : ∀ (kk : Nat), h ≤ kk → kk < t → ∀ (j : Nat), j < 4 →
      postS.get (4 + 4 * kk + j).toB256 = preS.get (4 + 4 * kk + j).toB256)
    (hx : x < t - h) (horder : h ≤ t) :
    (fun i => queueRecord postS.get (h + i)) x =
      (fun i => queueRecord preS.get (h + i)) x := by
  have e0 := preserved (h + x) (by omega) (by omega) 0 (by omega)
  have e1 := preserved (h + x) (by omega) (by omega) 1 (by omega)
  have e2 := preserved (h + x) (by omega) (by omega) 2 (by omega)
  have e3 := preserved (h + x) (by omega) (by omega) 3 (by omega)
  show queueRecord _ (h + x) = queueRecord _ (h + x)
  unfold queueRecord
  rw [show 4 + 4 * (h + x) = 4 + 4 * (h + x) + 0 by omega, e0, e1, e2, e3]

/-- Entrywise queue equality lifts to the stored queue: old entries agree, so the mapped ranges agree. -/
private theorem queued_map (preS postS : Stor) (h t : Nat)
    (preserved : ∀ (kk : Nat), h ≤ kk → kk < t → ∀ (j : Nat), j < 4 →
      postS.get (4 + 4 * kk + j).toB256 = preS.get (4 + 4 * kk + j).toB256)
    (horder : h ≤ t) :
    (List.range (t - h)).map (fun i => queueRecord postS.get (h + i)) =
      (List.range (t - h)).map (fun i => queueRecord preS.get (h + i)) := by
  have gen : ∀ (n : Nat) (f g : Nat → Bytes), (∀ x, x < n → f x = g x) →
      (List.range n).map f = (List.range n).map g := by
    intro n
    induction n with
    | zero => intro f g h; rfl
    | succ n ih =>
      intro f g h
      rw [List.range_succ, List.map_append, List.map_append, ih f g (fun x hx => h x (by omega))]
      simp only [List.map_cons, List.map_nil]
      rw [h n (by omega)]
  exact gen (t - h) _ _ (fun x hx => queued_entry _ _ _ _ _ preserved hx horder)

/-- A submission's storage keeps every old queue entry: record slots below the tail are untouched. -/
private theorem queued_preserved (sevm : Sevm) (s : Stor) (t h : Nat)
    (ht3 : s.get 3 = t.toB256) (hroom : t < 2 ^ 253) :
    ∀ (kk : Nat), h ≤ kk → kk < t → ∀ (j : Nat), j < 4 →
      (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * kk + j).toB256 =
        s.get (4 + 4 * kk + j).toB256 := by
  intro kk hkk hkt j hj
  have key0 : Lift.ConsolidationRequest.submissionKey (s.get 3) = (4 + 4 * t).toB256 := by
    unfold Lift.ConsolidationRequest.submissionKey
    rw [ht3, show (4 : B256) = (4 : Nat).toB256 from rfl, Nat.toB256_mul_toB256,
      Nat.toB256_add_toB256]
  have step : ∀ n : Nat, (1 : B256) + n.toB256 = (n + 1).toB256 := fun n => by
    rw [show (1 : B256) = Nat.toB256 1 by decide, Nat.toB256_add_toB256, Nat.add_comm]
  have nk : ∀ a b : Nat, a < 2 ^ 256 → b < 2 ^ 256 → a ≠ b → a.toB256 ≠ b.toB256 :=
    fun a b ha hb hab e => hab (by
      have := congrArg B256.toNat e
      rwa [B256.toNat_toB256_of_lt ha, B256.toNat_toB256_of_lt hb] at this)
  have c1 : (1 : B256) = Nat.toB256 1 := by decide
  have c3 : (3 : B256) = Nat.toB256 3 := by decide
  have kb : 4 + 4 * kk + j < 2 ^ 256 := by omega
  have tb : 4 + 4 * t + 3 < 2 ^ 256 := by omega
  have tb2 : 4 + 4 * t + 2 < 2 ^ 256 := by omega
  have tb1 : 4 + 4 * t + 1 < 2 ^ 256 := by omega
  have tb0 : 4 + 4 * t < 2 ^ 256 := by omega
  have three_lt : 3 < 2 ^ 256 := by decide
  have one_lt : 1 < 2 ^ 256 := by decide
  have lo : 3 < 4 + 4 * kk + j := by omega
  have lo1 : 1 < 4 + 4 * kk + j := by omega
  have lt0 : 4 + 4 * kk + j < 4 + 4 * t := by omega
  have lt1 : 4 + 4 * kk + j < 4 + 4 * t + 1 := by omega
  have lt2 : 4 + 4 * kk + j < 4 + 4 * t + 2 := by omega
  have lt3 : 4 + 4 * kk + j < 4 + 4 * t + 3 := by omega
  unfold Lift.ConsolidationRequest.submittedStorage
  simp only []
  rw [key0, step, step, step, show 4 + 4 * t + 1 + 1 = 4 + 4 * t + 2 by omega,
    show 4 + 4 * t + 2 + 1 = 4 + 4 * t + 3 by omega,
    Stor.get_set_ne _ (by rw [c3]; exact nk 3 _ three_lt kb lo.ne),
    Stor.get_set_ne _ (nk _ _ tb kb lt3.ne.symm),
    Stor.get_set_ne _ (nk _ _ tb2 kb lt2.ne.symm),
    Stor.get_set_ne _ (nk _ _ tb1 kb lt1.ne.symm),
    Stor.get_set_ne _ (nk _ _ tb0 kb lt0.ne.symm),
    Stor.get_set_ne _ (by rw [c1]; exact nk 1 _ one_lt kb lo1.ne)]

/-- The new last entry reads exactly the submitted record. -/
private theorem queued_last (sevm : Sevm) (s : Stor) (t h : Nat) (horder : h ≤ t)
    (r0' : (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * t).toB256 =
      sevm.caller.toB256)
    (r1' : (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * t + 1).toB256 =
      Sevm.dataWord sevm 0)
    (r2' : (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * t + 2).toB256 =
      Sevm.dataWord sevm 32)
    (r3' : (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * t + 3).toB256 =
      Sevm.dataWord sevm 64)
    (length : sevm.data.length = 96) :
    queueRecord (Lift.ConsolidationRequest.submittedStorage sevm s).get (h + (t - h)) =
      sevm.caller.toBytes ++ sevm.data := by
  have hteq : h + (t - h) = t := by omega
  rw [hteq]
  unfold queueRecord
  rw [r0', toAdr_toB256, r1', r2', r3']
  have z0 : (0 : B256).toNat = 0 := by decide
  have z32 : (32 : B256).toNat = 32 := by decide
  have z64 : (64 : B256).toNat = 64 := by decide
  simp only [Sevm.dataWord, z0, z32, z64,
    Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)]
  have h1 := List.sliceD_split sevm.data (0 : UInt8) 32 0 64
  have h2 := List.sliceD_split sevm.data (0 : UInt8) 32 32 32
  simp only [Nat.reduceAdd] at h1 h2
  simp only [List.append_assoc, ← h2, ← h1, sliceD_self _ length]

/-- The stored queue after the call is the stored queue before plus the new record. -/
private theorem queued_assemble (sevm : Sevm) (pre post : Devm) (s : Stor) (h t : Nat)
    (hs : pre.getStor addr = s) (horder : h ≤ t)
    (hstor : post.getStor addr = Lift.ConsolidationRequest.submittedStorage sevm s)
    (hh : (s.get 2).toNat = h) (ht : (s.get 3).toNat = t)
    (hhead : ((Lift.ConsolidationRequest.submittedStorage sevm s).get 2).toNat = h)
    (htail : ((Lift.ConsolidationRequest.submittedStorage sevm s).get 3).toNat = t + 1)
    (hmap : (List.range (t - h)).map
        (fun i => queueRecord (Lift.ConsolidationRequest.submittedStorage sevm s).get (h + i)) =
      (List.range (t - h)).map (fun i => queueRecord s.get (h + i)))
    (hlast : queueRecord (Lift.ConsolidationRequest.submittedStorage sevm s).get (h + (t - h)) =
      sevm.caller.toBytes ++ sevm.data) :
    storedQueue (post.getStor addr).get =
      storedQueue (pre.getStor addr).get ++ [sevm.caller.toBytes ++ sevm.data] := by
  unfold storedQueue
  rw [hstor, hs, hh, ht, hhead, htail,
    show t + 1 - h = (t - h) + 1 by omega, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [hmap, hlast]

/-- The submission case of C5a: from the storage law, the stored queue gains exactly the new record. -/
private theorem queued_submit_case {sevm : Sevm} {pre post : Devm} {i : Nat} {o : B256}
    (target : sevm.currentTarget = addr)
    (law : Lift.ConsolidationRequest.Submitted sevm pre post i o)
    (ordered : (pre.getStorVal addr 2).toNat ≤ (pre.getStorVal addr 3).toNat)
    (room : (pre.getStorVal addr 3).toNat < 2 ^ 253)
    (length : sevm.data.length = 96) :
    SubmissionQueued sevm pre post := by
    show storedQueue (post.getStor addr).get =
      storedQueue (pre.getStor addr).get ++ [sevm.caller.toBytes ++ sevm.data]
    unfold storedQueue
    set s := pre.getStor addr with hs_def
    set h := (s.get 2).toNat with hh_def
    set t := (s.get 3).toNat with ht_def
    have hstor : post.getStor addr =
        Lift.ConsolidationRequest.submittedStorage sevm s := by
      rw [← target, hs_def, ← target]
      exact law.storage
    have ordered' : h ≤ t := ordered
    have room' : t < 2 ^ 253 := room
    have ht3 : s.get 3 = t.toB256 := by simp only [ht_def, toB256_toNat]
    have room'' : (s.get 3).toNat < 2 ^ 253 := room'
    have preserved := queued_preserved sevm s t h ht3 room'
    have hrec := Lift.ConsolidationRequest.submittedStorage_record sevm room''
    obtain ⟨r0, r1, r2, r3, -, -, r6, r7⟩ := hrec
    have r0' : (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * t).toB256 =
        sevm.caller.toB256 := r0
    have r1' : (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * t + 1).toB256 =
        Sevm.dataWord sevm 0 := r1
    have r2' : (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * t + 2).toB256 =
        Sevm.dataWord sevm 32 := r2
    have r3' : (Lift.ConsolidationRequest.submittedStorage sevm s).get (4 + 4 * t + 3).toB256 =
        Sevm.dataWord sevm 64 := r3
    have hhead : ((Lift.ConsolidationRequest.submittedStorage sevm s).get 2).toNat = h := by
      rw [r6]
    have htail : ((Lift.ConsolidationRequest.submittedStorage sevm s).get 3).toNat = t + 1 := by
      rw [r7, ht3, Lift.RequestQueue.one_add_word, B256.toNat_toB256_of_lt (by omega)]
    have hmap := queued_map s
      (Lift.ConsolidationRequest.submittedStorage sevm s) h t preserved ordered'
    have hlast : queueRecord (Lift.ConsolidationRequest.submittedStorage sevm s).get (h + (t - h)) =
        sevm.caller.toBytes ++ sevm.data :=
      queued_last sevm s t h ordered' r0' r1' r2' r3' length
    have hfin : storedQueue (post.getStor addr).get =
        storedQueue (pre.getStor addr).get ++ [sevm.caller.toBytes ++ sevm.data] :=
      queued_assemble sevm pre post s h t hs_def.symm ordered' hstor hh_def.symm ht_def.symm
        hhead htail hmap hlast
    exact hfin

/-- **C5a. A submission is queued.** On a covered fork at the predeploy with head ≤ tail < 2^253, every successful
fresh 96-byte user frame appends its record. On a kept history from the checkpoint, `history_pointers` gives head ≤ tail
and the tail at most the number of submissions so far. -/
theorem submission_queued {sevm : Sevm} {pre post : Devm} (target : sevm.currentTarget = addr)
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (fresh : FreshEntry sevm pre) (user : sevm.caller ≠ systemAddress)
    (length : sevm.data.length = 96)
    (ordered : (pre.getStorVal addr 2).toNat ≤ (pre.getStorVal addr 3).toNat)
    (room : (pre.getStorVal addr 3).toNat < 2 ^ 253)
    (exec : Exec 0 sevm pre (.ok post)) :
    SubmissionQueued sevm pre post := by
  rcases Lift.ConsolidationRequest.exec_user_frame hcode fork fresh.stack fresh.aligned
    fresh.wf fresh.lengthBound user exec with ⟨i, o, law⟩ | ⟨_, _, empty, -⟩
  · exact queued_submit_case target law ordered room length
  · rw [empty] at length
    exact absurd length (by decide)

/-- The submission's storage reads, from the frame's start: slot 0's guard read and the body's count and tail reads. -/
def submissionReads (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm b 0 + sloadCost sevm (afterSload sevm b 0) 1 +
    sloadCost sevm (Lift.ConsolidationRequest.countStore sevm (afterSload sevm b 0)) 3

/-- The submission's storage writes and memory costs, from the frame's start with empty memory. -/
def submissionStores (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (afterSload sevm (afterSload sevm b 0) 1) 1 (1 + Lift.ConsolidationRequest.countWord sevm (afterSload sevm b 0)) +
    Lift.ConsolidationRequest.recordWritesGas sevm (Lift.ConsolidationRequest.tailRead sevm
    (afterSload sevm b 0)) (Lift.ConsolidationRequest.submissionKey
    (Lift.ConsolidationRequest.tailWord sevm (afterSload sevm b 0))) +
    Lift.ConsolidationRequest.sourceGas Mem.empty + Lift.ConsolidationRequest.copyGas
    (Mem.empty.write 0 (Lift.ConsolidationRequest.sourceWord sevm).toBytes) +
    Lift.ConsolidationRequest.log0Gas (Lift.ConsolidationRequest.copyMemory sevm Mem.empty) 116 +
    sstoreCost sevm (Lift.ConsolidationRequest.logged sevm (afterSload sevm b 0) Mem.empty) 3
    (1 + Lift.ConsolidationRequest.tailWord sevm (afterSload sevm b 0))

/-- Gas a fresh 96-byte submission consumes beyond the `G` it is left with: 269 for the straight-line instructions of
dispatch, guard, fee window and body; 87 per fee-loop iteration; the three storage reads at the fork's schedule; and
`submissionStores`: the six stores (count, four record words, tail) with the memory, copy and `LOG0` costs. -/
def submissionCharge (sevm : Sevm) (b : Devm) (iterations : Nat) : Nat :=
  269 + 87 * iterations + submissionReads sevm b + submissionStores sevm b

/-- The public charge is the library's exact submission charge (`submissionGas`) at empty memory. -/
theorem submissionCharge_eq (sevm : Sevm) (b : Devm) (iterations : Nat) :
    submissionCharge sevm b iterations =
      Lift.ConsolidationRequest.submissionGas sevm b Mem.empty iterations := by
  simp only [submissionCharge, submissionReads, submissionStores,
    Lift.ConsolidationRequest.submissionGas, Lift.ConsolidationRequest.bodyGas,
    Lift.RequestFee.plainPathGas, Lift.RequestFee.plainGuardGas,
    Lift.RequestFee.feeLoopGas_eq, Lift.RequestFee.postloopFixedGas_eq,
    Lift.RequestFee.plainGuardFixedGas_eq, Lift.RequestFee.paidGas_eq,
    Lift.ConsolidationRequest.bodyFixedGas, Lift.RequestSystem.dispatchGas]
  omega

/-- A fresh 96-byte user submission succeeds from `G + submissionCharge` and ends with exactly `G`, for every `G` above the 2,300 stipend. -/
def SubmissionLive (sevm : Sevm) (b : Devm) : Prop :=
  ∀ G, gCallStipend < G → ∃ post, Nonempty (Exec 0 sevm (Lift.St b [] Mem.empty
    (G + submissionCharge sevm b (quotedIterations (b.getStorVal addr 0)))) (.ok post)) ∧ post.gasLeft = G

/-- **C5b. A paid submission succeeds at an exact charge.** On a covered fork at the predeploy, 96 bytes from a user in a non-static frame, slot 0 off the inhibitor, value at least the quoted fee. -/
theorem submission_live {sevm : Sevm} {b : Devm} (target : sevm.currentTarget = addr)
    (hcode : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : sevm.data.length = 96)
    (dynamic : sevm.isStatic = false) (active : b.getStorVal addr 0 ≠ B256.max)
    (paid : quotedFee (b.getStorVal addr 0) ≤ sevm.value.toNat) :
    SubmissionLive sevm b := by
  intro G slack
  have hrun := Classical.choose_spec
    (Blanc.WordFakeExponential.run_exists_unique (b.getStorVal addr 0) 17 1 17 0).exists
  have hrun' : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0
      (Classical.choose
        (Blanc.WordFakeExponential.run_exists_unique (b.getStorVal addr 0) 17 1 17 0).exists).1
      (Classical.choose
        (Blanc.WordFakeExponential.run_exists_unique (b.getStorVal addr 0) 17 1 17 0).exists).2 := by
    rw [target]
    exact hrun
  obtain ⟨exec⟩ := Lift.ConsolidationRequest.exec_submission_exact (M := Mem.empty) (G := G)
    hcode fork user length dynamic slack (by rw [target]; exact active) hrun' paid
  rw [submissionCharge_eq]
  refine ⟨_, ⟨exec⟩, ?_⟩
  rw [Lift.ConsolidationRequest.submissionPost, Lift.St, Devm.gasLeft_setMach]

end Blanc.Composition.ConsolidationRequestPublic
