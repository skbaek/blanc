import Blanc.Lift.BuilderRequest.Surplus
import Blanc.Lift.BuilderRequest.Exit.Flood
import Blanc.Lift.BuilderRequest.Exit.Transaction

/-!
# Exit properties: surplus, the excess in naturals, source authentication

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`; the bytes and `sys-asm` `83f9801`.

**Source authentication.** A delivered exit record's source is exactly the caller of the frame that submitted it. No frame can record another address: `recordOf` takes the source from `sevm.caller`, and the frame law
`submittedStorage_record` reads it back from storage. **What is frame level and what is not.** The frame laws hold of any frame: any depth, any caller but SYSTEM, a contract's or a second submission in one transaction included. The sequence
statements take frames as a given list. `message_ok` is the top-level path and does not cover an internal `CALL`, and its `origin` premise excludes a second submission in the same transaction. That a chain's kept frames form the list is the chain-level link, not stated here.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune
open RequestSystem
open Delivery
open Creation (address)

/-! ## Surplus -/

/-- **The certificate has no node that moves ether**: no call-family or `CREATE` instruction and no `SELFDESTRUCT` terminal, over every entry of its program. -/
theorem cert_moves_no_value : BalSilentSet cert.prog (List.range cert.prog.length) = true := by decide +kernel

/-- **No successful frame at the code changes a balance**, for any caller, SYSTEM included, at any depth, on any fork. The value a message carries moves before the frame (`message_ok`, `transaction_ok`). -/
theorem frame_keeps_balances {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (exec : Exec 0 sevm pre (.ok post)) : post.getBal = pre.getBal :=
  BuilderRequest.frame_keeps_balances cert_check userPath.noExec cert_moves_no_value (by decide +kernel) hcode exec

/-- **A record does not read the value.** Two frames by the same caller with the same calldata make the same record, whatever value each carried. -/
theorem recordOf_value_free {s s' : Sevm} (hc : s.caller = s'.caller) (hd : s.data = s'.data) (h : s.data.length = 48)
    (h' : s'.data.length = 48) : recordOf s h = recordOf s' h' := by
  simp only [recordOf, hc, hd]

/-- **Surplus is locked at the exit contract.** A direct submission with any value at least the fee raises the balance by the whole value, and the storage is the submission's, which reads the caller and calldata and not the
value. The code cannot pay it out (`frame_keeps_balances`). -/
theorem surplus_locked {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E t : Adr} {chainId : UInt64}
    {prio maxFee i f n : Nat} {out : B256} (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t) (hnew : t ∉ benv.createdAccounts)
    (caller : E ≠ systemAddress) (value : tx.value.toB256 ≠ 0) (hlen : tx.data.length = 48)
    (hgas : i + submissions.regularBound n + submissions.stateBound + gCallStipend < tx.gas)
    (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess 2 (benv.state.getStor t)) 17 1 17 0 n out)
    (admit : Admits tx.data tx.value.toB256 (out / (17 : B256)))
    (noAlias : ((benv.state.getStor t).get 3).toNat < 2 ^ 253) (hcb : benv.stat.coinbase ≠ t) :
    ∃ (s : Sevm) (st : State) (bout' : BlockOutput), s.data = tx.data ∧
      processTransaction benv bout tx index = .ok (st, bout') ∧
      (st.get t).bal = (benv.state.get t).bal + tx.value.toB256 ∧
      (st.get t).stor = submittedStorage s (benv.state.getStor t) := by
  obtain ⟨entry, st, bout', hproc, hbal, hstor⟩ := submissions.transaction_balance (index := index) d installed hprecomp hnew
    caller value hlen hgas off wordRun admit noAlias hcb
  exact ⟨_, st, bout', rfl, hproc, hbal, hstor⟩

/-! ## The excess in naturals -/

/-- **The excess a system call stores, in naturals.** On storage representing a queue, the checked empty-calldata call stores in slot 0: on the inhibitor, 0 whatever the count; off it, with no word wrap in `excess + count`,
`max(0, excess + count - 2)`, natural subtraction being that `max`. `system_call_fifo` states the same through `excessNext`, a word function. -/
theorem system_call_excess {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) {st : QueueState Record}
    (rep : Represents 3 Record.word (storOf benv.state address) st) :
    ∃ post out, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
      (st.excess = 2 ^ 256 - 1 → (post.getStor address).get 0 = 0) ∧
      (st.excess ≠ 2 ^ 256 - 1 → st.excess + st.count < 2 ^ 256 →
        ((post.getStor address).get 0).toNat = st.excess + st.count - 2) := by
  obtain ⟨post, out, hcall, -, -, hrep⟩ := system_call_fifo hfork installed rep
  have h0 : (post.getStor address).get 0 = (drainedState 16 2 st).excess.toB256 := hrep.excess
  obtain ⟨h1, h2⟩ := drained_excess_cases 16 2 st
  refine ⟨post, out, hcall, fun hmax => ?_, fun hne hsum => ?_⟩
  · rw [h0, h1 hmax]
    rfl
  · rw [h0, B256.toNat_toB256_of_lt hrep.excess_lt, h2 hne hsum]
    rfl

/-- **The excess over a sequence, in naturals.** `excess_dynamics`' update: from the deployed storage, with fewer than `2 ^ 256` submissions before it, an empty-calldata call after frames `xs` stores 0 on the inhibitor, and
`max(0, excess + count - 2)` off it. -/
theorem excess_natural {xs : List Frame} {f : Frame} (hrange : (Delivery.submissions xs).length < 2 ^ 256) (call : f.event = .system false) :
    (queueAfter deployedQueue (xs ++ [f])).excess =
      if (queueAfter deployedQueue xs).excess = 2 ^ 256 - 1 then 0
      else (queueAfter deployedQueue xs).excess + (queueAfter deployedQueue xs).count - 2 :=
  excess_update (by decide) (by
    show load deployedQueue + _ < _
    rw [show load deployedQueue = 0 from rfl, Nat.zero_add]
    exact hrange) call

/-! ## Source authentication -/

/-- The caller of a submission's frame. -/
def Frame.submitter : Frame → Option Adr
  | .submission sevm .. => some sevm.caller
  | _ => none

/-- The callers of the frames' submissions, in order. -/
def submitters (frames : List Frame) : List Adr := frames.filterMap Frame.submitter

/-- **Each submitted record's source is its frame's caller.** In order, over any list of frames. -/
theorem sources_eq_submitters (frames : List Frame) :
    (Delivery.submissions frames).map Record.source = submitters frames := by
  induction frames with
  | nil => rfl
  | cons f rest ih =>
    cases f with
    | submission sevm pre post l i o rules target caller law =>
      show Record.source (recordOf sevm law.length) :: (Delivery.submissions rest).map Record.source =
        sevm.caller :: submitters rest
      rw [ih]
      rfl
    | feeRead sevm pre post l i o rules target caller law => exact ih
    | system benv data post out fork installed length run => exact ih

/-- **Exit source authentication, over the list.** On a chain from the deployed storage, within the word range: the system calls' concatenated output is exactly the records of the oldest `d` submissions, and those
records' sources are exactly the callers of the frames that submitted them, in order. A record's bytes begin with its source (`Record.out`). No statement here is about which frames a chain keeps. -/
theorem delivered_sources {frames : List Frame} {t : Stor} (chain : Chain deployedStorage frames t)
    (range : 4 + 3 * (Delivery.submissions frames).length ≤ 2 ^ 256) :
    ∃ rs : List Record, systemOutput frames = rs.flatMap Record.out ∧
      rs.map Record.source = (submitters frames).take (deliveredRecords deployedQueue frames) := by
  refine ⟨(Delivery.submissions frames).take (deliveredRecords deployedQueue frames), (delivery chain range).2.2, ?_⟩
  rw [← sources_eq_submitters, List.map_take]

/-- **No frame can record another address.** Every successful frame at the code, at any depth, by any caller but SYSTEM, a contract's included, on any fork's steps, on a tail in word range, is a fee read or
writes exactly its caller's word at its record's source slot. There is no premise on the caller's kind or on what ran earlier in the transaction. -/
theorem frame_records_caller {sevm : Sevm} {pre post : Devm} {l : StorageSteps sevm} (v : l.Valid) (hcode : sevm.code = code)
    (stack : pre.stack = []) (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory)
    (lengthBound : sevm.data.length < 2 ^ 256) (caller : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post))
    {tail : Nat} (ht : (pre.getStor sevm.currentTarget).get 3 = tail.toB256) (hb : queueBase 3 tail + 3 ≤ 2 ^ 256) :
    sevm.data = [] ∨ (post.getStor sevm.currentTarget).get (queueSlot 3 tail 0) = sevm.caller.toB256 := by
  rcases exec_user_frame_on v hcode stack aligned wf lengthBound caller exec with ⟨_, _, h⟩ | ⟨_, _, empty, _⟩
  · right
    rw [h.storage]
    exact (submittedStorage_record sevm ht hb).1
  · exact Or.inl empty

/-- **A batcher: two submissions in one transaction.** A frame at the code, then a second frame on the machine the first left, so with its warm slots, its original-value bookkeeping and its meter, as a contract making two `CALL`s in
one transaction would see, with a fresh stack and memory. On a represented queue at excess 0, count 0, the callers any but SYSTEM, each paying at least 1 wei: both succeed, and the storage represents the queue with both records at its back,
each with its own frame's caller as its source, and the two logs in order.

**About the gas.** Each frame's charge is exactly `submissionGasA` at its own base, the same formula on both; the bases differ, so the charges differ, through what `SLOAD` and `SSTORE` see: slots warmed by the first frame, and `SSTORE`'s original-value
case, since the count slot is no longer at its original value. The difference itself is not computed. Each charge is within `regularBound 1 + stateBound`, by a bound that holds at every base. **Frame level**: nothing here is the calling contract's own execution, the value
transfers or a message-level return; `message_ok` does not cover this, since its `origin` premise excludes a second submission in a transaction. -/
theorem batcher_witness {s1 s2 : Sevm} {b : Devm} {G1 G2 : Nat} {st : QueueState Record}
    (hc1 : s1.code = code) (hc2 : s2.code = code) (hf1 : s1.benvStat.fork = .amsterdam) (hf2 : s2.benvStat.fork = .amsterdam)
    (same : s2.currentTarget = s1.currentTarget) (caller1 : s1.caller ≠ systemAddress) (caller2 : s2.caller ≠ systemAddress)
    (hlen1 : s1.data.length = 48) (hlen2 : s2.data.length = 48) (dyn1 : s1.isStatic = false) (dyn2 : s2.isStatic = false)
    (v1 : 1 ≤ s1.value.toNat) (v2 : 1 ≤ s2.value.toNat) (slack1 : gCallStipend < G1) (slack2 : gCallStipend < G2)
    (rep : Represents 3 Record.word (fun key => (b.getStor s1.currentTarget).get key) st) (he : st.excess = 0) (hc : st.count = 0)
    (room : queueBase 3 (st.tail + 2) ≤ 2 ^ 256) :
    ∃ post1 post2,
      Nonempty (Exec 0 s1 (St b [] .empty (G1 + submissionGasA s1 b .empty 1)) (.ok post1)) ∧
      Nonempty (Exec 0 s2 (St post1 [] .empty (G2 + submissionGasA s2 post1 .empty 1)) (.ok post2)) ∧
      Represents 3 Record.word (fun key => (post2.getStor s1.currentTarget).get key)
        (submit (submit st (recordOf s1 hlen1)) (recordOf s2 hlen2)) ∧
      (submit (submit st (recordOf s1 hlen1)) (recordOf s2 hlen2)).queue = st.queue ++ [recordOf s1 hlen1, recordOf s2 hlen2] ∧
      (recordOf s1 hlen1).source = s1.caller ∧ (recordOf s2 hlen2).source = s2.caller ∧
      post2.logs = b.logs ++ [⟨s1.currentTarget, [], s1.caller.toBytes ++ s1.data⟩, ⟨s1.currentTarget, [], s2.caller.toBytes ++ s2.data⟩] ∧
      submissionGasA s1 b .empty 1 ≤ submissions.regularBound 1 + submissions.stateBound ∧
      submissionGasA s2 post1 .empty 1 ≤ submissions.regularBound 1 + submissions.stateBound := by
  have h0 : b.getStorVal s1.currentTarget 0 = 0 := by
    have : (b.getStor s1.currentTarget).get 0 = st.excess.toB256 := rep.excess
    rw [he] at this
    exact this
  have h1 : b.getStorVal s1.currentTarget 1 = 0 := by
    have : (b.getStor s1.currentTarget).get 1 = st.count.toB256 := rep.count
    rw [hc] at this
    exact this
  have fee : ((17 : B256) / (17 : B256)).toNat = 1 := by decide
  have x1 : storedExcess 2 s1 b = 0 := by
    rw [storedExcess, h0, h1]
    decide
  have e1 := exec_submission_amsterdam (b := b) (M := .empty) (G := G1) (finalOutput := 17) hc1 hf1 caller1 hlen1 dyn1 slack1
    (by rw [h0]; decide) (by rw [x1]; exact quote_zero_excess) (by rw [fee]; exact v1)
  have fx1 := submissionPostA_effects (b := b) (M := .empty) hf1 hlen1 Mem.wf_empty (G1 + submissionRepayA s1 b .empty)
  generalize hp1 : submissionPostA s1 (feeBaseA s1 b) .empty (G1 + submissionRepayA s1 b .empty) = post1 at e1 fx1
  have htail : queueBase 3 st.tail + 3 ≤ 2 ^ 256 := by
    simp only [queueBase] at room ⊢
    omega
  have rep1 := represents_submit s1 hlen1 rep htail (by rw [hc]; decide)
  have rep1' : Represents 3 Record.word (fun key => (post1.getStor s2.currentTarget).get key) (submit st (recordOf s1 hlen1)) := by
    rw [same, fx1.storage]
    exact rep1
  have p0 : post1.getStorVal s2.currentTarget 0 = 0 := by
    have : (post1.getStor s2.currentTarget).get 0 = (submit st (recordOf s1 hlen1)).excess.toB256 := rep1'.excess
    rw [show (submit st (recordOf s1 hlen1)).excess = 0 from he] at this
    exact this
  have p1 : post1.getStorVal s2.currentTarget 1 = (1 : Nat).toB256 := by
    have : (post1.getStor s2.currentTarget).get 1 = (submit st (recordOf s1 hlen1)).count.toB256 := rep1'.count
    rw [show (submit st (recordOf s1 hlen1)).count = 1 by show st.count + 1 = 1; omega] at this
    exact this
  have x2 : storedExcess 2 s2 post1 = 0 := by
    rw [storedExcess, p0, p1]
    decide
  have e2 := exec_submission_amsterdam (b := post1) (M := .empty) (G := G2) (finalOutput := 17) hc2 hf2 caller2 hlen2 dyn2 slack2
    (by rw [p0]; decide) (by rw [x2]; exact quote_zero_excess) (by rw [fee]; exact v2)
  have fx2 := submissionPostA_effects (b := post1) (M := .empty) hf2 hlen2 Mem.wf_empty (G2 + submissionRepayA s2 post1 .empty)
  generalize submissionPostA s2 (feeBaseA s2 post1) .empty (G2 + submissionRepayA s2 post1 .empty) = post2 at e2 fx2
  have htail2 : queueBase 3 (st.tail + 1) + 3 ≤ 2 ^ 256 := by
    simp only [queueBase] at room ⊢
    omega
  have rep2 := represents_submit s2 hlen2 rep1' htail2 (by
    show st.count + 1 + 1 < _
    rw [hc]
    decide)
  refine ⟨post1, post2, e1, e2, ?_, ?_, rfl, rfl, ?_, submissions.gas_le_bound s1 b 1, submissions.gas_le_bound s2 post1 1⟩
  · have hs : post2.getStor s1.currentTarget = submittedStorage s2 (post1.getStor s2.currentTarget) := by
      rw [← same]
      exact fx2.storage
    rw [hs]
    exact rep2
  · simp only [submit, List.append_assoc, List.singleton_append]
  · rw [fx2.logs, fx1.logs, same, List.append_assoc]
    rfl

end Blanc.Lift.BuilderRequest.Exit
