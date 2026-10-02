import Blanc.Lift.FloodLooper.Check
import Blanc.Lift.ExactWalkCallChild
import Blanc.Lift.WithdrawalRequest.UserGas
import Blanc.Lift.WithdrawalRequest.NatLiveness
import Blanc.Lift.WithdrawalRequest.CodeFacts
import Blanc.Lift.WithdrawalRequest.SubmissionLayout
import Blanc.Lift.WithdrawalRequest.SystemProtocol
import Blanc.Lift.ExactWalkSolc

/-!
# The flood caller makes exactly `k` committed submissions

The hand-written looper (`Blanc/Lift/FloodLooper`) reads a 32-byte count `k`
and a 56-byte submission payload from its calldata and makes `k` value-1 CALLs
to the withdrawal-request predeploy, each a committed submission at the
unchanged incoming excess.  This module composes the looper's lifted loop with
the predeploy's `exec_submission_fresh` (`Blanc/Lift/WithdrawalRequest/UserGas`)
through the shared child-CALL crossing (`Blanc/Lift/ExactWalkCallChild`) to
show the looper run succeeds and leaves the predeploy storage as the `k`-fold
`submit` image.

The construction is the refutation witness's block-B body: at excess 0 the fee
is 1, so value 1 pays each submission, and `k = 2895` drives the end-of-block
excess to `2893`.
-/

namespace Blanc.Lift.WithdrawalRequest.FloodWalk

open Jaune Blanc.Lift

/-- The looper's runtime bytes. -/
def code : ByteArray := Blanc.Lift.FloodLooper.code

/-- The looper's lifted program. -/
def prog : List SFunc := Blanc.Lift.FloodLooper.cert.prog

theorem prog_root : prog[0]? = some Blanc.Lift.FloodLooper.t_0000_c0 := rfl

theorem prog_head : prog[1]? = some Blanc.Lift.FloodLooper.t_0007_c1 := rfl

/-- The looper's calldata: the 32-byte count word followed by the 56-byte
submission payload. -/
def calldata (k : B256) (payload : Bytes) : Bytes := k.toBytes ++ payload

theorem calldata_length {k : B256} {payload : Bytes} (hp : payload.length = 56) :
    (calldata k payload).length = 88 := by
  simp only [calldata, List.length_append, B256.length_toBytes, hp]

/-- The leftover gas a committed submission leaves the caller, for an incoming
child gas grant `g`. -/
def submissionLeftover (msg : Msg) (iters g : Nat) : Nat :=
  g - userSubmissionGas (initSevm msg) (initDevm msg) Mem.empty iters

/-- A message into the installed withdrawal predeploy, carrying a 56-byte
payload with enough gas and value to pay the incoming word fee, executes a
committed submission: `exec (initEvm msg)` succeeds without error.  Stated so
it discharges the `h_exec` premise of `Ninst.runCompiled_call_nonzero_child`
at `msg = callChildMsg …`. -/
theorem submission_child_exec {msg : Msg} {iters : Nat} {out : B256}
    (hfork : CoveredFork msg.benv.stat.fork)
    (hcode : msg.code = Blanc.withdrawalRequestCode)
    (huser : msg.caller ≠ systemAddress)
    (hlen : msg.data.length = 56)
    (hstatic : msg.isStatic = false)
    (hactive : (initDevm msg).getStorVal msg.currentTarget 0 ≠ B256.max)
    (hrun : WordFakeExponential.Run ((initDevm msg).getStorVal msg.currentTarget 0)
      17 1 17 0 iters out)
    (hpaid : (out / (17 : B256)).toNat ≤ msg.value.toNat)
    (hgas : userSubmissionGas (initSevm msg) (initDevm msg) Mem.empty iters + gCallStipend
      < msg.gas) :
    exec (initEvm msg) =
      .ok (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0) Mem.empty
        (submissionLeftover msg iters msg.gas)) := by
  have hslack : gCallStipend < submissionLeftover msg iters msg.gas := by
    unfold submissionLeftover; omega
  have hfresh := exec_submission_fresh (sevm := initSevm msg) (b := initDevm msg)
    (G := submissionLeftover msg iters msg.gas) (iterations := iters) (finalOutput := out)
    hcode hfork huser hlen hstatic hslack hactive hrun hpaid
  rw [← userSubmissionGas_empty (initSevm msg) (initDevm msg) iters] at hfresh
  have hgasEq : submissionLeftover msg iters msg.gas +
      userSubmissionGas (initSevm msg) (initDevm msg) Mem.empty iters = msg.gas := by
    unfold submissionLeftover; omega
  rw [hgasEq] at hfresh
  have hStEq : St (initDevm msg) [] Mem.empty msg.gas = initDevm msg := by
    have h := St.self (d := initDevm msg) (S := []) (M := Mem.empty) rfl rfl
    rw [initDevm_gasLeft] at h
    exact h.symm
  rw [hStEq] at hfresh
  exact (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) _).mp hfresh

/-! ## What a committed submission leaves of accounts and gas -/

/-- An `SSTORE` keeps every account's code and balance. -/
private theorem afterSstore_code_bal {sevm : Sevm} {b : Devm} {key value : B256} (a : Adr) :
    ((afterSstore sevm b key value).getAcct a).code = (b.getAcct a).code ∧
    ((afterSstore sevm b key value).getAcct a).bal = (b.getAcct a).bal :=
  ⟨afterSstore_getCode sevm b key value a, afterSstore_getBal a⟩

private theorem afterSload_code_bal {sevm : Sevm} {b : Devm} {key : B256} (a : Adr) :
    ((afterSload sevm b key).getAcct a).code = (b.getAcct a).code ∧
    ((afterSload sevm b key).getAcct a).bal = (b.getAcct a).bal := by
  rw [afterSload_getAcct]
  exact ⟨rfl, rfl⟩

/-- A committed submission keeps every account's code and balance. -/
theorem submissionPost_code_bal (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat) (a : Adr) :
    ((submissionPost sevm b M G).getAcct a).code = (b.getAcct a).code ∧
    ((submissionPost sevm b M G).getAcct a).bal = (b.getAcct a).bal := by
  have h5 := afterSstore_code_bal (sevm := sevm) (b := submissionLogged sevm b M)
    (key := 3) (value := 1 + submissionTail sevm b) a
  have h4 := afterSstore_code_bal (sevm := sevm) (b := submissionWord1Store sevm b)
    (key := 1 + (1 + submissionKey sevm b)) (value := Sevm.dataWord sevm 32) a
  have h3 := afterSstore_code_bal (sevm := sevm) (b := submissionCallerStore sevm b)
    (key := 1 + submissionKey sevm b) (value := Sevm.dataWord sevm 0) a
  have h2 := afterSstore_code_bal (sevm := sevm) (b := submissionTailRead sevm b)
    (key := submissionKey sevm b) (value := sevm.caller.toB256) a
  have h1t := afterSload_code_bal (sevm := sevm) (b := submissionCountStore sevm b) (key := 3) a
  have h1 := afterSstore_code_bal (sevm := sevm) (b := submissionCountRead sevm b)
    (key := 1) (value := 1 + submissionCount sevm b) a
  have h0 := afterSload_code_bal (sevm := sevm) (b := b) (key := 1) a
  have hSt : ∀ d : Devm, (St d [] (submissionMemory sevm M) G).getAcct a = d.getAcct a :=
    fun _ => rfl
  rw [submissionPost, hSt]
  unfold submissionBase
  rw [h5.1, h5.2]
  have hLog : ∀ (d : Devm) (l : Log), (d.addLog l).getAcct a = d.getAcct a := fun _ _ => rfl
  unfold submissionLogged
  rw [hLog]
  unfold submissionWordsStore
  rw [h4.1, h4.2]
  unfold submissionWord1Store
  rw [h3.1, h3.2]
  unfold submissionCallerStore
  rw [h2.1, h2.2]
  unfold submissionTailRead
  rw [h1t.1, h1t.2]
  unfold submissionCountStore
  rw [h1.1, h1.2]
  unfold submissionCountRead
  exact h0

/-- The tail word survives the three queue writes when no queue key aliases slot 3. -/
theorem submissionLogged_tail (sevm : Sevm) (b : Devm) (M : Mem) (σ : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage (b.getStor sevm.currentTarget).get σ) (bounds : SubmissionBounds σ) :
    (submissionLogged sevm b M).getStorVal sevm.currentTarget 3 = σ.tail.toB256 := by
  have tail := submissionTail_eq sevm b σ rep
  have key := submissionKey_queueSlot sevm b σ.tail tail
  have offsets := submissionKey_offsets sevm b σ.tail tail
  have avoids : ∀ off, off ≤ 2 → Blanc.WithdrawalRequest.queueSlot σ.tail off ≠ (3 : B256) := fun off hoff =>
    submission_queueSlot_ne_metadata σ.tail off 3
      (Nat.lt_of_le_of_lt (Nat.add_le_add_left hoff _) bounds.tail_slot_lt) (by decide)
  have ne0 : submissionKey sevm b ≠ 3 := by
    rw [key]
    exact avoids 0 (by decide)
  have ne1 : 1 + submissionKey sevm b ≠ 3 := by
    rw [offsets.1]
    exact avoids 1 (by decide)
  have ne2 : 1 + (1 + submissionKey sevm b) ≠ 3 := by
    rw [offsets.2]
    exact avoids 2 (by decide)
  have hLog : ∀ (d : Devm) (l : Log),
      (d.addLog l).getStorVal sevm.currentTarget 3 = (Devm.getStor d sevm.currentTarget).get 3 :=
    fun _ _ => rfl
  unfold submissionLogged
  rw [hLog]
  simp only [submissionWordsStore, submissionWord1Store, submissionCallerStore,
    submissionTailRead, submissionCountStore, submissionCountRead,
    afterSstore_getStor_self, afterSload_getStor]
  rw [Stor.get_set_ne _ ne2, Stor.get_set_ne _ ne1, Stor.get_set_ne _ ne0,
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3)]
  exact rep.tail

/-- The queue slots a submission writes are pairwise distinct and avoid the metadata
slots, in the word arithmetic, under the submission bounds. -/
theorem submissionKey_distinct (sevm : Sevm) (b : Devm)
    (σ : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage (b.getStor sevm.currentTarget).get σ)
    (bounds : SubmissionBounds σ) :
    submissionKey sevm b ≠ 1 ∧ 1 + submissionKey sevm b ≠ 1 ∧
    1 + (1 + submissionKey sevm b) ≠ 1 ∧
    1 + submissionKey sevm b ≠ submissionKey sevm b ∧
    1 + (1 + submissionKey sevm b) ≠ submissionKey sevm b ∧
    1 + (1 + submissionKey sevm b) ≠ 1 + submissionKey sevm b := by
  have tail := submissionTail_eq sevm b σ rep
  have key := submissionKey_queueSlot sevm b σ.tail tail
  have offsets := submissionKey_offsets sevm b σ.tail tail
  have inWord : ∀ off, off ≤ 2 → Blanc.WithdrawalRequest.queueBase σ.tail + off < 2 ^ 256 :=
    fun off hoff => Nat.lt_of_le_of_lt (Nat.add_le_add_left hoff _) bounds.tail_slot_lt
  have metaNe : ∀ off, off ≤ 2 →
      Blanc.WithdrawalRequest.queueSlot σ.tail off ≠ (1 : B256) := fun off hoff =>
    submission_queueSlot_ne_metadata σ.tail off 1 (inWord off hoff) (by decide)
  have slots : ∀ a c, a ≤ 2 → c ≤ 2 → a ≠ c →
      Blanc.WithdrawalRequest.queueSlot σ.tail a ≠ Blanc.WithdrawalRequest.queueSlot σ.tail c := by
    intro a c ha hc hac eq
    have values := congrArg B256.toNat eq
    rw [submission_queueSlot_toNat σ.tail a (inWord a ha),
      submission_queueSlot_toNat σ.tail c (inWord c hc)] at values
    exact hac (Nat.add_left_cancel values)
  rw [offsets.2, offsets.1, key]
  exact ⟨metaNe 0 (by decide), metaNe 1 (by decide), metaNe 2 (by decide),
    slots 1 0 (by decide) (by decide) (by decide), slots 2 0 (by decide) (by decide) (by decide),
    slots 2 1 (by decide) (by decide) (by decide)⟩

/-- A committed submission never lowers the refund counter when none of its five stores
can take the clearing-reversal branch: each store's transaction-original value equals the
value it finds (`RefundSafe`), is zero, or the value it finds is nonzero.  The metadata
stores find the represented count and tail; the queue stores find the incoming values. -/
theorem submissionPost_refund_ge_of_safe (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat)
    (σ : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage (b.getStor sevm.currentTarget).get σ)
    (bounds : SubmissionBounds σ)
    (safe1 : RefundSafe (getOrigStorVal sevm sevm.currentTarget 1) σ.count.toB256)
    (safe3 : RefundSafe (getOrigStorVal sevm sevm.currentTarget 3) σ.tail.toB256)
    (safeQ : ∀ key, key = submissionKey sevm b ∨ key = 1 + submissionKey sevm b ∨
      key = 1 + (1 + submissionKey sevm b) →
      RefundSafe (getOrigStorVal sevm sevm.currentTarget key) (b.getStorVal sevm.currentTarget key)) :
    b.refundCounter ≤ (submissionPost sevm b M G).refundCounter := by
  obtain ⟨k1, k1', k1'', kk, kk2, kk3⟩ := submissionKey_distinct sevm b σ rep bounds
  -- the value of an untouched slot after a store at another key
  have keep : ∀ (d : Devm) (w x v : B256), w ≠ v →
      (afterSstore sevm d w x).getStorVal sevm.currentTarget v =
        d.getStorVal sevm.currentTarget v := by
    intro d w x v hne
    rw [getStorVal_eq_getStor, afterSstore_getStor_self, Stor.get_set_ne _ hne,
      ← getStorVal_eq_getStor]
  have hLog : ∀ (d : Devm) (l : Log), (d.addLog l).refundCounter = d.refundCounter :=
    fun _ _ => rfl
  have hSt : ∀ d : Devm, (St d [] (submissionMemory sevm M) G).refundCounter = d.refundCounter :=
    fun _ => rfl
  -- stage 1: the count store at slot 1
  have o1 : RefundSafe (getOrigStorVal sevm sevm.currentTarget 1)
      ((submissionCountRead sevm b).getStorVal sevm.currentTarget 1) := by
    rw [submissionCountRead, getStorVal_afterSload, getStorVal_eq_getStor, rep.count]
    exact safe1
  have r1 : (submissionCountRead sevm b).refundCounter ≤
      (submissionCountStore sevm b).refundCounter :=
    afterSstore_refundCounter_ge_of_safe sevm (submissionCountRead sevm b)
      1 (1 + submissionCount sevm b) o1
  -- stage 2: the caller word at `key`
  have o2 : RefundSafe (getOrigStorVal sevm sevm.currentTarget (submissionKey sevm b))
      ((submissionTailRead sevm b).getStorVal sevm.currentTarget (submissionKey sevm b)) := by
    rw [submissionTailRead, getStorVal_afterSload, submissionCountStore, keep _ _ _ _ k1.symm,
      submissionCountRead, getStorVal_afterSload]
    exact safeQ _ (Or.inl rfl)
  have r2 : (submissionTailRead sevm b).refundCounter ≤
      (submissionCallerStore sevm b).refundCounter :=
    afterSstore_refundCounter_ge_of_safe sevm (submissionTailRead sevm b)
      (submissionKey sevm b) sevm.caller.toB256 o2
  -- stage 3: the first payload word at `key + 1`
  have o3 : RefundSafe (getOrigStorVal sevm sevm.currentTarget (1 + submissionKey sevm b))
      ((submissionCallerStore sevm b).getStorVal sevm.currentTarget (1 + submissionKey sevm b)) := by
    rw [submissionCallerStore, keep _ _ _ _ kk.symm, submissionTailRead, getStorVal_afterSload,
      submissionCountStore, keep _ _ _ _ k1'.symm, submissionCountRead, getStorVal_afterSload]
    exact safeQ _ (Or.inr (Or.inl rfl))
  have r3 : (submissionCallerStore sevm b).refundCounter ≤
      (submissionWord1Store sevm b).refundCounter :=
    afterSstore_refundCounter_ge_of_safe sevm (submissionCallerStore sevm b)
      (1 + submissionKey sevm b) (Sevm.dataWord sevm 0) o3
  -- stage 4: the second payload word at `key + 2`
  have o4 : RefundSafe (getOrigStorVal sevm sevm.currentTarget (1 + (1 + submissionKey sevm b)))
      ((submissionWord1Store sevm b).getStorVal sevm.currentTarget
        (1 + (1 + submissionKey sevm b))) := by
    rw [submissionWord1Store, keep _ _ _ _ kk3.symm, submissionCallerStore, keep _ _ _ _ kk2.symm,
      submissionTailRead, getStorVal_afterSload, submissionCountStore, keep _ _ _ _ k1''.symm,
      submissionCountRead, getStorVal_afterSload]
    exact safeQ _ (Or.inr (Or.inr rfl))
  have r4 : (submissionWord1Store sevm b).refundCounter ≤
      (submissionWordsStore sevm b).refundCounter :=
    afterSstore_refundCounter_ge_of_safe sevm (submissionWord1Store sevm b)
      (1 + (1 + submissionKey sevm b)) (Sevm.dataWord sevm 32) o4
  -- stage 5: the tail store at slot 3, whose current value is the represented tail
  have o5 : RefundSafe (getOrigStorVal sevm sevm.currentTarget 3)
      ((submissionLogged sevm b M).getStorVal sevm.currentTarget 3) := by
    rw [submissionLogged_tail sevm b M σ rep bounds]
    exact safe3
  have r5 : (submissionLogged sevm b M).refundCounter ≤
      (submissionBase sevm b M).refundCounter :=
    afterSstore_refundCounter_ge_of_safe sevm (submissionLogged sevm b M)
      3 (1 + submissionTail sevm b) o5
  -- assemble: reads, the log, and `St` keep the counter
  have e1 : b.refundCounter = (submissionCountRead sevm b).refundCounter := by
    rw [submissionCountRead, afterSload_refundCounter]
  have e3 : (submissionCountStore sevm b).refundCounter =
      (submissionTailRead sevm b).refundCounter := by
    rw [submissionTailRead, afterSload_refundCounter]
  have e5 : (submissionWordsStore sevm b).refundCounter =
      (submissionLogged sevm b M).refundCounter := by
    rw [submissionLogged, hLog]
  have e6 : (submissionPost sevm b M G).refundCounter = (submissionBase sevm b M).refundCounter := by
    rw [submissionPost, hSt]
  rw [e6, e1]
  refine r1.trans ?_
  rw [e3]
  refine r2.trans (r3.trans (r4.trans ?_))
  rw [e5]
  exact r5

/-- The closed charge of one fresh submission at one fee-loop iteration, bounded with every
read and the three queue stores taken cold and fresh; the two metadata stores keep their
value charges, which fall to the warm charge once the slot is dirty. -/
theorem userSubmissionGas_le (sevm : Sevm) (b : Devm) (σ : Blanc.WithdrawalRequest.State)
    (rep : Blanc.WithdrawalRequest.RepresentsStorage (b.getStor sevm.currentTarget).get σ) (bounds : SubmissionBounds σ) :
    userSubmissionGas sevm b Mem.empty 1 ≤ 78145 +
      sstoreValueCost (getOrigStorVal sevm sevm.currentTarget 1) σ.count.toB256
        (1 + σ.count.toB256) +
      sstoreValueCost (getOrigStorVal sevm sevm.currentTarget 3) σ.tail.toB256
        (1 + σ.tail.toB256) := by
  have rep0 : Blanc.WithdrawalRequest.RepresentsStorage ((afterSload sevm b 0).getStor sevm.currentTarget).get σ := by
    rw [afterSload_getStor]
    exact rep
  have reads := sloadScheduleCost_le sevm (userSubmissionReads sevm b)
  have readsLen : (userSubmissionReads sevm b).length = 3 := rfl
  rw [readsLen] at reads
  have count : submissionCount sevm (afterSload sevm b 0) = σ.count.toB256 := rep0.count
  have countCur : (submissionCountRead sevm (afterSload sevm b 0)).getStorVal
      sevm.currentTarget 1 = σ.count.toB256 := by
    change (Devm.getStor (afterSload sevm (afterSload sevm b 0) 1) sevm.currentTarget).get 1 = _
    rw [afterSload_getStor]
    exact rep0.count
  have tail := submissionTail_eq sevm (afterSload sevm b 0) σ rep0
  have tailCur := submissionLogged_tail sevm (afterSload sevm b 0) Mem.empty σ rep0 bounds
  have s1 := sstoreCost_le_value sevm (submissionCountRead sevm (afterSload sevm b 0)) 1
    (1 + submissionCount sevm (afterSload sevm b 0))
  have s2 := sstoreCost_le_value sevm (submissionTailRead sevm (afterSload sevm b 0))
    (submissionKey sevm (afterSload sevm b 0)) sevm.caller.toB256
  have s3 := sstoreCost_le_value sevm (submissionCallerStore sevm (afterSload sevm b 0))
    (1 + submissionKey sevm (afterSload sevm b 0)) (Sevm.dataWord sevm 0)
  have s4 := sstoreCost_le_value sevm (submissionWord1Store sevm (afterSload sevm b 0))
    (1 + (1 + submissionKey sevm (afterSload sevm b 0))) (Sevm.dataWord sevm 32)
  have s5 := sstoreCost_le_value sevm (submissionLogged sevm (afterSload sevm b 0) Mem.empty) 3
    (1 + submissionTail sevm (afterSload sevm b 0))
  rw [countCur, count] at s1
  rw [tailCur, tail] at s5
  have v2 := sstoreValueCost_le (getOrigStorVal sevm sevm.currentTarget
    (submissionKey sevm (afterSload sevm b 0)))
    ((submissionTailRead sevm (afterSload sevm b 0)).getStorVal sevm.currentTarget
      (submissionKey sevm (afterSload sevm b 0))) sevm.caller.toB256
  have v3 := sstoreValueCost_le (getOrigStorVal sevm sevm.currentTarget
    (1 + submissionKey sevm (afterSload sevm b 0)))
    ((submissionCallerStore sevm (afterSload sevm b 0)).getStorVal sevm.currentTarget
      (1 + submissionKey sevm (afterSload sevm b 0))) (Sevm.dataWord sevm 0)
  have v4 := sstoreValueCost_le (getOrigStorVal sevm sevm.currentTarget
    (1 + (1 + submissionKey sevm (afterSload sevm b 0))))
    ((submissionWord1Store sevm (afterSload sevm b 0)).getStorVal sevm.currentTarget
      (1 + (1 + submissionKey sevm (afterSload sevm b 0)))) (Sevm.dataWord sevm 32)
  rw [userSubmissionGas_empty]
  unfold submissionStoreGas
  rw [count, tail]
  simp only [gasColdSload, gasStorageSet] at reads s1 s2 s3 s4 s5 v2 v3 v4
  omega

/-! ## The looper's calldata, memory and per-call constants -/

/-- The looper's memory after its one `CALLDATACOPY`: the payload at offset 0. -/
def payloadMem (payload : Bytes) : Mem := Mem.empty.write 0 payload

theorem payloadMem_size {payload : Bytes} (h : payload.length = 56) :
    (payloadMem payload).size = 64 := by
  rw [payloadMem, Mem.size_write_of_size rfl (by decide) h]
  rfl

theorem payloadMem_read {payload : Bytes} (h : payload.length = 56) :
    ((payloadMem payload).read 0 56).1 = payload := by
  rw [payloadMem, Mem.Reads.read (Mem.reads_empty.write Mem.wf_empty 0 payload)]
  simp only [Bytes.writeAt, List.takeD, List.nil_append, List.drop_nil, List.append_nil,
    List.sliceD, List.drop_zero]
  exact List.takeD_eq_self 0 h.symm

theorem calldata_word {k : B256} {payload : Bytes} :
    Bytes.toB256 ((calldata k payload).sliceD 0 32 0) = k := by
  simp only [calldata, List.sliceD, List.drop_zero]
  rw [List.takeD_eq_take _ (by simp only [List.length_append, B256.length_toBytes]; omega),
    List.take_length_append' (B256.length_toBytes k).symm, B256.toB256_toBytes]

theorem calldata_payload {k : B256} {payload : Bytes} (h : payload.length = 56) :
    (calldata k payload).sliceD 32 56 0 = payload := by
  simp only [calldata, List.sliceD]
  rw [List.drop_length_append' (B256.length_toBytes k).symm]
  exact List.takeD_eq_self 0 h.symm

/-- At incoming excess zero the word fee loop runs once and returns 17 (fee 1). -/
theorem wordRun_zero : WordFakeExponential.Run 0 17 1 17 0 1 17 := by
  refine WordFakeExponential.Run.step (by decide) ?_
  have hacc : WordFakeExponential.nextAccumulator 0 17 1 17 = 0 := by decide
  rw [hacc, show (0 : B256) + 17 = 17 by decide]
  exact WordFakeExponential.Run.stop _ _


/-! ## One looper `CALL`: a committed submission paying 1 -/

/-- The two metadata value charges of the `i`-th looper submission, read against the
transaction's original predeploy storage. -/
def metaValueGas (sevm : Sevm) (σ : Blanc.WithdrawalRequest.State) : Nat :=
  sstoreValueCost (getOrigStorVal sevm withdrawalRequestPredeployAddress 1) σ.count.toB256
      (1 + σ.count.toB256) +
    sstoreValueCost (getOrigStorVal sevm withdrawalRequestPredeployAddress 3) σ.tail.toB256
      (1 + σ.tail.toB256)

/-- Word constants of one looper call, each decided once. -/
private theorem flood_consts :
    (1 : B256) ≠ 0 ∧ (0 : B256) ≠ B256.max ∧ ((17 : B256) / 17).toNat ≤ (1 : B256).toNat ∧
    (0 : B256).toNat = 0 ∧ (56 : B256).toNat = 56 ∧ (1 : B256).toNat = 1 ∧
    memExtsSize 64 [(0, 56), (0, 0)] = 64 := by
  refine ⟨by decide, by decide, by decide, rfl, rfl, rfl, by decide⟩

/-- The caller's gas around one looper `CALL`. -/
private theorem call_gas_arith {Gc a fwd U m : Nat} (ha : a ≤ 2600)
    (hf : fwd ≤ Gc - (a + 0 + gasCallValue)) (hU : U ≤ 78145 + m)
    (hm : m ≤ 40000) (hfwd : 232600 ≤ fwd) :
    Gc - (fwd + (a + 0 + gasCallValue) + 0) + (fwd + gCallStipend - U) ≤ Gc ∧
    Gc ≤ Gc - (fwd + (a + 0 + gasCallValue) + 0) + (fwd + gCallStipend - U) + 87445 + m := by
  simp only [gasCallValue, gCallStipend] at hf ⊢
  omega

/-- **The looper's `CALL`.**  With the whole remaining gas pushed, value 1, the payload window
`[0, 56)` and an empty output window, the call into the installed predeploy at incoming excess
zero is a committed submission: the caller resumes with success pushed, its memory unchanged,
the predeploy storage representing `submit σ entry`, one wei moved and one submission log
appended.  The caller pays at most the fixed `CALL` charge less the stipend plus the child's
closed submission charge. -/
theorem flood_call {sevm : Sevm} {base : Devm} {S : List B256} {Gc : Nat} {cw : B256}
    {σ : Blanc.WithdrawalRequest.State} {entry : Blanc.WithdrawalRequest.Entry}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0) (hcaller : entry.caller = sevm.currentTarget)
    (huser : sevm.currentTarget ≠ systemAddress)
    (hself : sevm.currentTarget ≠ withdrawalRequestPredeployAddress)
    (hcw : cw.toAdr = withdrawalRequestPredeployAddress)
    (hcode : base.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (base.getStor withdrawalRequestPredeployAddress).get σ)
    (hexcess : σ.excess = 0) (hbounds : SubmissionBounds σ)
    (hsafe1 : RefundSafe (getOrigStorVal sevm withdrawalRequestPredeployAddress 1)
      σ.count.toB256)
    (hsafe3 : RefundSafe (getOrigStorVal sevm withdrawalRequestPredeployAddress 3)
      σ.tail.toB256)
    (hqueue : ∀ o, o ≤ 2 → getOrigStorVal sevm withdrawalRequestPredeployAddress
      (Blanc.WithdrawalRequest.queueSlot σ.tail o) = 0)
    (hbal : 1 ≤ (base.getBal sevm.currentTarget).toNat)
    (hroom : S.length < 1024) (hGlt : Gc < 2 ^ 256) (hG : 247892 ≤ Gc) :
    ∃ post G',
      Ninst.RunCompiled sevm
        (St base (Nat.toB256 Gc :: cw :: 1 :: 0 :: 56 :: 0 :: 0 :: S)
          (payloadMem (Blanc.WithdrawalRequest.submissionPayload entry)) Gc) (.exec .call)
        (St post (1 :: S) (payloadMem (Blanc.WithdrawalRequest.submissionPayload entry)) G') ∧
      G' ≤ Gc ∧ Gc ≤ G' + 87445 + metaValueGas sevm σ ∧
      post.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode ∧
      Blanc.WithdrawalRequest.RepresentsStorage
        (post.getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.submit σ entry) ∧
      (post.getBal sevm.currentTarget).toNat + 1 = (base.getBal sevm.currentTarget).toNat ∧
      post.error = base.error ∧
      post.logs = base.logs ++ [⟨withdrawalRequestPredeployAddress, [],
        Blanc.WithdrawalRequest.submissionLog entry⟩] ∧
      base.refundCounter ≤ post.refundCounter := by
  have hplen := Blanc.WithdrawalRequest.submissionPayload_length entry
  have hMsize := payloadMem_size hplen
  generalize hMp : payloadMem (Blanc.WithdrawalRequest.submissionPayload entry) = Mp at hMsize ⊢
  have hroom' : S.length < 1024 := hroom
  -- the parent after popping, and after warming the callee
  have hd1code : (addAccessedAddress (St base S Mp Gc) cw.toAdr).state.getCode cw.toAdr =
      Blanc.withdrawalRequestCode := by
    rw [hcw]
    exact hcode
  have hdel : accessDelegation (addAccessedAddress (St base S Mp Gc) cw.toAdr) cw.toAdr =
      ⟨false, cw.toAdr, Blanc.withdrawalRequestCode, 0,
        addAccessedAddress (St base S Mp Gc) cw.toAdr⟩ := by
    unfold accessDelegation
    simp only [hd1code, withdrawalRequestCode_nondelegated]
  have hnonempty : ¬ ((addAccessedAddress (St base S Mp Gc) cw.toAdr).getAcct cw.toAdr).Empty := by
    intro hE
    have hsz := hE.1
    change ((addAccessedAddress (St base S Mp Gc) cw.toAdr).state.getCode cw.toAdr).size = 0 at hsz
    rw [hd1code, withdrawalRequestCode_size] at hsz
    exact absurd hsz (by decide)
  have hacc : accessCost cw.toAdr base.accessedAddresses ≤ 2600 := by
    unfold accessCost
    split <;> decide
  have hext : (St base S Mp Gc).extCost [⟨(0 : B256).toNat, (56 : B256).toNat⟩,
      ⟨(0 : B256).toNat, (0 : B256).toNat⟩] = 0 := by
    have h0 : (0 : B256).toNat = 0 := rfl
    have h56 : (56 : B256).toNat = 56 := rfl
    simp only [Devm.extCost, St, Devm.memory_setMach, memExtsSize, h0, h56, hMsize]
    rfl
  have hgw : (Nat.toB256 Gc).toNat = Gc := B256.toNat_toB256_of_lt hGlt
  have hsplit := calculateMsgCallGas_all (value := (1 : B256).toNat) (gas := (Nat.toB256 Gc).toNat)
    (gl := Gc) (extra := accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue)
    (by decide) (by rw [hgw]) (by simp only [gasCallValue]; omega)
  -- the value moves out of the looper
  have hstate1 : (addAccessedAddress (St base S Mp Gc) cw.toAdr).state = base.state := rfl
  have hbalLt : ¬ base.state.bal sevm.currentTarget < 1 := by
    rw [B256.lt_iff_toNat_lt_toNat]
    change ¬ (base.getBal sevm.currentTarget).toNat < (1 : B256).toNat
    have h1 : (1 : B256).toNat = 1 := rfl
    omega
  have hsub : (addAccessedAddress (St base S Mp Gc) cw.toAdr).state.subBal sevm.currentTarget 1 =
      some (base.state.setBal sevm.currentTarget (base.state.bal sevm.currentTarget - 1)) := by
    rw [hstate1]
    unfold State.subBal
    simp only [hbalLt, ite_false]
  -- the child message and its facts
  have hdata : Mp.data.sliceD 0 56 0 = Blanc.WithdrawalRequest.submissionPayload entry := by
    rw [← hMp]
    exact payloadMem_read hplen
  generalize hstmid : base.state.setBal sevm.currentTarget
    (base.state.bal sevm.currentTarget - 1) = stmid at hsub
  generalize hfwd : except64th (Gc - (accessCost cw.toAdr base.accessedAddresses + 0 +
    gasCallValue)) = fwd at hsplit
  generalize hmsg : callChildMsg sevm
    (callSpawnParent (addAccessedAddress (St base S Mp Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) + 0)
      (0 : B256).toNat (56 : B256).toNat (0 : B256).toNat (0 : B256).toNat)
    (fwd + gCallStipend) 1 cw.toAdr cw.toAdr (0 : B256).toNat (56 : B256).toNat
    Blanc.withdrawalRequestCode false stmid = msg
  have mfork : CoveredFork msg.benv.stat.fork := by rw [← hmsg]; exact hfork
  have mcode : msg.code = Blanc.withdrawalRequestCode := by rw [← hmsg]; rfl
  have mcaller : msg.caller = sevm.currentTarget := by rw [← hmsg]; rfl
  have mtarget : msg.currentTarget = withdrawalRequestPredeployAddress := by rw [← hmsg]; exact hcw
  have mdata : msg.data = Blanc.WithdrawalRequest.submissionPayload entry := by
    rw [← hmsg]; exact hdata
  have mstatic : msg.isStatic = false := by
    rw [← hmsg]
    show (false || sevm.isStatic) = false
    rw [hstatic]; rfl
  have mvalue : msg.value = 1 := by rw [← hmsg]; rfl
  have mgas : msg.gas = fwd + gCallStipend := by rw [← hmsg]; rfl
  have mstat : msg.benv.stat = sevm.benvStat := by rw [← hmsg]; rfl
  have mstor : (initDevm msg).getStor withdrawalRequestPredeployAddress =
      base.getStor withdrawalRequestPredeployAddress := by
    rw [← hmsg]
    exact getStor_subBal_addBal hsub
  have rep' : Blanc.WithdrawalRequest.RepresentsStorage
      ((initDevm msg).getStor (initSevm msg).currentTarget).get σ := by
    change Blanc.WithdrawalRequest.RepresentsStorage
      ((initDevm msg).getStor msg.currentTarget).get σ
    rw [mtarget, mstor]
    exact hrep
  have mexcess : (initDevm msg).getStorVal msg.currentTarget 0 = 0 := by
    change ((initDevm msg).getStor (initSevm msg).currentTarget).get 0 = 0
    rw [rep'.excess, hexcess]
    rfl
  have mvc : metaValueGas sevm σ ≤ 40000 := by
    have a := sstoreValueCost_le (getOrigStorVal sevm withdrawalRequestPredeployAddress 1)
      σ.count.toB256 (1 + σ.count.toB256)
    have b := sstoreValueCost_le (getOrigStorVal sevm withdrawalRequestPredeployAddress 3)
      σ.tail.toB256 (1 + σ.tail.toB256)
    unfold metaValueGas
    simp only [gasStorageSet] at a b
    omega
  have muser := userSubmissionGas_le (initSevm msg) (initDevm msg) σ rep' hbounds
  have morig : ∀ key, getOrigStorVal (initSevm msg) (initSevm msg).currentTarget key =
      getOrigStorVal sevm withdrawalRequestPredeployAddress key := by
    intro key
    change getOrigStorVal (initSevm msg) msg.currentTarget key = _
    rw [mtarget]
    unfold getOrigStorVal getOrigAcct
    change (msg.benv.stat.origState.get _).stor.get key = _
    rw [mstat]
  rw [morig 1, morig 3] at muser
  have hfwdge : 232600 ≤ fwd := by
    rw [← hfwd]
    unfold except64th
    simp only [gasCallValue]
    omega
  have hexec := submission_child_exec (msg := msg) (iters := 1) (out := 17) mfork mcode
    (by rw [mcaller]; exact huser) (by rw [mdata]; exact hplen) mstatic
    (by rw [mexcess]; exact flood_consts.2.1) (by rw [mexcess]; exact wordRun_zero)
    (by rw [mvalue]; exact flood_consts.2.2.1)
    (by
      rw [mgas]
      unfold metaValueGas at mvc
      simp only [gCallStipend]
      omega)
  generalize hU : userSubmissionGas (initSevm msg) (initDevm msg) Mem.empty 1 = U at muser
  have hleft : submissionLeftover msg 1 msg.gas = fwd + gCallStipend - U := by
    rw [submissionLeftover, hU, mgas]
  rw [hleft] at hexec
  have herror : (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
      Mem.empty (fwd + gCallStipend - U)).error = none := by
    rw [show (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
        Mem.empty (fwd + gCallStipend - U)).error =
        (submissionBase (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
          Mem.empty).error from
      congrArg Meta.error (submissionPost_facts _ _ _ _).2.1,
      (submissionBase_inherited _ _ _).2, afterSload_error]
    rfl
  have hprec : sevm.benvStat.rules.isPrecomp cw.toAdr = false := by
    have h := withdrawalRequest_not_precompile hfork
    rw [hcw]
    exact propext (iff_of_false h (by decide))
  have run := Ninst.runCompiled_call_nonzero_child
    (devm := St base (Nat.toB256 Gc :: cw :: 1 :: 0 :: 56 :: 0 :: 0 :: S) Mp Gc)
    (gw := Nat.toB256 Gc) (cw := cw) (vw := 1) (iiw := 0) (isw := 56) (oiw := 0) (osw := 0)
    (s := S) (dp := false) (dadr := cw.toAdr) (code := Blanc.withdrawalRequestCode) (dgc := 0)
    (d1 := addAccessedAddress (St base S Mp Gc) cw.toAdr) (ext := 0)
    (acc := accessCost cw.toAdr base.accessedAddresses + 0) (create := 0)
    (mcc := fwd + (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue))
    (mcs := fwd + gCallStipend) (stmid := stmid)
    (cpost := submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0) Mem.empty
      (fwd + gCallStipend - U)) hfork rfl flood_consts.1 hext hdel rfl
    (by simp only [hnonempty, not_false_eq_true, ite_true]) hsplit ?gas hstatic hbalLt hdepth hprec hroom hsub ?exec ?err
  case gas =>
    have : fwd ≤ Gc - (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) := by
      rw [← hfwd]; unfold except64th; omega
    have hle : accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue ≤ Gc := by
      simp only [gasCallValue]; omega
    change fwd + (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) + 0 ≤ Gc
    rw [Nat.add_zero]
    exact (Nat.le_sub_iff_add_le hle).mp this
  case exec =>
    subst hmsg
    exact hexec
  case err => exact herror
  -- what the child left
  have cfacts := submissionPost_facts (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
    Mem.empty (fwd + gCallStipend - U)
  have cout : (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
      Mem.empty (fwd + gCallStipend - U)).output = [] := by
    rw [show (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
        Mem.empty (fwd + gCallStipend - U)).output =
        (submissionBase (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
          Mem.empty).output from congrArg Meta.output cfacts.2.1,
      (submissionBase_inherited _ _ _).1, afterSload_output]
    rfl
  have ccaller : entry.caller = (initSevm msg).caller := by rw [hcaller]; exact mcaller.symm
  have cpayload : (initSevm msg).data = Blanc.WithdrawalRequest.submissionPayload entry := mdata
  have crep := submissionPost_represents (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
    Mem.empty (fwd + gCallStipend - U) σ entry (by rw [afterSload_getStor]; exact rep')
    hbounds ccaller cpayload
  have clogs : (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
      Mem.empty (fwd + gCallStipend - U)).logs =
      [⟨withdrawalRequestPredeployAddress, [], Blanc.WithdrawalRequest.submissionLog entry⟩] := by
    have hlog0 : (initDevm msg).logs = [] := by
      change (match msg.benv.stat.rules.stateGas with
        | none => []
        | some _ => _) = []
      rw [mstat, CoveredFork.rules_stateGas_none hfork]
    rw [show (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
        Mem.empty (fwd + gCallStipend - U)).logs =
        (submissionBase (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
          Mem.empty).logs from congrArg Meta.logs cfacts.2.1,
      submissionBase_logs, afterSload_logs, hlog0, List.nil_append,
      submissionLog_eq (initSevm msg) Mem.empty Mem.wf_empty entry ccaller cpayload]
    change [(⟨msg.currentTarget, [], Blanc.WithdrawalRequest.submissionLog entry⟩ : Log)] = _
    rw [mtarget]
  have cacct := fun a => submissionPost_code_bal (initSevm msg)
    (afterSload (initSevm msg) (initDevm msg) 0) Mem.empty (fwd + gCallStipend - U) a
  have crefund : 0 ≤ (submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
      Mem.empty (fwd + gCallStipend - U)).refundCounter := by
    have rep0 : Blanc.WithdrawalRequest.RepresentsStorage
        ((afterSload (initSevm msg) (initDevm msg) 0).getStor (initSevm msg).currentTarget).get σ := by
      rw [afterSload_getStor]; exact rep'
    have tail0 := submissionTail_eq (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0) σ rep0
    have key0 := submissionKey_queueSlot (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
      σ.tail tail0
    have offs := submissionKey_offsets (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
      σ.tail tail0
    have morigT : ∀ key, getOrigStorVal (initSevm msg) (initSevm msg).currentTarget key =
        getOrigStorVal sevm withdrawalRequestPredeployAddress key := morig
    have h := submissionPost_refund_ge_of_safe (initSevm msg)
      (afterSload (initSevm msg) (initDevm msg) 0) Mem.empty (fwd + gCallStipend - U) σ rep0 hbounds
      (by rw [morigT]; exact hsafe1) (by rw [morigT]; exact hsafe3) (by
        intro key hkey
        right; left
        rw [morigT]
        rcases hkey with rfl | rfl | rfl
        · rw [key0]; exact hqueue 0 (by decide)
        · rw [offs.1]; exact hqueue 1 (by decide)
        · rw [offs.2]; exact hqueue 2 (by decide))
    have h0 : (afterSload (initSevm msg) (initDevm msg) 0).refundCounter = 0 := by
      rw [afterSload_refundCounter]; rfl
    rw [h0] at h
    exact h
  generalize hcp : submissionPost (initSevm msg) (afterSload (initSevm msg) (initDevm msg) 0)
    Mem.empty (fwd + gCallStipend - U) = cpost at run cout crep clogs cacct cfacts crefund
  -- the world the child started from
  have hinit : ∀ a, (initDevm msg).getAcct a = (stmid.addBal cw.toAdr 1).get a := by
    intro a
    rw [← hmsg]
    rfl
  have codeP : (cpost.getAcct withdrawalRequestPredeployAddress).code =
      Blanc.withdrawalRequestCode := by
    rw [(cacct _).1, (afterSload_code_bal _).1, hinit, ← hcw]
    change (stmid.addBal cw.toAdr 1).getCode cw.toAdr = _
    rw [State.addBal_getCode, ← hstmid, State.setBal_getCode]
    exact hd1code
  have balL : ((cpost.getAcct sevm.currentTarget).bal).toNat + 1 =
      (base.getBal sevm.currentTarget).toNat := by
    rw [(cacct _).2, (afterSload_code_bal _).2, hinit]
    have hne : cw.toAdr ≠ sevm.currentTarget := by rw [hcw]; exact hself.symm
    change ((stmid.setBal cw.toAdr (stmid.bal cw.toAdr + 1)).get sevm.currentTarget).bal.toNat + 1 = _
    rw [State.setBal_get_ne hne, ← hstmid, State.setBal_get_self]
    change (base.state.bal sevm.currentTarget - 1).toNat + 1 = (base.state.bal sevm.currentTarget).toNat
    have hle : (1 : B256) ≤ base.state.bal sevm.currentTarget :=
      B256.not_lt.mp hbalLt
    rw [B256.toNat_sub_eq_of_le _ _ hle]
    have h1 : (1 : B256).toNat = 1 := rfl
    rw [h1]
    change 1 ≤ (base.getBal sevm.currentTarget).toNat at hbal
    change 1 ≤ (base.state.bal sevm.currentTarget).toNat at hbal
    omega
  -- the parent the call resumes
  have pmem : (callSpawnParent (addAccessedAddress (St base S Mp Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) + 0)
      (0 : B256).toNat (56 : B256).toNat (0 : B256).toNat (0 : B256).toNat).memory = Mp := by
    change Mp.extends [((0 : B256).toNat, (56 : B256).toNat), ((0 : B256).toNat, (0 : B256).toNat)]
      = Mp
    have h0 : (0 : B256).toNat = 0 := rfl
    have h56 : (56 : B256).toNat = 56 := rfl
    have hz := flood_consts.2.2.2.2.2.2
    rcases Mp with ⟨data, size⟩
    change size = 64 at hMsize
    subst hMsize
    simp only [Mem.extends, h0, h56, hz]
  have pfacts := callChildPost_facts (callSpawnParent (addAccessedAddress (St base S Mp Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) + 0)
      (0 : B256).toNat (56 : B256).toNat (0 : B256).toNat (0 : B256).toNat) cpost
    (0 : B256).toNat (0 : B256).toNat cout
  generalize hpost : callChildPost (callSpawnParent (addAccessedAddress (St base S Mp Gc) cw.toAdr)
      (fwd + (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) + 0)
      (0 : B256).toNat (56 : B256).toNat (0 : B256).toNat (0 : B256).toNat) cpost
    (0 : B256).toNat (0 : B256).toNat = post at run pfacts
  obtain ⟨pstack, pmem', pgas, pstate, -, plogs, prefund, perr, -⟩ := pfacts
  rw [pmem] at pmem'
  have pstack' : post.stack = 1 :: S := pstack
  have hSt := St.self pstack' pmem'
  have hd1gas : (addAccessedAddress (St base S Mp Gc) cw.toAdr).gasLeft = Gc := rfl
  refine ⟨post, post.gasLeft, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hSt]; exact run
  · have hf : fwd ≤ Gc - (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) := by
      rw [← hfwd]; unfold except64th; omega
    have hU : U ≤ 78145 + metaValueGas sevm σ := by unfold metaValueGas; omega
    rw [pgas, callSpawnParent_gasLeft, hd1gas, cfacts.2.2.2.2.1]
    exact (call_gas_arith hacc hf hU mvc hfwdge).1
  · have hf : fwd ≤ Gc - (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) := by
      rw [← hfwd]; unfold except64th; omega
    have hU : U ≤ 78145 + metaValueGas sevm σ := by unfold metaValueGas; omega
    rw [pgas, callSpawnParent_gasLeft, hd1gas, cfacts.2.2.2.2.1]
    exact (call_gas_arith hacc hf hU mvc hfwdge).2
  · change (post.state.get _).code = _
    rw [pstate]
    exact codeP
  · change Blanc.WithdrawalRequest.RepresentsStorage (post.state.get _).stor.get _
    rw [pstate]
    have : (initSevm msg).currentTarget = withdrawalRequestPredeployAddress := mtarget
    rw [this] at crep
    exact crep
  · change (post.state.get _).bal.toNat + 1 = _
    rw [pstate]
    exact balL
  · rw [perr, callSpawnParent_error]
    rfl
  · rw [plogs, clogs]
    rfl
  · rw [prefund]
    have hp : (callSpawnParent (addAccessedAddress (St base S Mp Gc) cw.toAdr)
        (fwd + (accessCost cw.toAdr base.accessedAddresses + 0 + gasCallValue) + 0)
        (0 : B256).toNat (56 : B256).toNat (0 : B256).toNat (0 : B256).toNat).refundCounter =
        base.refundCounter := rfl
    rw [hp]
    omega

end Blanc.Lift.WithdrawalRequest.FloodWalk
