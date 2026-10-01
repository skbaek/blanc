import Blanc.Lift.WithdrawalRequest.SubmissionBody
import Blanc.Lift.WithdrawalRequest.Layout
import Blanc.WordByteRoundtrip
import Blanc.WordByteCodecs
import Blanc.BytesWrite
import Blanc.RevertPayload

/-! Typed 56-byte submissions and conditional sequential storage correspondence. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune
open Blanc.WithdrawalRequest

/-- Decode literal calldata, retaining every pubkey byte and the unsigned amount. -/
def decodeSubmission (sevm : Sevm) (hlen : sevm.data.length = 56) : Blanc.WithdrawalRequest.Entry where
  caller := sevm.caller
  pubkey := ⟨sevm.data.take 48, by rw [List.length_take, hlen]; rfl⟩
  amount := Bytes.toUInt64 (sevm.data.drop 48)

theorem decodeSubmission_payload (sevm : Sevm) (hlen : sevm.data.length = 56) :
    submissionPayload (decodeSubmission sevm hlen) = sevm.data := by
  have suffixLength : (sevm.data.drop 48).length = 8 := by
    rw [List.length_drop, hlen]
  simp only [submissionPayload, decodeSubmission]
  rw [Blanc.Bytes.toBytes_toUInt64_of_length suffixLength, List.take_append_drop]

/-- The stored caller is exactly the typed caller field. -/
theorem decodeSubmission_callerWord (sevm : Sevm) (hlen : sevm.data.length = 56) :
    callerWord (decodeSubmission sevm hlen) = sevm.caller.toB256 := rfl

theorem submission_dataWords (sevm : Sevm) (entry : Blanc.WithdrawalRequest.Entry)
    (payload : sevm.data = submissionPayload entry) :
    Sevm.dataWord sevm 0 = pubkeyWord entry ∧
    Sevm.dataWord sevm 32 = pubkeyAmountWord entry := by
  have prefixRoom : 32 ≤ entry.pubkey.val.length := by
    rw [entry.pubkey.property]
    decide
  constructor
  · simp only [Sevm.dataWord, payload, submissionPayload, pubkeyWord]
    change Bytes.toB256 ((entry.pubkey.val ++ entry.amount.toBytes).sliceD 0 32 0) = _
    rw [List.sliceD, List.drop_zero, List.takeD_eq_take _
      (by rw [List.length_append]; exact Nat.le_trans prefixRoom (Nat.le_add_right _ _))]
    rw [List.take_append_of_le_length prefixRoom]
  · simp only [Sevm.dataWord, payload, submissionPayload, pubkeyAmountWord,
      pubkeyAmountBytes]
    change Bytes.toB256 ((entry.pubkey.val ++ entry.amount.toBytes).sliceD 32 32 0) = _
    rw [List.sliceD, List.drop_append_of_le_length prefixRoom]
    have suffixLength : (entry.pubkey.val.drop 32 ++ entry.amount.toBytes).length = 24 := by
      simp only [List.length_append, List.length_drop, entry.pubkey.property, UInt64.length_toBytes]
    have padded := Blanc.List.takeD_length_add_append
      (entry.pubkey.val.drop 32 ++ entry.amount.toBytes) ([] : Bytes) 8 (0 : UInt8)
    rw [suffixLength, List.append_nil] at padded
    exact congrArg Bytes.toB256 padded

/-- Actual writes and the LOG0 read retain well-formed memory. -/
theorem submissionMemory_wf (sevm : Sevm) (M : Mem) (hwf : Mem.Wf M) :
    Mem.Wf (submissionMemory sevm M) := by
  exact ((hwf.write 0 (sevm.caller.toB256 <<< 96).toBytes).write 20
    (sevm.data.sliceD 0 56 0)).extend 0 76

/-- The actual LOG0 reads the caller's twenty bytes and the literal payload. -/
theorem submissionLog_eq (sevm : Sevm) (M : Mem) (hwf : Mem.Wf M)
    (entry : Blanc.WithdrawalRequest.Entry)
    (caller : entry.caller = sevm.caller) (payload : sevm.data = submissionPayload entry) :
    submissionLog sevm M = ⟨sevm.currentTarget, [], Blanc.WithdrawalRequest.submissionLog entry⟩ := by
  have copied : sevm.data.sliceD 0 56 0 = submissionPayload entry := by
    rw [payload, List.sliceD, List.drop_zero]
    exact List.takeD_eq_self 0 (submissionPayload_length entry).symm
  have reads := ((Mem.reads_data M).write hwf 0 (sevm.caller.toB256 <<< 96).toBytes).write
    (hwf.write 0 (sevm.caller.toB256 <<< 96).toBytes) 20 (sevm.data.sliceD 0 56 0)
  have image := reads.read 0 76
  let firstImage := Bytes.writeAt M.data.toList 0 (sevm.caller.toB256 <<< 96).toBytes
  change ((submissionCopyMemory sevm M).read 0 76).1 =
    (Bytes.writeAt firstImage 20 (sevm.data.sliceD 0 56 0)).sliceD 0 (20 + 56) 0 at image
  rw [copied] at image
  rw [Blanc.List.sliceD_add] at image
  rw [Bytes.sliceD_writeAt_before _ _ 0 20 20 (Nat.le_refl _)] at image
  rw [show 56 = (submissionPayload entry).length from (submissionPayload_length entry).symm,
    Bytes.sliceD_writeAt] at image
  have first : firstImage.sliceD 0 20 0 = sevm.caller.toBytes := by
    dsimp only [firstImage]
    rw [Bytes.sliceD_writeAt_inside _ _ 0 0 20 (Nat.le_refl _) (by
      rw [B256.length_toBytes]
      decide)]
    rw [Nat.sub_self, List.sliceD, List.drop_zero,
      List.takeD_eq_take _ (by rw [B256.length_toBytes]; decide)]
    rw [WordByteCodecs.shift96_take20_toAdr_bytes, toAdr_toB256]
  rw [first] at image
  rw [submissionLog, image, Blanc.WithdrawalRequest.submissionLog, caller]

/-- Explicit prospective margins; reachability must establish these separately. -/
structure SubmissionBounds (state : Blanc.WithdrawalRequest.State) : Prop where
  count_next_lt : state.count + 1 < 2 ^ 256
  tail_slot_lt : queueBase state.tail + 2 < 2 ^ 256

theorem submissionTail_eq (sevm : Sevm) (b : Devm) (state : Blanc.WithdrawalRequest.State)
    (rep : RepresentsStorage (b.getStor sevm.currentTarget).get state) :
    submissionTail sevm b = state.tail.toB256 := by
  change (Devm.getStor (afterSstore sevm (afterSload sevm b 1) 1
    (1 + submissionCount sevm b)) sevm.currentTarget).get 3 = _
  rw [afterSstore_getStor_self, afterSload_getStor,
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3)]
  exact rep.tail

/-- Queue keys agree modulo the word modulus, independently of alias bounds. -/
theorem submissionKey_queueSlot (sevm : Sevm) (b : Devm) (n : Nat)
    (tail : submissionTail sevm b = n.toB256) :
    submissionKey sevm b = queueSlot n 0 := by
  apply B256.toNat_inj
  simp only [submissionKey, tail, queueSlot, queueBase, B256.toNat_add,
    B256.toNat_mul, B256.toNat_toB256, Nat.lo_eq, Nat.add_zero]
  change (4 + (3 * (n % 2 ^ 256)) % 2 ^ 256) % 2 ^ 256 =
    (4 + 3 * n) % 2 ^ 256
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem submissionKey_offsets (sevm : Sevm) (b : Devm) (n : Nat)
    (tail : submissionTail sevm b = n.toB256) :
    1 + submissionKey sevm b = queueSlot n 1 ∧
    1 + (1 + submissionKey sevm b) = queueSlot n 2 := by
  rw [submissionKey_queueSlot sevm b n tail]
  constructor
  · apply B256.toNat_inj
    simp only [queueSlot, B256.toNat_add, B256.toNat_toB256, Nat.lo_eq, Nat.add_zero]
    change (1 + queueBase n % 2 ^ 256) % 2 ^ 256 = (queueBase n + 1) % 2 ^ 256
    simp only [Nat.add_mod, Nat.mod_mod, Nat.add_comm]
  · apply B256.toNat_inj
    simp only [queueSlot, B256.toNat_add, B256.toNat_toB256, Nat.lo_eq, Nat.add_zero]
    change (1 + (1 + queueBase n % 2 ^ 256) % 2 ^ 256) % 2 ^ 256 =
      (queueBase n + 2) % 2 ^ 256
    rw [Nat.add_mod_mod, ← Nat.add_assoc, Nat.add_mod_mod, Nat.add_comm]

/-- A bound is used only here to identify a modular key's natural value. -/
theorem submission_queueSlot_toNat (n offset : Nat)
    (bound : queueBase n + offset < 2 ^ 256) :
    (queueSlot n offset).toNat = queueBase n + offset :=
  B256.toNat_toB256_of_lt bound

theorem submission_queueSlot_ne_metadata (n offset k : Nat)
    (bound : queueBase n + offset < 2 ^ 256) (hmeta : k < 4) :
    queueSlot n offset ≠ k.toB256 := by
  intro eq
  have values := congrArg B256.toNat eq
  rw [submission_queueSlot_toNat n offset bound,
    B256.toNat_toB256_of_lt (Nat.lt_trans hmeta (by decide))] at values
  have lower : 4 ≤ queueBase n + offset :=
    Nat.le_trans (Nat.le_add_right 4 (3 * n)) (Nat.le_add_right _ offset)
  exact Nat.not_le_of_lt hmeta (values ▸ lower)

/-- Old live indices lie before the new tail's first key. -/
theorem submission_queueSlot_before (a n offset : Nat)
    (before : a < n) (hoff : offset ≤ 2) :
    queueBase a + offset < queueBase n := by
  calc
    queueBase a + offset < queueBase (a + 1) := by
      simpa only [queueBase, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
        Nat.add_lt_add_left (Nat.lt_of_le_of_lt hoff (by decide : 2 < 3)) (4 + 3 * a)
    _ ≤ queueBase n := Nat.add_le_add_left
      (Nat.mul_le_mul_left 3 (Nat.succ_le_of_lt before)) 4

theorem SubmissionBounds.tail_next_lt {state : Blanc.WithdrawalRequest.State}
    (bounds : SubmissionBounds state) : state.tail + 1 < 2 ^ 256 := by
  have leTriple := Nat.le_mul_of_pos_left state.tail (by decide : 0 < 3)
  have leBase : state.tail + 1 ≤ queueBase state.tail + 2 := by
    calc
      state.tail + 1 ≤ 3 * state.tail + 2 := Nat.add_le_add leTriple (by decide)
      _ ≤ queueBase state.tail + 2 := Nat.add_le_add_right (Nat.le_add_left _ 4) 2
  exact Nat.lt_of_le_of_lt leBase bounds.tail_slot_lt

/-- The actual ordered map, expressed through typed queue words. -/
theorem submissionPost_storage_typed (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat)
    (state : Blanc.WithdrawalRequest.State) (entry : Blanc.WithdrawalRequest.Entry)
    (rep : RepresentsStorage (b.getStor sevm.currentTarget).get state)
    (bounds : SubmissionBounds state) (caller : entry.caller = sevm.caller)
    (payload : sevm.data = submissionPayload entry) :
    (submissionPost sevm b M G).getStor sevm.currentTarget =
      (((((b.getStor sevm.currentTarget).set 1 (state.count + 1).toB256).set
        (queueSlot state.tail 0) (callerWord entry)).set
        (queueSlot state.tail 1) (pubkeyWord entry)).set
        (queueSlot state.tail 2) (pubkeyAmountWord entry)).set 3 (state.tail + 1).toB256 := by
  have count : submissionCount sevm b = state.count.toB256 := rep.count
  have tail := submissionTail_eq sevm b state rep
  have key := submissionKey_queueSlot sevm b state.tail tail
  have offsets := submissionKey_offsets sevm b state.tail tail
  have words := submission_dataWords sevm entry payload
  have countNext := one_add_toB256 bounds.count_next_lt
  have tailNext := one_add_toB256 bounds.tail_next_lt
  change 1 + state.count.toB256 = (state.count + 1).toB256 at countNext
  change 1 + state.tail.toB256 = (state.tail + 1).toB256 at tailNext
  rw [submissionPost_storage, count, tail, offsets.2, offsets.1, key,
    words.1, words.2, countNext, tailNext]
  rw [callerWord, caller]

private theorem submit_storageBounds (state : Blanc.WithdrawalRequest.State)
    (entry : Blanc.WithdrawalRequest.Entry) (repBounds : StorageBounds state)
    (coherent : Coherent state) (bounds : SubmissionBounds state) :
    StorageBounds (submit state entry) := by
  refine ⟨repBounds.excess_lt, bounds.count_next_lt, repBounds.head_lt,
    bounds.tail_next_lt, ?_⟩
  intro i hi
  have indexLe : i ≤ state.queue.length := by
    change i < (state.queue ++ [entry]).length at hi
    rw [List.length_append, List.length_singleton] at hi
    exact Nat.le_of_lt_succ hi
  have pointerLe : state.head + i ≤ state.tail := by
    rw [← coherent]
    exact Nat.add_le_add_left indexLe state.head
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 3 pointerLe) 4) 2)
    bounds.tail_slot_lt

theorem submissionPost_represents (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat)
    (state : Blanc.WithdrawalRequest.State) (entry : Blanc.WithdrawalRequest.Entry)
    (rep : RepresentsStorage (b.getStor sevm.currentTarget).get state)
    (bounds : SubmissionBounds state) (caller : entry.caller = sevm.caller)
    (payload : sevm.data = submissionPayload entry) :
    RepresentsStorage ((submissionPost sevm b M G).getStor sevm.currentTarget).get
      (submit state entry) := by
  rw [submissionPost_storage_typed sevm b M G state entry rep bounds caller payload]
  have avoids : ∀ off, off ≤ 2 → ∀ k, k < 4 → queueSlot state.tail off ≠ k.toB256 := by
    intro off hoff k hk
    exact submission_queueSlot_ne_metadata state.tail off k
      (Nat.lt_of_le_of_lt (Nat.add_le_add_left hoff _) bounds.tail_slot_lt) hk
  have avoids0 : ∀ off, off ≤ 2 → queueSlot state.tail off ≠ (0 : B256) :=
    fun off hoff => avoids off hoff 0 (by decide)
  have avoids1 : ∀ off, off ≤ 2 → queueSlot state.tail off ≠ (1 : B256) :=
    fun off hoff => avoids off hoff 1 (by decide)
  have avoids2 : ∀ off, off ≤ 2 → queueSlot state.tail off ≠ (2 : B256) :=
    fun off hoff => avoids off hoff 2 (by decide)
  have avoids3 : ∀ off, off ≤ 2 → queueSlot state.tail off ≠ (3 : B256) :=
    fun off hoff => avoids off hoff 3 (by decide)
  refine ⟨submit_coherent rep.coherent entry,
    submit_storageBounds state entry rep.bounds rep.coherent bounds, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Stor.get_set_ite, avoids0 2 (by decide),
      avoids0 1 (by decide), avoids0 0 (by decide),
      show (3 : B256) ≠ 0 from by decide, show (1 : B256) ≠ 0 from by decide,
      ite_false]
    exact rep.excess
  · simp only [Stor.get_set_ite, avoids1 2 (by decide),
      avoids1 1 (by decide), avoids1 0 (by decide),
      show (3 : B256) ≠ 1 from by decide, ite_false, ite_true, submit]
  · simp only [Stor.get_set_ite, avoids2 2 (by decide),
      avoids2 1 (by decide), avoids2 0 (by decide),
      show (3 : B256) ≠ 2 from by decide, show (1 : B256) ≠ 2 from by decide,
      ite_false]
    exact rep.head
  · rw [Stor.get_set_self]
    rfl
  · intro i hi
    simp only [submit] at hi ⊢
    by_cases old : i < state.queue.length
    · have before : state.head + i < state.tail := by
        rw [← rep.coherent]
        exact Nat.add_lt_add_left old state.head
      have unchanged : ∀ off, off ≤ 2 →
          ((((((b.getStor sevm.currentTarget).set 1 (state.count + 1).toB256).set
            (queueSlot state.tail 0) (callerWord entry)).set
            (queueSlot state.tail 1) (pubkeyWord entry)).set
            (queueSlot state.tail 2) (pubkeyAmountWord entry)).set 3
            (state.tail + 1).toB256).get (queueSlot (state.head + i) off) =
              (b.getStor sevm.currentTarget).get (queueSlot (state.head + i) off) := by
        intro off hoff
        have oldBound : queueBase (state.head + i) + off < 2 ^ 256 :=
          Nat.lt_of_le_of_lt (Nat.add_le_add_left hoff _) (rep.bounds.liveSlot_lt i old)
        have meta1 : (1 : B256) ≠ queueSlot (state.head + i) off :=
          (submission_queueSlot_ne_metadata _ off 1 oldBound (by decide)).symm
        have meta3 : (3 : B256) ≠ queueSlot (state.head + i) off :=
          (submission_queueSlot_ne_metadata _ off 3 oldBound (by decide)).symm
        have newNe : ∀ other, other ≤ 2 →
            queueSlot state.tail other ≠ queueSlot (state.head + i) off := by
          intro other hother eq
          have values := congrArg B256.toNat eq
          rw [submission_queueSlot_toNat _ other
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left hother _) bounds.tail_slot_lt),
            submission_queueSlot_toNat _ off oldBound] at values
          have lt := Nat.lt_of_lt_of_le (submission_queueSlot_before _ _ off before hoff)
            (Nat.le_add_right (queueBase state.tail) other)
          exact Nat.ne_of_lt lt values.symm
        simp only [Stor.get_set_ite, meta1, meta3, newNe 0 (by decide),
          newNe 1 (by decide), newNe 2 (by decide), ite_false]
      rw [unchanged 0 (by decide), unchanged 1 (by decide), unchanged 2 (by decide),
        List.getElem_append_left old]
      exact rep.live i old
    · have indexEq : i = state.queue.length := Nat.le_antisymm
        (Nat.le_of_lt_succ (by simpa only [List.length_append, List.length_singleton] using hi))
        (Nat.le_of_not_gt old)
      subst i
      rw [rep.coherent, List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      have different : ∀ a, a ≤ 2 → ∀ c, c ≤ 2 → a ≠ c →
          queueSlot state.tail a ≠ queueSlot state.tail c := by
        intro a ha c hc ne eq
        have values := congrArg B256.toNat eq
        rw [submission_queueSlot_toNat _ a
          (Nat.lt_of_le_of_lt (Nat.add_le_add_left ha _) bounds.tail_slot_lt),
          submission_queueSlot_toNat _ c
          (Nat.lt_of_le_of_lt (Nat.add_le_add_left hc _) bounds.tail_slot_lt)] at values
        exact ne (Nat.add_left_cancel values)
      simp only [Stor.get_set_ite, (avoids3 0 (by decide)).symm,
        (avoids3 1 (by decide)).symm, (avoids3 2 (by decide)).symm,
        different 1 (by decide) 0 (by decide) (by decide),
        different 2 (by decide) 0 (by decide) (by decide),
        different 2 (by decide) 1 (by decide) (by decide), ite_true, ite_false, and_self]

/-- The actual submission writes storage only at the executing address. -/
theorem submissionPost_other_storage (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat)
    (address : Adr) (other : address ≠ sevm.currentTarget) :
    (submissionPost sevm b M G).getStor address = b.getStor address := by
  rw [submissionPost]
  rw [show Devm.getStor (St (submissionBase sevm b M) [] (submissionMemory sevm M) G)
      address = Devm.getStor (submissionBase sevm b M) address from by
    generalize submissionBase sevm b M = finalBase
    rfl]
  simp only [submissionBase, submissionLogged, submissionWordsStore,
    submissionWord1Store, submissionCallerStore, submissionTailRead,
    submissionCountStore, submissionCountRead, afterSstore_getStor_ne _ _ _ _ _ other.symm,
    afterSload_getStor, Devm.addLog_getStor]

/-- Full typed effect support for the real STOP state, conditional on incoming representation. -/
theorem submissionPost_layout (sevm : Sevm) (b : Devm) (M : Mem) (G : Nat)
    (state : Blanc.WithdrawalRequest.State) (hlen : sevm.data.length = 56)
    (rep : RepresentsStorage (b.getStor sevm.currentTarget).get state)
    (bounds : SubmissionBounds state) (hwf : Mem.Wf M) :
    RepresentsStorage ((submissionPost sevm b M G).getStor sevm.currentTarget).get
      (submit state (decodeSubmission sevm hlen)) ∧
    (submissionPost sevm b M G).logs = b.logs ++
      [⟨sevm.currentTarget, [], Blanc.WithdrawalRequest.submissionLog (decodeSubmission sevm hlen)⟩] ∧
    Mem.Wf (submissionPost sevm b M G).memory ∧
    ∀ address, address ≠ sevm.currentTarget →
      (submissionPost sevm b M G).getStor address = b.getStor address := by
  have payload := (decodeSubmission_payload sevm hlen).symm
  have facts := submissionPost_facts sevm b M G
  refine ⟨submissionPost_represents sevm b M G state (decodeSubmission sevm hlen)
    rep bounds rfl payload, ?_, ?_, submissionPost_other_storage sevm b M G⟩
  · change (submissionPost sevm b M G).meta.logs = _
    rw [facts.2.1]
    change (submissionBase sevm b M).logs = _
    rw [submissionBase_logs,
      submissionLog_eq sevm M hwf (decodeSubmission sevm hlen) rfl payload]
  · rw [facts.2.2.2.1]
    exact submissionMemory_wf sevm M hwf

/-- Canonical successful literal submissions carry the conditional model/storage effect. -/
theorem exec_submission_layout {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (hstack : pre.stack = []) (user : sevm.caller ≠ systemAddress)
    (hlen : sevm.data.length = 56) (exec : Exec 0 sevm pre (.ok post))
    (state : Blanc.WithdrawalRequest.State)
    (rep : RepresentsStorage (pre.getStor sevm.currentTarget).get state)
    (bounds : SubmissionBounds state) (hwf : Mem.Wf pre.memory) :
    RepresentsStorage (post.getStor sevm.currentTarget).get
      (submit state (decodeSubmission sevm hlen)) ∧
    post.logs = pre.logs ++
      [⟨sevm.currentTarget, [], Blanc.WithdrawalRequest.submissionLog (decodeSubmission sevm hlen)⟩] ∧
    Mem.Wf post.memory ∧
    ∀ address, address ≠ sevm.currentTarget → post.getStor address = pre.getStor address := by
  obtain ⟨_, _, _, _, _, _, G, postEq⟩ := exec_submission hcode fork hstack user hlen exec
  rw [postEq]
  have warmed : RepresentsStorage ((afterSload sevm pre 0).getStor sevm.currentTarget).get state := by
    rw [afterSload_getStor]
    exact rep
  simpa only [afterSload_getStor, afterSload_logs] using
    submissionPost_layout sevm (afterSload sevm pre 0) pre.memory G state hlen warmed bounds hwf

end Blanc.Lift.WithdrawalRequest
