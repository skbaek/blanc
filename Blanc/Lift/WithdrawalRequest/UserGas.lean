import Blanc.Lift.WithdrawalRequest.SubmissionBody
import Blanc.Lift.WithdrawalRequest.FeeGetter
import Blanc.StorageAccessGas

/-! Closed fresh user charges and finite-word liveness of actual canonical walks. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- The five store charges retain each actual incoming state, including aliases. -/
def submissionStoreGas (sevm : Sevm) (b : Devm) (M : Mem) : Nat :=
  sstoreCost sevm (submissionCountRead sevm b) 1 (1 + submissionCount sevm b) +
  sstoreCost sevm (submissionTailRead sevm b) (submissionKey sevm b) sevm.caller.toB256 +
  sstoreCost sevm (submissionCallerStore sevm b) (1 + submissionKey sevm b)
    (Sevm.dataWord sevm 0) +
  sstoreCost sevm (submissionWord1Store sevm b) (1 + (1 + submissionKey sevm b))
    (Sevm.dataWord sevm 32) +
  sstoreCost sevm (submissionLogged sevm b M) 3 (1 + submissionTail sevm b)

/-- Fee, count, tail reads in execution order, with the actual incoming warm sets. -/
def userSubmissionReads (sevm : Sevm) (b : Devm) : SloadSchedule :=
  [(b, 0), (afterSload sevm b 0, 1),
    (submissionCountStore sevm (afterSload sevm b 0), 3)]

/-- The actual fresh submission allocation is one word, then three words. -/
theorem submissionMemory_empty_sizes (sevm : Sevm) :
    (submissionCallerMemory sevm Mem.empty).size = 32 ∧
    (submissionCopyMemory sevm Mem.empty).size = 96 ∧
    (submissionMemory sevm Mem.empty).size = 96 := by
  have callerSize : (submissionCallerMemory sevm Mem.empty).size = 32 := by
    unfold submissionCallerMemory
    rw [Mem.size_write_of_size rfl (by decide) (B256.length_toBytes _)]
    rfl
  have copySize : (submissionCopyMemory sevm Mem.empty).size = 96 := by
    unfold submissionCopyMemory
    rw [Mem.size_write_of_size callerSize (by decide) (List.length_sliceD _ _ _ _)]
    rfl
  refine ⟨callerSize, copySize, ?_⟩
  unfold submissionMemory
  rw [Mem.size_read_snd_of_le (by rw [copySize]) (by rw [copySize]; decide), copySize]

/-- Exact fresh MSTORE, CALLDATACOPY and LOG0 charges, including expansion. -/
theorem submissionMemory_empty_charges (sevm : Sevm) :
    submissionMstoreGas Mem.empty = 6 ∧
    submissionCopyGas sevm Mem.empty = 15 ∧
    submissionLogGas sevm Mem.empty = 983 := by
  obtain ⟨callerSize, copySize, _⟩ := submissionMemory_empty_sizes sevm
  refine ⟨rfl, ?_, ?_⟩
  · rw [submissionCopyGas, callerSize]
    rfl
  · rw [submissionLogGas, copySize]
    rfl

/-- The body charge keeps two selected reads and all five sequential stores. -/
theorem submissionBodyGas_empty (sevm : Sevm) (b : Devm) :
    submissionBodyGas sevm b Mem.empty = 1102 + sloadCost sevm b 1 +
      sloadCost sevm (submissionCountStore sevm b) 3 + submissionStoreGas sevm b Mem.empty := by
  obtain ⟨mstore, copy, log⟩ := submissionMemory_empty_charges sevm
  calc
    _ = (12 + 54 + 32 + 6 + 15 + 983) +
        (sloadCost sevm b 1 + sloadCost sevm (submissionCountStore sevm b) 3 +
          submissionStoreGas sevm b Mem.empty) := by
      simp only [submissionBodyGas, submissionCountGas, submissionWordsGas,
        submissionSuffixGas, submissionStoreGas, mstore, copy, log,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = _ := by simp only [← Nat.add_assoc]

/-- Closed fresh-frame charge: fixed opcodes, finite fee bodies, selected storage. -/
theorem userSubmissionGas_empty (sevm : Sevm) (b : Devm) (iterations : Nat) :
    userSubmissionGas sevm b Mem.empty iterations =
      1258 + 87 * iterations + sloadScheduleCost sevm (userSubmissionReads sevm b) +
        submissionStoreGas sevm (afterSload sevm b 0) Mem.empty := by
  calc
    _ = (1102 + 64 + 25 + 46 + 21) +
        (87 * iterations + sloadScheduleCost sevm (userSubmissionReads sevm b) +
          submissionStoreGas sevm (afterSload sevm b 0) Mem.empty) := by
      simp only [userSubmissionGas, submissionBodyGas_empty, feeLoopGas_eq,
        userSetupGas, userSetupFixedGas_eq, dispatchGas_eq, userSubmissionReads,
        sloadScheduleCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = _ := by simp only [← Nat.add_assoc]

/-- Exactly three selected reads, with warmth counted in their real incoming states. -/
theorem userSubmissionGas_empty_cold_count (sevm : Sevm) (b : Devm) (iterations : Nat) :
    userSubmissionGas sevm b Mem.empty iterations =
      1558 + 87 * iterations + 2000 * sloadColdCount sevm (userSubmissionReads sevm b) +
        submissionStoreGas sevm (afterSload sevm b 0) Mem.empty := by
  rw [userSubmissionGas_empty, sloadScheduleCost_eq]
  change 1258 + 87 * iterations + (300 + 2000 * sloadColdCount sevm
    (userSubmissionReads sevm b)) + submissionStoreGas sevm (afterSload sevm b 0) Mem.empty = _
  calc
    _ = (1258 + 300) + 87 * iterations + 2000 * sloadColdCount sevm (userSubmissionReads sevm b) +
        submissionStoreGas sevm (afterSload sevm b 0) Mem.empty := by
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = _ := rfl

/-- Fresh canonical STOP at the closed selected charge, retaining every store sentry. -/
theorem exec_submission_fresh {sevm : Sevm} {b : Devm} {G iterations : Nat}
    {finalOutput : B256}
    (code : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : sevm.data.length = 56)
    (dynamic : sevm.isStatic = false) (slack : gCallStipend < G)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0)
      17 1 17 0 iterations finalOutput)
    (paid : (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty
      (G + (1258 + 87 * iterations + sloadScheduleCost sevm (userSubmissionReads sevm b) +
        submissionStoreGas sevm (afterSload sevm b 0) Mem.empty)))
      (.ok (submissionPost sevm (afterSload sevm b 0) Mem.empty G))) := by
  rw [← userSubmissionGas_empty]
  exact exec_submission_exact code fork user length dynamic slack active wordRun paid

/-- A unique finite word fee/count supplies submission liveness, without an assumed Run.
The paid premise is the actual word fee; residual slack is sufficient, not minimal. -/
theorem exec_submission_word_live {sevm : Sevm} {b : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : sevm.data.length = 56)
    (dynamic : sevm.isStatic = false) (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max) :
    ∃! result : Nat × B256,
      WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0)
        17 1 17 0 result.1 result.2 ∧
      ∀ G, gCallStipend < G → (result.2 / (17 : B256)).toNat ≤ sevm.value.toNat →
        Nonempty (Exec 0 sevm (St b [] Mem.empty
          (G + (1258 + 87 * result.1 + sloadScheduleCost sevm (userSubmissionReads sevm b) +
            submissionStoreGas sevm (afterSload sevm b 0) Mem.empty)))
          (.ok (submissionPost sevm (afterSload sevm b 0) Mem.empty G))) := by
  obtain ⟨result, run, unique⟩ := WordFakeExponential.run_exists_unique
    (b.getStorVal sevm.currentTarget 0) 17 1 17 0
  refine ⟨result, ⟨run, ?_⟩, ?_⟩
  · intro G slack paid
    exact exec_submission_fresh code fork user length dynamic slack active run paid
  · intro other property
    exact unique other property.1

/-- Getter liveness uses the unique finite word fee and the existing closed charge.
The getter may be static and needs no SSTORE sentry slack. -/
theorem exec_fee_getter_word_live {sevm : Sevm} {b : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (empty : sevm.data = []) (zero : sevm.value = 0)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max) :
    ∃! result : Nat × B256,
      WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0)
        17 1 17 0 result.1 result.2 ∧
      ∀ G, Nonempty (Exec 0 sevm
        (St b [] Mem.empty (G + (180 + 87 * result.1 + sloadCost sevm b 0)))
        (.ok (feeGetterPost (afterSload sevm b 0) Mem.empty (result.2 / (17 : B256)) G))) := by
  obtain ⟨result, run, unique⟩ := WordFakeExponential.run_exists_unique
    (b.getStorVal sevm.currentTarget 0) 17 1 17 0
  refine ⟨result, ⟨run, ?_⟩, ?_⟩
  · intro G
    exact exec_fee_getter_fresh code fork user empty zero active run
  · intro other property
    exact unique other property.1

end Blanc.Lift.WithdrawalRequest
