import Blanc.Lift.WithdrawalRequest.ExactFeeDomain
import Blanc.Lift.WithdrawalRequest.BalanceHistory

/-! Nat payment is sufficient for a fresh active submission, independently of
fee-domain membership. History supplies code; activation remains explicit. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.ExecutionTrace

/-- Nat-paid fresh submission liveness at the unique actual word iteration
count. There is no assumed fee run or no-wrap domain. -/
theorem exec_submission_nat_live {sevm : Sevm} {b : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : sevm.data.length = 56)
    (dynamic : sevm.isStatic = false) (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (model : Blanc.WithdrawalRequest.State)
    (excessEq : model.excess = (b.getStorVal sevm.currentTarget 0).toNat)
    (paid : Blanc.WithdrawalRequest.fee model ≤ sevm.value.toNat) :
    ∃! result : Nat × B256,
      WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0)
        17 1 17 0 result.1 result.2 ∧
      ∀ G, gCallStipend < G →
        Nonempty (Exec 0 sevm (St b [] Mem.empty
          (G + (1258 + 87 * result.1 + sloadScheduleCost sevm (userSubmissionReads sevm b) +
            submissionStoreGas sevm (afterSload sevm b 0) Mem.empty)))
          (.ok (submissionPost sevm (afterSload sevm b 0) Mem.empty G))) := by
  obtain ⟨result, ⟨run, live⟩, unique⟩ :=
    exec_submission_word_live code fork user length dynamic active
  refine ⟨result, ⟨run, ?_⟩, ?_⟩
  · intro G slack
    exact live G slack ((word_fee_le_nat run model excessEq).trans paid)
  · intro other property
    exact unique other ⟨property.1, fun G slack _ => property.2 G slack⟩

/-- A raw fresh-frame context fixes the predeploy code, target, input and
dynamic mode; other environmental fields remain those supplied by the caller. -/
def historySubmissionSevm (world : Jaune.State) (sevm : Sevm) (data : Bytes) : Sevm :=
  { sevm with
    code := world.getCode withdrawalRequestPredeployAddress
    currentTarget := withdrawalRequestPredeployAddress
    data := data
    isStatic := false }

private theorem fresh_user_inhibited {sevm : Sevm} {b : Devm}
    (code : sevm.code = Blanc.withdrawalRequestCode) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (lengthBound : sevm.data.length < 2 ^ 256)
    (inhibited : b.getStorVal sevm.currentTarget 0 = B256.max) :
    ∀ gas post, ¬ Nonempty (Exec 0 sevm (St b [] Mem.empty gas) (.ok post)) := by
  intro gas post successful
  obtain ⟨run⟩ := successful
  have effect := exec_frame_effect (pre := St b [] Mem.empty gas)
    code fork rfl rfl Mem.wf_empty lengthBound run
  exact effect.user_guards user |>.1 inhibited

/-- After a configured history, inhibited user frames cannot succeed; active
Nat-paid submissions have a unique word count and exact fresh-frame gas.
Checkpoint CODE is the only installation premise, with no storage model. -/
theorem history_submission_nat_live {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (sevm : Sevm) (b : Devm) (data : Bytes) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (length : data.length = 56) :
    let fresh := historySubmissionSevm future.state sevm data
    let base := b.withState future.state
    (base.getStorVal withdrawalRequestPredeployAddress 0 = B256.max →
      ∀ gas post, ¬ Nonempty (Exec 0 fresh (St base [] Mem.empty gas) (.ok post))) ∧
    (base.getStorVal withdrawalRequestPredeployAddress 0 ≠ B256.max →
      fakeExp 1 (base.getStorVal withdrawalRequestPredeployAddress 0).toNat 17 ≤
        sevm.value.toNat →
      ∃! result : Nat × B256,
        WordFakeExponential.Run (base.getStorVal withdrawalRequestPredeployAddress 0)
          17 1 17 0 result.1 result.2 ∧
        ∀ G, gCallStipend < G →
          Nonempty (Exec 0 fresh (St base [] Mem.empty
            (G + (1258 + 87 * result.1 + sloadScheduleCost fresh (userSubmissionReads fresh base) +
              submissionStoreGas fresh (afterSload fresh base 0) Mem.empty)))
            (.ok (submissionPost fresh (afterSload fresh base 0) Mem.empty G)))) := by
  have installed : (historySubmissionSevm future.state sevm data).code =
      Blanc.withdrawalRequestCode := history_canonical_code history code
  refine ⟨?_, ?_⟩
  · intro inhibited
    have bound : (historySubmissionSevm future.state sevm data).data.length < 2 ^ 256 := by
      change data.length < 2 ^ 256
      rw [length]
      decide
    exact fresh_user_inhibited installed fork user bound inhibited
  · intro active paid
    let model : Blanc.WithdrawalRequest.State :=
      ⟨((b.withState future.state).getStorVal withdrawalRequestPredeployAddress 0).toNat,
        0, 0, 0, []⟩
    exact exec_submission_nat_live installed fork user length rfl active model rfl paid

/-- A fresh fee read at a configured-history state returns the unique word
fee at its exact charge. Nat equality is characterized, never assumed. -/
theorem history_fee_getter_word_live {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (sevm : Sevm) (b : Devm) (fork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) :
    let fresh := { historySubmissionSevm future.state sevm [] with value := 0 }
    let base := b.withState future.state
    (base.getStorVal withdrawalRequestPredeployAddress 0 = B256.max →
      ∀ gas post, ¬ Nonempty (Exec 0 fresh (St base [] Mem.empty gas) (.ok post))) ∧
    (base.getStorVal withdrawalRequestPredeployAddress 0 ≠ B256.max →
      ∃! result : Nat × B256,
        WordFakeExponential.Run (base.getStorVal withdrawalRequestPredeployAddress 0)
          17 1 17 0 result.1 result.2 ∧
        ((result.2 / (17 : B256)).toNat =
          fakeExp 1 (base.getStorVal withdrawalRequestPredeployAddress 0).toNat 17 ↔
          NatFeeDomain (base.getStorVal withdrawalRequestPredeployAddress 0) result.1) ∧
        ∀ G, Nonempty (Exec 0 fresh
          (St base [] Mem.empty (G + (180 + 87 * result.1 + sloadCost fresh base 0)))
          (.ok (feeGetterPost (afterSload fresh base 0) Mem.empty
            (result.2 / (17 : B256)) G)))) := by
  have installed :
      ({ historySubmissionSevm future.state sevm [] with value := 0 } : Sevm).code =
        Blanc.withdrawalRequestCode := history_canonical_code history code
  refine ⟨?_, ?_⟩
  · intro inhibited
    exact fresh_user_inhibited installed fork user (by change 0 < 2 ^ 256; decide) inhibited
  · intro active
    obtain ⟨result, ⟨run, live⟩, unique⟩ :=
      exec_fee_getter_word_live installed fork user rfl rfl active
    let model : Blanc.WithdrawalRequest.State :=
      ⟨((b.withState future.state).getStorVal withdrawalRequestPredeployAddress 0).toNat,
        0, 0, 0, []⟩
    have equality := word_fee_eq_iff_natFeeDomain run model rfl
    refine ⟨result, ⟨run, equality, live⟩, ?_⟩
    intro other property
    exact unique other ⟨property.1, property.2.2⟩

end Blanc.Lift.WithdrawalRequest
