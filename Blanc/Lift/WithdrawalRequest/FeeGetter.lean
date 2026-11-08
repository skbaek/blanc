import Blanc.Lift.WithdrawalRequest.UserFeeDispatch

/-!
The actual word-fee getter return, an instance of `RequestFee.returnTree`.
Fragment alignment is explicit; the full canonical specialization starts with
fresh memory and constructs its exit without a continuation premise.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- A successful getter leaves exactly the named RETURN state, including its error field. -/
theorem fee_getter_inv {sevm : Sevm} {b post : Devm} {M : Mem} {fee : B256} {G : Nat}
    (aligned : M.size % 32 = 0)
    (run : SFunc.Run prog sevm (St b [fee] M G) t_0082_c0 (.halted post)) :
    ∃ G', post = RequestFee.feeGetterPost b M fee G' :=
  RequestFee.return_inv aligned run

/-- Construct the actual return outcome at exactly the getter charge. -/
theorem fee_getter_exact {sevm : Sevm} {b : Devm} {M : Mem} {fee : B256} {G : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (aligned : M.size % 32 = 0) :
    SFunc.RunExact prog sevm (St b [fee] M (G + RequestFee.feeGetterGas M)) t_0082_c0
      (.halted (RequestFee.feeGetterPost b M fee G)) :=
  RequestFee.return_exact hfork.rules_push0 aligned

/-- Full raw getter execution charge, excluding any call-frame settlement charge. -/
def userFeeGetterGas (sevm : Sevm) (b : Devm) (M : Mem) (iterations : Nat) : Nat :=
  RequestFee.feeGetterGas M + 75 + RequestFee.feeLoopGas iterations + userSetupGas sevm b + dispatchGas


theorem userFeeGetterGas_empty (sevm : Sevm) (b : Devm) (iterations : Nat) :
    userFeeGetterGas sevm b Mem.empty iterations = 180 + 87 * iterations + sloadCost sevm b 0 := by
  calc
    _ = (13 + 75 + 25 + 46 + 21) + (87 * iterations + sloadCost sevm b 0) := by
      simp only [userFeeGetterGas, RequestFee.feeGetterGas_empty, RequestFee.feeLoopGas_eq,
        userSetupGas, userSetupFixedGas_eq, dispatchGas_eq,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ = _ := by simp only [← Nat.add_assoc]

/-- Successful canonical empty-calldata execution returns the actual finite word fee. -/
theorem exec_fee_getter {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (hfork : CoveredFork sevm.benvStat.fork)
    (hstack : pre.stack = []) (aligned : pre.memory.size % 32 = 0)
    (wf : Mem.Wf pre.memory)
    (user : sevm.caller ≠ systemAddress) (empty : sevm.data = [])
    (exec : Exec 0 sevm pre (.ok post)) :
    sevm.value = 0 ∧ pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput ∧
      ∃ G, post = RequestFee.feeGetterPost (afterSload sevm pre 0) pre.memory (finalOutput / (17 : B256)) G ∧
        post.output = (finalOutput / (17 : B256)).toBytes := by
  obtain ⟨active, iterations, finalOutput, wordRun, accepted⟩ :=
    exec_user_fee_dispatch hcode hfork hstack user exec
  rcases accepted with ⟨hlen, _, _⟩ | ⟨_, zero, _, run⟩
  · simp only [empty, List.length_nil] at hlen
    exact False.elim ((by decide : (0 : B256) ≠ 56) hlen)
  · obtain ⟨G, postEq⟩ := fee_getter_inv aligned run
    exact ⟨zero, active, iterations, finalOutput, wordRun, G, postEq,
      postEq ▸ (RequestFee.feeGetterPost_facts _ _ _ _ wf aligned).1⟩

/-- Construct a complete raw canonical getter Exec with an actual RETURN outcome. -/
theorem exec_fee_getter_exact {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat}
    {finalOutput : B256}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (hfork : CoveredFork sevm.benvStat.fork)
    (aligned : M.size % 32 = 0) (user : sevm.caller ≠ systemAddress)
    (empty : sevm.data = []) (zero : sevm.value = 0)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] M (G + userFeeGetterGas sevm b M iterations))
      (.ok (RequestFee.feeGetterPost (afterSload sevm b 0) M (finalOutput / (17 : B256)) G))) := by
  have hlen : sevm.data.length.toB256 = 0 := by rw [empty]; rfl
  have branchGas : userFeeDispatchGas sevm = 75 := by
    rw [userFeeDispatchGas_eq, hlen]
    rfl
  have tail := user_fee_prefix_exact hfork active wordRun
    (.inr ⟨hlen, zero, fee_getter_exact (b := afterSload sevm b 0)
      (fee := finalOutput / (17 : B256)) (G := G) hfork aligned⟩)
  rw [branchGas] at tail
  have hgas : G + userFeeGetterGas sevm b M iterations =
      (G + RequestFee.feeGetterGas M + 75 + RequestFee.feeLoopGas iterations + userSetupGas sevm b) + dispatchGas := by
    simp only [userFeeGetterGas, Nat.add_assoc]
  rw [hgas]
  exact exec_of_dispatch hcode hfork (by
    simpa only [dispatchTail, ite_eq_right user] using tail)

/-- Fresh-memory specialization has the proved closed execution charge. -/
theorem exec_fee_getter_fresh {sevm : Sevm} {b : Devm} {G iterations : Nat} {finalOutput : B256}
    (hcode : sevm.code = Blanc.withdrawalRequestCode) (hfork : CoveredFork sevm.benvStat.fork)
    (user : sevm.caller ≠ systemAddress) (empty : sevm.data = []) (zero : sevm.value = 0)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + (180 + 87 * iterations + sloadCost sevm b 0)))
      (.ok (RequestFee.feeGetterPost (afterSload sevm b 0) Mem.empty (finalOutput / (17 : B256)) G))) := by
  rw [← userFeeGetterGas_empty]
  exact exec_fee_getter_exact hcode hfork (by decide) user empty zero active wordRun

end Blanc.Lift.WithdrawalRequest
