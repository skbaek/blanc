import Blanc.Lift.WithdrawalRequest.FeeLoop
import Blanc.Lift.RequestFee.Getter

/-!
Postloop word division and calldata/value guards. Raw CALLDATASIZE is a
word conversion, so these fragment interfaces keep its exact word guards.
The selected continuations start before getter memory or submission stores.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

export RequestFee (postloopFixedGas getterGuardGas)

/-- JUMPDEST/CALLVALUE/LT/PUSH/JUMPI. -/
def submissionGuardGas : Nat := gJumpdest + gBase + 2 * gVerylow + gHigh

/-- The selected postloop path ends before its memory/storage body. -/
def userFeeDispatchGas (sevm : Sevm) : Nat :=
  postloopFixedGas + if sevm.data.length.toB256 = 56 then submissionGuardGas else getterGuardGas

theorem submissionGuardGas_eq : submissionGuardGas = 19 := rfl

theorem userFeeDispatchGas_eq (sevm : Sevm) :
    userFeeDispatchGas sevm = if sevm.data.length.toB256 = 56 then 64 else 75 := by
  by_cases h : sevm.data.length.toB256 = 56
  · simp only [userFeeDispatchGas, RequestFee.postloopFixedGas_eq, submissionGuardGas_eq, ite_eq_left h]
  · simp only [userFeeDispatchGas, RequestFee.postloopFixedGas_eq, RequestFee.getterGuardGas_eq, ite_eq_right h]

private def feeBranch (sevm : Sevm) : SFunc :=
  if sevm.data.length.toB256 = 56 then t_0088_c0 else t_0078_c0

private def lenWord : RequestFee.PushWord := ⟨0x38, [], by decide⟩
private def submissionDest : RequestFee.PushWord := ⟨0x88, [], by decide⟩
private def revertDest : RequestFee.PushWord := ⟨0x01, [0xf4], by decide⟩

private theorem prefix_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator : B256} {o : Outcome}
    (run : SFunc.Run prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M G) t_0068_c0 o) :
    ∃ G', SFunc.Run prog sevm (St b [output / denominator] M G') (feeBranch sevm) o :=
  RequestFee.postloop_inv (len := lenWord) (dest := submissionDest) rfl run

private theorem prefix_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator : B256} {o : Outcome}
    (tail : SFunc.RunExact prog sevm (St b [output / denominator] M G) (feeBranch sevm) o) :
    SFunc.RunExact prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + 45)) t_0068_c0 o :=
  RequestFee.postloop_exact (len := lenWord) (dest := submissionDest) rfl tail

private theorem getter_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {fee : B256} {o : Outcome}
    (run : SFunc.Run prog sevm (St b [fee] M G) t_0078_c0 o) :
    sevm.data.length.toB256 = 0 ∧ sevm.value = 0 ∧
      ∃ G', SFunc.Run prog sevm (St b [fee] M G') t_0082_c0 o :=
  RequestFee.guard_inv (dest := revertDest) (accept := t_0082_c0) (revert := t_01f4_c0) rfl run

private theorem getter_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {fee : B256} {o : Outcome} (empty : sevm.data.length.toB256 = 0) (zero : sevm.value = 0)
    (tail : SFunc.RunExact prog sevm (St b [fee] M G) t_0082_c0 o) :
    SFunc.RunExact prog sevm (St b [fee] M (G + 30)) t_0078_c0 o :=
  RequestFee.guard_exact (dest := revertDest) (revert := t_01f4_c0) empty zero tail

private theorem submission_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {fee : B256} {o : Outcome}
    (run : SFunc.Run prog sevm (St b [fee] M G) t_0088_c0 o) :
    fee.toNat ≤ sevm.value.toNat ∧
      ∃ G', SFunc.Run prog sevm (St b [] M G') t_008f_c0 o := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  winv 3
  rcases ric_branch run with ⟨paid, G', run⟩ | ⟨_, _, run⟩
  · exact ⟨toNat_ge_of_ltCheck_eq_zero paid, G', run.uncut⟩
  · exact False.elim (revert_tail_no_run run.uncut)

private theorem submission_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {fee : B256} {o : Outcome} (paid : fee.toNat ≤ sevm.value.toNat)
    (tail : SFunc.RunExact prog sevm (St b [] M G) t_008f_c0 o) :
    SFunc.RunExact prog sevm (St b [fee] M (G + 19)) t_0088_c0 o := by
  have hgas : G + 19 = G + 10 + 3 + 3 + 2 + 1 := by
    simp only [Nat.add_assoc]
  have hnot : ¬ sevm.value < fee := by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt_of_ge paid
  rw [hgas]
  unfold t_0088_c0
  refine rx_dest ?_
  refine rx_callvalue (by change 1 < 1024; decide) ?_
  refine rx_lt (v := 0) ?_ (by decide) ?_
  · simp only [B256.ltCheck, ite_eq_right hnot]
  · refine rx_push rfl (by change 1 < 1024; decide) ?_
    exact rx_branch_zero tail

/-- Success reaches exactly an adequately paid submission or a zero-value getter. -/
theorem user_fee_dispatch_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator : B256} {o : Outcome}
    (run : SFunc.Run prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M G) t_0068_c0 o) :
    (sevm.data.length.toB256 = 56 ∧ (output / denominator).toNat ≤ sevm.value.toNat ∧
      ∃ G', SFunc.Run prog sevm (St b [] M G') t_008f_c0 o) ∨
    (sevm.data.length.toB256 = 0 ∧ sevm.value = 0 ∧
      ∃ G', SFunc.Run prog sevm (St b [output / denominator] M G') t_0082_c0 o) := by
  obtain ⟨_, run⟩ := prefix_inv run
  by_cases hlen : sevm.data.length.toB256 = 56
  · simp only [feeBranch, ite_eq_left hlen] at run
    exact .inl ⟨hlen, submission_inv run⟩
  · simp only [feeBranch, ite_eq_right hlen] at run
    exact .inr (getter_inv run)


/-- Either visible accepted exit continuation transports through its exact selected charge. -/
theorem user_fee_dispatch_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {output accumulator counter numerator denominator : B256} {o : Outcome}
    (tail :
      (sevm.data.length.toB256 = 56 ∧ (output / denominator).toNat ≤ sevm.value.toNat ∧
        SFunc.RunExact prog sevm (St b [] M G) t_008f_c0 o) ∨
      (sevm.data.length.toB256 = 0 ∧ sevm.value = 0 ∧
        SFunc.RunExact prog sevm (St b [output / denominator] M G) t_0082_c0 o)) :
    SFunc.RunExact prog sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + userFeeDispatchGas sevm))
      t_0068_c0 o := by
  rcases tail with ⟨hlen, paid, tail⟩ | ⟨empty, zero, tail⟩
  · rw [userFeeDispatchGas_eq, ite_eq_left hlen]
    have hgas : G + 64 = G + 19 + 45 := by simp only [Nat.add_assoc]
    rw [hgas]
    apply prefix_exact
    simp only [feeBranch, ite_eq_left hlen]
    exact submission_exact paid tail
  · have hlen : sevm.data.length.toB256 ≠ 56 := by rw [empty]; decide
    rw [userFeeDispatchGas_eq, ite_eq_right hlen]
    have hgas : G + 75 = G + 30 + 45 := by simp only [Nat.add_assoc]
    rw [hgas]
    apply prefix_exact
    simp only [feeBranch, ite_eq_right hlen]
    exact getter_exact empty zero tail

/-- Successful canonical user execution reaches one accepted memory/storage boundary. -/
theorem exec_user_fee_dispatch {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = Blanc.withdrawalRequestCode)
    (hfork : CoveredFork sevm.benvStat.fork) (hstack : pre.stack = [])
    (user : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post)) :
    pre.getStorVal sevm.currentTarget 0 ≠ B256.max ∧
    ∃ iterations finalOutput,
      WordFakeExponential.Run (pre.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput ∧
      ((sevm.data.length.toB256 = 56 ∧ (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat ∧
        ∃ G, SFunc.Run prog sevm (St (afterSload sevm pre 0) [] pre.memory G) t_008f_c0 (.halted post)) ∨
       (sevm.data.length.toB256 = 0 ∧ sevm.value = 0 ∧
        ∃ G, SFunc.Run prog sevm (St (afterSload sevm pre 0) [finalOutput / (17 : B256)] pre.memory G)
          t_0082_c0 (.halted post))) := by
  obtain ⟨active, iterations, finalOutput, wordRun, _, _, run⟩ :=
    exec_fee_loop hcode hfork hstack user exec
  exact ⟨active, iterations, finalOutput, wordRun, user_fee_dispatch_inv run⟩

/-- Visible accepted body continuations construct the whole user prefix through fee dispatch. -/
theorem user_fee_prefix_exact {sevm : Sevm} {b : Devm} {M : Mem} {G iterations : Nat}
    {finalOutput : B256} {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork)
    (active : b.getStorVal sevm.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (b.getStorVal sevm.currentTarget 0) 17 1 17 0 iterations finalOutput)
    (tail :
      (sevm.data.length.toB256 = 56 ∧ (finalOutput / (17 : B256)).toNat ≤ sevm.value.toNat ∧
        SFunc.RunExact prog sevm (St (afterSload sevm b 0) [] M G) t_008f_c0 o) ∨
      (sevm.data.length.toB256 = 0 ∧ sevm.value = 0 ∧
        SFunc.RunExact prog sevm (St (afterSload sevm b 0) [finalOutput / (17 : B256)] M G) t_0082_c0 o)) :
    SFunc.RunExact prog sevm
      (St b [] M (G + userFeeDispatchGas sevm + feeLoopGas iterations + userSetupGas sevm b))
      t_001a_c0 o := by
  apply user_fee_loop_exact hfork active wordRun
  intro finalCounter
  exact user_fee_dispatch_exact tail

end Blanc.Lift.WithdrawalRequest
