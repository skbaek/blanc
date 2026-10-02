import Blanc.Lift.WithdrawalRequest.ModelBounds

/-!
A symbolic obstruction to preserving the Nat fee domain on the original
specification history, even with its existing model resource certificate.
This module makes no claim about EVM executions or configured histories.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune
open Blanc.WithdrawalRequest

private theorem zero_excess_history (entry : Blanc.WithdrawalRequest.Entry)
    (bound k : Nat) (within : k ≤ bound) :
    ∃ (state : Blanc.WithdrawalRequest.State) (submissions : List Submission)
      (outputs : List Blanc.WithdrawalRequest.Entry)
      (history : History initial state submissions outputs),
      ModelResources bound history ∧ state.excess = 0 ∧ state.count = k ∧
        submissions.length = k ∧ (submissions.map Submission.value).sum = k := by
  induction k with
  | zero =>
    exact ⟨Blanc.WithdrawalRequest.system initial, [], [] ++ emitted initial,
      History.system History.start, ModelResources.system ModelResources.start,
      rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨state, submissions, outputs, history, resources, zero, count, length, total⟩ :=
      ih (by omega)
    have enabled : state.excess ≠ excessInhibitor := by
      rw [zero]
      decide
    have paid : fee state ≤ (⟨entry, 1⟩ : Submission).value := by
      rw [fee_at_zero_excess state zero]
    have countBound : (submit state entry).count ≤ bound := by
      rw [submit_count, count]
      omega
    refine ⟨submit state entry, submissions ++ [⟨entry, 1⟩], outputs,
      History.submit history ⟨entry, 1⟩ enabled paid,
      ModelResources.submit (submission := ⟨entry, 1⟩) (enabled := enabled) (paid := paid) resources
        (by change (1 : Nat) < 2 ^ 256; decide) countBound,
      zero, ?_, ?_, ?_⟩
    · rw [submit_count, count]
    · rw [List.length_append, List.length_singleton, length]
    · simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
      rw [total]

/-- The original Nat model and resource certificate admit terminal states
outside every Nat fee no-wrap domain, while recording a word-sized total
payment. No later accepted submission or actual execution is asserted. -/
theorem model_resources_fee_domain_limit (entry : Blanc.WithdrawalRequest.Entry)
    (n : Nat) (large : natFeeExcessCeiling + 2 ≤ n) (cap : n ≤ 2 * 2 ^ 64) :
    ∃ (state : Blanc.WithdrawalRequest.State) (submissions : List Submission)
      (outputs : List Blanc.WithdrawalRequest.Entry)
      (history : History initial state submissions outputs),
      ModelResources n history ∧ submissions.length = n ∧
        (submissions.map Submission.value).sum = n ∧ n < 2 ^ 256 ∧
        state.excess = n - 2 ∧
        (∀ iterations, ¬ NatFeeDomain state.excess.toB256 iterations) ∧
        (∀ value : B256, ¬ fee state ≤ value.toNat) := by
  obtain ⟨state, submissions, outputs, history, resources, zero, count, length, total⟩ :=
    zero_excess_history entry n n (Nat.le_refl n)
  have capWidth : 2 * (2 : Nat) ^ 64 < 2 ^ 256 := by decide
  have paymentWidth : n < 2 ^ 256 := by omega
  have zeroEnabled : (0 : Nat) ≠ excessInhibitor := by decide
  have excessEq : (Blanc.WithdrawalRequest.system state).excess = n - 2 := by
    rw [system_excess]
    simp only [effectiveExcess, zero, ite_eq_right zeroEnabled, Nat.zero_add,
      count, targetPerBlock]
  have excessLarge : natFeeExcessCeiling ≤ (Blanc.WithdrawalRequest.system state).excess := by
    rw [excessEq]
    omega
  have excessWidth : (Blanc.WithdrawalRequest.system state).excess < 2 ^ 256 := by
    rw [excessEq]
    omega
  refine ⟨Blanc.WithdrawalRequest.system state, submissions, outputs ++ emitted state,
    History.system history, ModelResources.system resources, length, total,
    paymentWidth, excessEq, ?_, ?_⟩
  · intro iterations domain
    have small := domain.excess_lt
    rw [B256.toNat_toB256_of_lt excessWidth] at small
    omega
  · intro value paid
    have small := nat_paid_excess_lt (Blanc.WithdrawalRequest.system state) value paid
    omega

end Blanc.Lift.WithdrawalRequest
