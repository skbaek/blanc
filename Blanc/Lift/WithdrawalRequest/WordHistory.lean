import Blanc.WordFakeExponential
import Blanc.Lift.WithdrawalRequest.SubmissionLayout

/-!
Word-fee admission variant of the EIP-7002 model history. Submissions are
admitted exactly when the bytecode's executed word fee at the represented
excess is paid; the unchanged Nat-priced `History` remains the reference model.
Bookkeeping margins are derived from the number of recorded submissions alone,
not from any payment, balance or fee-domain premise.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.WithdrawalRequest

/-- The bytecode's executed word fee at the model excess, paid by `value`. -/
def WordFeePaid (state : Blanc.WithdrawalRequest.State) (value : Nat) : Prop :=
  ∃ iterations output, WordFakeExponential.Run state.excess.toB256 17 1 17 0 iterations output ∧
    (output / (17 : B256)).toNat ≤ value

/-- Replay of word-fee-admitted submissions and system steps from a checkpoint.
The transitions are the original specification's `submit` and `system`. -/
inductive WordHistory (checkpoint : Blanc.WithdrawalRequest.State) :
    Blanc.WithdrawalRequest.State → List Submission → List Blanc.WithdrawalRequest.Entry → Prop
  | start : WordHistory checkpoint checkpoint [] []
  | submit {state submissions outputs} (history : WordHistory checkpoint state submissions outputs)
      (submission : Submission) (enabled : state.excess ≠ excessInhibitor)
      (paid : WordFeePaid state submission.value) :
      WordHistory checkpoint (Blanc.WithdrawalRequest.submit state submission.entry)
        (submissions ++ [submission]) outputs
  | system {state submissions outputs} (history : WordHistory checkpoint state submissions outputs) :
      WordHistory checkpoint (Blanc.WithdrawalRequest.system state) submissions
        (outputs ++ emitted state)

/-- Exact ordered conservation under word-fee admission. -/
theorem WordHistory.conservation {checkpoint state : Blanc.WithdrawalRequest.State}
    {submissions : List Submission} {outputs : List Blanc.WithdrawalRequest.Entry}
    (history : WordHistory checkpoint state submissions outputs) :
    checkpoint.queue ++ submissions.map Submission.entry = outputs ++ state.queue := by
  induction history with
  | start => simp only [List.map_nil, List.append_nil, List.nil_append]
  | submit history submission enabled paid ih =>
    simp only [List.map_append, List.map_singleton, submit_queue]
    rw [← List.append_assoc, ih, List.append_assoc]
  | system history ih =>
    change checkpoint.queue ++ List.map Submission.entry _ =
      (_ ++ List.take maxPerBlock _) ++ List.drop maxPerBlock _
    rw [List.append_assoc, List.take_append_drop]
    exact ih

/-- The occurrence cap of the word-regime margin: `3 * cap + 6 < 2 ^ 256`. -/
def wordOccurrenceCap : Nat := 2 ^ 254

/-- Bookkeeping margins measured by the number of recorded submissions. -/
structure WordMargin (occurrences : Nat) (state : Blanc.WithdrawalRequest.State) : Prop where
  excess_count_le : effectiveExcess state + state.count ≤ occurrences
  tail_le : state.tail ≤ occurrences
  coherent : Coherent state

private theorem effectiveExcess_le_excess (state : Blanc.WithdrawalRequest.State) :
    effectiveExcess state ≤ state.excess := by
  by_cases inhibited : state.excess = excessInhibitor
  · rw [effectiveExcess, ite_eq_left inhibited]
    exact Nat.zero_le _
  · rw [effectiveExcess, ite_eq_right inhibited]

/-- From INIT, excess plus pending count and the queue tail never exceed the
number of word-admitted submissions recorded so far. -/
theorem WordHistory.margin {state : Blanc.WithdrawalRequest.State}
    {submissions : List Submission} {outputs : List Blanc.WithdrawalRequest.Entry}
    (history : WordHistory initial state submissions outputs) :
    WordMargin submissions.length state := by
  induction history with
  | start =>
    refine ⟨?_, Nat.le_refl 0, initial_coherent⟩
    simp only [Blanc.WithdrawalRequest.initial, effectiveExcess, ite_true, Nat.zero_add,
      List.length_nil, Nat.le_refl]
  | @submit state submissions outputs history submission enabled paid ih =>
    have old := ih.excess_count_le
    have oldTail := ih.tail_le
    refine ⟨?_, ?_, submit_coherent ih.coherent submission.entry⟩
    · have same : effectiveExcess (Blanc.WithdrawalRequest.submit state submission.entry) =
          effectiveExcess state := rfl
      rw [same, submit_count, List.length_append, List.length_singleton]
      omega
    · simp only [Blanc.WithdrawalRequest.submit, List.length_append, List.length_singleton]
      omega
  | @system state submissions outputs history ih =>
    have old := ih.excess_count_le
    have oldTail := ih.tail_le
    have next := effectiveExcess_le_excess (Blanc.WithdrawalRequest.system state)
    rw [system_excess, targetPerBlock] at next
    refine ⟨?_, ?_, system_coherent ih.coherent⟩
    · rw [system_count, Nat.add_zero]
      omega
    · by_cases drained : state.queue.length ≤ maxPerBlock
      · rw [(system_drained_pointers state drained).2]
        exact Nat.zero_le _
      · rw [(system_live_pointers state drained).2]
        exact oldTail

/-- Every bookkeeping word fits and the queue never reaches slots 0–3, for
any state reached with at most `wordOccurrenceCap` recorded submissions. -/
theorem WordMargin.bounds {occurrences : Nat} {state : Blanc.WithdrawalRequest.State}
    (margin : WordMargin occurrences state) (cap : occurrences ≤ wordOccurrenceCap) :
    effectiveExcess state ≤ wordOccurrenceCap ∧ state.count ≤ wordOccurrenceCap ∧
      state.head ≤ state.tail ∧ state.tail ≤ wordOccurrenceCap ∧
      state.queue.length = state.tail - state.head ∧
      effectiveExcess state + state.count < 2 ^ 256 ∧
      queueBase state.tail + 2 < 2 ^ 256 := by
  have sum := margin.excess_count_le
  have tail := margin.tail_le
  have coherent := margin.coherent
  change state.head + state.queue.length = state.tail at coherent
  have fits : 3 * wordOccurrenceCap + 6 < 2 ^ 256 := by decide
  simp only [queueBase]
  omega

/-- The prospective margins of the next submission when it is still within the cap. -/
theorem WordMargin.submission_bounds {occurrences : Nat} {state : Blanc.WithdrawalRequest.State}
    (margin : WordMargin occurrences state) (room : occurrences + 1 ≤ wordOccurrenceCap) :
    SubmissionBounds state := by
  have sum := margin.excess_count_le
  have tail := margin.tail_le
  have fits : 3 * wordOccurrenceCap + 6 < 2 ^ 256 := by decide
  constructor
  · omega
  · simp only [queueBase]
    omega

end Blanc.Lift.WithdrawalRequest
