import Blanc.Lift.WithdrawalRequest.NatFeeBound
import Blanc.Lift.WithdrawalRequest.SubmissionLayout

/-!
Model-side queue and bookkeeping bounds on the existing Nat-priced history.
The resource certificate adds only word-sized submission values and a prefix
count cap. It does not certify actual EVM history admission or fee no-wrap.
-/

namespace Blanc.Lift.WithdrawalRequest
open Jaune
open Blanc.WithdrawalRequest

/-- Resource facts indexed by the unchanged specification history. Every
submission is already enabled and Nat-paid in that history. -/
inductive ModelResources (bound : Nat) :
    {state : Blanc.WithdrawalRequest.State} → {submissions : List Submission} →
    {outputs : List Blanc.WithdrawalRequest.Entry} → History initial state submissions outputs → Prop
  | start : ModelResources bound History.start
  | submit {state submissions outputs} {history : History initial state submissions outputs}
      {submission : Submission} {enabled : state.excess ≠ excessInhibitor}
      {paid : fee state ≤ submission.value}
      (resources : ModelResources bound history)
      (wordValue : submission.value < 2 ^ 256)
      (countBound : (submit state submission.entry).count ≤ bound) :
      ModelResources bound (History.submit history submission enabled paid)
  | system {state submissions outputs} {history : History initial state submissions outputs}
      (resources : ModelResources bound history) :
      ModelResources bound (History.system history)

/-- Derived resource and queue-credit invariant; none of these fields is a
premise of ModelResources. -/
structure ModelBookkeeping (bound : Nat) (state : Blanc.WithdrawalRequest.State) : Prop where
  count_le : state.count ≤ bound
  resource_lt : effectiveExcess state + state.count < natFeeExcessCeiling + bound
  queue_credit : 8 * state.tail ≤ 8 * (effectiveExcess state + state.count) + state.head
  coherent : Coherent state
  empty_tail : state.queue = [] → state.tail = 0

private theorem ModelBookkeeping.initial (bound : Nat) :
    ModelBookkeeping bound initial := by
  constructor
  · exact Nat.zero_le _
  · simp only [Blanc.WithdrawalRequest.initial, effectiveExcess, ite_true,
      Nat.zero_add, natFeeExcessCeiling]
    omega
  · simp only [Blanc.WithdrawalRequest.initial, effectiveExcess, ite_true,
      Nat.zero_add, Nat.mul_zero, Nat.le_refl]
  · exact initial_coherent
  · intro empty
    rfl

private theorem ModelBookkeeping.submit {bound : Nat} {state : Blanc.WithdrawalRequest.State}
    (invariant : ModelBookkeeping bound state) (submission : Submission)
    (enabled : state.excess ≠ excessInhibitor) (paid : fee state ≤ submission.value)
    (wordValue : submission.value < 2 ^ 256)
    (countBound : (submit state submission.entry).count ≤ bound) :
    ModelBookkeeping bound (submit state submission.entry) := by
  have paidWord : fee state ≤ submission.value.toB256.toNat := by
    rw [B256.toNat_toB256_of_lt wordValue]
    exact paid
  have excessLt := nat_paid_excess_lt state submission.value.toB256 paidWord
  have oldCredit := invariant.queue_credit
  simp only [effectiveExcess, ite_eq_right enabled] at oldCredit
  constructor
  · exact countBound
  · dsimp only [Blanc.WithdrawalRequest.submit]
    simp only [effectiveExcess, ite_eq_right enabled]
    change state.count + 1 ≤ bound at countBound
    omega
  · dsimp only [Blanc.WithdrawalRequest.submit]
    simp only [effectiveExcess, ite_eq_right enabled]
    omega
  · exact submit_coherent invariant.coherent submission.entry
  · intro empty
    have lengths := congrArg List.length empty
    simp only [Blanc.WithdrawalRequest.submit, List.length_append,
      List.length_singleton, List.length_nil] at lengths
    omega

private theorem ModelBookkeeping.system {bound : Nat} {state : Blanc.WithdrawalRequest.State}
    (invariant : ModelBookkeeping bound state)
    (margin : natFeeExcessCeiling + bound ≤ excessInhibitor) :
    ModelBookkeeping bound (Blanc.WithdrawalRequest.system state) := by
  have oldSumLt := invariant.resource_lt
  have oldCredit := invariant.queue_credit
  have nextLt : (Blanc.WithdrawalRequest.system state).excess < natFeeExcessCeiling + bound := by
    rw [system_excess]
    omega
  have nextEnabled : (Blanc.WithdrawalRequest.system state).excess ≠ excessInhibitor := by omega
  have nextEffective : effectiveExcess (Blanc.WithdrawalRequest.system state) =
      effectiveExcess state + state.count - 2 := by
    rw [effectiveExcess, ite_eq_right nextEnabled, system_excess, targetPerBlock]
  constructor
  · rw [system_count]
    exact Nat.zero_le _
  · rw [system_count, Nat.add_zero]
    simp only [effectiveExcess, ite_eq_right nextEnabled]
    exact nextLt
  · by_cases drained : state.queue.length ≤ maxPerBlock
    · have pointers := system_drained_pointers state drained
      rw [pointers.1, pointers.2]
      exact Nat.zero_le _
    · have pointers := system_live_pointers state drained
      have large : 16 < state.queue.length := by
        change ¬ state.queue.length ≤ 16 at drained
        omega
      have length : (emitted state).length = 16 := by
        rw [emitted_length]
        change min 16 state.queue.length = 16
        omega
      rw [pointers.1, pointers.2, nextEffective, system_count, Nat.add_zero, length]
      omega
  · exact system_coherent invariant.coherent
  · intro empty
    have length := congrArg List.length empty
    rw [system_queue] at length
    simp only [List.length_drop, List.length_nil] at length
    have drained : state.queue.length ≤ maxPerBlock := by omega
    exact (system_drained_pointers state drained).2

/-- The invariant is derived from INIT on exactly the certified history. -/
theorem ModelResources.bookkeeping {bound : Nat}
    {state : Blanc.WithdrawalRequest.State} {submissions : List Submission}
    {outputs : List Blanc.WithdrawalRequest.Entry} {history : History initial state submissions outputs}
    (resources : ModelResources bound history)
    (margin : natFeeExcessCeiling + bound ≤ excessInhibitor) :
    ModelBookkeeping bound state := by
  induction resources with
  | start => exact ModelBookkeeping.initial bound
  | @submit state submissions outputs history submission enabled paid resources wordValue countBound ih =>
    exact ModelBookkeeping.submit ih submission enabled paid wordValue countBound
  | system resources ih => exact ModelBookkeeping.system ih margin

/-- Concrete prospective storage margins derived from the resource certificate.
This is a model theorem, not an actual-trace admission certificate. -/
theorem ModelResources.prospective_margins
    {state : Blanc.WithdrawalRequest.State} {submissions : List Submission}
    {outputs : List Blanc.WithdrawalRequest.Entry} {history : History initial state submissions outputs}
    (resources : ModelResources (2 ^ 64) history) :
    SubmissionBounds state ∧ effectiveExcess state + state.count < 2 ^ 256 := by
  have inhibitorMargin : natFeeExcessCeiling + 2 ^ 64 ≤ excessInhibitor := by decide
  have resourceMargin : natFeeExcessCeiling + 2 ^ 64 < 2 ^ 256 := by decide
  have countMargin : (2 : Nat) ^ 64 + 1 < 2 ^ 256 := by decide
  have slotMargin :
      24 * (natFeeExcessCeiling + 2 ^ 64) + 42 ≤ 7 * 2 ^ 256 := by decide
  have invariant := resources.bookkeeping inhibitorMargin
  have resourceLt := invariant.resource_lt
  have credit := invariant.queue_credit
  have coherent := invariant.coherent
  change state.head + state.queue.length = state.tail at coherent
  constructor
  · constructor
    · have countLe := invariant.count_le
      omega
    · simp only [queueBase]
      by_cases empty : state.queue = []
      · have tailZero := invariant.empty_tail empty
        omega
      · have lengthPos := List.length_pos_iff_ne_nil.mpr empty
        omega
  · exact Nat.lt_trans resourceLt resourceMargin

end Blanc.Lift.WithdrawalRequest
