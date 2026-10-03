import Blanc.Lift.WithdrawalRequest.WordReplay
import Blanc.Lift.WithdrawalRequest.ExactFeeDomain
import Blanc.ExecutionAccountingStoragePrefix

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionAccountingReplay

/-- The actually admitted word price; system calls and getters contribute zero. -/
def wordEventPrice (event : WordReplayEvent) : Nat :=
  match event.kind with
  | .submission _ _ output => (output / (17 : B256)).toNat
  | .system | .getter _ _ => 0

/-- Payment at an actual submission's incoming storage, together with the
separate exact Nat correspondence domain. This does not identify the incoming
word with a replayed Nat model state or assert domain membership. -/
def WordReplayEvent.SubmissionFeeLaw (event : WordReplayEvent) : Prop :=
  let excess := (event.frame.pre.getStor withdrawalRequestPredeployAddress).get 0
  match event.kind with
  | .submission _ iterations output =>
    excess ≠ B256.max ∧
    WordFakeExponential.Run excess 17 1 17 0 iterations output ∧
    wordEventPrice event ≤ event.frame.sevm.value.toNat ∧
    wordEventPrice event ≤ fakeExp 1 excess.toNat 17 ∧
    (wordEventPrice event = fakeExp 1 excess.toNat 17 ↔ NatFeeDomain excess iterations)
  | .system | .getter _ _ => True

private theorem WordReplayGuard.submission_fee_law {storage : Stor} {event : WordReplayEvent}
    (guard : WordReplayGuard storage event) : event.SubmissionFeeLaw := by
  cases tag : event.kind with
  | system => simp only [WordReplayEvent.SubmissionFeeLaw, tag]
  | getter iterations output => simp only [WordReplayEvent.SubmissionFeeLaw, tag]
  | submission entry iterations output =>
    have input := guard.input
    simp only [wordEventInput, tag] at input
    obtain ⟨caller, entryCaller, payload, active, run, paid⟩ := input
    let model : Blanc.WithdrawalRequest.State :=
      { Blanc.WithdrawalRequest.initial with excess := (storage.get 0).toNat }
    have lower := word_fee_le_nat run model rfl
    have domain := word_fee_eq_iff_natFeeDomain run model rfl
    rw [WordReplayEvent.SubmissionFeeLaw, tag, ← guard.pre, wordEventPrice, tag]
    refine ⟨active, run, paid, ?_, ?_⟩
    · simpa only [Blanc.WithdrawalRequest.fee, model,
        Blanc.WithdrawalRequest.feeUpdateFraction] using lower
    · simpa only [Blanc.WithdrawalRequest.fee, model,
        Blanc.WithdrawalRequest.feeUpdateFraction] using domain

theorem WordReplayGuard.price_le {storage : Stor} {event : WordReplayEvent}
    (guard : WordReplayGuard storage event) :
    wordEventPrice event ≤ event.frame.sevm.value.toNat := by
  cases tag : event.kind with
  | system =>
    rw [wordEventPrice, tag]
    exact Nat.zero_le _
  | submission entry iterations output =>
    have input := guard.input
    simp only [wordEventInput, tag] at input
    simpa only [wordEventPrice, tag] using input.2.2.2.2.2
  | getter iterations output =>
    rw [wordEventPrice, tag]
    exact Nat.zero_le _

theorem WordStorageReplay.price_sum_le {pre post : Stor} {events : List WordReplayEvent}
    (replay : WordStorageReplay pre events post) :
    (events.map wordEventPrice).sum ≤
      (events.map (fun event => event.frame.sevm.value.toNat)).sum := by
  induction replay with
  | nil => exact Nat.le_refl 0
  | cons guard tail ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add guard.price_le ih

/-- Every actual committed submission paid the bytecode's word fee at its own
incoming storage. These same ordered events share the retained value budget.
The Nat comparison and exact equality domain are separate conclusions; no Nat
payment, domain membership or queue representation is assumed or derived. -/
theorem history_word_fee_budget {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    ∃ events : List WordReplayEvent,
      WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress) events
        (future.state.getStor withdrawalRequestPredeployAddress) ∧
      events.map WordReplayEvent.frame = trace.settledFrames.flatMap balanceFrameObservation ∧
      (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat +
          (events.map wordEventPrice).sum ≤
        (future.state.bal withdrawalRequestPredeployAddress).toNat ∧
      (future.state.bal withdrawalRequestPredeployAddress).toNat < 2 ^ 256 ∧
      (∀ event ∈ events, event.SubmissionFeeLaw) := by
  obtain ⟨events, replay, observed⟩ := history_word_storage_replay trace code
  have values := history_message_values_bound trace code
  rw [← observed, List.map_map] at values
  refine ⟨events, replay, observed, ?_, B256.toNat_lt _, ?_⟩
  · exact Nat.le_trans (Nat.add_le_add_left replay.price_sum_le _) values
  · intro event member
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp member
    exact replay.split.2.head_guard.submission_fee_law


end Blanc.Lift.WithdrawalRequest
