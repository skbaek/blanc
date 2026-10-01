import Blanc.Lift.WithdrawalRequest.WordReplay

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionAccountingReplay

/-- The actually admitted word price; system calls and getters contribute zero. -/
def wordEventPrice (event : WordReplayEvent) : Nat :=
  match event.kind with
  | .submission _ _ output => (output / (17 : B256)).toNat
  | .system | .getter _ _ => 0

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

/-- The exact committed replay events share the retained message-value budget. -/
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
      (future.state.bal withdrawalRequestPredeployAddress).toNat < 2 ^ 256 := by
  obtain ⟨events, replay, observed⟩ := history_word_storage_replay trace code
  have values := history_message_values_bound trace code
  rw [← observed, List.map_map] at values
  refine ⟨events, replay, observed, ?_, B256.toNat_lt _⟩
  exact Nat.le_trans (Nat.add_le_add_left replay.price_sum_le _) values

/-- Every list prefix of these same replay events fits within the final retained balance. -/
theorem history_word_fee_prefix_budget {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    ∃ events : List WordReplayEvent,
      WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress) events
        (future.state.getStor withdrawalRequestPredeployAddress) ∧
      events.map WordReplayEvent.frame = trace.settledFrames.flatMap balanceFrameObservation ∧
      (future.state.bal withdrawalRequestPredeployAddress).toNat < 2 ^ 256 ∧
      ∀ left right : List WordReplayEvent, events = left ++ right →
        (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat +
            (left.map wordEventPrice).sum ≤
          (future.state.bal withdrawalRequestPredeployAddress).toNat := by
  obtain ⟨events, replay, observed, budget, wordBound⟩ := history_word_fee_budget trace code
  refine ⟨events, replay, observed, wordBound, ?_⟩
  intro left right split
  rw [split, List.map_append, List.sum_append] at budget
  omega

end Blanc.Lift.WithdrawalRequest
