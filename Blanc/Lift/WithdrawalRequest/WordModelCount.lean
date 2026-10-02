import Blanc.Lift.WithdrawalRequest.WordModelReplay
import Blanc.Lift.WithdrawalRequest.ResetOccurrence
import Blanc.ExecutionRequestSegments
import Blanc.ExecutionBodyGas

/-!
The unchanged initial model's count along actual ordered word events. The
canonical withdrawal occurrence resets this count once per configured block;
the actual full-block frame bound controls every intervening event prefix.
No Nat payment, fee-domain or incoming storage representation is assumed.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionAccountingReplay ExecutionTrace Blanc.WithdrawalRequest

private theorem WordReplayGuard.system_kind {storage : Stor} {event : WordReplayEvent}
    (guard : WordReplayGuard storage event)
    (caller : event.frame.sevm.caller = systemAddress) : event.kind = .system := by
  cases kind : event.kind with
  | system => rfl
  | submission entry iterations output =>
    have input := guard.input
    simp only [wordEventInput, kind] at input
    exact False.elim (input.1 caller)
  | getter iterations output =>
    have input := guard.input
    simp only [wordEventInput, kind] at input
    exact False.elim (input.1 caller)

private theorem WordStorageReplay.system_kinds {pre post : Stor} {events : List WordReplayEvent}
    (replay : WordStorageReplay pre events post) :
    ∀ event ∈ events, event.frame.sevm.caller = systemAddress → event.kind = .system := by
  induction replay with
  | nil =>
    intro event member
    exact False.elim (List.not_mem_nil member)
  | cons guard tail ih =>
    intro event member caller
    rcases List.mem_cons.mp member with head | rest
    · subst event
      exact guard.system_kind caller
    · exact ih event rest caller

private theorem wordModelUpdate_count_le (state : Blanc.WithdrawalRequest.State)
    (event : WordReplayEvent) : (wordModelUpdate state event).count ≤ state.count + 1 := by
  cases kind : event.kind <;>
    simp only [wordModelUpdate, kind, system_count, submit_count] <;> omega

private theorem wordModelFold_count_le (events : List WordReplayEvent)
    (state : Blanc.WithdrawalRequest.State) :
    (events.foldl wordModelUpdate state).count ≤ state.count + events.length := by
  induction events generalizing state with
  | nil => exact Nat.le_refl _
  | cons event events ih =>
    have rest := ih (wordModelUpdate state event)
    have step := wordModelUpdate_count_le state event
    simp only [List.foldl_cons, List.length_cons]
    omega

private theorem balanceObservation_length_le (frames : List Exec.Frame) :
    (frames.flatMap balanceFrameObservation).length ≤ frames.length := by
  induction frames with
  | nil => exact Nat.le_refl _
  | cons frame frames ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    by_cases observed : frame.sevm.currentTarget = withdrawalRequestPredeployAddress ∧
        frame.sevm.isStatic = false
    · simp only [balanceFrameObservation, ite_eq_left observed, List.length_singleton]
      omega
    · simp only [balanceFrameObservation, ite_eq_right observed, List.length_nil]
      omega

private theorem blockEvents_count_lt {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (events : List WordReplayEvent)
    (observed : events.map WordReplayEvent.frame = block.settledFrames.flatMap balanceFrameObservation)
    (systemKinds : ∀ event ∈ events,
      event.frame.sevm.caller = systemAddress → event.kind = .system)
    (state : Blanc.WithdrawalRequest.State) :
    (events.foldl wordModelUpdate state).count < 2 ^ 64 := by
  obtain ⟨frame, frames, target, caller, dynamic, preEq, postEq, storage, reset, view, payments⟩ :=
    block_requests_reset_occurrence history block code
  have mapped : events.map WordReplayEvent.frame =
      (block.beforeWithdrawalFrames.flatMap balanceFrameObservation) ++
        frame :: (block.afterWithdrawalFrames.flatMap balanceFrameObservation) := by
    rw [observed]
    simp only [ConfiguredBlockTrace.settledFrames, AppliedBodyTrace.settledFrames,
      RequestsTrace.settledFrames, ConfiguredBlockTrace.beforeWithdrawalFrames,
      ConfiguredBlockTrace.afterWithdrawalFrames, List.flatMap_append, view,
      List.append_assoc, List.singleton_append]
  obtain ⟨before, remaining, equality, beforeMap, remainingMap⟩ := List.map_eq_append_iff.mp mapped
  obtain ⟨event, after, remainingEq, frameEq, afterMap⟩ := List.map_eq_cons_iff.mp remainingMap
  have resetKind : event.kind = .system := systemKinds event (by
    rw [equality, remainingEq]
    exact List.mem_append_right before (List.mem_cons_self)) (by rw [frameEq]; exact caller)
  have count := wordModelFold_count_le after
    (wordModelUpdate (before.foldl wordModelUpdate state) event)
  have fullLength : events.length < 2 ^ 64 := by
    have lengthEq := congrArg List.length observed
    rw [List.length_map] at lengthEq
    exact Nat.lt_of_le_of_lt (lengthEq ▸ balanceObservation_length_le block.settledFrames)
      block.settledFrames_length_lt
  rw [equality, remainingEq, List.foldl_append, List.foldl_cons]
  simp only [wordModelUpdate, resetKind, system_count] at count ⊢
  simp only [equality, remainingEq, List.length_append, List.length_cons] at fullLength
  omega

private theorem historyEvents_count_lt {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (events : List WordReplayEvent)
    (observed : events.map WordReplayEvent.frame = trace.settledFrames.flatMap balanceFrameObservation)
    (systemKinds : ∀ event ∈ events,
      event.frame.sevm.caller = systemAddress → event.kind = .system) :
    (events.foldl wordModelUpdate initial).count < 2 ^ 64 ∧
      ∀ beforeEvents, beforeEvents <+: events →
        (beforeEvents.foldl wordModelUpdate initial).count < 2 * 2 ^ 64 := by
  induction trace generalizing events with
  | refl valid context chainId =>
    simp only [ConfiguredHistoryTrace.settledFrames, List.flatMap_nil] at observed
    have empty := List.eq_nil_of_map_eq_nil observed
    subst events
    constructor
    · decide
    · intro beforeEvents preceding
      have prefixEmpty := List.eq_nil_of_prefix_nil preceding
      subst beforeEvents
      decide
  | @step current future prior block ih =>
    simp only [ConfiguredHistoryTrace.settledFrames, List.flatMap_append] at observed
    obtain ⟨earlier, currentEvents, equality, earlierMap, currentMap⟩ :=
      List.map_eq_append_iff.mp observed
    subst events
    have earlierKinds : ∀ event ∈ earlier,
        event.frame.sevm.caller = systemAddress → event.kind = .system := by
      intro event member caller
      exact systemKinds event (List.mem_append_left currentEvents member) caller
    have currentKinds : ∀ event ∈ currentEvents,
        event.frame.sevm.caller = systemAddress → event.kind = .system := by
      intro event member caller
      exact systemKinds event (List.mem_append_right earlier member) caller
    have previous := ih earlier earlierMap earlierKinds
    constructor
    · rw [List.foldl_append]
      exact blockEvents_count_lt prior block code currentEvents currentMap currentKinds
        (earlier.foldl wordModelUpdate initial)
    · intro beforeEvents preceding
      rcases List.prefix_or_prefix_of_prefix preceding
          (List.prefix_append earlier currentEvents) with oldPrefix | newPrefix
      · exact previous.2 beforeEvents oldPrefix
      · obtain ⟨inside, prefixEq⟩ := List.prefix_iff_exists_eq_append.mp newPrefix
        have insidePrefix : inside <+: currentEvents := by
          rw [prefixEq, List.prefix_append_right_inj] at preceding
          exact preceding
        have count := wordModelFold_count_le inside (earlier.foldl wordModelUpdate initial)
        have insideLength := insidePrefix.length_le
        have currentLength : currentEvents.length < 2 ^ 64 := by
          have lengthEq := congrArg List.length currentMap
          rw [List.length_map] at lengthEq
          exact Nat.lt_of_le_of_lt (lengthEq ▸ balanceObservation_length_le block.settledFrames)
            block.settledFrames_length_lt
        rw [prefixEq, List.foldl_append]
        omega

/-- At every exact event prefix of the actual configured replay, the original
INITIAL MODEL FOLD count is below the two-block cap. This does not identify
the raw count slot and assumes neither Nat payment nor storage representation. -/
theorem history_word_model_prefix_count_lt {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    {events : List WordReplayEvent}
    (replay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress) events
      (future.state.getStor withdrawalRequestPredeployAddress))
    (observed : events.map WordReplayEvent.frame = trace.settledFrames.flatMap balanceFrameObservation) :
    ∀ beforeEvents, beforeEvents <+: events →
      (beforeEvents.foldl wordModelUpdate initial).count < 2 * 2 ^ 64 :=
  (historyEvents_count_lt trace code events observed replay.system_kinds).2

/-- For the exact actual event list, only Nat payment remains needed by the
conditional model bridge; every submission's count cap is derived here. -/
theorem history_word_model_admission_of_nat_paid
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    {events : List WordReplayEvent}
    (replay : WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress) events
      (future.state.getStor withdrawalRequestPredeployAddress))
    (observed : events.map WordReplayEvent.frame = trace.settledFrames.flatMap balanceFrameObservation)
    (paid : ∀ before event after, events = before ++ event :: after →
      match event.kind with
      | .submission _ _ _ => fee (before.foldl wordModelUpdate initial) ≤ event.frame.sevm.value.toNat
      | _ => True) :
    WordModelAdmission (2 * 2 ^ 64) initial events := by
  intro before event after equality
  have payment := paid before event after equality
  cases kind : event.kind with
  | system => trivial
  | getter iterations output => trivial
  | submission entry iterations output =>
    have count := history_word_model_prefix_count_lt trace code replay observed (before ++ [event])
      (by
        refine ⟨after, ?_⟩
        rw [List.append_assoc, List.singleton_append]
        exact equality.symm)
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, wordModelUpdate, kind] at count
    simp only [kind] at payment ⊢
    exact ⟨payment, Nat.le_of_lt count⟩

end Blanc.Lift.WithdrawalRequest
