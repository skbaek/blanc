import Blanc.Lift.WithdrawalRequest.WordReplay
import Blanc.Lift.WithdrawalRequest.ModelBounds
import Blanc.Lift.WithdrawalRequest.SystemStorage

/-!
The actual guarded word replay read through the unchanged Nat-priced EIP model:
the per-event model update, the submissions and outputs it records, and the
storage representation each guarded occurrence preserves. No fee-domain
conclusion is assumed.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionAccountingReplay Blanc.WithdrawalRequest

/-- Each actual event uses the original specification transition. -/
def wordModelUpdate (state : Blanc.WithdrawalRequest.State) (event : WordReplayEvent) :
    Blanc.WithdrawalRequest.State :=
  match event.kind with
  | .system => Blanc.WithdrawalRequest.system state
  | .submission entry _ _ => submit state entry
  | .getter _ _ => state

/-- Actual occurrence values and entries, in replay order. -/
def wordModelSubmissions (events : List WordReplayEvent) : List Submission :=
  events.flatMap fun event =>
    match event.kind with
    | .submission entry _ _ => [⟨entry, event.frame.sevm.value.toNat⟩]
    | _ => []

/-- Output entries of the original model at each system occurrence. -/
def wordModelOutputs (state : Blanc.WithdrawalRequest.State) :
    List WordReplayEvent → List Blanc.WithdrawalRequest.Entry
  | [] => []
  | event :: events =>
    (match event.kind with | .system => emitted state | _ => []) ++
      wordModelOutputs (wordModelUpdate state event) events

theorem WordReplayGuard.enabled {storage : Stor}
    {state : Blanc.WithdrawalRequest.State} (rep : RepresentsStorage storage.get state)
    (active : storage.get 0 ≠ B256.max) : state.excess ≠ excessInhibitor := by
  intro inhibited
  apply active
  rw [rep.excess, inhibited]
  rfl

/-- The guarded raw system update inherits the typed storage theorem. -/
theorem wordSystemStorage_represents {storage : Stor} {event : WordReplayEvent}
    {state : Blanc.WithdrawalRequest.State} (guard : WordReplayGuard storage event)
    (rep : RepresentsStorage storage.get state)
    (sumBound : effectiveExcess state + state.count < 2 ^ 256) :
    RepresentsStorage (wordSystemStorage storage).get (Blanc.WithdrawalRequest.system state) := by
  have incoming : RepresentsStorage (event.frame.pre.getStorVal event.frame.sevm.currentTarget)
      state := by
    change RepresentsStorage (event.frame.pre.getStor event.frame.sevm.currentTarget).get state
    rw [guard.target, ← guard.pre]
    exact rep
  have outgoing := systemFramePost_represents event.frame.sevm event.frame.pre
    event.frame.pre.memory 0 state incoming sumBound
  change RepresentsStorage ((systemFramePost event.frame.sevm event.frame.pre
    event.frame.pre.memory 0).getStor event.frame.sevm.currentTarget).get
      (Blanc.WithdrawalRequest.system state) at outgoing
  rw [systemFramePost_word_storage, guard.target, ← guard.pre] at outgoing
  exact outgoing

/-- The guarded raw submission update inherits the typed storage theorem. -/
theorem wordSubmissionStorage_represents {storage : Stor} {event : WordReplayEvent}
    {state : Blanc.WithdrawalRequest.State} (guard : WordReplayGuard storage event)
    (rep : RepresentsStorage storage.get state) (bounds : SubmissionBounds state)
    (entry : Blanc.WithdrawalRequest.Entry) (caller : entry.caller = event.frame.sevm.caller)
    (payload : event.frame.sevm.data = submissionPayload entry) :
    RepresentsStorage (wordSubmissionStorage event.frame.sevm storage).get (submit state entry) := by
  have incoming : RepresentsStorage
      ((afterSload event.frame.sevm event.frame.pre 0).getStor event.frame.sevm.currentTarget).get
      state := by
    rw [afterSload_getStor, guard.target, ← guard.pre]
    exact rep
  have outgoing := submissionPost_represents event.frame.sevm
    (afterSload event.frame.sevm event.frame.pre 0) event.frame.pre.memory 0 state entry
    incoming bounds caller payload
  rw [submissionPost_word_storage, guard.target, ← guard.pre] at outgoing
  exact outgoing

end Blanc.Lift.WithdrawalRequest
