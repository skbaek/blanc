import Blanc.Lift.WithdrawalRequest.WordReplay
import Blanc.Lift.WithdrawalRequest.ModelBounds
import Blanc.Lift.WithdrawalRequest.SystemStorage

/-!
Conditional composition of the actual guarded word replay with the unchanged
Nat-priced EIP model. Nat payment and prefix submission counts remain open
admission obligations; no storage margin or fee-domain conclusion is assumed.
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

/-- Only unresolved Nat payment and count admission, at exact event prefixes.
The opening state can be any already-certified prefix of the same History. -/
def WordModelAdmission (bound : Nat) (state : Blanc.WithdrawalRequest.State)
    (events : List WordReplayEvent) : Prop :=
  ∀ before event after, events = before ++ event :: after →
    match event.kind with
    | .submission entry _ _ =>
      fee (before.foldl wordModelUpdate state) ≤ event.frame.sevm.value.toNat ∧
      (submit (before.foldl wordModelUpdate state) entry).count ≤ bound
    | _ => True

private theorem WordModelAdmission.tail {bound : Nat}
    {state : Blanc.WithdrawalRequest.State} {event : WordReplayEvent}
    {events : List WordReplayEvent} (admitted : WordModelAdmission bound state (event :: events)) :
    WordModelAdmission bound (wordModelUpdate state event) events := by
  intro before next after equality
  have original := admitted (event :: before) next after (by
    rw [List.cons_append, equality])
  simpa only [List.foldl_cons] using original

private theorem WordReplayGuard.enabled {storage : Stor}
    {state : Blanc.WithdrawalRequest.State} (rep : RepresentsStorage storage.get state)
    (active : storage.get 0 ≠ B256.max) : state.excess ≠ excessInhibitor := by
  intro inhibited
  apply active
  rw [rep.excess, inhibited]
  rfl

/-- The guarded raw system update inherits the typed storage theorem. -/
private theorem wordSystemStorage_represents {storage : Stor} {event : WordReplayEvent}
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
private theorem wordSubmissionStorage_represents {storage : Stor} {event : WordReplayEvent}
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

/-- Compose exact word occurrences into the same Nat-paid specification
history, deriving every prospective storage margin from its resources.
The only additional obligations are the explicit prefix admission predicate. -/
theorem WordStorageReplay.model {pre post : Stor} {events : List WordReplayEvent}
    (replay : WordStorageReplay pre events post) {bound : Nat}
    (boundCap : bound ≤ 2 * 2 ^ 64)
    {state : Blanc.WithdrawalRequest.State} {submissions : List Submission}
    {outputs : List Blanc.WithdrawalRequest.Entry}
    (history : History initial state submissions outputs)
    (resources : ModelResources bound history) (rep : RepresentsStorage pre.get state)
    (admitted : WordModelAdmission bound state events) :
    ∃ nextHistory : History initial (events.foldl wordModelUpdate state)
        (submissions ++ wordModelSubmissions events) (outputs ++ wordModelOutputs state events),
      ModelResources bound nextHistory ∧
        RepresentsStorage post.get (events.foldl wordModelUpdate state) := by
  induction replay generalizing state submissions outputs with
  | nil =>
    simp only [List.foldl_nil, wordModelSubmissions, List.flatMap_nil,
      wordModelOutputs, List.append_nil]
    exact ⟨history, resources, rep⟩
  | @cons storage post event rest guard tail ih =>
    have margins := resources.prospective_margins boundCap
    have tailAdmission := admitted.tail
    cases kind : event.kind with
    | system =>
      simp only [wordModelUpdate, kind] at tailAdmission
      have caller : event.frame.sevm.caller = systemAddress := by
        simpa only [wordEventInput, kind] using guard.input
      have nextRep : RepresentsStorage (wordEventUpdate storage event).get
          (Blanc.WithdrawalRequest.system state) := by
        simpa only [wordEventUpdate, wordStorageUpdate, guard.dynamic, caller, ite_true] using
          wordSystemStorage_represents guard rep margins.2
      have nextHistory := History.system history
      have nextResources := ModelResources.system resources
      have result := ih nextHistory nextResources nextRep tailAdmission
      simpa only [List.foldl_cons, wordModelUpdate, kind, wordModelSubmissions,
        List.flatMap_cons, List.nil_append, wordModelOutputs, List.append_assoc] using result
    | submission entry iterations output =>
      simp only [wordModelUpdate, kind] at tailAdmission
      obtain ⟨caller, entryCaller, payload, active, feeRun, wordPaid⟩ :=
        (show event.frame.sevm.caller ≠ systemAddress ∧ entry.caller = event.frame.sevm.caller ∧
          event.frame.sevm.data = submissionPayload entry ∧ storage.get 0 ≠ B256.max ∧
          WordFakeExponential.Run (storage.get 0) 17 1 17 0 iterations output ∧
          (output / (17 : B256)).toNat ≤ event.frame.sevm.value.toNat from by
            simpa only [wordEventInput, kind] using guard.input)
      have headAdmission := admitted [] event rest (by rw [List.nil_append])
      have paidAndCap : fee state ≤ event.frame.sevm.value.toNat ∧
          (submit state entry).count ≤ bound := by
        simpa only [List.foldl_nil, kind] using headAdmission
      have enabled := WordReplayGuard.enabled rep active
      have length : event.frame.sevm.data.length = 56 := by
        rw [payload, submissionPayload_length]
      have nextRep : RepresentsStorage (wordEventUpdate storage event).get (submit state entry) := by
        simpa only [wordEventUpdate, wordStorageUpdate, guard.dynamic, caller, length,
          ite_true, ite_false] using
          wordSubmissionStorage_represents guard rep margins.1 entry entryCaller payload
      let submission : Submission := ⟨entry, event.frame.sevm.value.toNat⟩
      have nextHistory := History.submit history submission enabled paidAndCap.1
      have nextResources : ModelResources bound nextHistory := ModelResources.submit
        (enabled := enabled) (paid := paidAndCap.1) resources
        (B256.toNat_lt event.frame.sevm.value) paidAndCap.2
      have result := ih nextHistory nextResources nextRep tailAdmission
      simpa only [List.foldl_cons, wordModelUpdate, kind, wordModelSubmissions,
        List.flatMap_cons, wordModelOutputs, List.nil_append, List.append_assoc,
        submission] using result
    | getter iterations output =>
      simp only [wordModelUpdate, kind] at tailAdmission
      obtain ⟨caller, empty, value, active, feeRun⟩ :=
        (show event.frame.sevm.caller ≠ systemAddress ∧ event.frame.sevm.data = [] ∧
          event.frame.sevm.value = 0 ∧ storage.get 0 ≠ B256.max ∧
          WordFakeExponential.Run (storage.get 0) 17 1 17 0 iterations output from by
            simpa only [wordEventInput, kind] using guard.input)
      have nextRep : RepresentsStorage (wordEventUpdate storage event).get state := by
        simpa only [wordEventUpdate, wordStorageUpdate, guard.dynamic, caller, empty,
          List.length_nil, ite_true, ite_false, (by decide : ¬ (0 : Nat) = 56)] using rep
      have result := ih history resources nextRep tailAdmission
      simpa only [List.foldl_cons, wordModelUpdate, kind, wordModelSubmissions,
        List.flatMap_cons, List.nil_append, wordModelOutputs] using result

end Blanc.Lift.WithdrawalRequest
