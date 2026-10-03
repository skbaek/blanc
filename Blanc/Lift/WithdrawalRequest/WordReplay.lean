import Blanc.Lift.WithdrawalRequest.BalanceHistory
import Blanc.ExecutionAccountingStorageFold

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionAccountingReplay

/-- The five sequential submission writes, with all word aliases retained. -/
def wordSubmissionStorage (sevm : Sevm) (storage : Stor) : Stor :=
  let counted := storage.set 1 (1 + storage.get 1)
  let tail := counted.get 3
  let key := 4 + 3 * tail
  ((((counted.set key sevm.caller.toB256).set (1 + key) (Sevm.dataWord sevm 0)).set
    (1 + (1 + key)) (Sevm.dataWord sevm 32)).set 3 (1 + tail))

def wordSystemCount (storage : Stor) : B256 :=
  let difference := storage.get 3 - storage.get 2
  if difference.toNat < 16 then difference else 16

def wordSystemPointers (storage : Stor) : Stor :=
  let advanced := storage.get 2 + wordSystemCount storage
  if advanced = storage.get 3 then (storage.set 2 0).set 3 0
  else storage.set 2 advanced

def wordSystemNewExcess (storage : Stor) : B256 :=
  let old := storage.get 0
  let effective := if old = B256.max then 0 else old
  let total := storage.get 1 + effective
  if (2 : B256) < total then total - 2 else 0

/-- Pure bookkeeping over raw words, independent of any queue interpretation. -/
def wordSystemStorage (storage : Stor) : Stor :=
  let pointers := wordSystemPointers storage
  (pointers.set 0 (wordSystemNewExcess pointers)).set 1 0

/-- Input-derived storage update; inadmissible branches are excluded by replay guards. -/
def wordStorageUpdate (sevm : Sevm) (storage : Stor) : Stor :=
  if sevm.isStatic = false then
    if sevm.caller = systemAddress then wordSystemStorage storage
    else if sevm.data.length = 56 then wordSubmissionStorage sevm storage else storage
  else storage

private theorem systemFramePointers_word_storage (sevm : Sevm) (base : Devm) (memory : Mem) :
    (systemFramePointers sevm base memory).getStor sevm.currentTarget =
      wordSystemPointers (base.getStor sevm.currentTarget) := by
  unfold systemFramePointers systemPointerBase
  by_cases drained : systemAdvancedHead (systemHead sevm base) (systemCount sevm base) =
      systemTail sevm base
  · rw [ite_eq_left drained, afterSstore_getStor_self, afterSstore_getStor_self,
      systemQueuePost_storage]
    unfold wordSystemPointers
    change (base.getStor sevm.currentTarget).get 2 +
      wordSystemCount (base.getStor sevm.currentTarget) =
        (base.getStor sevm.currentTarget).get 3 at drained
    rw [ite_eq_left drained]
  · rw [ite_eq_right drained, afterSstore_getStor_self, systemQueuePost_storage]
    unfold wordSystemPointers
    change ¬ (base.getStor sevm.currentTarget).get 2 +
      wordSystemCount (base.getStor sevm.currentTarget) =
        (base.getStor sevm.currentTarget).get 3 at drained
    rw [ite_eq_right drained]
    rfl

theorem systemFramePost_word_storage (sevm : Sevm) (base : Devm) (memory : Mem) (gas : Nat) :
    (systemFramePost sevm base memory gas).getStor sevm.currentTarget =
      wordSystemStorage (base.getStor sevm.currentTarget) := by
  rw [systemFramePost_storage]
  simp only [systemNewExcess, systemExcessSum, systemPendingCount, systemExcessRead,
    systemEffectiveExcess, systemOldExcess, getStorVal_eq_getStor, afterSload_getStor,
    systemFramePointers_word_storage, wordSystemStorage, wordSystemNewExcess]

theorem submissionPost_word_storage (sevm : Sevm) (pre : Devm) (memory : Mem) (gas : Nat) :
    (submissionPost sevm (afterSload sevm pre 0) memory gas).getStor sevm.currentTarget =
      wordSubmissionStorage sevm (pre.getStor sevm.currentTarget) := by
  rw [submissionPost_storage]
  simp only [submissionCount, submissionKey, submissionTail, submissionCountStore,
    submissionCountRead, afterSstore_getStor_self, afterSload_getStor,
    getStorVal_eq_getStor, wordSubmissionStorage]

theorem FrameEffect.word_storage {sevm : Sevm} {pre post : Devm}
    (effect : FrameEffect sevm pre post) :
    post.getStor sevm.currentTarget = wordStorageUpdate sevm (pre.getStor sevm.currentTarget) := by
  cases effect with
  | system caller dynamic gas state =>
    rw [state, systemFramePost_word_storage]
    simp only [wordStorageUpdate, dynamic, caller, ite_true]
  | submission caller dynamic length active iterations output fee paid gas state =>
    rw [state, submissionPost_word_storage]
    simp only [wordStorageUpdate, dynamic, caller, length, ite_true, ite_false]
  | getter caller empty value active iterations output fee gas state bytes =>
    rw [state, (feeGetterPost_preserves _ _ _ _).1 sevm.currentTarget, afterSload_getStor]
    by_cases dynamic : sevm.isStatic = false
    · simp only [wordStorageUpdate, dynamic, caller, empty, List.length_nil,
        ite_true, ite_false, (by decide : ¬ (0 : Nat) = 56)]
    · rw [wordStorageUpdate, ite_eq_right dynamic]

/-- Data and actual frame provenance only; no saved post-state equality is an event field. -/
inductive WordReplayKind where
  | system
  | submission (entry : Blanc.WithdrawalRequest.Entry) (iterations : Nat) (output : B256)
  | getter (iterations : Nat) (output : B256)

structure WordReplayEvent where
  frame : Exec.Frame
  kind : WordReplayKind

def wordEventUpdate (storage : Stor) (event : WordReplayEvent) : Stor :=
  wordStorageUpdate event.frame.sevm storage

/-- Branch guards price and type the input at this occurrence's incoming storage. -/
def wordEventInput (storage : Stor) (event : WordReplayEvent) : Prop :=
  let sevm := event.frame.sevm
  match event.kind with
  | .system => sevm.caller = systemAddress
  | .submission entry iterations output =>
    sevm.caller ≠ systemAddress ∧ entry.caller = sevm.caller ∧
    sevm.data = Blanc.WithdrawalRequest.submissionPayload entry ∧
    storage.get 0 ≠ B256.max ∧
    WordFakeExponential.Run (storage.get 0) 17 1 17 0 iterations output ∧
    (output / (17 : B256)).toNat ≤ sevm.value.toNat
  | .getter iterations output =>
    sevm.caller ≠ systemAddress ∧ sevm.data = [] ∧ sevm.value = 0 ∧
    storage.get 0 ≠ B256.max ∧
    WordFakeExponential.Run (storage.get 0) 17 1 17 0 iterations output

structure WordReplayGuard (storage : Stor) (event : WordReplayEvent) : Prop where
  pre : storage = event.frame.pre.getStor withdrawalRequestPredeployAddress
  target : event.frame.sevm.currentTarget = withdrawalRequestPredeployAddress
  dynamic : event.frame.sevm.isStatic = false
  pc : event.frame.pc = 0
  code : event.frame.sevm.code = Blanc.withdrawalRequestCode
  fork : CoveredFork event.frame.sevm.benvStat.fork
  entry : balanceEntryCondition event.frame.sevm event.frame.pre
  input : wordEventInput storage event

abbrev WordStorageReplay := GuardedStorageReplay wordEventUpdate WordReplayGuard

def wordReplayCarrier : ReplayCarrier withdrawalRequestPredeployAddress :=
  storageFoldCarrier withdrawalRequestPredeployAddress WordReplayEvent wordEventUpdate WordReplayGuard

def wordReplayObservation : ReplayObservation wordReplayCarrier where
  O := Exec.Frame
  obs events := events.map WordReplayEvent.frame
  obs_nil := rfl
  obs_append := fun _ _ => List.map_append
  frameObs := balanceFrameObservation
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change WordStorageReplay (pre.getStor withdrawalRequestPredeployAddress) []
      (post.getStor withdrawalRequestPredeployAddress)
    rw [storage]
    exact .nil _

private theorem FrameEffect.word_event {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (committed : Execution.commits (.ok post) = true)
    (effect : FrameEffect sevm pre post)
    (target : sevm.currentTarget = withdrawalRequestPredeployAddress)
    (dynamic : sevm.isStatic = false) (code : sevm.code = Blanc.withdrawalRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (entry : balanceEntryCondition sevm pre) :
    ∃ event : WordReplayEvent, event.frame = Exec.Frame.ofRun run committed ∧
      WordReplayGuard (pre.getStor withdrawalRequestPredeployAddress) event ∧
      wordEventUpdate (pre.getStor withdrawalRequestPredeployAddress) event =
        post.getStor withdrawalRequestPredeployAddress := by
  have storage := effect.word_storage
  rw [target] at storage
  cases effect with
  | system caller _ gas state =>
    refine ⟨⟨Exec.Frame.ofRun run committed, .system⟩, rfl,
      ⟨rfl, target, dynamic, rfl, code, fork, entry, caller⟩, storage.symm⟩
  | submission caller _ length active iterations output fee paid gas state =>
    refine ⟨⟨Exec.Frame.ofRun run committed,
      .submission (decodeSubmission sevm length) iterations output⟩, rfl,
      ⟨rfl, target, dynamic, rfl, code, fork, entry, ?_⟩, storage.symm⟩
    refine ⟨caller, rfl, (decodeSubmission_payload sevm length).symm, ?_, ?_, paid⟩
    · simpa only [getStorVal_eq_getStor, target] using active
    · simpa only [getStorVal_eq_getStor, target] using fee
  | getter caller empty value active iterations output fee gas state bytes =>
    refine ⟨⟨Exec.Frame.ofRun run committed, .getter iterations output⟩, rfl,
      ⟨rfl, target, dynamic, rfl, code, fork, entry, ?_⟩, storage.symm⟩
    refine ⟨caller, empty, value, ?_, ?_⟩
    · simpa only [getStorVal_eq_getStor, target] using active
    · simpa only [getStorVal_eq_getStor, target] using fee

private theorem wordReplayTargetHandler {sevm : Sevm} {pre post : Devm}
    (semantic : balanceSem.Run sevm pre post)
    (target : sevm.currentTarget = withdrawalRequestPredeployAddress) :
    Exec.CoreAccounting withdrawalRequestPredeployAddress balanceSem balanceEntryCondition
      wordReplayCarrier wordReplayObservation 0 sevm pre (.ok post) := by
  intro run committed fork installed admitted
  have entry := admitted.root target
  have effect := semantic.2 fork entry
  have frames : Exec.committedFrames run = [Exec.Frame.ofRun run committed] := by
    rw [Exec.committedFrames, dite_eq_left committed, canonical_descendants run semantic.1]
  refine ⟨?_, ?_⟩
  · intro static
    rw [frames]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change balanceFrameObservation (Exec.Frame.ofRun run committed) = []
    apply ite_eq_right
    intro condition
    have impossible : sevm.isStatic = false := condition.2
    rw [static] at impossible
    cases impossible
  · intro _
    cases static : sevm.isStatic with
    | false =>
      obtain ⟨event, frame, guard, storage⟩ :=
        effect.word_event run committed target static semantic.1 fork entry
      refine ⟨[event], ?_, ?_⟩
      · change WordStorageReplay (pre.getStor withdrawalRequestPredeployAddress) [event]
          (post.getStor withdrawalRequestPredeployAddress)
        apply GuardedStorageReplay.cons guard
        rw [storage]
        exact .nil _
      · rw [frames]
        change [event.frame] = balanceFrameObservation (Exec.Frame.ofRun run committed) ++ []
        rw [frame, balanceFrameObservation, ite_eq_left ⟨target, static⟩, List.append_nil]
    | true =>
      refine ⟨[], ?_, ?_⟩
      · change WordStorageReplay (pre.getStor withdrawalRequestPredeployAddress) []
          (post.getStor withdrawalRequestPredeployAddress)
        rw [(effect.static_preserves static).1 withdrawalRequestPredeployAddress]
        exact .nil _
      · rw [frames]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        change [] = balanceFrameObservation (Exec.Frame.ofRun run committed)
        symm
        apply ite_eq_right
        intro condition
        have impossible : sevm.isStatic = false := condition.2
        rw [static] at impossible
        cases impossible

/-- Foreign executions reuse the common accounting traversal and settlement chronology. -/
theorem wordReplay_coreAccounting :
    Exec.Fa (Exec.WknSem withdrawalRequestPredeployAddress balanceSem
      (fun pc sevm pre out _ =>
        Exec.CoreAccounting withdrawalRequestPredeployAddress balanceSem balanceEntryCondition
          wordReplayCarrier wordReplayObservation pc sevm pre out)) := by
  apply Exec.coreAccounting withdrawalRequestPredeployAddress balanceSem balanceEntryCondition
    wordReplayCarrier wordReplayObservation GuardedStorageReplay.append (fun _ _ => ())
  · intro sevm state foreign
    rfl
  · exact balanceFrameObservation_foreign
  · intro sevm pre post semantic target _
    exact wordReplayTargetHandler semantic target

def wordReplayLadder : AccountingLadderAdmitted balanceSpec withdrawalRequestPredeployAddress
    balanceEntryCondition where
  carrier := wordReplayCarrier
  append := GuardedStorageReplay.append
  tag := fun _ _ => ()
  preserves := balanceSpec_preserves
  view := wordReplayObservation
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
      bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact (wordReplay_coreAccounting pc sevm pre out run installed run committed fork installed
      admitted).2 entryBound

/-- Exact raw-storage replay of actual committed nonstatic target frames.
    Input guards hold at each connected replay pre-storage; no Nat queue model is assumed. -/
theorem history_word_storage_replay {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    ∃ events : List WordReplayEvent,
      WordStorageReplay (checkpoint.state.getStor withdrawalRequestPredeployAddress) events
        (future.state.getStor withdrawalRequestPredeployAddress) ∧
      events.map WordReplayEvent.frame = trace.settledFrames.flatMap balanceFrameObservation := by
  apply wordReplayLadder.configuredHistory trace (history_balanceEntryCondition trace)
  refine ⟨?_, trivial, trivial⟩
  change some (checkpoint.state.getCode withdrawalRequestPredeployAddress).toList =
    some Blanc.withdrawalRequestCode.toList
  rw [code]


end Blanc.Lift.WithdrawalRequest
