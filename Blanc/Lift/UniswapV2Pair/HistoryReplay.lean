import Blanc.Lift.UniswapV2Pair.SourceReplay
import Blanc.Lift.UniswapV2Pair.ApproveSource
import Blanc.Lift.SegmentedHistory

/-! A retained outer invocation carries its original raw execution. Its complete
source transcript consumes nested turns once; observations read committed raw
frames, rather than flattening recursively consumed source invocations. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Metadata is anchored to the original located frame, including its raw run. -/
structure HistoryStep where
  located : Exec.LocatedFrame
  entry : Entry
  transcript : Transcript

def HistoryStep.source (step : HistoryStep) : SourceInvocation :=
  { context := writerContext step.located.frame.sevm step.located.path,
    entry := step.entry, transcript := step.transcript }

def HistoryStep.approve (located : Exec.LocatedFrame) : HistoryStep :=
  { located := located, entry := approveDecodedEntry located.frame.sevm,
    transcript := .done }

/-- Storage replay is connected through the existing exact-consumption fold. -/
def HistoryReplay (U : WriterKey → Prop) (pre : Stor)
    (steps : List HistoryStep) (post : Stor) : Prop :=
  PairStorageReplay U pre (steps.map HistoryStep.source) post

theorem HistoryReplay.nil (U : WriterKey → Prop) (stor : Stor) :
    HistoryReplay U stor [] stor := PairStorageReplay.nil U stor

theorem HistoryReplay.append {U : WriterKey → Prop} {a b c : Stor}
    {left right : List HistoryStep}
    (first : HistoryReplay U a left b) (second : HistoryReplay U b right c) :
    HistoryReplay U a (left ++ right) c := by
  unfold HistoryReplay
  rw [List.map_append]
  exact PairStorageReplay.append first second

def historyReplayCarrier (pair : Adr) (U : WriterKey → Prop) :
    Blanc.ExecutionAccountingReplay.ReplayCarrier pair where
  Snap := Stor
  Step := HistoryStep
  Tag := Unit
  Replay := HistoryReplay U
  ofState world := world.getStor pair
  frameEntry _ world := world.getStor pair
  nil := HistoryReplay.nil U
  silent := fun storage _ => storage
  credit := by
    intro _ pre post _ storage _ _
    exact ⟨[], by rw [storage]; exact HistoryReplay.nil U _⟩
  entry_eq_ofState := by
    intro _ _ _ _ transfer _
    exact congrFun (benvAfterTransfer_getStor_eq transfer) pair

/-- Settlement-pruned actual frames; a static invocation contributes no write. -/
def pairFrameObservation (pair : Adr) (frame : Exec.Frame) : List Exec.Frame :=
  if frame.sevm.currentTarget = pair ∧ frame.sevm.isStatic = false then [frame] else []

def historyObservation (pair : Adr) (U : WriterKey → Prop) :
    Blanc.ExecutionAccountingReplay.ReplayObservation (historyReplayCarrier pair U) where
  O := Exec.Frame
  obs steps := steps.flatMap fun step =>
    (Exec.committedFrames step.located.frame.run).flatMap (pairFrameObservation pair)
  obs_nil := rfl
  obs_append := fun _ _ => List.flatMap_append
  frameObs := pairFrameObservation pair
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change HistoryReplay U (pre.getStor pair) [] (post.getStor pair)
    rw [storage]
    exact HistoryReplay.nil U _

/-- The real pc0 approval execution produces a replay for every incoming
representation. Freshness is derived from its actual touched keys in the
fixed universe; no source acceptance or replay is supplied by the caller. -/
theorem approve_history_replay {U : WriterKey → Prop} {sevm : Sevm}
    {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (located : Exec.LocatedFrame)
    (original : located.frame = Exec.Frame.ofRun run committed)
    (injective : WriterInj U) (apart : WriterApart U)
    (touched : ∀ k ∈ approveTouched sevm.caller (approveSpender sevm), U k)
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3) :
    HistoryReplay U (b.getStor sevm.currentTarget)
      [HistoryStep.approve located] (post.getStor sevm.currentTarget) := by
  intro st K included rep
  have fresh : WriterFreshKeys K (approveTouched sevm.caller (approveSpender sevm)) :=
    Blanc.SlotFootprint.FreshKeys.of_universe injective apart included touched
  obtain ⟨_, _, _, residual, result, consumed⟩ :=
    approve_bytecode_exact_consumes (current := {state := st, logs := [], updates := []})
      (invocation := located.path) rep fresh representable codeEq fork selector run
  refine ⟨approveSourceState st sevm.caller (approveSpender sevm) (approveAmount sevm),
    WriterExtend K (approveTouched sevm.caller (approveSpender sevm)), ?_,
    fun _ h => Or.inl h, ?_, result.2.1⟩
  · change SourceReplay st [(HistoryStep.approve located).source] _
    rw [HistoryStep.source, HistoryStep.approve, original]
    exact .cons consumed rfl (.nil _)
  · intro k member
    rcases member with tracked | written
    · exact included k tracked
    · exact touched k written

/-- Selection is from the original outermost-target walk. A nonroot producer
retains the entering occurrence, including the original child counter and
successful settlement, rather than inventing a path from list membership. -/
theorem selected_approve_history {U : WriterKey → Prop} {pair : Adr}
    {pc : Nat} {rootSevm : Sevm} {pre : Devm} {out : Execution}
    (root : Exec pc rootSevm pre out) (located : Exec.LocatedFrame)
    (selected : located ∈ (Exec.retainedTargetTurns pair root).filterMap Sum.getRight?)
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (original : located.frame = Exec.Frame.ofRun run committed)
    (injective : WriterInj U) (apart : WriterApart U)
    (touched : ∀ k ∈ approveTouched sevm.caller (approveSpender sevm), U k)
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x095ea7b3) :
    HistoryReplay U (b.getStor sevm.currentTarget)
        [HistoryStep.approve located] (post.getStor sevm.currentTarget) ∧
      ((HistoryStep.approve located).source.context = writerContext sevm located.path) ∧
      ((historyObservation pair U).obs [HistoryStep.approve located] =
        (Exec.committedFrames run).flatMap (pairFrameObservation pair)) ∧
      (located.path ≠ [] → Nonempty (Exec.LocatedFrame.EnteringOccurrence root located)) := by
  refine ⟨approve_history_replay run committed located original injective apart touched
    representable codeEq fork selector, ?_, ?_, ?_⟩
  · change writerContext located.frame.sevm located.path = _
    rw [original]
    rfl
  · change ((Exec.committedFrames located.frame.run).flatMap (pairFrameObservation pair)) ++
      [] = _
    rw [original, List.append_nil]
    rfl
  · intro nonroot
    exact (Exec.retainedTargetTurns_entering pair root located selected nonroot).2.2

end Blanc.Lift.UniswapV2Pair
