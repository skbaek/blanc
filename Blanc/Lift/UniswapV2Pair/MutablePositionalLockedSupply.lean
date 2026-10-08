import Blanc.Lift.UniswapV2Pair.MutablePositionalFold
import Blanc.Lift.UniswapV2Pair.LockedSupply
import Blanc.Lift.UniswapV2Pair.PairNoCallSource
import Blanc.Lift.UniswapV2Pair.PermitSourceOccurrence

namespace Blanc.Lift.UniswapV2Pair
open Jaune

private theorem positional_locked_extend {U K : WriterKey → Prop} {keys : List WriterKey}
    (sub : ∀ k, K k → U k) (good : ∀ k ∈ keys, U k) :
    ∀ k, WriterExtend K keys k → U k := by
  intro k tracked
  rcases tracked with old | touched
  · exact sub k old
  · exact good k touched

section Outcomes

variable {U : WriterKey → Prop} (inj : WriterInj U) (apart : WriterApart U)
  {current : Checkpoint} {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
  {K : WriterKey → Prop}
  (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
  (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
  (representable : sevm.data.length < 2 ^ 256) (sub : ∀ k, K k → U k)
  (wrep : WriterRep K (b.getStor sevm.currentTarget) current.state)
  (locked : current.state.unlocked = 0)
include inj apart run codeEq fork representable sub wrep locked

private theorem positional_locked_transfer_outcome (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (good : ∀ k ∈ transferTouched sevm.caller (transferRecipient sevm), U k) :
    PairFrameOutcomeWith PositionalChildConsumes sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  obtain ⟨_, _, _, _, result, consumed, annotated⟩ := transfer_bytecode_positional_consumes
    (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  refine ⟨_, _, _, _, _, Or.inl ⟨selector, rfl, rfl⟩, ⟨annotated, fun _ => rfl⟩, ?_, result.sourceLogs,
    result.logs, rfl⟩
  refine ⟨_, positional_locked_extend sub good, ?_, ?_⟩
  · rw [result.sourceState]
    exact result.representation
  · rw [result.sourceState]
    exact locked

private theorem positional_locked_approve_outcome (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (good : ∀ k ∈ approveTouched sevm.caller (approveSpender sevm), U k) :
    PairFrameOutcomeWith PositionalChildConsumes sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  obtain ⟨_, _, _, _, ⟨_, representation, _, _, _, _, sourceLogs, _, _, rawLogs, _⟩,
      consumed, annotated⟩ := approve_bytecode_positional_consumes (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  refine ⟨_, _, _, _, _, Or.inr (Or.inl ⟨selector, rfl, rfl⟩), ⟨annotated, fun _ => rfl⟩, ?_, sourceLogs,
    rawLogs, rfl⟩
  exact ⟨_, positional_locked_extend sub good, representation, locked⟩

private theorem positional_locked_transferFrom_outcome (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (good : ∀ k ∈ transferFromTouched (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm), U k) :
    PairFrameOutcomeWith PositionalChildConsumes sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  obtain ⟨_, _, _, _, result, consumed, annotated⟩ := transferFrom_bytecode_positional_consumes
    (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  refine ⟨_, _, _, _, _, Or.inr (Or.inr (Or.inl ⟨selector, rfl, rfl⟩)), ⟨annotated, fun _ => rfl⟩, ?_,
    result.sourceLogs, result.logs, rfl⟩
  refine ⟨_, positional_locked_extend sub good, ?_, ?_⟩
  · rw [result.sourceState]
    exact result.representation
  · rw [result.sourceState]
    unfold transferFromSourceState transferFromAllowanceState
    split
    · exact locked
    · exact locked

omit inj apart in
private theorem positional_locked_initialize_outcome (freshOutput : b.output = [])
    (selector : Blanc.Sevm.selector sevm = 0x485cc955) :
    PairFrameOutcomeWith PositionalChildConsumes sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  obtain ⟨_, _, _, _, _, result, consumed, annotated⟩ := initialize_bytecode_positional_consumes
    (invocation := invocation) wrep representable freshOutput codeEq fork selector run
  refine ⟨_, _, _, [], [], Or.inr (Or.inr (Or.inr (Or.inl ⟨selector, rfl, rfl⟩))), ⟨annotated, fun _ => rfl⟩,
    ?_, ?_, ?_, rfl⟩
  · refine ⟨K, sub, ?_, ?_⟩
    · rw [result.sourceCurrent]
      exact result.representation
    · rw [result.sourceCurrent]
      exact locked
  · rw [result.sourceCurrent, List.append_nil]
  · rw [result.logs, List.append_nil]

private theorem positional_locked_permit_outcome (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : b.getCode sevm.currentTarget = code) (freshOutput : b.output = [])
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (good : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm, U k) :
    PairFrameOutcomeWith PositionalChildConsumes sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  have touched : ∀ k ∈ permitTouched (permitOwner sevm) (permitSpender sevm), U k := by
    intro k member
    apply good _ (Exec.mem_rawFrameRoots_self run) rfl k
    apply List.mem_append_left
    rw [pairDecodedKeys, ite_eq_right (by rw [selector]; decide),
      ite_eq_right (by rw [selector]; decide), ite_eq_right (by rw [selector]; decide),
      ite_eq_left selector]
    exact member
  obtain ⟨_, _, _, _, actual, settled, views, result, auth, annotated, consumed, _, _⟩ :=
    permit_bytecode_positional_consumes (invocation := invocation) inj apart sub sem image wrep touched
      (by rw [installed]; exact image.symm) representable codeEq fork selector freshOutput run
      (fun F member target k viewKey => good F member target k (List.mem_append_right _ viewKey))
  obtain ⟨_, representation, _, _, _, _, _, _, sourceLogs, _, output, rawLogs, _⟩ := result
  refine ⟨_, _, _, _, _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨selector, rfl, actual.out, settled.entered, views, rfl, auth⟩)))),
    ⟨annotated, ?_⟩, ?_, sourceLogs, rawLogs, rfl⟩
  · intro committed
    change RunStatus.success [] = RunStatus.success post.output
    rw [output]
  · exact ⟨_, positional_locked_extend sub touched, representation, locked⟩

private theorem positional_locked_view_outcome (view : StaticView)
    (selector : Blanc.Sevm.selector sevm = view.selector)
    (good : ∀ k ∈ staticViewDecodedKeys sevm, U k) :
    PairFrameOutcomeWith PositionalChildConsumes sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good
  obtain ⟨_, _, _, storage, logs, _, _, consumed, annotated, frameCurrent, _, _⟩ :=
    staticView_source_positional_selected (ctx := writerContext sevm invocation) wrep fresh
      representable rfl codeEq fork view selector run
  refine ⟨_, _, _, [], [], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨view, selector, rfl, rfl⟩)))), ⟨annotated, fun _ => rfl⟩, ?_, ?_, ?_, rfl⟩
  · refine ⟨_, positional_locked_extend sub good, ?_, ?_⟩
    · rw [frameCurrent, storage sevm.currentTarget]
      exact wrep.extend fresh
    · rw [frameCurrent]
      exact locked
  · rw [frameCurrent, List.append_nil]
  · rw [logs, List.append_nil]

end Outcomes

/-- Existing locked supply is used only for actual selector admissibility.
Every final model result below is constructed by one reviewed positional producer
at the supplied incoming checkpoint and invocation. -/
theorem lockedPairPositionalSupply {U : WriterKey → Prop}
    (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList) (pair : Adr) :
    PairFrameSupplyWith PositionalChildConsumes pair (LockedRep U) (LockedGood U)
      LockedAuth (lockedOwnedRaw pair) := by
  intro current invocation sevm b post G run target codeEq installedCode fork freshOutput
    representable roots rep
  obtain ⟨oldEntry, oldNested, _, _, _, admitted, _⟩ :=
    lockedPairSupply inj apart sem image pair current invocation run target codeEq installedCode
      fork freshOutput representable roots rep
  subst target
  have roots : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm, U k := roots
  have good : ∀ k ∈ pairDecodedKeys sevm, U k := fun k member =>
    roots _ (Exec.mem_rawFrameRoots_self run) rfl k (List.mem_append_left _ member)
  obtain ⟨K, sub, wrep, locked⟩ := rep
  rcases admitted with ⟨selector, _, _⟩ | ⟨selector, _, _⟩ | ⟨selector, _, _⟩ |
    ⟨selector, _, _⟩ | ⟨selector, _, _⟩ | ⟨view, selector, _, _⟩
  · exact positional_locked_transfer_outcome inj apart run codeEq fork representable sub wrep
      locked selector (by rw [pairDecodedKeys, ite_eq_left selector] at good; exact good)
  · exact positional_locked_approve_outcome inj apart run codeEq fork representable sub wrep
      locked selector (by
        rw [pairDecodedKeys, ite_eq_right (by rw [selector]; decide), ite_eq_left selector] at good
        exact good)
  · exact positional_locked_transferFrom_outcome inj apart run codeEq fork representable sub wrep
      locked selector (by
        rw [pairDecodedKeys, ite_eq_right (by rw [selector]; decide),
          ite_eq_right (by rw [selector]; decide), ite_eq_left selector] at good
        exact good)
  · exact positional_locked_initialize_outcome run codeEq fork representable sub wrep locked
      freshOutput selector
  · exact positional_locked_permit_outcome inj apart run codeEq fork representable sub wrep
      locked sem image installedCode freshOutput selector roots
  · have viewGood : ∀ k ∈ staticViewDecodedKeys sevm, U k := fun k member =>
      roots _ (Exec.mem_rawFrameRoots_self run) rfl k (List.mem_append_right _ member)
    exact positional_locked_view_outcome inj apart run codeEq fork representable sub wrep locked
      view selector viewGood

/-- The complete same-slot fold with a real positional producer for every locked Pair child. -/
theorem locked_mutable_source_slot_turns
    {U : WriterKey → Prop} {pair : Adr}
    (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    {root : Exec.Deriv} {frame : Frame} {request : Request} {reply : ExternalResult} {index : Nat}
    (observed : SourceCallAt root frame request reply index)
    (pairEq : frame.context.pair = pair) (mutable : externalStatic frame request = false)
    (installed : some (observed.call.occurrence.node.devm.getCode pair).toList = sem.image)
    (rep : LockedRep U frame.current.state (observed.call.occurrence.node.devm.getStor pair))
    (time : frame.context.timestamp = observed.call.occurrence.node.sevm.benvStat.time)
    (fork : CoveredFork observed.call.occurrence.node.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = pair → LockedGood U F) :
    ∃ (events : List (Log ⊕ Exec.LocatedFrame)) (turns : List MutableTurn)
      (c : Checkpoint) (added : List PendingLog) (rets : List ChildReturn),
      SourceSlotEvents observed.call frame.context.pair index events ∧
      events.filterMap Sum.getRight? = observed.paths ∧
      turns.map MutableTurn.event = events ∧
      PositionalMutableTurns frame request 0 events (mutableTranscript turns .done)
        {complete := true, frame := {frame with current := c}, childReturns := rets} ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
        LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      LockedRep U c.state (observed.call.returned.devm.getStor pair) ∧
      c.logs = frame.current.logs ++ added ∧
      ∃ L : List Log,
        observed.call.returned.devm.logs = observed.call.occurrence.node.devm.logs ++ L ∧
        added.map (PendingLog.rawWith (lockedOwnedRaw pair)) = L.map some := by
  exact mutable_source_slot_turns (lockedPairPositionalSupply inj apart sem image pair)
    (fun _ _ _ same rep => LockedRep.congr same rep) sem image observed pairEq mutable
    installed rep time fork good

end Blanc.Lift.UniswapV2Pair
