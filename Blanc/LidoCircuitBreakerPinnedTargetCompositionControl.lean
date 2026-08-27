import Blanc.LidoCircuitBreakerPinnedTargetComposition
import Blanc.LidoCircuitBreakerPublicPauseControl

/-!
# Pinned-target composition control

This module installs the compiled pinned-target stub in the existing row-19
production public-pause world.  The total EVM execution below is the concrete
boundary witness used to inhabit both the full public outcome family and the
final pinned-target conclusion.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- Row 19 with the compiled pinned-target stub installed at the pause target. -/
def stubPauseWorldState : State :=
  State.set
    (State.set (.empty : State) configWorldOwner
      { Acct.nil with stor := pauseLastWorldStor, code := configWorldCode })
    pauseWorldCallee
      { Acct.nil with code := PinnedTargetControl.stubCode }

/-- Ample gas for the production public pause and both compiled-stub calls. -/
def stubPauseWorldGas : Nat := 100000

/-- The row-19 public message, with only its world state and original state
changed to install the compiled stub. -/
def stubPauseWorldMsg : Msg :=
  { (pauseWorldMsg pauseLastWorldStor stubPauseWorldGas) with
    benv :=
      { (pauseWorldMsg pauseLastWorldStor stubPauseWorldGas).benv with
        state := stubPauseWorldState
        stat :=
          { (pauseWorldMsg pauseLastWorldStor stubPauseWorldGas).benv.stat with
            origState := stubPauseWorldState } } }

def stubPauseWorldSevm : Sevm := initSevm stubPauseWorldMsg

def stubPauseWorldPre : Devm := initDevm stubPauseWorldMsg

private structure StubPauseWorldFixture where
  post : Devm
  rawExec : exec (initEvm stubPauseWorldMsg) = .ok post

private def stubPauseWorldFixture? : Option StubPauseWorldFixture :=
  match rawExec : exec (initEvm stubPauseWorldMsg) with
  | .ok post => some { post, rawExec }
  | .error _ => none

private theorem stubPauseWorldFixture_nonempty :
    Nonempty StubPauseWorldFixture := by
  have available : stubPauseWorldFixture?.isSome = true := by
    native_decide
  cases fixture : stubPauseWorldFixture? with
  | none => simp [fixture] at available
  | some witness => exact ⟨witness⟩

private noncomputable def stubPauseWorldFixture : StubPauseWorldFixture :=
  Classical.choice stubPauseWorldFixture_nonempty

/-- The total evaluator's concrete successful result. -/
noncomputable def stubPauseWorldFinal : Devm := stubPauseWorldFixture.post

/-- Executable anti-vacuity: the production runtime with the installed stub
terminates successfully. -/
theorem stubPauseWorld_exec :
    exec (initEvm stubPauseWorldMsg) = .ok stubPauseWorldFinal :=
  stubPauseWorldFixture.rawExec

theorem stubPauseWorldState_get_breaker :
    stubPauseWorldState.get configWorldOwner =
      { Acct.nil with stor := pauseLastWorldStor, code := configWorldCode } := by
  rw [stubPauseWorldState,
    State.get_set_ne _ pauseWorld_callee_ne_owner, State.get_set_self]

theorem stubPauseWorldState_get_target :
    stubPauseWorldState.get pauseWorldCallee =
      { Acct.nil with code := PinnedTargetControl.stubCode } := by
  rw [stubPauseWorldState, State.get_set_self]

theorem stubPauseWorld_targetCode :
    stubPauseWorldState.getCode pauseWorldCallee =
      PinnedTargetControl.stubCode := by
  show (stubPauseWorldState.get pauseWorldCallee).code = _
  rw [stubPauseWorldState_get_target]

theorem stubPauseWorld_codeBytes :
    stubPauseWorldSevm.code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [stubPauseWorldSevm, stubPauseWorldMsg, initSevm] using
    pauseWorld_msgCode pauseLastWorldStor stubPauseWorldGas

private theorem stubPauseWorld_pcFree :
    Prog.pcFree (runtime officialParams) = true := by
  native_decide

/-- The successful total execution, reflected into the public production
program's exact compiled semantics. -/
theorem stubPauseWorld_run :
    Prog.RunCompiledTo stubPauseWorldSevm stubPauseWorldPre
      (runtime officialParams) (.ok stubPauseWorldFinal) := by
  have codeEq : some stubPauseWorldSevm.code.toList =
      Prog.compile (runtime officialParams) := by
    rw [stubPauseWorld_codeBytes, lidoCircuitBreakerCode_compile]
  have raw : exec ⟨0, stubPauseWorldSevm, stubPauseWorldPre⟩ =
      .ok stubPauseWorldFinal := by
    simpa only [stubPauseWorldSevm, stubPauseWorldPre, initEvm] using
      stubPauseWorld_exec
  exact Prog.RunCompiledTo.of_runCompiled
    ((Prog.runCompiled_iff_exec stubPauseWorld_pcFree codeEq).2 raw)

theorem stubPauseWorld_currentTarget :
    stubPauseWorldSevm.currentTarget = configWorldOwner := rfl

theorem stubPauseWorld_callerWord :
    stubPauseWorldSevm.caller.toB256 = pauseWorldPauser :=
  pauseWorld_pauserAdr_toB256

theorem stubPauseWorld_getStorVal {key : B256} :
    stubPauseWorldPre.getStorVal configWorldOwner key =
      pauseLastWorldStor.get key := by
  change (stubPauseWorldState.get configWorldOwner).stor.get key = _
  rw [stubPauseWorldState_get_breaker]

theorem stubPauseWorld_targetCodeAt :
    CodeAt stubPauseWorldPre pauseWorldCallee
      PinnedTargetControl.stubCode := by
  exact stubPauseWorld_targetCode

/-- The executable installed-stub world satisfies the complete production
public-entry premise bundle. -/
theorem stubPauseWorld_publicPausePremises :
    PublicPauseEntryPremises stubPauseWorldSevm stubPauseWorldPre
      configWorldOwner pauseWorldCallee.toB256 pauseWorldDuration 1 1
      pauseWorldCallee.toB256 [] PinnedTargetControl.stubCode := by
  refine {
    productionBytes := stubPauseWorld_codeBytes
    currentTarget := stubPauseWorld_currentTarget
    codeAddress := rfl
    valueZero := rfl
    dynamic := rfl
    entered := ?_
    image := ?_
    calldata := rfl
    selectorEq := ?_
    targetCanonical := validAdr_toB256 pauseWorldCallee
    targetNonzero := by decide
    callerNonzero := ?_
    unlocked := rfl
    targetCodeAt := ?_
    assigned := ?_
    live := ?_
    durationRead := ?_
    indexRead := ?_
    lengthRead := ?_
    lastRead := ?_
    assignmentCountNe := ?_
    assignmentIndexNe := pauseWorld_assignCallee_ne_indexCallee
    assignmentLengthNe := pauseWorld_length_ne_assignCallee.symm
    assignmentEntryNe := pauseWorld_entryOne_ne_assignCallee.symm
    countRemovedEntryNe := ?_
    countMovedIndexNe := ?_
    countIndexNe := ?_
    countLengthNe := ?_
    countEntryNe := ?_
  }
  · decide
  · unfold MemImage
    exact ⟨Mem.wf_empty, Mem.reads_empty⟩
  · have dataEq : stubPauseWorldSevm.data =
        (pauseWorldSevm pauseLastWorldStor stubPauseWorldGas).data := by
      change stubPauseWorldMsg.data =
        (pauseWorldMsg pauseLastWorldStor stubPauseWorldGas).data
      rfl
    have selectorEq : Sevm.selector stubPauseWorldSevm =
        Sevm.selector
          (pauseWorldSevm pauseLastWorldStor stubPauseWorldGas) := by
      unfold Sevm.selector Sevm.dataWord
      rw [dataEq]
    exact selectorEq.trans
      (pauseWorld_selector pauseLastWorldStor stubPauseWorldGas)
  · rw [stubPauseWorld_callerWord]
    decide
  · rw [show pauseWorldCallee.toB256.toAdr = pauseWorldCallee from
      toAdr_toB256 pauseWorldCallee]
    exact stubPauseWorld_targetCodeAt
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_callerWord,
      stubPauseWorld_getStorVal, pauseLastStor_assignment]
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_callerWord,
      stubPauseWorld_getStorVal, pauseLastStor_expiry]
    decide
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_getStorVal,
      pauseLastStor_duration]
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_getStorVal,
      pauseLastStor_index]
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_getStorVal,
      pauseLastStor_length]
  · rw [stubPauseWorld_currentTarget, stubPauseWorld_getStorVal,
      pauseLastStor_entry]
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_assignCallee_ne_count
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_length_ne_count.symm
  · rw [stubPauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm

theorem stubPauseWorld_target_ne_owner :
    pauseWorldCallee.toB256.toAdr ≠
      stubPauseWorldSevm.currentTarget := by
  rw [toAdr_toB256, stubPauseWorld_currentTarget]
  exact pauseWorld_callee_ne_owner

private theorem stubPauseWorld_target_not_precompile :
    stubPauseWorldSevm.benvStat.rules.isPrecomp pauseWorldCallee = false := by
  native_decide

/-- Every exact `pauseAfterSet` occurrence extracted from the concrete run
contains the actual compiled-stub CALL and STATICCALL executions. -/
theorem stubPauseWorld_boundaryExecutions
    (entry : Devm)
    (reached : PublicPauseAfterSetAt
      ((runtime officialParams).main :: (runtime officialParams).aux)
      stubPauseWorldSevm stubPauseWorldPre pauseWorldCallee.toB256
      pauseWorldDuration PinnedTargetControl.stubCode
      (.ok stubPauseWorldFinal) entry) :
    LidoPinnedBoundaryExecutions
      ((runtime officialParams).main :: (runtime officialParams).aux)
      stubPauseWorldSevm entry pauseWorldCallee
      PinnedTargetControl.stubProgram pauseWorldDuration
      (.ok stubPauseWorldFinal) := by
  rcases reached with
    ⟨targetWindow, durationWindow, targetCodeAt, -, afterSetRun⟩
  rw [toAdr_toB256] at targetCodeAt
  exact stubBoundaryExecutions_of_afterSet_ok
    (by rfl) (by rfl) pauseWorld_callee_ne_owner
    stubPauseWorld_target_not_precompile targetCodeAt targetWindow
    durationWindow stubPauseWorld_publicPausePremises.entered
    stubPauseWorld_publicPausePremises.dynamic afterSetRun

/-- Closed concrete application of the full production T2 committed-outcome
family.  Its noninterference premise is derived from this run's actual stub
CALL and STATICCALL occurrences. -/
theorem stubPauseWorld_committed_outcomes :
    PublicPauseCommittedOutcomes stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldDuration
      PinnedTargetControl.stubCode (.ok stubPauseWorldFinal) := by
  apply publicPause_stub_committed_outcomes
    stubPauseWorld_publicPausePremises stubPauseWorld_target_ne_owner
    stubPauseWorld_run rfl
  intro entry reached
  simpa only [toAdr_toB256] using
    stubPauseWorld_boundaryExecutions entry reached

/-- Closed end-to-end public composition control: the same concrete final
state carries the full T2 family, the actual target invocation witness, and
the target's `PausedAt` conclusion. -/
theorem stubPauseWorld_pinnedTarget :
    PublicPausePinnedTargetConclusion stubPauseWorldSevm stubPauseWorldPre
      pauseWorldCallee.toB256 pauseWorldDuration
      PinnedTargetControl.stubCode PinnedTargetControl.stubProgram
      PinnedTargetControl.pausedUntil (.ok stubPauseWorldFinal)
      stubPauseWorldFinal := by
  obtain ⟨entry, reached⟩ := publicPause_reaches_pauseAfterSet
    stubPauseWorld_publicPausePremises stubPauseWorld_run
  apply publicPause_stubPinnedTarget stubPauseWorld_publicPausePremises
    stubPauseWorld_target_ne_owner stubPauseWorld_run entry reached
  · simpa only [toAdr_toB256] using
      stubPauseWorld_boundaryExecutions entry reached
  · rfl

end Blanc.LidoCircuitBreaker
