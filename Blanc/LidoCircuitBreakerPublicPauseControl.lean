import Blanc.LidoCircuitBreakerPublicPause
import Blanc.LidoCircuitBreakerPauseJoin
import Blanc.LidoCircuitBreakerPauseWorldRun

/-!
# Public-pause anti-vacuity control

The row-19 production witness instantiates the public-entry premise bundle and
therefore the outcome family's exact reached-state theorem.  This is a control
for premise inhabitation, not a new contract or a liveness claim.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- The existing row-19 production world satisfies every public-entry premise
without assuming its terminal result. -/
theorem pauseLastWorld_publicPausePremises :
    PublicPauseEntryPremises pauseLastSevm pauseLastPre configWorldOwner
      pauseWorldCallee.toB256 pauseWorldDuration 1 1
      pauseWorldCallee.toB256 [] calleeCode := by
  refine {
    productionBytes := pauseWorld_codeBytes _ _
    currentTarget := pauseWorld_currentTarget _ _
    codeAddress := pauseWorld_codeAddress _ _
    valueZero := pauseWorld_value _ _
    dynamic := pauseWorld_static _ _
    entered := ?_
    image := ?_
    calldata := pauseWorld_data _ _
    selectorEq := pauseWorld_selector _ _
    targetCanonical := validAdr_toB256 pauseWorldCallee
    targetNonzero := by decide
    callerNonzero := ?_
    unlocked := ?_
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
  · simp only [pauseLastSevm]
    rw [pauseWorld_depth]
    decide
  · simp only [pauseLastPre]
    unfold MemImage
    rw [pauseWorld_memory]
    exact ⟨Mem.wf_empty, Mem.reads_empty⟩
  · simp only [pauseLastSevm]
    rw [pauseWorld_callerWord]
    decide
  · rfl
  · rw [show (pauseWorldCallee.toB256).toAdr = pauseWorldCallee from
      toAdr_toB256 pauseWorldCallee]
    exact pauseWorld_calleeCodeAt _ _
  · simp only [pauseLastSevm, pauseLastPre]
    rw [pauseWorld_currentTarget, pauseWorld_callerWord]
    exact pauseWorld_lastAssignment _
  · simp only [pauseLastSevm, pauseLastPre]
    rw [pauseWorld_time, pauseWorld_currentTarget, pauseWorld_callerWord,
      pauseWorld_getStorVal, pauseLastStor_expiry]
    decide
  · simp only [pauseLastSevm, pauseLastPre]
    rw [pauseWorld_currentTarget, pauseWorld_getStorVal,
      pauseLastStor_duration]
  · simp only [pauseLastSevm, pauseLastPre]
    rw [pauseWorld_currentTarget, pauseWorld_getStorVal,
      pauseLastStor_index]
  · simp only [pauseLastSevm, pauseLastPre]
    rw [pauseWorld_currentTarget, pauseWorld_getStorVal,
      pauseLastStor_length]
  · simp only [pauseLastSevm, pauseLastPre]
    rw [pauseWorld_currentTarget, pauseWorld_getStorVal,
      pauseLastStor_entry]
  · simp only [pauseLastSevm]
    rw [pauseWorld_callerWord]
    exact pauseWorld_assignCallee_ne_count
  · simp only [pauseLastSevm]
    rw [pauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm
  · simp only [pauseLastSevm]
    rw [pauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · simp only [pauseLastSevm]
    rw [pauseWorld_callerWord]
    exact pauseWorld_indexCallee_ne_count.symm
  · simp only [pauseLastSevm]
    rw [pauseWorld_callerWord]
    exact pauseWorld_length_ne_count.symm
  · simp only [pauseLastSevm]
    rw [pauseWorld_callerWord]
    exact pauseWorld_entryOne_ne_count.symm

/-- Anti-vacuity: the public-entry reached-state theorem is inhabited by the
existing complete row-19 production run. -/
theorem pauseLastWorld_publicPauseReach :
    ∃ post : Devm,
      PublicPauseAfterSetReach
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseLastSevm pauseLastPre pauseWorldCallee.toB256 pauseWorldDuration
        calleeCode (.ok post) := by
  obtain ⟨post, run, _compiled⟩ := pauseLastWorld_run
  exact ⟨post,
    publicPause_reaches_pauseAfterSet pauseLastWorld_publicPausePremises run⟩

end Blanc.LidoCircuitBreaker
