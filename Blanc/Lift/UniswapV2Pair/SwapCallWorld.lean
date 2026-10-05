import Blanc.Lift.UniswapV2Pair.MutableTurns

/-!
# World effects of a mutable external call, tied to its turns

`mutable_call_turns` derives the turn queue of one actual CALL/STATICCALL step and says, in a
separate existential, which child produced the turns. This module restates that consumption
with the child pinned to the step itself (`Xinst.Run` of the same pre-state and post-state)
and adds what the child derivation gives for the storage of every code-bearing account after
the call: the committed child's endpoint storage when the turns come from a committed child,
and the pre-call storage when the call produced no turn (no frame was entered, or the entered
child rolled back). The swap frame consumes it for its two optimistic transfers and its
callback.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The provenance of one actual mutable call step `pre → d` of derivation `D` with turn
queue `turns`: either no turn, no committed child and every code-bearing account's storage
as before the call; or one committed child of this very step, a sub-derivation of `D`, whose
retained Pair events are the turns and whose committed endpoint is every code-bearing
account's storage after the call. -/
def MutableCallWorld (pair : Adr) (D : Exec.Deriv) (sevm : Sevm) (pre : Devm) (x : Xinst)
    (d : Devm) (turns : List MutableTurn) : Prop :=
  (turns = [] ∧
    (Xinst.Run sevm pre x .none (.ok d) ∨ ∃ (child : Evm) (raw : Execution),
      Xinst.Run sevm pre x (.some ⟨child, raw⟩) (.ok d) ∧ ¬ Execution.commits raw = true) ∧
    ∀ a, pre.getCode a ≠ .empty → ∀ key, (d.getStor a).get key = (pre.getStor a).get key) ∨
  ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw)
    (committed : Execution.commits raw = true),
    Xinst.Run sevm pre x (.some ⟨child, raw⟩) (.ok d) ∧
    (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
    turns.map MutableTurn.event = Exec.targetLogEventsFrom pair [] 0 childRun committed ∧
    ∀ a, pre.getCode a ≠ .empty → ∀ key,
      (d.getStor a).get key = ((Execution.committedPost raw committed).getStor a).get key

/-- `mutable_call_turns` with the deriving child pinned to the step and the storage of every
code-bearing account after the call (`MutableCallWorld`). -/
theorem mutable_call_world {pair : Adr} {Rep : State → Stor → Prop} {Good : Exec.Deriv → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop} {owned : Event → Option Log}
    (supply : PairFrameSupply pair Rep Good Auth owned)
    (repCongr : ∀ st (s s' : Stor), (∀ k, s'.get k = s.get k) → Rep st s → Rep st s')
    (sem : CodeSem) (image : sem.image = some code.toList)
    {D : Exec.Deriv} {frame : Frame} {request : Request} {sevm : Sevm} {pre d : Devm}
    {x : Xinst} (call : Blanc.Lift.StepIn D sevm pre (.exec x) d)
    (callFamily : x = .call ∨ x = .staticcall)
    (pairEq : frame.context.pair = pair) (mutable : externalStatic frame request = false)
    (installed : some (pre.getCode pair).toList = sem.image)
    (rep : Rep frame.current.state (pre.getStor pair))
    (time : frame.context.timestamp = sevm.benvStat.time)
    (fork : CoveredFork sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = pair → Good F) :
    ∃ (turns : List MutableTurn) (c : Checkpoint) (added : List PendingLog)
      (rets : List ChildReturn),
      ExactTurns frame request 0 (mutableTranscript turns .done)
        { complete := true, frame := { frame with current := c }, childReturns := rets } ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
        Auth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      Rep c.state (d.getStor pair) ∧ c.logs = frame.current.logs ++ added ∧
      (∃ L : List Log, d.logs = pre.logs ++ L ∧
        added.map (PendingLog.rawWith owned) = L.map some) ∧
      MutableCallWorld pair D sevm pre x d turns := by
  have nonempty : pre.getCode pair ≠ .empty := by
    intro empty
    have imageEmpty : sem.image = some [] := by
      rw [← installed, empty, ByteArray.toList_empty]
    exact sem.ne_nil imageEmpty rfl
  have unchanged : d.logs = pre.logs →
      (∀ a, pre.getCode a ≠ .empty → ∀ key, (d.getStor a).get key = (pre.getStor a).get key) →
      (Xinst.Run sevm pre x .none (.ok d) ∨ ∃ (child : Evm) (raw : Execution),
        Xinst.Run sevm pre x (.some ⟨child, raw⟩) (.ok d) ∧ ¬ Execution.commits raw = true) →
      ∃ (turns : List MutableTurn) (c : Checkpoint) (added : List PendingLog)
        (rets : List ChildReturn),
        ExactTurns frame request 0 (mutableTranscript turns .done)
          { complete := true, frame := { frame with current := c }, childReturns := rets } ∧
        (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
          Auth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
        Rep c.state (d.getStor pair) ∧ c.logs = frame.current.logs ++ added ∧
        (∃ L : List Log, d.logs = pre.logs ++ L ∧
          added.map (PendingLog.rawWith owned) = L.map some) ∧
        MutableCallWorld pair D sevm pre x d turns := by
    intro unlogged same reason
    refine ⟨[], frame.current, [], [], ExactTurns.done frame request 0, ?_,
      repCongr _ _ _ (same pair nonempty) rep, (List.append_nil _).symm,
      ⟨[], by rw [unlogged, List.append_nil], rfl⟩, Or.inl ⟨rfl, reason, same⟩⟩
    intro located entry nested member
    simp only [List.not_mem_nil] at member
  obtain ⟨xl, inRoots, pc, stepRun⟩ := call
  have xrun : Xinst.Run sevm pre x xl (.ok d) := by
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at stepRun
    exact stepRun
  cases xl with
  | none =>
    have storage := Xinst.none_getStor_eq xrun
    exact unchanged ((Xinst.call_run_logs fork callFamily xrun).1 rfl)
      (fun a _ key => by rw [storage]) (Or.inl xrun)
  | some slot =>
    obtain ⟨child, raw⟩ := slot
    obtain ⟨childRun, childRoots⟩ := inRoots
    have spawnRun := xrun
    unfold Xinst.Run XStep.Run at spawnRun
    cases spawned : Xinst.step sevm pre x with
    | done result =>
      rw [spawned] at spawnRun
      cases spawnRun.1
    | spawn callee resume =>
      rw [spawned] at spawnRun
      obtain ⟨settled, runFrame, resumed⟩ := spawnRun
      unfold RunFrame at runFrame
      cases entered : callee.enter with
      | done result =>
        rw [entered] at runFrame
        cases runFrame.1
      | run evm =>
        rw [entered] at runFrame
        obtain ⟨raw', slotEq, settledEq⟩ := runFrame
        cases slotEq
        rw [settledEq] at resumed
        have world := fun a (codeA : pre.getCode a ≠ .empty) =>
          Xinst.spawn_run_getStor fork spawned entered childRun resumed.symm codeA
        by_cases settles : Jaune.Frame.settlementCommits callee raw = true
        · have committed := Jaune.Frame.raw_commits_of_settlementCommits settles
          obtain ⟨entryWorld, _, entry, stat, childFork, short⟩ :=
            Xinst.spawn_child_world fork spawned entered
          have childInstalled := CodeSem.At.callChild spawned entered callFamily installed
          have childRep : Rep frame.current.state (child.dyna.getStor pair) := by
            rw [entryWorld pair nonempty]
            exact rep
          obtain ⟨turns, c, added, L, rets, events, auth, finalRep, cLogs, rawLogs, images,
              consume⟩ :=
            mutable_retained_fold_inv supply repCongr sem image childRun committed frame 0 0 []
              pairEq mutable childInstalled childRep (fun _ => entry) short
              (by rw [stat]; exact time) childFork
              (fun located member => by
                obtain ⟨root, target⟩ :=
                  Exec.retainedTargetFramesFromAt_rawFrameRoot pair childRun committed member
                exact good _ (childRoots _ root) target)
          have finished := consume .done
            { complete := true, frame := { frame with current := c }, childReturns := [] }
            (ExactTurns.done _ request _)
          have callLogs := ((Xinst.call_run_logs fork callFamily xrun).2 child raw rfl).1 committed
          have childLogs := Xinst.spawn_child_logs fork spawned entered
          refine ⟨turns, c, added, rets, ?_, auth,
            repCongr _ _ _ ((world pair nonempty).1 settles) finalRep, cLogs,
            ⟨L, by rw [callLogs, rawLogs, childLogs, List.nil_append], images⟩,
            Or.inr ⟨child, raw, childRun, committed, xrun, childRoots, events,
              fun a codeA => (world a codeA).1 settles⟩⟩
          simpa only [List.append_nil] using finished
        · have notCommitted : ¬ Execution.commits raw = true := by
            intro committed
            obtain ⟨msg, calleeEq⟩ := Xinst.call_spawn_ofCall fork callFamily spawned
            subst calleeEq
            exact settles (Jaune.Frame.settlementCommits_ofCall_of_raw_commits committed)
          exact unchanged
            (((Xinst.call_run_logs fork callFamily xrun).2 child raw rfl).2 notCommitted)
            (fun a codeA => (world a codeA).2 settles)
            (Or.inr ⟨child, raw, xrun, notCommitted⟩)

end Blanc.Lift.UniswapV2Pair
