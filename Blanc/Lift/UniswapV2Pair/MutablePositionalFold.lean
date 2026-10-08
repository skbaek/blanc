import Blanc.Lift.UniswapV2Pair.MutableTurns
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueEquality
import Blanc.Lift.CursorOccurrenceRoots

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- A child consumes the same incoming segment and result and retains its actual output. -/
def PositionalChildConsumes (D : Exec.Deriv) (segment : SegmentResult)
    (transcript : Transcript) (child : RunResult) : Prop :=
  PositionalConsumes D D 0 segment transcript child ∧
    ∀ committed : Execution.commits D.exn = true,
      child.status = .success (Execution.committedPost D.exn committed).output

/-- Positional turns instantiate the original fold's two introductions. -/
theorem positionalMutableTurnRules :
    MutableTurnRules PositionalChildConsumes PositionalMutableTurns := by
  refine ⟨fun mutable rest => .foreignLog mutable rest, ?_⟩
  intro frame request turn located entry events nested tail child out selected rest
  exact .invoke selected.1 (selected.2 located.frame.committed) rest

/-- Fold the complete events of this original call slot at its full parent index. -/
theorem mutable_source_slot_turns
    {pair : Adr} {Rep : State → Stor → Prop} {Good : Exec.Deriv → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop} {owned : Event → Option Log}
    (supply : PairFrameSupplyWith PositionalChildConsumes pair Rep Good Auth owned)
    (repCongr : ∀ st (s s' : Stor), (∀ k, s'.get k = s.get k) → Rep st s → Rep st s')
    (sem : CodeSem) (image : sem.image = some code.toList)
    {root : Exec.Deriv} {frame : Frame} {request : Request} {reply : ExternalResult} {index : Nat}
    (observed : SourceCallAt root frame request reply index)
    (pairEq : frame.context.pair = pair) (mutable : externalStatic frame request = false)
    (installed : some (observed.call.occurrence.node.devm.getCode pair).toList = sem.image)
    (rep : Rep frame.current.state (observed.call.occurrence.node.devm.getStor pair))
    (time : frame.context.timestamp = observed.call.occurrence.node.sevm.benvStat.time)
    (fork : CoveredFork observed.call.occurrence.node.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = pair → Good F) :
    ∃ (events : List (Log ⊕ Exec.LocatedFrame)) (turns : List MutableTurn)
      (c : Checkpoint) (added : List PendingLog) (rets : List ChildReturn),
      SourceSlotEvents observed.call frame.context.pair index events ∧
      events.filterMap Sum.getRight? = observed.paths ∧
      turns.map MutableTurn.event = events ∧
      PositionalMutableTurns frame request 0 events (mutableTranscript turns .done)
        {complete := true, frame := {frame with current := c}, childReturns := rets} ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
        Auth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      Rep c.state (observed.call.returned.devm.getStor pair) ∧
      c.logs = frame.current.logs ++ added ∧
      ∃ L : List Log,
        observed.call.returned.devm.logs = observed.call.occurrence.node.devm.logs ++ L ∧
        added.map (PendingLog.rawWith owned) = L.map some := by
  let call := observed.call
  let x : Xinst := match request.kind with | .call => .call | .staticCall => .staticcall
  have family : x = .call ∨ x = .staticcall := by
    dsimp only [x]
    cases request.kind with
    | call => exact Or.inl rfl
    | staticCall => exact Or.inr rfl
  have decoded : Xinst.At call.occurrence.node.sevm.code call.occurrence.node.pc x := by
    have opcode :=  call.occurrence.decoded
    rw [call.instruction] at opcode
    exact opcode
  have primitive : Xinst.Run call.occurrence.node.sevm call.occurrence.node.devm x
      call.occurrence.slot (.ok call.returned.devm) := by
    have run := call.occurrence.stepRun
    rw [call.instruction, call.result, Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at run
    exact run
  have nonempty : call.occurrence.node.devm.getCode pair ≠ .empty := by
    intro empty
    have imageEmpty : sem.image = some [] := by
      rw [← installed, empty, ByteArray.toList_empty]
    exact sem.ne_nil imageEmpty rfl
  have unchanged : ∀ events,
      SourceSlotEvents call frame.context.pair index events → events = [] →
      (∀ k, (call.returned.devm.getStor pair).get k =
        (call.occurrence.node.devm.getStor pair).get k) →
      call.returned.devm.logs = call.occurrence.node.devm.logs →
      ∃ (turns : List MutableTurn) (c : Checkpoint) (added : List PendingLog)
        (rets : List ChildReturn),
        events.filterMap Sum.getRight? = observed.paths ∧
        turns.map MutableTurn.event = events ∧
        PositionalMutableTurns frame request 0 events (mutableTranscript turns .done)
          {complete := true, frame := {frame with current := c}, childReturns := rets} ∧
        (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
          Auth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
        Rep c.state (call.returned.devm.getStor pair) ∧ c.logs = frame.current.logs ++ added ∧
        ∃ L : List Log, call.returned.devm.logs = call.occurrence.node.devm.logs ++ L ∧
          added.map (PendingLog.rawWith owned) = L.map some := by
    intro events actual empty same logs
    subst events
    refine ⟨[], frame.current, [], [], actual.queue.paths_unique observed.queue, rfl,
      PositionalMutableTurns.done frame request 0, ?_, repCongr _ _ _ same rep,
      (List.append_nil _).symm, [], ?_, rfl⟩
    · intro located entry nested member
      simp only [List.not_mem_nil] at member
    · rw [logs, List.append_nil]
  rcases observed.queue with ⟨none, paths⟩ |
    ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed, slot, run, paths⟩
  · have actual : SourceSlotEvents call frame.context.pair index [] := Or.inl ⟨none, rfl⟩
    rw [none] at primitive
    obtain ⟨turns, c, added, rets, rest⟩ := unchanged [] actual rfl
      (fun k => by rw [Xinst.none_getStor_eq primitive])
      ((Xinst.call_run_logs fork family primitive).1 rfl)
    exact ⟨[], turns, c, added, rets, actual, rest⟩
  · let events := if settles : Jaune.Frame.settlementCommits callee raw = true then
        Exec.targetLogEventsFrom frame.context.pair [index] 0 child
          (Jaune.Frame.raw_commits_of_settlementCommits settles) else []
    have actual : SourceSlotEvents call frame.context.pair index events :=
      Or.inr ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed, slot, run, rfl⟩
    obtain ⟨xi, opcode, spawned, pcEq⟩ := Evm.step_spawn_inv spawn
    have same : xi = x := Ninst.exec.inj (Inst.next.inj (Option.some.inj (opcode.symm.trans decoded)))
    subst xi
    have childRoots := call.slotFilledWith
    rw [slot] at childRoots
    obtain ⟨selected, roots⟩ := childRoots
    have sameRun := Exec.unique selected child
    subst selected
    obtain ⟨settledStorage, rolledStorage⟩ :=
      Evm.step_run_getStor fork spawn enter child resumed nonempty
    by_cases settles : Jaune.Frame.settlementCommits callee raw = true
    · have committed := Jaune.Frame.raw_commits_of_settlementCommits settles
      obtain ⟨world, _, entry, stat, childFork, short⟩ :=
        Xinst.spawn_child_world fork spawned enter
      have childInstalled := CodeSem.At.callChild spawned enter family installed
      have childRep : Rep frame.current.state (evm.dyna.getStor pair) := by
        rw [world pair nonempty]
        exact rep
      obtain ⟨turns, c, added, L, rets, mapped, auth, finalRep, sourceLogs, rawLogs,
        images, consume⟩ :=
        mutable_retained_fold_inv_with supply positionalMutableTurnRules repCongr sem image child
          committed frame 0 0 [index] pairEq mutable childInstalled childRep (fun _ => entry)
          short (by rw [stat]; exact time) childFork
          (fun located member => by
            obtain ⟨root, target⟩ :=
              Exec.retainedTargetFramesFromAt_rawFrameRoot pair child committed member
            exact good _ (roots _ root) target)
      have finished := consume [] .done
        {complete := true, frame := {frame with current := c}, childReturns := []}
        (PositionalMutableTurns.done _ request _)
      have callLogs := ((Xinst.call_run_logs fork family primitive).2 evm raw slot).1 committed
      have childLogs := Xinst.spawn_child_logs fork spawned enter
      refine ⟨events, turns, c, added, rets, actual, actual.queue.paths_unique observed.queue,
        ?_, ?_, auth, repCongr _ _ _ (settledStorage settles) finalRep, sourceLogs,
        L, ?_, images⟩
      · simpa only [events, dite_eq_left settles, pairEq] using mapped
      · simpa only [events, dite_eq_left settles, pairEq, List.append_nil] using finished
      · rw [callLogs, rawLogs, childLogs, List.nil_append]
    · have empty : events = [] := by
        dsimp only [events]
        rw [dite_eq_right settles]
      have notCommitted : ¬ Execution.commits raw = true := by
        intro committed
        obtain ⟨calleeEq, _, _⟩ := Step.spawn.inj (spawn.symm.trans observed.spawned)
        apply settles
        rw [calleeEq]
        exact Jaune.Frame.settlementCommits_ofCall_of_raw_commits committed
      obtain ⟨turns, c, added, rets, rest⟩ := unchanged events actual empty (rolledStorage settles)
        (((Xinst.call_run_logs fork family primitive).2 evm raw slot).2 notCommitted)
      exact ⟨events, turns, c, added, rets, actual, rest⟩

end Blanc.Lift.UniswapV2Pair
