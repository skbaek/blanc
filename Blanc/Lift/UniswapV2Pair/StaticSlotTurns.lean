import Blanc.Lift.UniswapV2Pair.StaticViewTurns
import Blanc.ExecutionPathLocator

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The SAME supplied STATICCALL slot supplies its actual ordered static turn
queue. Entry/code/context are derived from its primitive and frame equations. -/
theorem sync_static_slot_turns_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {path : List Nat} {root : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence root)
    (instruction : occurrence.instruction = Ninst.staticcall)
    {callee : Jaune.Frame} {resume : Resume} {pc' : Nat}
    {childEvm : Evm} {raw : Execution}
    (slot : occurrence.slot = .some ⟨childEvm, raw⟩)
    (step : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
      .spawn callee resume pc')
    (enter : callee.enter = .run childEvm)
    (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (occurrence.node.devm.getCode frame.context.pair).toList = sem.image)
    (rep : WriterRep K (occurrence.node.devm.getStor frame.context.pair) frame.current.state)
    (fresh : ∀ located ∈ (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight?,
      WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm))
    (time : frame.context.timestamp = occurrence.node.sevm.benvStat.time)
    (fork : CoveredFork occurrence.node.sevm.benvStat.fork) :
    occurrence.slot = .some ⟨childEvm, raw⟩ ∧
      ∃ views : List StaticViewTurn,
        views.map Prod.fst =
          (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight? ∧
        (∀ picked ∈ views, picked.Authentic frame) ∧
        ExactTurns frame request 0 (staticViewTranscript views .done)
          { complete := true, frame := frame,
            childReturns := staticViewChildReturns frame request 0 views } := by
  have decoded : Ninst.At occurrence.node.sevm.code occurrence.node.pc Ninst.staticcall := by
    rw [← instruction]
    exact occurrence.decoded
  have primitiveSpawn : Ninst.step
      ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ Ninst.staticcall =
      .spawn callee resume pc' := by
    rw [← Evm.step_next decoded]
    exact step
  have xspawn : Xinst.step occurrence.node.sevm occurrence.node.devm .staticcall =
      .spawn callee resume := XStep.toStep_spawn (by
    simpa only [Ninst.staticcall, Ninst.step_exec] using primitiveSpawn)
  have nonempty : occurrence.node.devm.getCode frame.context.pair ≠ .empty := by
    intro empty
    have imageEmpty : sem.image = some [] := by
      rw [← installed, empty, ByteArray.toList_empty]
    exact sem.ne_nil imageEmpty rfl
  obtain ⟨pcZero, codes, actualCode⟩ := Blanc.Evm.step_spawn_child step enter
  have childInstalled : sem.At frame.context.pair childEvm.pc childEvm.sta childEvm.dyna := by
    refine ⟨?_, ?_⟩
    · rw [codes]
      exact installed
    · intro target
      have childCode : childEvm.sta.code = occurrence.node.devm.getCode frame.context.pair := by
        by_cases same : occurrence.node.sevm.currentTarget = childEvm.sta.currentTarget
        · have sameInner : callee.inner.currentTarget = occurrence.node.sevm.currentTarget :=
            (Blanc.Frame.enter_run_currentTarget enter).symm.trans same.symm
          have direct := Blanc.Xinst.step_staticcall_sameTarget_code xspawn sameInner
            (by rw [← Blanc.Frame.enter_run_currentTarget enter, target]
                exact sem.not_delegation installed)
          rw [Blanc.Frame.enter_run_code enter, direct,
            ← Blanc.Frame.enter_run_currentTarget enter, target]
        · rw [← target]
          exact actualCode same (by rw [target]; exact nonempty)
            (by rw [target]; exact sem.not_delegation installed)
      exact ⟨(congrArg (fun bytes : ByteArray => some bytes.toList) childCode).trans installed, pcZero⟩
  have storageEq := (Blanc.Evm.step_spawn_child_world fork step enter nonempty).1
  change childEvm.dyna.getStor frame.context.pair =
    occurrence.node.devm.getStor frame.context.pair at storageEq
  have childRep : WriterRep K (childEvm.dyna.getStor frame.context.pair) frame.current.state := by
    rw [storageEq]
    exact rep
  have entry : childEvm.dyna.stack = [] ∧ childEvm.dyna.memory = Mem.empty := by
    obtain ⟨benv, _, rfl⟩ := Jaune.Frame.enter_run_inv enter
    exact ⟨rfl, rfl⟩
  obtain ⟨short, childFork⟩ := Blanc.ExecutionTrace.Evm.step_spawn_child_data fork step enter
  have childStatic := Blanc.Ninst.step_staticcall_run_isStatic primitiveSpawn enter
  have statEq : childEvm.sta.benvStat = occurrence.node.sevm.benvStat :=
    (Jaune.Frame.enter_run_benvStat enter).trans (Xinst.step_spawn_benvStat xspawn)
  refine ⟨slot, ?_⟩
  apply staticView_raw_retained_turns_inv sem image childRun childInstalled childRep fresh
    (fun _ => entry) short
  · rw [statEq]
    exact time
  · exact childStatic
  · exact childFork




/-- The existing filtered-slot fold at the supplied actual first occurrence. -/
theorem sync_static_slot_filtered_turns_inv {K : WriterKey → Prop}
    {frame : Frame} {request : Request} {path : List Nat} {root : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence root) (returned : Exec.Deriv)
    (instruction : occurrence.instruction = Ninst.staticcall)
    (result : occurrence.stepResult = .ok returned.devm)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (occurrence.node.devm.getCode frame.context.pair).toList = sem.image)
    (rep : WriterRep K (occurrence.node.devm.getStor frame.context.pair) frame.current.state)
    (time : frame.context.timestamp = occurrence.node.sevm.benvStat.time)
    (fork : CoveredFork occurrence.node.sevm.benvStat.fork) :
      ((occurrence.slot = .none ∧
          ExactTurns frame request 0 .done
            { complete := true, frame := frame, childReturns := [] }) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' occurrence.node.sevm returned.devm occurrence.node.exn)
          (spawn : Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned.devm),
          occurrence.slot = .some ⟨childEvm, raw⟩ ∧
          occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
          ((∀ located ∈
            (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight?
            else []),
            WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm)) →
            ∃ views : List StaticViewTurn,
              views.map Prod.fst =
                (if Jaune.Frame.settlementCommits callee raw = true then
              (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight?
            else []) ∧
              (∀ picked ∈ views, picked.Authentic frame) ∧
              ExactTurns frame request 0 (staticViewTranscript views .done)
                { complete := true, frame := frame,
                  childReturns := staticViewChildReturns frame request 0 views })) := by
  have actual : Step.Run
      (Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩)
      occurrence.slot (.ok returned.devm) := by
    rw [Evm.step_next occurrence.decoded]
    change Ninst.StepRun occurrence.node.pc occurrence.node.sevm occurrence.node.devm
      occurrence.instruction occurrence.slot (.ok returned.devm)
    rw [← result]
    exact occurrence.stepRun
  cases slotEq : occurrence.slot with
  | none =>
    exact Or.inl ⟨rfl, ExactTurns.done _ _ _⟩
  | some pairSlot =>
    rcases pairSlot with ⟨childEvm, raw⟩
    have actualSome : Step.Run
        (Evm.step ⟨occurrence.node.pc, occurrence.node.sevm, occurrence.node.devm⟩)
        (.some ⟨childEvm, raw⟩) (.ok returned.devm) := by
      simpa only [slotEq] using actual
    obtain ⟨callee, resume, pc', spawn, enter, resumed⟩ := Step.Run.some_inv actualSome
    have filled := occurrence.filled
    rw [slotEq] at filled
    obtain ⟨childRun⟩ := filled
    obtain ⟨next, exactRun⟩ := Exec.exists_next_of_run_spawn occurrence.node.exc
      spawn enter childRun resumed.symm
    refine Or.inr ⟨childEvm, raw, callee, resume, pc', childRun, next,
      spawn, enter, resumed.symm, rfl, exactRun, ?_⟩
    intro fresh
    by_cases committed : Jaune.Frame.settlementCommits callee raw = true
    · have selectedFresh : ∀ located ∈
          (Exec.retainedTargetTurnsAt frame.context.pair path childRun).filterMap Sum.getRight?,
          WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm) := by
        simpa only [ite_eq_left committed] using fresh
      obtain ⟨views, mapped, authentic, exactTurns⟩ :=
        (sync_static_slot_turns_inv occurrence instruction slotEq spawn enter childRun
          sem image installed rep selectedFresh time fork).2
      exact ⟨views, by simpa only [ite_eq_left committed] using mapped, authentic, exactTurns⟩
    · refine ⟨[], ?_, ?_, ?_⟩
      · simp only [List.map_nil, ite_eq_right committed]
      · intro picked member
        cases member
      · exact ExactTurns.done _ _ _

end Blanc.Lift.UniswapV2Pair
