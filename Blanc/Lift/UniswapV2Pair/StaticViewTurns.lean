import Blanc.Lift.UniswapV2Pair.StaticViewSource
import Blanc.Lift.SegmentedHistory

/-! Actual static getter executions supply invocation turns at the incoming checkpoint. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- A successful raw static view supplies one exact source invocation and extends only
its decoded finite footprint. Its actual sender, value, static flag and return bytes are retained. -/
theorem staticView_turn_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {turn : Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) frame.current.state)
    (fresh : WriterFreshKeys K (staticViewDecodedKeys sevm))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∃ view : StaticView,
      Blanc.Sevm.selector sevm = view.selector ∧
      view.argumentSize + 4 ≤ sevm.data.length ∧
      some post.output = getterResult frame.current.state (view.entry sevm) ∧
      WriterRep (WriterExtend K (staticViewDecodedKeys sevm))
        (post.getStor sevm.currentTarget) frame.current.state ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧
      (∀ (tail : Transcript) (out : TurnsResult),
        ExactTurns frame request (turn + 1) tail out →
        ExactTurns frame request turn
          (.invoke sevm.caller sevm.value sevm.isStatic (view.entry sevm) .done tail)
          { out with childReturns :=
              [{ context := childContext frame request turn sevm.caller sevm.value sevm.isStatic,
                 entry := view.entry sevm, status := .success post.output }] ++ out.childReturns }) := by
  let ctx := childContext frame request turn sevm.caller sevm.value sevm.isStatic
  obtain ⟨_, view, selector, length, result, storage, logs,
    _, _, consumed, _, _, _⟩ :=
    staticView_source_handler_inv rep fresh representable (ctx := ctx) rfl
      codeEq fork static run
  have extended : WriterRep (WriterExtend K (staticViewDecodedKeys sevm))
      (post.getStor sevm.currentTarget) frame.current.state := by
    rw [storage sevm.currentTarget]
    exact rep.extend fresh
  refine ⟨view, selector, length, result, extended, storage, logs, ?_⟩
  intro tail out rest
  have invoked := ExactTurns.invoke (frame := frame) (request := request)
    (turn := turn) consumed rest
  exact invoked


/-- A committing target-root view supplies the entire selected queue at its
original entering path. The source tail is constructed from the actual
singleton projection, and the physical context fields match this raw frame. -/
theorem staticView_target_turns_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {turn : Nat} {path : List Nat}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) frame.current.state)
    (fresh : WriterFreshKeys K (staticViewDecodedKeys sevm))
    (representable : sevm.data.length < 2 ^ 256)
    (pair : frame.context.pair = sevm.currentTarget)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∃ view : StaticView,
      Blanc.Sevm.selector sevm = view.selector ∧
      view.argumentSize + 4 ≤ sevm.data.length ∧
      some post.output = getterResult frame.current.state (view.entry sevm) ∧
      WriterRep (WriterExtend K (staticViewDecodedKeys sevm))
        (post.getStor sevm.currentTarget) frame.current.state ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧
      (∀ committed : Execution.commits (.ok post) = true,
        Exec.retainedTargetTurnsAt sevm.currentTarget path run =
          [.inr ⟨path, Exec.Frame.ofRun run committed⟩]) ∧
      childContext frame request turn sevm.caller sevm.value sevm.isStatic =
        { pair := sevm.currentTarget, sender := sevm.caller, value := sevm.value,
          timestamp := sevm.benvStat.time, isStatic := true,
          invocation := frame.context.invocation ++ [request.site.ordinal, turn] } ∧
      ExactTurns frame request turn
        (.invoke sevm.caller sevm.value sevm.isStatic (view.entry sevm) .done .done)
        { complete := true, frame := frame,
          childReturns :=
            [{ context := childContext frame request turn sevm.caller sevm.value sevm.isStatic,
               entry := view.entry sevm, status := .success post.output }] } := by
  obtain ⟨view, selector, length, result, extended, storage, logs, consume⟩ :=
    staticView_turn_inv (request := request) (turn := turn)
      rep fresh representable codeEq fork static run
  refine ⟨view, selector, length, result, extended, storage, logs, ?_, ?_, ?_⟩
  · intro committed
    rw [Exec.retainedTargetTurnsAt_eq_map_prefix,
      Exec.retainedTargetTurns_target_stop sevm.currentTarget run committed rfl]
    simp only [List.map_cons, List.map_nil, Exec.RetainedTargetTurn.rebase,
      List.append_nil]
  · simp only [childContext, pair, time, static, Bool.or_true]
  · exact consume .done { complete := true, frame := frame, childReturns := [] }
      (ExactTurns.done frame request (turn + 1))


/-- A halted foreign static frame emits no selected Pair invocation. The
source queue is derived from this actual retained projection. -/
theorem staticView_foreign_halt_turns_inv {frame : Frame} {request : Request}
    {turn : Nat} {path : List Nat} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .halt out)
    (foreign : sevm.currentTarget ≠ frame.context.pair)
    (static : sevm.isStatic = true) :
    (Exec.retainedTargetTurnsAt frame.context.pair path (.halt step)).filterMap
      Sum.getRight? = [] ∧
    ExactTurns frame request turn .done
      { complete := true, frame := frame, childReturns := [] } := by
  refine ⟨?_, ExactTurns.done frame request turn⟩
  by_cases committed : Execution.commits out = true
  · rw [Exec.retainedTargetTurnsAt_filterMap_eq _ _ _ committed,
      Exec.retainedTargetFramesFromAt_halt _ _ _ step committed foreign]
  · simp only [Exec.retainedTargetTurnsAt, dite_eq_right committed, List.filterMap_nil]

end Blanc.Lift.UniswapV2Pair
