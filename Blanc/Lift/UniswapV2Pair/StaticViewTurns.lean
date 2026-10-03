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

end Blanc.Lift.UniswapV2Pair
