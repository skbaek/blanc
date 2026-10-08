import Blanc.Lift.UniswapV2Pair.BurnPositionalTransfers
import Blanc.Lift.CursorGasCall

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnFinalAfterCallTree (site : BurnFinalBalanceSite) : SFunc :=
  match site.callTree with
  | .dest (.next _ (.next _ (.next _ tail))) => tail
  | _ => .undefined

/-- Each final site produces its original-root occurrence from the supplied
request cursor; the gap starts at the preceding actual returned parent. -/
theorem burn_final_call_of_request_cursor {root start : Exec.Deriv}
    {b post : Devm} {R : List B256} {M : Mem} {K : List SFunc}
    {p token a x y : B256} (site : BurnFinalBalanceSite)
    (cut : CursorStateAt code cert start site.callTree b
      (0 :: token :: p :: 36 :: p :: 32 :: a :: x :: y :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil start step.occurrence.node ∧
      step.occurrence.node.sevm = start.sevm ∧
      step.occurrence.node.exn = start.exn ∧
      step.occurrence.node.devm = St b
        (gas.toB256 :: token :: p :: 36 :: p :: 32 :: a :: x :: y :: R) M gas ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) start.sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧
      cursor.f = burnFinalAfterCallTree site ∧ cursor.K.map Cont.f = K := by
  have shape : site.callTree = .dest (.next (.reg .pop)
      (.next (.reg .gas) (.next (.exec .staticcall) (burnFinalAfterCallTree site)))) := by
    cases site <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨beforeGas⟩ := opened.line cert_check success fork [.reg .pop] rfl
    (by intro n member x equal; subst n
        simp only [List.mem_singleton, reduceCtorEq] at member)
    (by intro g d line
        obtain ⟨_, pop, line⟩ := Line.of_run_cons line
        obtain ⟨g', state⟩ := ri_pop pop
        cases line
        exact ⟨g', state⟩)
  exact beforeGas.gasCall cert_check reached success fork

end Blanc.Lift.UniswapV2Pair
