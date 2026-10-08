import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorOccurrence
import Blanc.Lift.InvWalkGas

/-! Actual GAS-to-external-call cursor transport. -/
namespace Blanc.Lift
open Jaune

/-- The gas word, actual occurrence, filled slot, and returned cursor come
from the supplied cursor in the supplied original parent execution. -/
theorem CursorStateAt.gasCall {code : ByteArray} {c : Cert}
    {root start : Exec.Deriv} {b post : Devm} {S : List B256}
    {M : Mem} {K : List SFunc} {x : Xinst} {tail : SFunc}
    (cut : CursorStateAt code c start (.next (.reg .gas) (.next (.exec x) tail)) b S M K)
    (checked : Cert.check code c = true) (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root x) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil start step.occurrence.node ∧
      step.occurrence.node.sevm = start.sevm ∧
      step.occurrence.node.exn = start.exn ∧
      step.occurrence.node.devm = St b (gas.toB256 :: S) M gas ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) start.sevm
        step.occurrence.node.devm (.exec x) step.returned.devm ∧
      CursorOK code c step.returned cursor ∧ cursor.f = tail ∧
      cursor.K.map Cont.f = K := by
  obtain ⟨call, κ, _, _, sameSevm, sameExn, placed, tree, line, sameK, free⟩ :=
    cursor_nexts_line_cont_free_forward checked cut.placed [.reg .gas]
      (.next (.exec x) tail) cut.tree (cut.exn_eq.trans success)
      (cut.sevm_eq ▸ fork)
  obtain ⟨g, state⟩ := cut.state
  rw [cut.sevm_eq, state] at line
  obtain ⟨_, primitive, line⟩ := Line.of_run_cons line
  cases line
  obtain ⟨gas, callState⟩ := ri_gas_remaining primitive
  have gap := cut.free.trans (free (by
    intro n member y equal
    simp only [List.mem_singleton, equal, reduceCtorEq] at member))
  have env := sameSevm.trans cut.sevm_eq
  have outcome := sameExn.trans cut.exn_eq
  obtain ⟨step, cursor, nodeEq, _, primitiveCall, synthetic, _, returned⟩ :=
    cursor_next_call_occurrence_forward checked (reached.trans gap.1) placed tree
      (outcome.trans success) (env ▸ fork)
  have nextShape : cursor.f = tail ∧ cursor.K = κ.K := by
    rcases κ with ⟨f, pc, a, m, pending⟩
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  refine ⟨step, cursor, gas, ?_, ?_, ?_, ?_, ?_, returned, nextShape.1, ?_⟩
  · rw [nodeEq]; exact gap
  · rw [nodeEq]; exact env
  · rw [nodeEq]; exact outcome
  · rw [nodeEq]; exact callState
  · simpa only [nodeEq, env] using primitiveCall
  · rw [nextShape.2, sameK]; exact cut.continuations

end Blanc.Lift

