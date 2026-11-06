import Blanc.Lift.ForeignKeep

/-!
# A frame whose chain enters no frame keeps the foreign world

`ChainNoExec run`: no node of the frame's own chain decodes an external instruction. `frameKeeps_of_noExec` gives
`FrameKeepsForeign` from it at a committed frame's entry. Each coin's code supplies `ChainNoExec` for the selectors the
pool sends, in its own module. Nothing here names a coin.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift

/-- Chain nodes of a frame decode no external instruction. -/
abbrev ChainNoExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out) : Prop :=
  ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N → ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x)

/-- **What a pool's coin frame keeps, from its code**: a committed frame on the pool's selectors whose
chain decodes no external instruction keeps the foreign world. -/
theorem frameKeeps_of_noExec (c : Exec.Frame) (hpc : c.pc = 0)
    (hsg : c.sevm.benvStat.rules.stateGas = none)
    (h : ∀ {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out),
      c.sevm = sevm → c.pre = pre → ChainNoExec run) : FrameKeepsForeign c := by
  obtain ⟨cpc, sevm, pre, out, run, committed⟩ := c
  dsimp only at hpc hsg h
  subst hpc
  exact frameKeepsForeign_of_noExec _ hsg (h run rfl rfl)

end Blanc.Lift.CurveCoins
