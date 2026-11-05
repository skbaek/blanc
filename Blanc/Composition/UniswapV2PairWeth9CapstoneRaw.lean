import Blanc.Lift.RetainedTargetCompleteness
import Blanc.Lift.ReachChain
import Blanc.Lift.Weth9.CommittedSpawn
import Blanc.Lift.Token20.Check
import Blanc.ExecutionReachable
import Blanc.ExecutionTraceFrames

/-!
# Raw frame roots along a same-frame chain (C6(b) capstone support)

Contract-neutral facts about `Exec.rawFrameDescendants` (all entered child roots, rolled-back ones
included), the raw analogues of `RetainedTargetCompleteness`'s committed-frame facts:

* `Exec.Deriv.ExecFreeUntil.rawFrameDescendants_eq`: an exec-free span enters no child;
* `Exec.Deriv.ParentStep.rawFrameDescendants_cases`: across one parent step, a raw descendant is the
  continuation's or lies in the raw roots of the child that step entered;
The message-call raw-root projection is now owned by
`Blanc/ExecutionTraceMessageRoots.lean`.

And two callee facts: a WETH9 frame whose selector is not `withdraw` enters no child, whatever its
outcome (`weth9_rawFrameDescendants_nil`); Token20 frames enter none
(`token20_rawFrameDescendants_nil`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- An exec-free span of the chain enters no child of its own. -/
theorem execFreeUntil_rawFrameDescendants_eq {start stop : Exec.Deriv}
    (free : Exec.Deriv.ExecFreeUntil start stop) :
    Exec.rawFrameDescendants start.exc = Exec.rawFrameDescendants stop.exc := by
  exact Blanc.Exec.Deriv.ExecFreeUntil.rawFrameDescendants_eq free

/-- Across one parent step, a raw descendant is a raw descendant of the continuation or a raw root
of the child that the step entered. -/
theorem parentStep_rawFrameDescendants_cases {N returned : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep returned N) :
    ∀ d ∈ Exec.rawFrameDescendants N.exc, d ∈ Exec.rawFrameDescendants returned.exc ∨
      ∃ (frame : Jaune.Frame) (resume : Resume) (nextPc : Nat) (childEvm : Evm)
        (raw : Execution) (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw),
        Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn frame resume nextPc ∧
        frame.enter = .run childEvm ∧ d ∈ Exec.rawFrameRoots child := by
  exact Blanc.Exec.Deriv.ParentStep.rawFrameDescendants_cases edge

/-- A chain with no exec node enters no child. -/
theorem deriv_rawFrameDescendants_nil (N : Exec.Deriv)
    (h : ∀ M, Exec.Deriv.ParentPrefix N M → ∀ x, ¬ Ninst.At M.sevm.code M.pc (.exec x)) :
    Exec.rawFrameDescendants N.exc = [] := by
  obtain ⟨pc, sevm, pre, out, run⟩ := N
  exact Exec.rawFrameDescendants_eq_nil_of_noExec run h

/-- **A WETH9 frame that does not select `withdraw` enters no child**, whatever its outcome. -/
theorem weth9_rawFrameDescendants_nil {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (hcode : sevm.code = Weth9.code)
    (fork : CoveredFork sevm.benvStat.fork)
    (notWithdraw : Sevm.selector sevm ≠ Bytes.toB256 [0x2e, 0x1a, 0x7d, 0x4d]) :
    Exec.rawFrameDescendants run = [] := by
  apply Exec.rawFrameDescendants_eq_nil_of_noExec run
  intro N hN x hx
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix Weth9.cert_check
    (R := ⟨0, sevm, pre, out, run⟩) rfl hcode fork hN
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hx
  change Reach (StepIn ⟨0, sevm, pre, out, run⟩) Weth9.prog sevm ⟨pre, Weth9.t_0000_c0, []⟩
    (κ.conf N.devm) at reach
  exact notWithdraw (Weth9.weth9_withdraw_reach StepIn.toRun reach ⟨x, g, hf⟩).2.1

/-- **A Token20 frame enters no child.** -/
theorem token20_rawFrameDescendants_nil {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Blanc.Lift.Token20.code) :
    Exec.rawFrameDescendants run = [] :=
  Exec.rawFrameDescendants_eq_nil_of_reach run (noPushBefore_zero _ _)
    (hcode ▸ Blanc.Lift.Token20.spawnFreeReach)


end Blanc.Composition.UniswapV2PairWeth9Capstone
