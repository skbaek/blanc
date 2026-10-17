import Blanc.Lift.RetainedTargetCompleteness
import Blanc.Lift.ReachChain
import Blanc.Lift.Weth9.CommittedSpawn
import Blanc.Lift.VyperNonreentrantDeployed.Token20.Check
import Blanc.ExecutionReachable
import Blanc.ExecutionTraceFrames

/-!
# Raw frame roots along a same-frame chain (C6(b) capstone support)

Contract-neutral facts about `Exec.rawFrameDescendants` (all entered child roots, rolled-back ones
included), the raw analogues of `RetainedTargetCompleteness`'s committed-frame facts:

* `Exec.Deriv.ExecFreeUntil.rawFrameDescendants_eq`: an exec-free span enters no child;
* `Exec.Deriv.ParentStep.rawFrameDescendants_cases`: across one parent step, a raw descendant is the
  continuation's or lies in the raw roots of the child that step entered;
* `MessageCallTrace.rawFrames_run`: a call trace's raw frames are the raw roots of the derivation of
  its entered frame.

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
  rcases free with ⟨reached, clean⟩
  induction reached with
  | refl => rfl
  | @step root next tail edge rest ih =>
      have rootClean : ∀ x : Xinst,
          ¬ Ninst.At root.sevm.code root.pc (.exec x) := by
        rcases clean root (.refl _) with back | rootClean
        · exact ((Blanc.Exec.Deriv.ParentStep.not_parentPrefix_back edge) rest back).elim
        · exact rootClean
      have nextClean : ∀ node, Exec.Deriv.ParentPrefix next node →
          Exec.Deriv.ParentPrefix tail node ∨
            ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x) :=
        fun node reached => clean node (.step edge reached)
      rw [← ih nextClean]
      cases edge with
      | cont hstep next => simp only [Exec.rawFrameDescendants]
      | doneOk hstep henter hresume next =>
          rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
          exact (rootClean x decoded).elim
      | runOk hstep henter child hresume next =>
          rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
          exact (rootClean x decoded).elim

/-- Across one parent step, a raw descendant is a raw descendant of the continuation or a raw root
of the child that the step entered. -/
theorem parentStep_rawFrameDescendants_cases {N returned : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep returned N) :
    ∀ d ∈ Exec.rawFrameDescendants N.exc, d ∈ Exec.rawFrameDescendants returned.exc ∨
      ∃ (frame : Jaune.Frame) (resume : Resume) (nextPc : Nat) (childEvm : Evm)
        (raw : Execution) (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw),
        Evm.step ⟨N.pc, N.sevm, N.devm⟩ = .spawn frame resume nextPc ∧
        frame.enter = .run childEvm ∧ d ∈ Exec.rawFrameRoots child := by
  intro d member
  cases edge with
  | cont hstep next => exact Or.inl (by simpa only [Exec.rawFrameDescendants] using member)
  | doneOk hstep henter hresume next =>
      exact Or.inl (by simpa only [Exec.rawFrameDescendants] using member)
  | runOk hstep henter child hresume next =>
      simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
      rcases member with rfl | inChild | later
      · exact Or.inr ⟨_, _, _, _, _, child, hstep, henter, Exec.mem_rawFrameRoots_self child⟩
      · refine Or.inr ⟨_, _, _, _, _, child, hstep, henter, ?_⟩
        simp only [Exec.rawFrameRoots, List.mem_cons]
        exact Or.inr inChild
      · exact Or.inl later

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
    (hcode : sevm.code = VyperNonreentrantDeployed.Token20.code) :
    Exec.rawFrameDescendants run = [] :=
  Exec.rawFrameDescendants_eq_nil_of_reach run (noPushBefore_zero _ _)
    (hcode ▸ VyperNonreentrantDeployed.Token20.spawnFreeReach)

/-- **A call trace's raw frames are the raw roots of its entered frame's derivation.** -/
theorem messageCallTrace_rawFrames_run {msg : Msg} {state : Jaune.State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (target : msg.target.isNone = false)
    (auths : msg.tenv.stat.auths.isEmpty = true)
    (nodeleg : getDelegatedCodeAddress msg.code = none) {cevm : Evm}
    (enter : (Frame.ofCall msg).enter = .run cevm) :
    ∃ (raw : Execution) (run : Exec cevm.pc cevm.sta cevm.dyna raw),
      trace.rawFrames = Exec.rawFrameRoots run := by
  cases trace with
  | createCollision htarget => simp only [target, Bool.false_eq_true] at htarget
  | createRun htarget => simp only [target, Bool.false_eq_true] at htarget
  | callRun htarget delegated refund hdelegation execMsg execMsgEq evm core coreTrace result =>
    have delegatedEq : delegated = msg := by
      unfold messageCallDelegation at hdelegation
      simp only [auths, ↓reduceIte] at hdelegation
      exact (Prod.mk.inj (Except.ok.inj hdelegation)).1.symm
    subst delegated
    have execEq : execMsg = msg := by
      rw [execMsgEq]
      simp only [messageCallExecutionMessage, nodeleg]
    subst execEq
    rcases coreTrace with ⟨slot, retained, run⟩
    have hrun := run
    unfold ProcessMessage RunFrame at hrun
    rw [enter] at hrun
    obtain ⟨raw, slotEq, -⟩ := hrun
    subst slotEq
    rcases cevm with ⟨pc, sevm, pre⟩
    cases retained with
    | some exn => exact ⟨raw, exn, rfl⟩

end Blanc.Composition.UniswapV2PairWeth9Capstone
