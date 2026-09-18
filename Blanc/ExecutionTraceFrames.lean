import Blanc.ExecDeterminism
import Blanc.ExecutionFrames
import Blanc.ExecutionHistory

/-!
# Raw frame roots of retained execution traces

This module projects the raw, actually entered frame roots retained by each
contract-neutral trace carrier.  It deliberately does not apply settlement or
commitment filtering.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

def RetainedXlot.rawFrames {slot : Xlot} :
    RetainedXlot slot → List Exec.Deriv
  | .none => []
  | .some run => Exec.rawFrameRoots run

def ProcessMessageTrace.rawFrames
    (trace : ProcessMessageTrace msg out) : List Exec.Deriv :=
  trace.retained.rawFrames

def ProcessCreateMessageTrace.rawFrames
    (trace : ProcessCreateMessageTrace msg out) : List Exec.Deriv :=
  trace.retained.rawFrames

def MessageCallTrace.rawFrames :
    MessageCallTrace msg state out → List Exec.Deriv
  | .createCollision .. => []
  | .createRun _ _ _ _ core _ => core.rawFrames
  | .callRun _ _ _ _ _ _ _ _ core _ => core.rawFrames

def TransactionTrace.rawFrames
    (trace : TransactionTrace benv bout tx index state bout') :
    List Exec.Deriv :=
  trace.message.rawFrames

def ApplyTransactionsTrace.rawFrames :
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → List Exec.Deriv
  | .nil _ _ => []
  | .cons head tail => head.rawFrames ++ tail.rawFrames

def SystemMessageTrace.rawFrames
    (trace : SystemMessageTrace benv target data state out) :
    List Exec.Deriv :=
  trace.message.rawFrames

def RequestsTrace.rawFrames
    (trace : RequestsTrace benv bout state bout') : List Exec.Deriv :=
  trace.withdrawal.rawFrames ++ trace.consolidation.rawFrames

def AppliedBodyTrace.rawFrames
    (trace : AppliedBodyTrace benv txs wds state bout) : List Exec.Deriv :=
  trace.beacon.rawFrames ++ trace.history.rawFrames ++
    trace.transactions.rawFrames ++ trace.requests.rawFrames

def ConfiguredBlockTrace.rawFrames
    (trace : ConfiguredBlockTrace cfg pre post) : List Exec.Deriv :=
  trace.bodyTrace.rawFrames

def ConfiguredHistoryTrace.rawFrames :
    ConfiguredHistoryTrace cfg checkpoint future → List Exec.Deriv
  | .refl _ _ _ => []
  | .step prior block => prior.rawFrames ++ block.rawFrames

end ExecutionTrace

private theorem Exec.rawFrameDescendants_trans
    {run : Exec pc sevm pre out} {d e : Exec.Deriv}
    (hd : d ∈ Exec.rawFrameDescendants run)
    (he : e ∈ Exec.rawFrameRoots d.exc) :
    e ∈ Exec.rawFrameDescendants run := by
  induction run generalizing d e with
  | halt hstep =>
      simp only [Exec.rawFrameDescendants, List.not_mem_nil] at hd
  | cont hstep next ih =>
      have hd' : d ∈ Exec.rawFrameDescendants next := by
        simpa [Exec.rawFrameDescendants] using hd
      simpa [Exec.rawFrameDescendants] using ih hd' he
  | doneErr hstep henter hresume =>
      simp only [Exec.rawFrameDescendants, List.not_mem_nil] at hd
  | doneOk hstep henter hresume next ih =>
      have hd' : d ∈ Exec.rawFrameDescendants next := by
        simpa [Exec.rawFrameDescendants] using hd
      simpa [Exec.rawFrameDescendants] using ih hd' he
  | runErr hstep henter child hresume ih =>
      simp only [Exec.rawFrameDescendants, List.mem_cons] at hd ⊢
      rcases hd with rfl | hd
      · simpa [Exec.rawFrameRoots, Exec.rawFrameDescendants] using he
      · exact Or.inr (ih hd he)
  | runOk hstep henter child hresume next childIh nextIh =>
      simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at hd ⊢
      rcases hd with rfl | hd
      · have he' : e = (⟨_, _, _, _, child⟩ : Exec.Deriv) ∨
            e ∈ Exec.rawFrameDescendants child := by
          simpa [Exec.rawFrameRoots, Exec.rawFrameDescendants] using he
        rcases he' with rfl | he'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl he')
      · rcases hd with childHd | nextHd
        · exact Or.inr (Or.inl (childIh childHd he))
        · exact Or.inr (Or.inr (nextIh nextHd he))

/-/ A raw frame root of a raw frame root is a raw frame root. -/
theorem Exec.rawFrameRoots_trans
    {run : Exec pc sevm pre out} {d e : Exec.Deriv}
    (hd : d ∈ Exec.rawFrameRoots run)
    (he : e ∈ Exec.rawFrameRoots d.exc) :
    e ∈ Exec.rawFrameRoots run := by
  simp only [Exec.rawFrameRoots, List.mem_cons] at hd ⊢
  rcases hd with rfl | hd
  · simpa [Exec.rawFrameRoots] using he
  · exact Or.inr (Exec.rawFrameDescendants_trans hd he)

/-- A childless source step's successful continuation: its raw descendants are
the raw descendants of every successful run from the step's own state. -/
theorem Exec.rawFrameDescendants_sub_of_stepNone
    {pc : Nat} {sevm : Sevm} {pre inter post : Devm} {n : Ninst}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter (.ok post))
    (run : Exec pc sevm pre (.ok post)) :
    ∀ d ∈ Exec.rawFrameDescendants next, d ∈ Exec.rawFrameDescendants run := by
  intro d member
  have hstatic : Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ n :=
    Evm.step_next hat
  unfold Ninst.StepRun at step
  cases run with
  | halt h => cases Ninst.step_ne_halt_ok (hstatic.symm.trans h)
  | cont h next' =>
      have hs := hstatic.symm.trans h
      cases Ninst.step_cont_pc hs
      rw [hs] at step
      obtain ⟨-, interEq⟩ := step
      cases interEq
      cases Subsingleton.elim next next'
      simpa [Exec.rawFrameDescendants] using member
  | doneOk h henter hr next' =>
      have hs := hstatic.symm.trans h
      cases Ninst.step_spawn_pc hs
      rw [hs] at step
      obtain ⟨r, frameRun, resultEq⟩ := step
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨-, rfl⟩ := frameRun
      rw [hr] at resultEq
      cases resultEq
      cases Subsingleton.elim next next'
      simpa [Exec.rawFrameDescendants] using member
  | runOk h henter child hr next' =>
      have hs := hstatic.symm.trans h
      rw [hs] at step
      obtain ⟨r, frameRun, -⟩ := step
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨raw, impossible, -⟩ := frameRun
      cases impossible

/-- A spawning source step with a filled slot: the child's raw roots and the
continuation's raw descendants are raw descendants of every successful run from
the step's own state. -/
theorem Exec.rawFrameDescendants_sub_of_stepSome
    {pc : Nat} {sevm : Sevm} {pre inter post : Devm} {n : Ninst}
    {cevm : Evm} {raw : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter (.ok post))
    (run : Exec pc sevm pre (.ok post)) :
    (∀ d ∈ Exec.rawFrameRoots child, d ∈ Exec.rawFrameDescendants run) ∧
      ∀ d ∈ Exec.rawFrameDescendants next, d ∈ Exec.rawFrameDescendants run := by
  have hstatic : Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ n :=
    Evm.step_next hat
  unfold Ninst.StepRun at step
  cases run with
  | halt h => cases Ninst.step_ne_halt_ok (hstatic.symm.trans h)
  | cont h next' =>
      have hs := hstatic.symm.trans h
      rw [hs] at step
      obtain ⟨impossible, -⟩ := step
      cases impossible
  | doneOk h henter hr next' =>
      have hs := hstatic.symm.trans h
      rw [hs] at step
      obtain ⟨r, frameRun, -⟩ := step
      unfold RunFrame at frameRun
      rw [henter] at frameRun
      obtain ⟨impossible, -⟩ := frameRun
      cases impossible
  | runOk h henter child' hr next' =>
      have hs := hstatic.symm.trans h
      cases Ninst.step_spawn_pc hs
      rw [hs] at step
      obtain ⟨r, frameRun, resultEq⟩ := step
      obtain ⟨enterEq, rEq⟩ := RunFrame.some_inv frameRun
      have same := henter.symm.trans enterEq
      cases same
      cases Exec.result_unique child child'
      cases Subsingleton.elim child child'
      rw [rEq, hr] at resultEq
      cases resultEq
      cases Subsingleton.elim next next'
      constructor
      · intro d member
        simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
        simp only [Exec.rawFrameRoots, List.mem_cons] at member
        rcases member with rfl | member
        · exact Or.inl rfl
        · exact Or.inr (Or.inl member)
      · intro d member
        simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr member)

/-- A jump's successful continuation: its raw descendants are the raw
descendants of every successful run from the jump's own state. -/
theorem Exec.rawFrameDescendants_sub_of_jump
    {pc pc' : Nat} {sevm : Sevm} {pre inter post : Devm} {j : Jinst}
    (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter (.ok post))
    (run : Exec pc sevm pre (.ok post)) :
    ∀ d ∈ Exec.rawFrameDescendants next, d ∈ Exec.rawFrameDescendants run := by
  intro d member
  have hstatic : Evm.step ⟨pc, sevm, pre⟩ = Step.ofJump (j.run ⟨pc, sevm, pre⟩) :=
    Evm.step_jump hat
  have runEq : j.run ⟨pc, sevm, pre⟩ = .ok ⟨pc', inter⟩ := step
  rw [runEq] at hstatic
  cases run with
  | halt h => cases hstatic.symm.trans h
  | cont h next' =>
      cases hstatic.symm.trans h
      cases Subsingleton.elim next next'
      simpa [Exec.rawFrameDescendants] using member
  | doneOk h henter hr next' => cases hstatic.symm.trans h
  | runOk h henter child hr next' => cases hstatic.symm.trans h

end Blanc
