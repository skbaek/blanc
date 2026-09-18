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

end Blanc
