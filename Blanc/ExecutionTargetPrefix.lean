import Blanc.Lift.OutermostFrames
import Blanc.ExecutionTraceSettledForest

/-!
Complete descendant blocks in settled prefixes at an arbitrary non-static
target, with list observation membership and first-observation splitting.
No code image, token book, Pair model or replay premise is introduced.
-/

namespace Blanc.ExecutionTrace

open Jaune Blanc

/-- Every non-static target frame of `pre` has its whole block of descendants inside `pre`. -/
def TargetClosed (pair : Adr) (pre : List Exec.Frame) : Prop :=
  ∀ (b₁ : List Exec.Frame) (G : Exec.Frame) (b₂ : List Exec.Frame), pre = b₁ ++ G :: b₂ →
    G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      (Exec.descendantFrames G.run).length ≤ b₂.length

/-- The whole settled list is target-closed. -/
theorem settledFrames_targetClosed {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    TargetClosed pair trace.settledFrames := by
  intro b₁ G b₂ split _ _
  obtain ⟨r, rfl⟩ := trace.settledFrames_contig split
  rw [List.length_append]
  omega

/-- The settled frames before an unlocked position are target-closed: a non-static target frame whose
block reached the position would enclose it. -/
theorem before_targetClosed {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {before : List Exec.Frame}
    {f : Exec.Frame} {after : List Exec.Frame} (split : trace.settledFrames = before ++ f :: after)
    (noOpaque : ∀ A ∈ before, A.Encloses f →
      ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) :
    TargetClosed pair before := by
  intro b₁ G b₂ inBefore atPair mutable
  rw [inBefore, List.append_assoc, List.cons_append] at split
  obtain ⟨r, rest⟩ := trace.settledFrames_contig split
  have inB : G ∈ before := by
    rw [inBefore]
    exact List.mem_append_right _ List.mem_cons_self
  refine Nat.le_of_not_lt fun longer => noOpaque G inB ?_ ⟨atPair, mutable⟩
  rcases List.append_eq_append_iff.mp rest with ⟨a', descEq, tailEq⟩ | ⟨c', b₂Eq, -⟩
  · cases a' with
    | nil =>
        rw [List.append_nil] at descEq
        rw [descEq] at longer
        exact absurd longer (Nat.lt_irrefl _)
    | cons y a'' =>
        obtain ⟨rfl, -⟩ := List.cons.inj tailEq
        change f ∈ Exec.descendantFrames G.run
        rw [descEq]
        exact List.mem_append_right _ List.mem_cons_self
  · rw [b₂Eq, List.length_append] at longer
    omega


end Blanc.ExecutionTrace
