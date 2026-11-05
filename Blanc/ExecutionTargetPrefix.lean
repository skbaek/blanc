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

theorem TargetClosed.nil (pair : Adr) : TargetClosed pair [] := by
  intro b₁ G b₂ split
  cases b₁ <;> cases split

/-- A target-closed prefix extended by a part that is target-closed in itself. -/
theorem TargetClosed.append {pair : Adr} {X Y : List Exec.Frame} (closed : TargetClosed pair X)
    (inY : TargetClosed pair Y) : TargetClosed pair (X ++ Y) := by
  intro b₁ G b₂ split atPair mutable
  rcases List.split_append_cons split with ⟨m, inX, rfl⟩ | ⟨n, -, inY'⟩
  · have short := closed b₁ G m inX atPair mutable
    rw [List.length_append]
    omega
  · exact inY n G b₂ inY' atPair mutable

/-- A frame observed by the target lies in the observation of every list holding it. -/
theorem mem_flatMap_obsAt {pair : Adr} {fs : List Exec.Frame} {G : Exec.Frame} (member : G ∈ fs)
    (atPair : G.sevm.currentTarget = pair) (mutable : G.sevm.isStatic = false) :
    G ∈ fs.flatMap (Blanc.Exec.Frame.obsAt pair) := by
  refine List.mem_flatMap.mpr ⟨G, member, ?_⟩
  rw [Blanc.Exec.Frame.obsAt, ite_eq_left_of_eq_true _ _ (eq_true ⟨atPair, mutable⟩)]
  exact List.mem_singleton_self G

/-- A gap (a list with no non-static target frame) is target-closed. -/
theorem TargetClosed.gap {pair : Adr} {gap : List Exec.Frame}
    (quiet : gap.flatMap (Blanc.Exec.Frame.obsAt pair) = []) : TargetClosed pair gap := by
  intro b₁ G b₂ split atPair mutable
  have inGap : G ∈ gap := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have member := mem_flatMap_obsAt (pair := pair) inGap atPair mutable
  rw [quiet] at member
  cases member

/-- A frame's committed subtree is target-closed. -/
theorem TargetClosed.committed (pair : Adr) (F : Exec.Frame) :
    TargetClosed pair (Exec.committedFrames F.run) := by
  intro b₁ G b₂ split _ _
  rw [Exec.Frame.committedFrames_self] at split
  cases b₁ with
  | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj split
      exact Nat.le_refl _
  | cons x b₁' =>
      obtain ⟨-, inDesc⟩ := List.cons.inj split
      obtain ⟨r, rfl⟩ := Exec.descendantFrames_contig F.run inDesc
      rw [List.length_append]
      omega

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


/-- The first observed frame of a list splits it into a gap, that frame and the rest. -/
theorem obsAt_first {pair : Adr} :
    ∀ {fs : List Exec.Frame} {F₀ : Exec.Frame} {xs : List Exec.Frame},
      fs.flatMap (Blanc.Exec.Frame.obsAt pair) = F₀ :: xs →
      ∃ gap rest, fs = gap ++ F₀ :: rest ∧ gap.flatMap (Blanc.Exec.Frame.obsAt pair) = [] ∧
        F₀.sevm.currentTarget = pair ∧ F₀.sevm.isStatic = false ∧
        xs = rest.flatMap (Blanc.Exec.Frame.obsAt pair)
  | [], _, _, h => by cases h
  | y :: ys, F₀, xs, h => by
      rw [List.flatMap_cons] at h
      by_cases hy : y.sevm.currentTarget = pair ∧ y.sevm.isStatic = false
      · rw [Blanc.Exec.Frame.obsAt, ite_eq_left_of_eq_true _ _ (eq_true hy), List.singleton_append] at h
        obtain ⟨rfl, rfl⟩ := List.cons.inj h
        exact ⟨[], ys, rfl, rfl, hy.1, hy.2, rfl⟩
      · rw [Blanc.Exec.Frame.obsAt, ite_eq_right_of_eq_false _ _ (eq_false hy), List.nil_append] at h
        obtain ⟨gap, rest, rfl, quiet, atPair, mutable, rfl⟩ := obsAt_first h
        refine ⟨y :: gap, rest, rfl, ?_, atPair, mutable, rfl⟩
        rw [List.flatMap_cons, Blanc.Exec.Frame.obsAt, ite_eq_right_of_eq_false _ _ (eq_false hy), List.nil_append]
        exact quiet

end Blanc.ExecutionTrace
