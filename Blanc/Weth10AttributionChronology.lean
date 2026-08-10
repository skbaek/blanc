import Blanc.Weth10Attribution
import Blanc.Weth10HolderFlowWriteCompleteness

/-!
Chronology relations over the WETH10 attribution ledger.

This module mirrors the `FlowAction`-labelled same-frame chronology of
`Weth10HolderFlowCompiled` at the `CountedFrame` altitude: one labelled
parent-continuation edge (`ParentStepCounted`), its reflexive-transitive
prefix closure (`ParentPrefixCounted`), the exact descendant-stream split
equations for both, prefix composition, and the uniqueness/linearity facts
matching `Weth10HolderFlowWriteCompleteness`.  The labels are the counted
committed contributions of `Exec.attributionInner`, so a chronological
prefix accounts for exactly the attribution records of every committed
spawn it crosses.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- Counted committed contributions of the proper descendants of an
arbitrary proof-indexed execution, excluding the derivation's own frame
record.  This is the `CountedFrame` mirror of
`Exec.Deriv.descendantFlowActions`. -/
def Exec.Deriv.descendantCounted (dp : DeployParams) (ca : Adr)
    (deriv : Exec.Deriv) : List CountedFrame :=
  Exec.attributionInner dp ca deriv.exc

/-- One same-frame continuation edge, labelled by exactly the counted
committed contribution crossed by that edge.  Child-derivation edges are
intentionally not constructors: this relation follows the enclosing frame
chronologically, mirroring `Exec.Deriv.ParentStepActions`.  Unlike the
action-labelled original, the retained label needs the commit proof, so the
spawn label is a dependent `if`. -/
inductive Exec.Deriv.ParentStepCounted (dp : DeployParams) (ca : Adr) :
    Exec.Deriv → Exec.Deriv → List CountedFrame → Prop
  | cont
      {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
      (next : Exec pc' sevm post out) :
      ParentStepCounted dp ca
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .cont hstep next⟩ []
  | doneOk
      {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {f : Jaune.Frame} {rsm : Resume}
      {r : Except (EvmError × State × AdrSet × Tra) Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
      (henter : f.enter = .done r)
      (hresume : rsm.run r = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStepCounted dp ca
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .doneOk hstep henter hresume next⟩ []
  | runOk
      {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {f : Jaune.Frame} {rsm : Resume} {childEvm : Evm}
      {raw out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
      (henter : f.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : rsm.run (f.settle raw) = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStepCounted dp ca
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out,
          .runOk hstep henter child hresume next⟩
        (if h : Blanc.Weth10.Frame.settlementCommits f raw = true then
          Exec.frameContribution dp ca
            (Exec.Frame.ofRun child
              (Blanc.Weth10.Frame.raw_commits_of_settlementCommits h))
            (Exec.attributionInner dp ca child)
         else [])

/-- A chronological same-frame prefix, labelled by all counted committed
contributions crossed before its endpoint. -/
inductive Exec.Deriv.ParentPrefixCounted (dp : DeployParams) (ca : Adr) :
    Exec.Deriv → Exec.Deriv → List CountedFrame → Prop
  | refl (root : Exec.Deriv) : ParentPrefixCounted dp ca root root []
  | step {root next tail : Exec.Deriv}
      {headCounted tailCounted : List CountedFrame}
      (head : Exec.Deriv.ParentStepCounted dp ca next root headCounted)
      (rest : Exec.Deriv.ParentPrefixCounted dp ca next tail tailCounted) :
      Exec.Deriv.ParentPrefixCounted dp ca root tail
        (headCounted ++ tailCounted)

/-- One labelled parent-continuation edge is exactly the corresponding split
of the descendant counted-frame stream. -/
theorem Exec.Deriv.ParentStepCounted.descendantCounted_eq
    {dp : DeployParams} {ca : Adr}
    {next root : Exec.Deriv} {counted : List CountedFrame}
    (edge : Exec.Deriv.ParentStepCounted dp ca next root counted) :
    Exec.Deriv.descendantCounted dp ca root =
      counted ++ Exec.Deriv.descendantCounted dp ca next := by
  cases edge with
  | cont =>
      simp [Exec.Deriv.descendantCounted, Exec.attributionInner]
  | doneOk =>
      simp [Exec.Deriv.descendantCounted, Exec.attributionInner]
  | runOk hstep henter child hresume next =>
      simp only [Exec.Deriv.descendantCounted, Exec.attributionInner]

/-- The counted prefix relation accounts for every committed spawn before
its endpoint and leaves exactly that endpoint's remaining descendant
stream. -/
theorem Exec.Deriv.ParentPrefixCounted.descendantCounted_eq
    {dp : DeployParams} {ca : Adr}
    {root tail : Exec.Deriv} {counted : List CountedFrame}
    (hprefix : Exec.Deriv.ParentPrefixCounted dp ca root tail counted) :
    Exec.Deriv.descendantCounted dp ca root =
      counted ++ Exec.Deriv.descendantCounted dp ca tail := by
  induction hprefix with
  | refl => simp
  | step head rest ih =>
      rw [head.descendantCounted_eq, ih, List.append_assoc]

/-- Chronological prefixes compose without losing the counted-frame order. -/
theorem Exec.Deriv.ParentPrefixCounted.trans
    {dp : DeployParams} {ca : Adr}
    {root mid tail : Exec.Deriv} {left right : List CountedFrame}
    (hleft : Exec.Deriv.ParentPrefixCounted dp ca root mid left)
    (hright : Exec.Deriv.ParentPrefixCounted dp ca mid tail right) :
    Exec.Deriv.ParentPrefixCounted dp ca root tail (left ++ right) := by
  induction hleft with
  | refl => simpa using hright
  | step head rest ih =>
      simpa only [List.append_assoc] using
        Exec.Deriv.ParentPrefixCounted.step head (ih hright)

/-- Append one exact parent-continuation edge to a chronological prefix. -/
theorem Exec.Deriv.ParentPrefixCounted.snoc
    {dp : DeployParams} {ca : Adr}
    {root current next : Exec.Deriv} {before selected : List CountedFrame}
    (hprefix : Exec.Deriv.ParentPrefixCounted dp ca root current before)
    (hedge : Exec.Deriv.ParentStepCounted dp ca next current selected) :
    Exec.Deriv.ParentPrefixCounted dp ca root next
      (before ++ selected) := by
  apply hprefix.trans
  simpa using Exec.Deriv.ParentPrefixCounted.step hedge
    (Exec.Deriv.ParentPrefixCounted.refl next)

/-- The same-frame continuation edge out of a fixed proof-indexed derivation
is unique, including its counted-frame label. -/
theorem Exec.Deriv.ParentStepCounted.unique
    {dp : DeployParams} {ca : Adr}
    {root nextLeft nextRight : Exec.Deriv}
    {leftCounted rightCounted : List CountedFrame}
    (left : Exec.Deriv.ParentStepCounted dp ca
      nextLeft root leftCounted)
    (right : Exec.Deriv.ParentStepCounted dp ca
      nextRight root rightCounted) :
    nextLeft = nextRight ∧ leftCounted = rightCounted := by
  cases left <;> cases right <;> simp_all

/-- Counted same-frame prefixes from one concrete `Exec` proof form a linear
chain, mirroring `Exec.Deriv.ParentPrefixActions.linear`. -/
theorem Exec.Deriv.ParentPrefixCounted.linear
    {dp : DeployParams} {ca : Adr}
    {root leftTail rightTail : Exec.Deriv}
    {leftCounted rightCounted : List CountedFrame}
    (left : Exec.Deriv.ParentPrefixCounted dp ca
      root leftTail leftCounted)
    (right : Exec.Deriv.ParentPrefixCounted dp ca
      root rightTail rightCounted) :
    (∃ suffix, Exec.Deriv.ParentPrefixCounted dp ca
      leftTail rightTail suffix) ∨
    (∃ suffix, Exec.Deriv.ParentPrefixCounted dp ca
      rightTail leftTail suffix) := by
  induction left generalizing rightTail rightCounted with
  | refl =>
      exact Or.inl ⟨rightCounted, right⟩
  | @step root next leftTail headCounted leftCounted head rest ih =>
      cases right with
      | refl =>
          exact Or.inr ⟨headCounted ++ leftCounted, .step head rest⟩
      | @step _ rightNext rightTail rightHeadCounted rightCounted
          rightHead rightRest =>
          have unique := head.unique rightHead
          cases unique.1
          cases unique.2
          exact ih rightRest

end Weth10

end Blanc
