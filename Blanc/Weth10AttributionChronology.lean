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
        (if h : Blanc.Frame.settlementCommits f raw = true then
          Exec.frameContribution dp ca
            (Exec.Frame.ofRun child
              (Blanc.Frame.raw_commits_of_settlementCommits h))
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

/-! ## Relabelling bridges from the action-labelled chronology -/

/-- Every action-labelled same-frame continuation edge admits a counted
relabelling on the same derivation edge. -/
theorem Exec.Deriv.ParentStepActions.exists_counted
    {dp : DeployParams} {ca : Adr}
    {next root : Exec.Deriv} {actions : List FlowAction}
    (edge : Exec.Deriv.ParentStepActions dp ca next root actions) :
    ∃ counted, Exec.Deriv.ParentStepCounted dp ca next root counted := by
  cases edge with
  | cont hstep next => exact ⟨[], .cont hstep next⟩
  | doneOk hstep henter hresume next =>
      exact ⟨[], .doneOk hstep henter hresume next⟩
  | runOk hstep henter child hresume next =>
      exact ⟨_, .runOk hstep henter child hresume next⟩

/-- Every action-labelled chronological prefix admits a counted relabelling
along the same derivation path. -/
theorem Exec.Deriv.ParentPrefixActions.exists_counted
    {dp : DeployParams} {ca : Adr}
    {root tail : Exec.Deriv} {actions : List FlowAction}
    (path : Exec.Deriv.ParentPrefixActions dp ca root tail actions) :
    ∃ counted, Exec.Deriv.ParentPrefixCounted dp ca root tail counted := by
  induction path with
  | refl root => exact ⟨[], .refl root⟩
  | step head rest ih =>
      rcases head.exists_counted with ⟨headCounted, headEdge⟩
      rcases ih with ⟨tailCounted, tailPath⟩
      exact ⟨headCounted ++ tailCounted, .step headEdge tailPath⟩

/-! ## Generic nil transfer from the frames traversal -/

/-- A derivation without retained descendant frames contributes no counted
records: the attribution stream prunes settlement-noncommitting children in
exactly the same places as the frames traversal. -/
theorem Exec.attributionInner_eq_nil_of_descendantFrames_eq_nil
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : Exec.descendantFrames run = []) :
    Exec.attributionInner dp ca run = [] := by
  revert h
  induction run with
  | halt hstep =>
      intro h
      simp [Exec.attributionInner]
  | cont hstep next ih =>
      intro h
      simp only [Exec.attributionInner]
      exact ih (by simpa only [Exec.descendantFrames] using h)
  | doneErr hstep henter hresume =>
      intro h
      simp [Exec.attributionInner]
  | doneOk hstep henter hresume next ih =>
      intro h
      simp only [Exec.attributionInner]
      exact ih (by simpa only [Exec.descendantFrames] using h)
  | runErr hstep henter child hresume ihChild =>
      intro h
      simp [Exec.attributionInner]
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro h
      simp only [Exec.descendantFrames] at h
      simp only [Exec.attributionInner]
      split at h
      · exact absurd h (by simp)
      · rename_i hnot
        rw [dif_neg hnot, List.nil_append]
        exact ihNext (by simpa using h)

/-- Public analog of the compiled module's halt-step emptiness: a derivation
whose step halts retains no descendant frames. -/
theorem Exec.descendantFrames_eq_nil_of_halt_step
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out haltOut : Execution}
    (run : Exec pc sevm pre out)
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .halt haltOut) :
    Exec.descendantFrames run = [] := by
  cases run with
  | halt h => simp [Exec.descendantFrames]
  | cont h next => cases hstep.symm.trans h
  | doneErr h henter hresume => cases hstep.symm.trans h
  | doneOk h henter hresume next => cases hstep.symm.trans h
  | runErr h henter child hresume => cases hstep.symm.trans h
  | runOk h henter child hresume next => cases hstep.symm.trans h

/-- A childless instruction's continuation edge carries no counted records:
the spawn arm is impossible, and both remaining arms are label-free. -/
theorem Exec.Deriv.ParentStepActions.counted_of_isChildless
    {dp : DeployParams} {ca : Adr}
    {n : Ninst} {next current : Exec.Deriv}
    {selected : List FlowAction}
    (edge : Exec.Deriv.ParentStepActions dp ca next current selected)
    (hat : Ninst.At current.sevm.code current.pc n)
    (hchildless : NinstIsChildless n) :
    Exec.Deriv.ParentStepCounted dp ca next current [] := by
  cases edge with
  | cont hstep next => exact .cont hstep next
  | doneOk hstep henter hresume next =>
      exact .doneOk hstep henter hresume next
  | runOk hstep henter child hresume next =>
      have hspawn := (Evm.step_next hat).symm.trans hstep
      rcases Ninst.step_spawn_inv hspawn with ⟨x, rfl, hx⟩
      exact hchildless.elim

/-- Append one empty-labelled edge to an empty-labelled counted prefix. -/
private theorem Exec.Deriv.ParentPrefixCounted.snocNil
    {dp : DeployParams} {ca : Adr}
    {root current next : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefixCounted dp ca root current [])
    (hedge : Exec.Deriv.ParentStepCounted dp ca next current []) :
    Exec.Deriv.ParentPrefixCounted dp ca root next [] := by
  simpa using hprefix.snoc hedge

/-! ## Counted childless walk over the compiled runtime -/

/-- A compiled-source cursor over the original retained frame whose
chronological prefix carries an exactly-empty counted label.  This is the
counted mirror of `Exec.Frame.CompiledCursor`: the action-labelled prefix is
retained only existentially, because the counted walk needs it solely to
drive the shared advancing primitives. -/
structure Exec.Frame.CountedCursor (dp : DeployParams) (ca : Adr)
    (frame : Exec.Frame) (fs : List Func) (table : List (Nat × Func))
    (body : Func) (final : Devm) : Type where
  pc : Nat
  pre : Devm
  current : Exec pc frame.sevm pre frame.out
  parentPrefix : ∃ actions, Exec.Deriv.ParentPrefixActions dp ca
    ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
    ⟨pc, frame.sevm, pre, frame.out, current⟩ actions
  countedPrefix : Exec.Deriv.ParentPrefixCounted dp ca
    ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
    ⟨pc, frame.sevm, pre, frame.out, current⟩ []
  run : Func.RunCompiled fs frame.sevm pre body final
  codeSlice : subcode frame.sevm.code.toList pc
    (Func.compile table pc body)
  codeBoundary : noPushBefore frame.sevm.code pc 32 = true

/-- Follow one known childless machine continuation while preserving the
empty counted prefix; the counted mirror of `Exec.Frame.advance_cont`. -/
theorem Exec.Frame.advance_cont_counted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {pc nextPc : Nat} {stepPre nextPre : Devm}
    (current : Exec pc frame.sevm stepPre frame.out)
    (hprefix : ∃ actions, Exec.Deriv.ParentPrefixActions dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ actions)
    (hcounted : Exec.Deriv.ParentPrefixCounted dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ [])
    (hstep : Evm.step ⟨pc, frame.sevm, stepPre⟩ = .cont nextPc nextPre) :
    ∃ continuation : Exec nextPc frame.sevm nextPre frame.out,
      (∃ actions, Exec.Deriv.ParentPrefixActions dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨nextPc, frame.sevm, nextPre, frame.out, continuation⟩ actions) ∧
      Exec.Deriv.ParentPrefixCounted dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨nextPc, frame.sevm, nextPre, frame.out, continuation⟩ [] := by
  rcases hprefix with ⟨before, hbefore⟩
  rcases frame with ⟨rootPc, sevm, rootPre, out, rootRun, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok final =>
      cases current with
      | halt h => cases hstep.symm.trans h
      | cont h next =>
          cases hstep.symm.trans h
          refine ⟨next, ⟨before ++ [],
            hbefore.snoc (Exec.Deriv.ParentStepActions.cont h next)⟩, ?_⟩
          exact hcounted.snocNil (Exec.Deriv.ParentStepCounted.cont h next)
      | doneOk h henter hresume next => cases hstep.symm.trans h
      | runOk h henter child hresume next => cases hstep.symm.trans h

/-- Advance one childless source instruction while preserving the empty
counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.selectNextChildless`. -/
theorem Exec.Frame.CountedCursor.selectNextChildless
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {n : Ninst} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table (.next n tail) final)
    (hchildless : NinstIsChildless n) :
    ∃ tailCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table tail final,
      Ninst.Run frame.sevm cursor.pre n tailCursor.pre := by
  have compiled := cursor.run
  cases compiled with
  | next hcompiled htail =>
      have hat : Ninst.At frame.sevm.code cursor.pc n :=
        ninstAt_of_subcode_next cursor.codeSlice
      rcases cursor.parentPrefix with ⟨before, hbefore⟩
      rcases Blanc.Weth10.Exec.Frame.advance_runCompiled_next (frame := frame)
          cursor.current hbefore hat
          hcompiled with
        ⟨xl, continuation, selected, _occurrence, hedge, hnextPrefix⟩
      have hcountedEdge := hedge.counted_of_isChildless hat hchildless
      obtain ⟨nextBoundary, nextSub⟩ :=
        Func.noPushBefore_next cursor.codeSlice cursor.codeBoundary
      exact ⟨⟨cursor.pc + n.size, _, continuation, ⟨_, hnextPrefix⟩,
        cursor.countedPrefix.snocNil hcountedEdge, htail, nextSub,
        nextBoundary⟩, Ninst.Run.of_runCompiled hcompiled⟩

/-- Peel a childless source line while preserving the empty counted prefix;
the counted mirror of `Exec.Frame.CompiledCursor.peelChildlessLine`. -/
theorem Exec.Frame.CountedCursor.peelChildlessLine
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {line : Line} {tail : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table (line +++ tail) final)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    ∃ tailCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table tail final,
      Line.Run frame.sevm cursor.pre line tailCursor.pre := by
  induction line with
  | nil => exact ⟨cursor, .nil⟩
  | cons n line ih =>
      change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
        (.next n (line +++ tail)) final at cursor
      rcases cursor.selectNextChildless (hchildless n (by simp)) with
        ⟨nextCursor, hrun⟩
      rcases ih nextCursor (fun i hi => hchildless i (by simp [hi])) with
        ⟨tailCursor, hline⟩
      exact ⟨tailCursor, .cons hrun hline⟩

/-- Select the fall-through arm of a compiled branch when the flag is known
zero, preserving the empty counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.selectBranchZero`. -/
theorem Exec.Frame.CountedCursor.selectBranchZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (.branch left right) final)
    (hstack : (0 : B256) :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table left final,
      stack <<+ arm.pre.stack := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩, hw.2⟩
  | succ hne _hroom hpop _hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hne hw.1).elim

/-- Select the jumped arm of a compiled branch when the flag is known
nonzero, preserving the empty counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.selectBranchSucc`. -/
theorem Exec.Frame.CountedCursor.selectBranchSucc
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {flag : B256} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (.branch left right) final)
    (hflag : flag ≠ 0)
    (hstack : flag :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table right final,
      stack <<+ arm.pre.stack := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, _hsubLeft, _hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero _hroom hpop _hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hflag hw.1.symm).elim
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨afterJump, hpJump, hcJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterJump hpJump hcJump
          hstepJumpdest with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨loc + 1, _, armExec, hpArm, hcArm, hright,
        hsubRight, hboundRight⟩, hw.2⟩

/-- A matching compiled dispatch leaf advances to its stored body while
removing the selector word from the stack; the counted mirror of the
compiled module's dispatch-leaf step. -/
private theorem Exec.Frame.CountedCursor.reachDispatchLeaf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {sig w : B256} {f body : Func} {k : Nat} {stack : Stack}
    (hmem : (sig, f) ∈ [(w, body)])
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (dispatchWith k (.leaf w body)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table f final,
      stack <<+ bodyCursor.pre.stack := by
  have heq : (sig, f) = (w, body) := List.mem_singleton.mp hmem
  injection heq with hsig hfun
  subst w
  subst body
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
    ([Ninst.pushB256 sig, Ninst.eq] +++ (f <?> .call k)) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hline⟩
  have hflag : (sig =? sig) :: stack <<+ branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with ⟨afterPush, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨afterEq, heqRun, hnil⟩
    cases hnil
    have hpushed : sig :: sig :: stack <<+ afterPush.stack := by
      simpa using prefix_of_push (of_run_pushB256 hpush) hstack
    exact prefix_of_eq heqRun hpushed
  rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at hflag
  rcases branchCursor.selectBranchSucc
      (left := .call k) (right := f) (flag := (1 : B256))
      (by decide) hflag with
    ⟨bodyCursor, hbodyStack⟩
  exact ⟨bodyCursor, hbodyStack⟩

/-- Reach the selected body of a generated sorted dispatch tree while
keeping the empty counted prefix; the counted mirror of the compiled
module's dispatch traversal. -/
private theorem Exec.Frame.CountedCursor.reachDispatchWith_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
      {fs : List Func} {table : List (Nat × Func)} {k : Nat}
      {final : Devm} {stack : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
        (dispatchWith k (DispatchTree.build n xs)) final) →
      (sig :: stack <<+ cursor.pre.stack) →
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table f final,
        stack <<+ bodyCursor.pre.stack := by
  intro n
  induction n with
  | zero =>
      intro xs sig f dp ca frame fs table k final stack _hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeaf hmem hstack
      · exfalso
        simp only [List.length_cons] at hlen
        omega
  | succ n ih =>
      intro xs sig f dp ca frame fs table k final stack hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeaf hmem hstack
      · simp only [List.length_cons] at hlen
        have htakeLen :
            (((w, body) :: y :: ys).take
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_take, List.length_cons]
          omega
        have hdropLen :
            (((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_drop, List.length_cons]
          omega
        obtain ⟨z, zs, hdrop⟩ :
            ∃ z zs, ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) = z :: zs := by
          rcases hd : ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) with _ | ⟨z, zs⟩
          · exfalso
            have hl := congrArg List.length hd
            simp only [List.length_drop, List.length_cons,
              List.length_nil] at hl
            omega
          · exact ⟨z, zs, rfl⟩
        have hsortedSplit : DispatchTree.sorted
            (((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ++
              ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2)) = true := by
          rw [List.take_append_drop]
          exact hsorted
        have hsortedTake := DispatchTree.sorted_append_left hsortedSplit
        have hsortedDrop := DispatchTree.sorted_append_right hsortedSplit
        have hmemSplit :
            (sig, f) ∈ ((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ∨
              (sig, f) ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
          apply List.mem_append.mp
          rw [List.take_append_drop]
          exact hmem
        change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
          ([Ninst.dup 0,
              Ninst.pushB256 (leftmostFsig
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2)))),
              Ninst.gt] +++
            (dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).take
                    ((((w, body) :: y :: ys).length + 1) / 2))) <?>
              dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))))) final
          at cursor
        rcases cursor.peelChildlessLine
            (by simp [NinstIsChildless, Ninst.pushB256]) with
          ⟨branchCursor, hline⟩
        have hflagPrefix :
            (leftmostFsig (DispatchTree.build n
                (((w, body) :: y :: ys).drop
                  ((((w, body) :: y :: ys).length + 1) / 2))) >? sig) ::
              sig :: stack <<+ branchCursor.pre.stack := by
          rcases Line.of_run_cons hline with
            ⟨afterDup, hdup, hrestDup⟩
          rcases Line.of_run_cons hrestDup with
            ⟨afterPush, hpush, hrestPush⟩
          rcases Line.of_run_cons hrestPush with
            ⟨afterGt, hgt, hnil⟩
          cases hnil
          have hdupStack : sig :: sig :: stack <<+ afterDup.stack :=
            prefix_of_dup_val hdup (by show_nth) hstack
          have hpushStack :
              leftmostFsig (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))) ::
                sig :: sig :: stack <<+ afterPush.stack := by
            simpa using prefix_of_push (of_run_pushB256 hpush) hdupStack
          exact prefix_of_gt hgt hpushStack
        have hleftmost :
            leftmostFsig (DispatchTree.build n
              (((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2))) = z.fst := by
          rw [hdrop, DispatchTree.leftmostFsig_build]
        rw [hleftmost] at hflagPrefix
        rcases hmemSplit with hmemTake | hmemDrop
        · have hlt : sig < z.fst := by
            have hz : z ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
              rw [hdrop]
              exact List.mem_cons_self ..
            exact DispatchTree.fst_lt_of_sorted_append
              hsortedSplit hmemTake hz
          have hcheck : (z.fst >? sig) = 1 := by
            simp [B256.gtCheck, hlt]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchSucc (flag := (1 : B256))
              (by decide) hflagPrefix with
            ⟨leftCursor, hleftStack⟩
          rcases ih hsortedTake htakeLen hmemTake leftCursor hleftStack with
            ⟨bodyCursor, hbodyStack⟩
          exact ⟨bodyCursor, hbodyStack⟩
        · have hle : z.fst ≤ sig := by
            have hsortedZ : DispatchTree.sorted (z :: zs) = true := by
              rw [← hdrop]
              exact hsortedDrop
            rw [hdrop] at hmemDrop
            exact DispatchTree.fst_le_of_sorted_mem hsortedZ hmemDrop
          have hcheck : (z.fst >? sig) = 0 := by
            simp [B256.gtCheck, not_lt_of_ge hle]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchZero hflagPrefix with
            ⟨rightCursor, hrightStack⟩
          rcases ih hsortedDrop hdropLen hmemDrop rightCursor hrightStack with
            ⟨bodyCursor, hbodyStack⟩
          exact ⟨bodyCursor, hbodyStack⟩

/-- Public counted form of sorted dispatch reachability; the counted mirror
of `Exec.Frame.CompiledCursor.reachDispatchWith`. -/
theorem Exec.Frame.CountedCursor.reachDispatchWith
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {funcs : List (B256 × Func)} {sig : B256} {f : Func}
    {k : Nat} {stack : Stack}
    (hsorted : DispatchTree.sorted funcs = true)
    (hmem : (sig, f) ∈ funcs)
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (dispatchWith k (DispatchTree.ofSorted funcs)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table f final,
      stack <<+ bodyCursor.pre.stack :=
  cursor.reachDispatchWith_build hsorted (Nat.le_succ _) hmem hstack

/-- The actual retained root execution, advanced past the runtime's entry
`JUMPDEST`, is a counted cursor at the WETH10 main body; the counted mirror
of `Exec.Frame.compiledMainCursor`. -/
theorem Exec.Frame.compiledMainCursorCounted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) :
    Nonempty (Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (weth10 dp).main frame.post) := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hcode := context.invocation.2.2.2
      have hcompiled := Prog.runCompiled_of_exec e pre (weth10 dp) post
        (weth10_pcFree dp) run hcode
      rcases hcompiled with ⟨compiledMid, hcompiledBurn, hmain⟩
      have hget :
          (table 0 (((weth10 dp).main) :: weth10Aux))[0]? =
            some (0, (weth10 dp).main) := rfl
      rcases subcode_of_get?_eq_some hcode hget with ⟨hjumpdest, hsub⟩
      have hboundary : noPushBefore e.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run hjumpdest with
        ⟨actualMid, continuation, hburn, hgas, _hprec⟩
      have hmid : actualMid = compiledMid :=
        Devm.eq_of_burnBy (Devm.BurnBy.of_burn hburn hgas)
          hcompiledBurn
      subst compiledMid
      have hstep : Evm.step ⟨0, e, pre⟩ = .cont 1 actualMid :=
        Evm.jumpdest_cont hjumpdest (Devm.BurnBy.of_burn hburn hgas)
      have hrootPrefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixActions.refl _
      have hrootCounted : Exec.Deriv.ParentPrefixCounted dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixCounted.refl _
      rcases Exec.Frame.advance_cont_counted
          (frame := ⟨0, e, pre, .ok post, run, committed⟩)
          run ⟨[], hrootPrefix⟩ hrootCounted hstep with
        ⟨actualContinuation, hentryPrefix, hentryCounted⟩
      exact ⟨⟨1, actualMid, actualContinuation, hentryPrefix,
        hentryCounted, hmain, hsub, hboundary⟩⟩

/-- A successful authentic non-receive invocation reaches the counted cursor
for its exact listed selector body; the counted mirror of
`Exec.Frame.compiledSelectorBodyCursor`. -/
theorem Exec.Frame.compiledSelectorBodyCursorCounted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    Nonempty (Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post) := by
  rcases Blanc.Weth10.Exec.Frame.compiledMainCursorCounted (frame := frame)
      context with ⟨mainCursor⟩
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (receiveEther <?>
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))))
    frame.post at mainCursor
  rcases mainCursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨entryBranchCursor, hentryLine⟩
  have hflagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        entryBranchCursor.pre.stack := by
    rcases Line.of_run_cons hentryLine with
      ⟨afterSize, hsize, hrestSize⟩
    rcases Line.of_run_cons hrestSize with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hsizePrefix : [frame.sevm.data.length.toB256] <<+
        afterSize.stack :=
      prefix_of_push (of_run_calldatasize hsize) nil_pref
    exact prefix_of_iszero hzero hsizePrefix
  have hflagZero : (frame.sevm.data.length.toB256 =? 0) = 0 := by
    simp [B256.eqCheck, hnonempty]
  rw [hflagZero] at hflagPrefix
  rcases entryBranchCursor.selectBranchZero hflagPrefix with
    ⟨dispatchPrefixCursor, _hdispatchStack⟩
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))
    frame.post at dispatchPrefixCursor
  rcases dispatchPrefixCursor.peelChildlessLine
      (by simp [fsig, cdl, shiftRight, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨dispatchCursor, hfsig⟩
  have hselectorPrefix : Sevm.selector frame.sevm :: [] <<+
      dispatchCursor.pre.stack :=
    prefix_of_fsig nil_pref hfsig
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (dispatchWith fallbackSlot
      (DispatchTree.ofSorted (weth10Funcs dp))) frame.post at dispatchCursor
  rcases dispatchCursor.reachDispatchWith (weth10Funcs_sorted dp)
      hmem hselectorPrefix with
    ⟨bodyCursor, _hbodyStack⟩
  exact ⟨bodyCursor⟩

/-- A successful counted cursor at a nonpayable wrapper reaches its guarded
body; the counted mirror of `Exec.Frame.CompiledCursor.enterNonpayable`. -/
theorem Exec.Frame.CountedCursor.enterNonpayable
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (nonpayable body) final) :
    Nonempty (Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table body final) := by
  have hvalue : frame.sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled cursor.run)
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
    ([Ninst.callvalue, Ninst.iszero] +++ (body <?> Func.revert)) final
    at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨branchCursor, hline⟩
  have hflagPrefix : [frame.sevm.value =? 0] <<+
      branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with
      ⟨afterValue, hcallvalue, hrestValue⟩
    rcases Line.of_run_cons hrestValue with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hvaluePrefix : [frame.sevm.value] <<+ afterValue.stack :=
      prefix_of_push (of_run_callvalue hcallvalue) nil_pref
    exact prefix_of_iszero hzero hvaluePrefix
  rw [hvalue] at hflagPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at hflagPrefix
  rcases branchCursor.selectBranchSucc (flag := (1 : B256))
      (by decide) hflagPrefix with
    ⟨bodyCursor, _hbodyStack⟩
  exact ⟨bodyCursor⟩

/-- Closing a counted cursor at a terminal source instruction: the retained
frame's entire proper-descendant counted stream is empty.  The counted
mirror of `Exec.Frame.CompiledCursor.finishLast`. -/
theorem Exec.Frame.CountedCursor.finishAttributionInner
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {i : Linst} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table (.last i) final) :
    Exec.attributionInner dp ca frame.run = [] := by
  have hat : Linst.At frame.sevm.code cursor.pc i :=
    Linst.at_of_slice cursor.codeSlice
  have hstep := Evm.step_last (devm := cursor.pre) hat
  have htail : Exec.attributionInner dp ca cursor.current = [] :=
    Exec.attributionInner_eq_nil_of_descendantFrames_eq_nil cursor.current
      (Exec.descendantFrames_eq_nil_of_halt_step cursor.current hstep)
  have hp := cursor.countedPrefix.descendantCounted_eq
  change Exec.attributionInner dp ca frame.run =
    [] ++ Exec.attributionInner dp ca cursor.current at hp
  rw [htail] at hp
  simpa using hp

/-- Any listed nonpayable selector whose guarded body is a childless line
ending in a terminal instruction contributes an empty proper-descendant
counted stream; the counted mirror of
`Exec.Frame.descendantFlowActions_eq_nil_of_nonpayableChildless`. -/
theorem Exec.Frame.attributionInner_eq_nil_of_nonpayableChildless
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {line : Line} {i : Linst}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm,
      nonpayable (line +++ Func.last i)) ∈ weth10Funcs dp)
    (hchildless : ∀ n ∈ line, NinstIsChildless n) :
    Exec.attributionInner dp ca frame.run = [] := by
  rcases Blanc.Weth10.Exec.Frame.compiledSelectorBodyCursorCounted (frame := frame)
      context hnonempty hmem with
    ⟨wrapperCursor⟩
  rcases wrapperCursor.enterNonpayable with ⟨bodyCursor⟩
  rcases bodyCursor.peelChildlessLine hchildless with ⟨lastCursor, -⟩
  exact lastCursor.finishAttributionInner

/-! ## Counted silent walk to the selector body

The counted cursor walk above discards the frame's entry-state observations.
The allowance-region arms need them: they must relate the tagged allowance
keys read at frame entry to the counted walk's own body cursor.  These are the
counted mirrors of the compiled module's silent dispatch walk, carrying a
`Devm.DispatchSilent` witness alongside the counted prefix. -/

section CountedSilentCursor

open scoped LogOutputHinv

/-- Zero-branch selection preserving the empty counted prefix and the
entry observations. -/
theorem Exec.Frame.CountedCursor.selectBranchZeroSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (.branch left right) final)
    (hstack : (0 : B256) :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table left final,
      stack <<+ arm.pre.stack ∧
      Devm.DispatchSilent cursor.pre arm.pre := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩, hw.2,
        Devm.DispatchSilent.of_popBurnBy hpop⟩
  | succ hne _hroom hpop _hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hne hw.1).elim

/-- Nonzero-branch selection preserving the empty counted prefix and the
entry observations. -/
theorem Exec.Frame.CountedCursor.selectBranchSuccSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm} {flag : B256} {stack : Stack}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (.branch left right) final)
    (hflag : flag ≠ 0)
    (hstack : flag :: stack <<+ cursor.pre.stack) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table right final,
      stack <<+ arm.pre.stack ∧
      Devm.DispatchSilent cursor.pre arm.pre := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, _hsubLeft, _hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero _hroom hpop _hleft =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      exact (hflag hw.1.symm).elim
  | succ hne hroom hpop hright =>
      have hw := popBurn_pref (Devm.PopBurn.of_popBurnBy hpop) hstack
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨afterJump, hpJump, hcJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterJump hpJump hcJump
          hstepJumpdest with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨loc + 1, _, armExec, hpArm, hcArm, hright,
        hsubRight, hboundRight⟩, hw.2,
        Devm.DispatchSilent.of_popBurnBy hpop⟩

/-- Select the fall-through arm when successful execution of the jumped
arm is impossible, retaining the compiled branch pop/burn relation; the
counted mirror of `Exec.Frame.CompiledCursor.selectBranchLeftWithBurn`. -/
theorem Exec.Frame.CountedCursor.selectBranchLeftWithBurn
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (.branch left right) final)
    (hnoRight : ∀ pre, ¬ Func.Run fs frame.sevm pre right final) :
    ∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table left final,
      Devm.PopBurnBy [0] (gVerylow + gHigh) cursor.pre arm.pre := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      _hjumpdest, _hjumpable, _hsubRight, _hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩, hpop⟩
  | succ _hne _hroom _hpop hright =>
      exact absurd (Func.Run.of_runCompiled hright) (hnoRight _)

/-- A matching compiled dispatch leaf advances to its stored body while
preserving the empty counted prefix and the entry observations. -/
theorem Exec.Frame.CountedCursor.reachDispatchLeafSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)} {final : Devm}
    {sig w : B256} {f body : Func} {k : Nat} {stack : Stack}
    (hmem : (sig, f) ∈ [(w, body)])
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (dispatchWith k (.leaf w body)) final)
    (hstack : sig :: stack <<+ cursor.pre.stack) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table f final,
      stack <<+ bodyCursor.pre.stack ∧
      Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  have heq : (sig, f) = (w, body) := List.mem_singleton.mp hmem
  injection heq with hsig hfun
  subst w
  subst body
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
    ([Ninst.pushB256 sig, Ninst.eq] +++ (f <?> .call k)) final at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless, Ninst.pushB256]) with
    ⟨branchCursor, hline⟩
  have hflag : (sig =? sig) :: stack <<+ branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with ⟨afterPush, hpush, hrest⟩
    rcases Line.of_run_cons hrest with ⟨afterEq, heqRun, hnil⟩
    cases hnil
    have hpushed : sig :: sig :: stack <<+ afterPush.stack := by
      simpa using prefix_of_push (of_run_pushB256 hpush) hstack
    exact prefix_of_eq heqRun hpushed
  rw [show (sig =? sig) = 1 from by simp [B256.eqCheck]] at hflag
  rcases branchCursor.selectBranchSuccSilent
      (left := .call k) (right := f) (flag := (1 : B256))
      (by decide) hflag with
    ⟨bodyCursor, hbodyStack, hbranchSilent⟩
  exact ⟨bodyCursor, hbodyStack,
    (Devm.DispatchSilent.of_pushEq hline).trans hbranchSilent⟩

/-- Reach the selected body of a generated sorted dispatch tree while
keeping the empty counted prefix and the entry observations. -/
theorem Exec.Frame.CountedCursor.reachDispatchWithSilent_build :
    ∀ {n : Nat} {xs : List (B256 × Func)} {sig : B256} {f : Func}
      {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
      {fs : List Func} {table : List (Nat × Func)} {k : Nat}
      {final : Devm} {stack : Stack},
      DispatchTree.sorted xs = true →
      xs.length ≤ n + 1 →
      (sig, f) ∈ xs →
      (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
        (dispatchWith k (DispatchTree.build n xs)) final) →
      (sig :: stack <<+ cursor.pre.stack) →
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table f final,
        stack <<+ bodyCursor.pre.stack ∧
        Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  intro n
  induction n with
  | zero =>
      intro xs sig f dp ca frame fs table k final stack _hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeafSilent hmem hstack
      · exfalso
        simp only [List.length_cons] at hlen
        omega
  | succ n ih =>
      intro xs sig f dp ca frame fs table k final stack hsorted hlen hmem
        cursor hstack
      rcases xs with _ | ⟨⟨w, body⟩, _ | ⟨y, ys⟩⟩
      · cases hmem
      · exact cursor.reachDispatchLeafSilent hmem hstack
      · simp only [List.length_cons] at hlen
        have htakeLen :
            (((w, body) :: y :: ys).take
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_take, List.length_cons]
          omega
        have hdropLen :
            (((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2)).length ≤
              n + 1 := by
          simp only [List.length_drop, List.length_cons]
          omega
        obtain ⟨z, zs, hdrop⟩ :
            ∃ z zs, ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) = z :: zs := by
          rcases hd : ((w, body) :: y :: ys).drop
              ((((w, body) :: y :: ys).length + 1) / 2) with _ | ⟨z, zs⟩
          · exfalso
            have hl := congrArg List.length hd
            simp only [List.length_drop, List.length_cons,
              List.length_nil] at hl
            omega
          · exact ⟨z, zs, rfl⟩
        have hsortedSplit : DispatchTree.sorted
            (((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ++
              ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2)) = true := by
          rw [List.take_append_drop]
          exact hsorted
        have hsortedTake := DispatchTree.sorted_append_left hsortedSplit
        have hsortedDrop := DispatchTree.sorted_append_right hsortedSplit
        have hmemSplit :
            (sig, f) ∈ ((w, body) :: y :: ys).take
                ((((w, body) :: y :: ys).length + 1) / 2) ∨
              (sig, f) ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
          apply List.mem_append.mp
          rw [List.take_append_drop]
          exact hmem
        change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
          ([Ninst.dup 0,
              Ninst.pushB256 (leftmostFsig
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2)))),
              Ninst.gt] +++
            (dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).take
                    ((((w, body) :: y :: ys).length + 1) / 2))) <?>
              dispatchWith k
                (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))))) final
          at cursor
        rcases cursor.peelChildlessLine
            (by simp [NinstIsChildless, Ninst.pushB256]) with
          ⟨branchCursor, hline⟩
        have hlineSilent := Devm.DispatchSilent.of_dupPushGt hline
        have hflagPrefix :
            (leftmostFsig (DispatchTree.build n
                (((w, body) :: y :: ys).drop
                  ((((w, body) :: y :: ys).length + 1) / 2))) >? sig) ::
              sig :: stack <<+ branchCursor.pre.stack := by
          rcases Line.of_run_cons hline with
            ⟨afterDup, hdup, hrestDup⟩
          rcases Line.of_run_cons hrestDup with
            ⟨afterPush, hpush, hrestPush⟩
          rcases Line.of_run_cons hrestPush with
            ⟨afterGt, hgt, hnil⟩
          cases hnil
          have hdupStack : sig :: sig :: stack <<+ afterDup.stack :=
            prefix_of_dup_val hdup (by show_nth) hstack
          have hpushStack :
              leftmostFsig (DispatchTree.build n
                  (((w, body) :: y :: ys).drop
                    ((((w, body) :: y :: ys).length + 1) / 2))) ::
                sig :: sig :: stack <<+ afterPush.stack := by
            simpa using prefix_of_push (of_run_pushB256 hpush) hdupStack
          exact prefix_of_gt hgt hpushStack
        have hleftmost :
            leftmostFsig (DispatchTree.build n
              (((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2))) = z.fst := by
          rw [hdrop, DispatchTree.leftmostFsig_build]
        rw [hleftmost] at hflagPrefix
        rcases hmemSplit with hmemTake | hmemDrop
        · have hlt : sig < z.fst := by
            have hz : z ∈ ((w, body) :: y :: ys).drop
                ((((w, body) :: y :: ys).length + 1) / 2) := by
              rw [hdrop]
              exact List.mem_cons_self ..
            exact DispatchTree.fst_lt_of_sorted_append
              hsortedSplit hmemTake hz
          have hcheck : (z.fst >? sig) = 1 := by
            simp [B256.gtCheck, hlt]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchSuccSilent (flag := (1 : B256))
              (by decide) hflagPrefix with
            ⟨leftCursor, hleftStack, hbranchSilent⟩
          rcases ih hsortedTake htakeLen hmemTake leftCursor hleftStack with
            ⟨bodyCursor, hbodyStack, hbodySilent⟩
          exact ⟨bodyCursor, hbodyStack,
            (hlineSilent.trans hbranchSilent).trans hbodySilent⟩
        · have hle : z.fst ≤ sig := by
            have hsortedZ : DispatchTree.sorted (z :: zs) = true := by
              rw [← hdrop]
              exact hsortedDrop
            rw [hdrop] at hmemDrop
            exact DispatchTree.fst_le_of_sorted_mem hsortedZ hmemDrop
          have hcheck : (z.fst >? sig) = 0 := by
            simp [B256.gtCheck, not_lt_of_ge hle]
          rw [hcheck] at hflagPrefix
          rcases branchCursor.selectBranchZeroSilent hflagPrefix with
            ⟨rightCursor, hrightStack, hbranchSilent⟩
          rcases ih hsortedDrop hdropLen hmemDrop rightCursor hrightStack with
            ⟨bodyCursor, hbodyStack, hbodySilent⟩
          exact ⟨bodyCursor, hbodyStack,
            (hlineSilent.trans hbranchSilent).trans hbodySilent⟩

/-- The actual retained root execution, advanced past the runtime's entry
`JUMPDEST`, is a counted cursor at the WETH10 main body whose state
retains the frame-entry observations. -/
theorem Exec.Frame.compiledMainCursorCountedSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame) :
    ∃ cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (weth10 dp).main frame.post,
      Devm.DispatchSilent frame.pre cursor.pre := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hcode := context.invocation.2.2.2
      have hcompiled := Prog.runCompiled_of_exec e pre (weth10 dp) post
        (weth10_pcFree dp) run hcode
      rcases hcompiled with ⟨compiledMid, hcompiledBurn, hmain⟩
      have hget :
          (table 0 (((weth10 dp).main) :: weth10Aux))[0]? =
            some (0, (weth10 dp).main) := rfl
      rcases subcode_of_get?_eq_some hcode hget with ⟨hjumpdest, hsub⟩
      have hboundary : noPushBefore e.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run hjumpdest with
        ⟨actualMid, continuation, hburn, hgas, _hprec⟩
      have hmid : actualMid = compiledMid :=
        Devm.eq_of_burnBy (Devm.BurnBy.of_burn hburn hgas)
          hcompiledBurn
      subst compiledMid
      have hstep : Evm.step ⟨0, e, pre⟩ = .cont 1 actualMid :=
        Evm.jumpdest_cont hjumpdest (Devm.BurnBy.of_burn hburn hgas)
      have hrootPrefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixActions.refl _
      have hrootCounted : Exec.Deriv.ParentPrefixCounted dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨0, e, pre, .ok post, run⟩ [] :=
        Exec.Deriv.ParentPrefixCounted.refl _
      rcases Exec.Frame.advance_cont_counted
          (frame := ⟨0, e, pre, .ok post, run, committed⟩)
          run ⟨[], hrootPrefix⟩ hrootCounted hstep with
        ⟨actualContinuation, hentryPrefix, hentryCounted⟩
      exact ⟨⟨1, actualMid, actualContinuation, hentryPrefix,
        hentryCounted, hmain, hsub, hboundary⟩,
        Devm.DispatchSilent.of_burnBy
          (Devm.BurnBy.of_burn hburn hgas)⟩

/-- A successful authentic non-receive invocation reaches the counted
cursor for its exact listed selector body while retaining the frame-entry
observations; the counted mirror of
`Exec.Frame.compiledSelectorBodyCursorSilent`. -/
theorem Exec.Frame.compiledSelectorBodyCursorCountedSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame} {body : Func}
    (context : Blanc.Weth10.Exec.Frame.AuthenticContext dp ca frame)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hmem : (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
      Devm.DispatchSilent frame.pre bodyCursor.pre := by
  rcases Blanc.Weth10.Exec.Frame.compiledMainCursorCountedSilent (frame := frame)
      context with
    ⟨mainCursor, hmainSilent⟩
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (receiveEther <?>
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))))
    frame.post at mainCursor
  rcases mainCursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨entryBranchCursor, hentryLine⟩
  have hentrySilent := Devm.DispatchSilent.of_entryFlag hentryLine
  have hflagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        entryBranchCursor.pre.stack := by
    rcases Line.of_run_cons hentryLine with
      ⟨afterSize, hsize, hrestSize⟩
    rcases Line.of_run_cons hrestSize with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hsizePrefix : [frame.sevm.data.length.toB256] <<+
        afterSize.stack :=
      prefix_of_push (of_run_calldatasize hsize) nil_pref
    exact prefix_of_iszero hzero hsizePrefix
  have hflagZero : (frame.sevm.data.length.toB256 =? 0) = 0 := by
    simp [B256.eqCheck, hnonempty]
  rw [hflagZero] at hflagPrefix
  rcases entryBranchCursor.selectBranchZeroSilent hflagPrefix with
    ⟨dispatchPrefixCursor, _hdispatchStack, hentryBranchSilent⟩
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))
    frame.post at dispatchPrefixCursor
  rcases dispatchPrefixCursor.peelChildlessLine
      (by simp [fsig, cdl, shiftRight, NinstIsChildless,
        Ninst.pushB256]) with
    ⟨dispatchCursor, hfsig⟩
  have hfsigSilent := Devm.DispatchSilent.of_fsig hfsig
  have hselectorPrefix : Sevm.selector frame.sevm :: [] <<+
      dispatchCursor.pre.stack :=
    prefix_of_fsig nil_pref hfsig
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (dispatchWith fallbackSlot
      (DispatchTree.ofSorted (weth10Funcs dp))) frame.post at dispatchCursor
  rcases dispatchCursor.reachDispatchWithSilent_build (weth10Funcs_sorted dp)
      (Nat.le_succ _) hmem hselectorPrefix with
    ⟨bodyCursor, _hbodyStack, hdispatchSilent⟩
  exact ⟨bodyCursor,
    hmainSilent.trans (hentrySilent.trans
      (hentryBranchSilent.trans (hfsigSilent.trans hdispatchSilent)))⟩

/-- A successful counted cursor at a nonpayable wrapper reaches its
guarded body while retaining the entry observations; the counted mirror
of `Exec.Frame.CompiledCursor.enterNonpayableSilent`. -/
theorem Exec.Frame.CountedCursor.enterNonpayableSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (nonpayable body) final) :
    ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table body final,
      Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  have hvalue : frame.sevm.value = 0 :=
    value_eq_zero_of_run_nonpayable
      (Func.Run.of_runCompiled cursor.run)
  change Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
    ([Ninst.callvalue, Ninst.iszero] +++ (body <?> Func.revert)) final
    at cursor
  rcases cursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨branchCursor, hline⟩
  have hlineSilent := Devm.DispatchSilent.of_callvalueFlag hline
  have hflagPrefix : [frame.sevm.value =? 0] <<+
      branchCursor.pre.stack := by
    rcases Line.of_run_cons hline with
      ⟨afterValue, hcallvalue, hrestValue⟩
    rcases Line.of_run_cons hrestValue with
      ⟨afterZero, hzero, hnil⟩
    cases hnil
    have hvaluePrefix : [frame.sevm.value] <<+ afterValue.stack :=
      prefix_of_push (of_run_callvalue hcallvalue) nil_pref
    exact prefix_of_iszero hzero hvaluePrefix
  rw [hvalue] at hflagPrefix
  have hone : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [hone] at hflagPrefix
  rcases branchCursor.selectBranchSuccSilent (flag := (1 : B256))
      (by decide) hflagPrefix with
    ⟨bodyCursor, _hbodyStack, hbranchSilent⟩
  exact ⟨bodyCursor, hlineSilent.trans hbranchSilent⟩

/-- Follow one generated internal source call while retaining the entry
observations; the silent mirror of `Exec.Frame.CountedCursor.enterCall`. -/
theorem Exec.Frame.CountedCursor.enterCallSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        Devm.DispatchSilent cursor.pre bodyCursor.pre := by
  cases hrun : cursor.run with
  | call hget hroom hburn hbody =>
      rcases subcode_compile_call cursor.codeSlice with
        ⟨loc, p, hgetTable, hloc, hpushAt, hjump⟩
      have hpf := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) hgetTable)
      rw [hget] at hpf
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at hpf
      subst p
      rcases subcode_of_get?_eq_some hcode hgetTable with
        ⟨hjumpdest, hsub⟩
      have hjumpable := Prog.jumpable_of_get?_table hcode hgetTable
      rcases hpushAt with ⟨le, hpush⟩
      rcases Evm.call_steps (le := le) hpush hjump hjumpdest
          hjumpable.1 hloc hroom hburn with
        ⟨hstepPush, hstepJump, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJump with
        ⟨afterJump, hpJump, hcJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterJump hpJump hcJump
          hstepJumpdest with
        ⟨bodyExec, hpBody, hcBody⟩
      exact ⟨_, hget, ⟨loc + 1, _, bodyExec, hpBody, hcBody, hbody,
        hsub, hjumpable.2⟩, Devm.DispatchSilent.of_burnBy hburn⟩

/-- Select whichever branch arm the committed run actually took while
retaining the entry observations; the silent mirror of
`Exec.Frame.CountedCursor.selectBranchSplit`. -/
theorem Exec.Frame.CountedCursor.selectBranchSplitSilent
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (.branch left right) final) :
    (∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table left final,
      Devm.DispatchSilent cursor.pre arm.pre) ∨
    (∃ arm : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table right final,
      Devm.DispatchSilent cursor.pre arm.pre) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact Or.inl ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩, Devm.DispatchSilent.of_popBurnBy hpop⟩
  | succ hne hroom hpop hright =>
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨afterJump, hpJump, hcJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterJump hpJump hcJump
          hstepJumpdest with
        ⟨armExec, hpArm, hcArm⟩
      exact Or.inr ⟨⟨loc + 1, _, armExec, hpArm, hcArm, hright,
        hsubRight, hboundRight⟩, Devm.DispatchSilent.of_popBurnBy hpop⟩

end CountedSilentCursor

/-! ## Counted branch and call traversal

Two further counted mirrors that carry no entry observation: the branch arm
the committed run actually took, and one generated internal source call. -/

/-- Select whichever branch arm the committed run actually took while
preserving the empty counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.selectBranch`. -/
theorem Exec.Frame.CountedCursor.selectBranchSplit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table
      (.branch left right) final) :
    Nonempty (Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table left final) ∨
      Nonempty (Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame fs table right final) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _hlocEq, hloc, hpush, hjumpi, hsubLeft, hboundLeft,
      hjumpdest, hjumpable, hsubRight, hboundRight⟩
  have compiled := cursor.run
  cases compiled with
  | zero hroom hpop hleft =>
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨hstepPush, hstepJumpi⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨armExec, hpArm, hcArm⟩
      exact Or.inl ⟨⟨cursor.pc + 4, _, armExec, hpArm, hcArm, hleft,
        hsubLeft, hboundLeft⟩⟩
  | succ hne hroom hpop hright =>
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable
          hloc hne hroom hpop with
        ⟨hstepPush, hstepJumpi, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJumpi with
        ⟨afterJump, hpJump, hcJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterJump hpJump hcJump
          hstepJumpdest with
        ⟨armExec, hpArm, hcArm⟩
      exact Or.inr ⟨⟨loc + 1, _, armExec, hpArm, hcArm, hright,
        hsubRight, hboundRight⟩⟩

/-- Follow one generated internal source call while preserving the empty
counted prefix; the counted mirror of
`Exec.Frame.CompiledCursor.enterCall`. -/
theorem Exec.Frame.CountedCursor.enterCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      Nonempty (Blanc.Weth10.Exec.Frame.CountedCursor dp ca frame (f₀ :: aux)
        (table 0 (f₀ :: aux)) body final) := by
  cases hrun : cursor.run with
  | call hget hroom hburn hbody =>
      rcases subcode_compile_call cursor.codeSlice with
        ⟨loc, p, hgetTable, hloc, hpushAt, hjump⟩
      have hpf := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) hgetTable)
      rw [hget] at hpf
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at hpf
      subst p
      rcases subcode_of_get?_eq_some hcode hgetTable with
        ⟨hjumpdest, hsub⟩
      have hjumpable := Prog.jumpable_of_get?_table hcode hgetTable
      rcases hpushAt with ⟨le, hpush⟩
      rcases Evm.call_steps (le := le) hpush hjump hjumpdest
          hjumpable.1 hloc hroom hburn with
        ⟨hstepPush, hstepJump, hstepJumpdest⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          cursor.current cursor.parentPrefix
          cursor.countedPrefix hstepPush with
        ⟨afterPush, hpPush, hcPush⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterPush hpPush hcPush
          hstepJump with
        ⟨afterJump, hpJump, hcJump⟩
      rcases Blanc.Weth10.Exec.Frame.advance_cont_counted (frame := frame)
          afterJump hpJump hcJump
          hstepJumpdest with
        ⟨bodyExec, hpBody, hcBody⟩
      exact ⟨_, hget, ⟨⟨loc + 1, _, bodyExec, hpBody, hcBody, hbody,
        hsub, hjumpable.2⟩⟩⟩

/-! ## Identifying the counted label of an exact source `CALL` -/

/-- The counted label selected by an exact source `CALL` edge is precisely
the attribution stream of its retained raw child.  For a `CALL` frame raw
commitment and settlement commitment coincide, so no separate commitment
hypothesis is needed. -/
theorem Exec.Deriv.ParentStepCounted.selected_eq_retained_of_call
    {dp : DeployParams} {ca : Adr}
    {pc nextPc : Nat} {sevm : Sevm} {pre post : Devm} {out : Execution}
    {current : Exec pc sevm pre out}
    {continuation : Exec nextPc sevm post out}
    {xl : Xlot} {selected : List CountedFrame}
    (hat : Ninst.At sevm.code pc Ninst.call)
    (filled : xl.Filled)
    (step : Ninst.StepRun pc sevm pre Ninst.call xl (.ok post))
    (retained : RetainedXlot xl)
    (edge : Exec.Deriv.ParentStepCounted dp ca
      ⟨nextPc, sevm, post, out, continuation⟩
      ⟨pc, sevm, pre, out, current⟩ selected) :
    selected = retained.attributionStream dp ca := by
  cases edge with
  | cont hstep next =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨trivial, trivial⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      rfl
  | doneOk hstep henter hresume next =>
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call .none (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled (show Xlot.Filled .none from trivial) step actual).1
      subst xl
      cases retained
      rfl
  | runOk hstep henter child hresume next =>
      rename_i spawned resume childEvm raw
      have hs := (Evm.step_next hat).symm.trans hstep
      have actual :
          Ninst.StepRun pc sevm pre Ninst.call
            (.some ⟨childEvm, raw⟩) (.ok post) := by
        simp only [Ninst.StepRun, hs, Step.Run]
        exact ⟨_, RunFrame.of_run henter, hresume.symm⟩
      have actualFilled : Xlot.Filled (.some ⟨childEvm, raw⟩) := ⟨child⟩
      have hslot := (Ninst.StepRun.unique_exec_of_filled
        filled actualFilled step actual).1
      subst xl
      cases retained with
      | some retainedRun =>
          have hrun : retainedRun = child := Subsingleton.elim _ _
          subst retainedRun
          rcases Ninst.step_call_spawn_ofCall hs with ⟨msg, rfl⟩
          by_cases hraw : Execution.commits raw = true
          · have hcommit : Blanc.Frame.settlementCommits
                (Frame.ofCall msg) raw = true :=
              Frame.settlementCommits_ofCall_of_raw_commits hraw
            simp [hcommit, RetainedXlot.attributionStream,
              Exec.attributionStream, hraw]
          · have hnot : ¬ Blanc.Frame.settlementCommits
                (Frame.ofCall msg) raw = true := fun h =>
              hraw (Blanc.Frame.raw_commits_of_settlementCommits h)
            simp [RetainedXlot.attributionStream,
              Exec.attributionStream, hnot, hraw]

end Weth10

end Blanc
