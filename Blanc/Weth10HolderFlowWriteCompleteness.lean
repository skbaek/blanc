import Blanc.Weth10HolderFlowAuthenticity
import Blanc.Weth10HolderFlowCompiled
import Blanc.Weth10HolderFlowSelectorFacts

/-!
Proof-indexed balance-write occurrences for the compiled WETH10 runtime.

The occurrence relation records an actually executed `SSTORE` in the original
`Exec` derivation.  Its key is required to be in the address-shaped balance
region and is tied to the retained normalized holder.  It deliberately does
not require the stored word to differ from the old word: an EVM-executed
no-op `SSTORE` is still an occurrence that must be classified.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- The same-frame continuation edge out of a fixed proof-indexed derivation
is unique, including its retained child-action label. -/
theorem Exec.Deriv.ParentStepActions.unique
    {dp : DeployParams} {ca : Adr}
    {root nextLeft nextRight : Exec.Deriv}
    {leftActions rightActions : List FlowAction}
    (left : Exec.Deriv.ParentStepActions dp ca
      nextLeft root leftActions)
    (right : Exec.Deriv.ParentStepActions dp ca
      nextRight root rightActions) :
    nextLeft = nextRight ∧ leftActions = rightActions := by
  cases left <;> cases right <;> simp_all

/-- Same-frame prefixes from one concrete `Exec` proof form a linear chain.
This is the generic ordering fact needed to compare an arbitrary occurrence
with a compiled source cursor. -/
theorem Exec.Deriv.ParentPrefixActions.linear
    {dp : DeployParams} {ca : Adr}
    {root leftTail rightTail : Exec.Deriv}
    {leftActions rightActions : List FlowAction}
    (left : Exec.Deriv.ParentPrefixActions dp ca
      root leftTail leftActions)
    (right : Exec.Deriv.ParentPrefixActions dp ca
      root rightTail rightActions) :
    (∃ suffix, Exec.Deriv.ParentPrefixActions dp ca
      leftTail rightTail suffix) ∨
    (∃ suffix, Exec.Deriv.ParentPrefixActions dp ca
      rightTail leftTail suffix) := by
  induction left generalizing rightTail rightActions with
  | refl =>
      exact Or.inl ⟨rightActions, right⟩
  | @step root next leftTail headActions leftActions head rest ih =>
      cases right with
      | refl =>
          exact Or.inr ⟨headActions ++ leftActions, .step head rest⟩
      | @step _ rightNext rightTail rightHeadActions rightActions
          rightHead rightRest =>
          have unique := head.unique rightHead
          cases unique.1
          cases unique.2
          exact ih rightRest

/-- An actual proof-indexed `SSTORE` whose raw key is an address-shaped WETH
balance key.  The machine states, recursive slot, raw key, stored value, and
normalized holder are all indices, so later classification cannot replace
this occurrence with an endpoint storage comparison. -/
def Exec.Frame.BalanceSstoreOccurrence
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (stepPre stepPost : Devm) (slot : Xlot)
    (key value : B256) (holder : Adr) : Prop :=
  frame.NinstOccurrence dp ca (.reg .sstore) stepPre stepPost slot ∧
    ValidAdr key ∧
    key = holder.toB256 ∧
    ∃ tail : Stack, key :: value :: tail <<+ stepPre.stack

/-- Any arbitrary instruction occurrence and any compiled cursor in the same
retained frame are comparable along the unique same-frame continuation chain.
The first arm is the source-recursion case (the occurrence is in the cursor's
remaining body); the second identifies the finite prefix that must be ruled
out when entering a source body through hidden compiler instructions. -/
theorem Exec.Frame.NinstOccurrence.comparable_with_cursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    {n : Ninst} {stepPre stepPost : Devm} {slot : Xlot}
    (occurrence : frame.NinstOccurrence dp ca n stepPre stepPost slot)
    (cursor : frame.CompiledCursor dp ca fs table body final) :
    ∃ (pc : Nat) (current : Exec pc frame.sevm stepPre frame.out),
      Ninst.At frame.sevm.code pc n ∧
      ((∃ suffix, Exec.Deriv.ParentPrefixActions dp ca
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
          ⟨pc, frame.sevm, stepPre, frame.out, current⟩ suffix) ∨
       (∃ suffix, Exec.Deriv.ParentPrefixActions dp ca
          ⟨pc, frame.sevm, stepPre, frame.out, current⟩
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
          suffix)) := by
  rcases occurrence with
    ⟨pc, current, _continuation, _before, _selected, hprefix, hat,
      _filled, _step, _prec, _edge⟩
  exact ⟨pc, current, hat, cursor.parentPrefix.linear hprefix⟩

/-- The same occurrence data as `NinstOccurrence`, but with its chronological
prefix starting at an arbitrary same-frame derivation. -/
def Exec.Frame.NinstOccurrenceFromDeriv
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (start : Exec.Deriv)
    (n : Ninst) (stepPre stepPost : Devm) (slot : Xlot) : Prop :=
  ∃ (pc : Nat)
      (current : Exec pc frame.sevm stepPre frame.out)
      (continuation : Exec (pc + n.size) frame.sevm stepPost frame.out)
      (crossed selected : List FlowAction),
    Exec.Deriv.ParentPrefixActions dp ca
      start
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ crossed ∧
    Ninst.At frame.sevm.code pc n ∧
    Xlot.Filled slot ∧
    Ninst.StepRun pc frame.sevm stepPre n slot (.ok stepPost) ∧
    Exec.Deriv.Prec
      ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ ∧
    Exec.Deriv.ParentStepActions dp ca
      ⟨pc + n.size, frame.sevm, stepPost, frame.out, continuation⟩
      ⟨pc, frame.sevm, stepPre, frame.out, current⟩ selected

/-- Cursor-indexed specialization of `NinstOccurrenceFromDeriv`. -/
def Exec.Frame.NinstOccurrenceFromCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    (cursor : frame.CompiledCursor dp ca fs table body final)
    (n : Ninst) (stepPre stepPost : Devm) (slot : Xlot) : Prop :=
  frame.NinstOccurrenceFromDeriv dp ca
    ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
    n stepPre stepPost slot

/-- Strengthened cursor comparison: either the arbitrary occurrence belongs
to the cursor's remaining same-frame execution, or it lies in the finite
compiler prefix before that cursor. -/
theorem Exec.Frame.NinstOccurrence.fromCursor_or_before
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {body : Func} {final : Devm}
    {n : Ninst} {stepPre stepPost : Devm} {slot : Xlot}
    (occurrence : frame.NinstOccurrence dp ca n stepPre stepPost slot)
    (cursor : frame.CompiledCursor dp ca fs table body final) :
    frame.NinstOccurrenceFromCursor cursor n stepPre stepPost slot ∨
      ∃ (pc : Nat) (current : Exec pc frame.sevm stepPre frame.out)
          (before : List FlowAction),
        Ninst.At frame.sevm.code pc n ∧
        Exec.Deriv.ParentPrefixActions dp ca
          ⟨pc, frame.sevm, stepPre, frame.out, current⟩
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
          before := by
  rcases occurrence with
    ⟨pc, current, continuation, _rootBefore, selected, rootPrefix, hat,
      filled, step, prec, edge⟩
  rcases cursor.parentPrefix.linear rootPrefix with
    ⟨crossed, after⟩ | ⟨beforeActions, before⟩
  · exact Or.inl ⟨pc, current, continuation, crossed, selected, after,
      hat, filled, step, prec, edge⟩
  · exact Or.inr ⟨pc, current, beforeActions, hat, before⟩

/-- Generic source-membership step for a `.next` node.  An arbitrary actual
occurrence in the cursor suffix is either the cursor's exact source head or
belongs to the tail cursor after that head. -/
theorem Exec.Frame.CompiledCursor.ninstOccurrenceFromCursor_head_or_tail
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {source : Ninst} {tail : Func} {final : Devm}
    {n : Ninst} {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.next source tail) final)
    (occurrence : frame.NinstOccurrenceFromCursor cursor n
      stepPre stepPost slot) :
    (n = source ∧ stepPre = cursor.pre) ∨
      ∃ (tailCursor : frame.CompiledCursor dp ca fs sourceTable tail final)
          (sourceSlot : Xlot),
        frame.NinstOccurrence dp ca source cursor.pre tailCursor.pre
          sourceSlot ∧
        frame.NinstOccurrenceFromCursor tailCursor n
          stepPre stepPost slot := by
  rcases occurrence with
    ⟨pc, current, continuation, crossed, selected, hpath, hat,
      filled, step, prec, edge⟩
  cases hpath with
  | refl =>
      have sourceAt : Ninst.At frame.sevm.code cursor.pc source :=
        ninstAt_of_subcode_next cursor.codeSlice
      have same : source = n := by
        simpa only [Ninst.At, Option.some.injEq, Inst.next.injEq] using
          sourceAt.symm.trans hat
      exact Or.inl ⟨same.symm, rfl⟩
  | @step _ next _ headActions tailActions head rest =>
      rcases cursor.selectNextWithActions with
        ⟨tailCursor, sourceSlot, sourceActions, sourceOccurrence,
          sourceEdge, _tailActions⟩
      have unique := head.unique sourceEdge
      cases unique.1
      cases unique.2
      exact Or.inr ⟨tailCursor, sourceSlot, sourceOccurrence,
        pc, current, continuation, tailActions, selected, rest, hat,
        filled, step, prec, edge⟩

private theorem Ninst.At.false_of_jinstAt
    {code : ByteArray} {pc : Nat} {n : Ninst} {j : Jinst}
    (nextAt : Ninst.At code pc n) (jumpAt : Jinst.At code pc j) : False := by
  unfold Ninst.At at nextAt
  unfold Jinst.At at jumpAt
  rw [nextAt] at jumpAt
  cases jumpAt

private theorem Ninst.At.eq_of_at
    {code : ByteArray} {pc : Nat} {left right : Ninst}
    (leftAt : Ninst.At code pc left) (rightAt : Ninst.At code pc right) :
    left = right := by
  unfold Ninst.At at leftAt rightAt
  simpa only [Option.some.injEq, Inst.next.injEq] using
    leftAt.symm.trans rightAt

/-- A same-frame compiler prefix all of whose current instruction boundaries
are known not to be `SSTORE`. -/
inductive Exec.Deriv.ParentNonSstorePrefix
    (dp : DeployParams) (ca : Adr) : Exec.Deriv → Exec.Deriv → Prop
  | refl (root : Exec.Deriv) : ParentNonSstorePrefix dp ca root root
  | step {root next tail : Exec.Deriv}
      (edge : Exec.Deriv.ParentStepActions dp ca next root [])
      (notStore : ¬ Ninst.At root.sevm.code root.pc (.reg .sstore))
      (rest : ParentNonSstorePrefix dp ca next tail) :
      ParentNonSstorePrefix dp ca root tail

/-- Remove a compiler-only non-SSTORE prefix from an arbitrary balance-write
occurrence while retaining its exact machine states, recursive slot, and
same-frame continuation proof. -/
theorem Exec.Deriv.ParentNonSstorePrefix.trim_balanceSstoreOccurrence
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {start tail : Exec.Deriv}
    (compilerPrefix : Exec.Deriv.ParentNonSstorePrefix dp ca start tail)
    {stepPre stepPost : Devm} {slot : Xlot}
    (occurrence : frame.NinstOccurrenceFromDeriv dp ca start
      (.reg .sstore) stepPre stepPost slot) :
    frame.NinstOccurrenceFromDeriv dp ca tail
      (.reg .sstore) stepPre stepPost slot := by
  induction compilerPrefix with
  | refl => exact occurrence
  | @step root next tail edge notStore rest ih =>
      rcases occurrence with
        ⟨pc, current, continuation, crossed, selected, hpath, hat,
          filled, stepRun, prec, occurrenceEdge⟩
      cases hpath with
      | refl => exact (notStore hat).elim
      | @step _ occurrenceNext _ headActions tailActions head suffix =>
          have unique := edge.unique head
          cases unique.1
          cases unique.2
          apply ih
          exact ⟨pc, current, continuation, tailActions, selected, suffix,
            hat, filled, stepRun, prec, occurrenceEdge⟩

inductive Exec.Frame.CompiledCursor.ActualBranch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.branch left right) final) : Prop
  | zero
      (arm : frame.CompiledCursor dp ca fs sourceTable left final)
      (pop : Devm.PopBurnBy [0] (gVerylow + gHigh)
        cursor.pre arm.pre)
      (compilerPrefix : Exec.Deriv.ParentNonSstorePrefix dp ca
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
        ⟨arm.pc, frame.sevm, arm.pre, frame.out, arm.current⟩) :
      ActualBranch cursor
  | succ (flag : B256)
      (nonzero : flag ≠ 0)
      (arm : frame.CompiledCursor dp ca fs sourceTable right final)
      (pop : Devm.PopBurnBy [flag]
        (gVerylow + gHigh + gJumpdest) cursor.pre arm.pre)
      (compilerPrefix : Exec.Deriv.ParentNonSstorePrefix dp ca
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
        ⟨arm.pc, frame.sevm, arm.pre, frame.out, arm.current⟩) :
      ActualBranch cursor

/-- Select the actually executed source branch arm and retain the explicit
relative prefix across only the compiler's PUSH/JUMPI/JUMPDEST glue, together
with the exact flag pop that selected that arm. -/
private theorem Exec.Frame.CompiledCursor.selectBranchWithSourcePrefix
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {left right : Func} {final : Devm}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.branch left right) final) :
    cursor.ActualBranch := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, _locEq, locBound, pushAt, jumpiAt, leftSub, leftBoundary,
      jumpdestAt, jumpable, rightSub, rightBoundary⟩
  cases cursor.run with
  | zero room pop leftRun =>
      rcases Evm.branch_zero_steps pushAt jumpiAt locBound room pop with
        ⟨pushStep, jumpiStep⟩
      rcases frame.advance_cont cursor.current cursor.parentPrefix
          pushStep with
        ⟨afterPush, afterPushPrefix⟩
      rcases frame.advance_cont afterPush afterPushPrefix jumpiStep with
        ⟨armExec, armPrefix⟩
      have currentEq : cursor.current = .cont pushStep afterPush :=
        Exec.unique _ _
      have afterPushEq : afterPush = .cont jumpiStep armExec :=
        Exec.unique _ _
      let arm : frame.CompiledCursor dp ca fs sourceTable left final :=
        ⟨cursor.pc + 4, _, armExec, cursor.actions, armPrefix,
          leftRun, leftSub, leftBoundary⟩
      have pushEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨cursor.pc + 3, frame.sevm, _, frame.out, afterPush⟩
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ [] :=
        by
          rw [currentEq]
          exact .cont pushStep afterPush
      have jumpiEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨cursor.pc + 4, frame.sevm, arm.pre, frame.out, arm.current⟩
          ⟨cursor.pc + 3, frame.sevm, _, frame.out, afterPush⟩ [] :=
        by
          rw [afterPushEq]
          exact .cont jumpiStep arm.current
      have pushNotStore : ¬ Ninst.At frame.sevm.code cursor.pc
          (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.At.eq_of_at storeAt pushAt
        cases impossible
      have jumpiNotStore : ¬ Ninst.At frame.sevm.code (cursor.pc + 3)
          (.reg .sstore) := fun storeAt =>
        Ninst.At.false_of_jinstAt storeAt jumpiAt
      exact .zero arm pop (.step pushEdge pushNotStore
        (.step jumpiEdge jumpiNotStore (.refl _)))
  | succ nonzero room pop rightRun =>
      rcases Evm.branch_succ_steps pushAt jumpiAt jumpdestAt jumpable
          locBound nonzero room pop with
        ⟨pushStep, jumpiStep, jumpdestStep⟩
      rcases frame.advance_cont cursor.current cursor.parentPrefix
          pushStep with
        ⟨afterPush, afterPushPrefix⟩
      rcases frame.advance_cont afterPush afterPushPrefix jumpiStep with
        ⟨afterJump, afterJumpPrefix⟩
      rcases frame.advance_cont afterJump afterJumpPrefix jumpdestStep with
        ⟨armExec, armPrefix⟩
      have currentEq : cursor.current = .cont pushStep afterPush :=
        Exec.unique _ _
      have afterPushEq : afterPush = .cont jumpiStep afterJump :=
        Exec.unique _ _
      have afterJumpEq : afterJump = .cont jumpdestStep armExec :=
        Exec.unique _ _
      let arm : frame.CompiledCursor dp ca fs sourceTable right final :=
        ⟨loc + 1, _, armExec, cursor.actions, armPrefix,
          rightRun, rightSub, rightBoundary⟩
      have pushEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨cursor.pc + 3, frame.sevm, _, frame.out, afterPush⟩
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ [] :=
        by
          rw [currentEq]
          exact .cont pushStep afterPush
      have jumpiEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨loc, frame.sevm, _, frame.out, afterJump⟩
          ⟨cursor.pc + 3, frame.sevm, _, frame.out, afterPush⟩ [] :=
        by
          rw [afterPushEq]
          exact .cont jumpiStep afterJump
      have jumpdestEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨loc + 1, frame.sevm, arm.pre, frame.out, arm.current⟩
          ⟨loc, frame.sevm, _, frame.out, afterJump⟩ [] :=
        by
          rw [afterJumpEq]
          exact .cont jumpdestStep arm.current
      have pushNotStore : ¬ Ninst.At frame.sevm.code cursor.pc
          (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.At.eq_of_at storeAt pushAt
        cases impossible
      have jumpiNotStore : ¬ Ninst.At frame.sevm.code (cursor.pc + 3)
          (.reg .sstore) := fun storeAt =>
        Ninst.At.false_of_jinstAt storeAt jumpiAt
      have jumpdestNotStore : ¬ Ninst.At frame.sevm.code loc
          (.reg .sstore) := fun storeAt =>
        Ninst.At.false_of_jinstAt storeAt jumpdestAt
      exact .succ _ nonzero arm pop (.step pushEdge pushNotStore
        (.step jumpiEdge jumpiNotStore
          (.step jumpdestEdge jumpdestNotStore (.refl _))))

/-- Flag-retaining reverse traversal through a compiled branch. -/
theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_branchWithFlag
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {left right : Func} {final : Devm}
    {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.branch left right) final)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    (∃ arm : frame.CompiledCursor dp ca fs sourceTable left final,
      Devm.PopBurnBy [0] (gVerylow + gHigh) cursor.pre arm.pre ∧
      frame.NinstOccurrenceFromCursor arm (.reg .sstore)
        stepPre stepPost slot) ∨
    (∃ (flag : B256), flag ≠ 0 ∧
      ∃ arm : frame.CompiledCursor dp ca fs sourceTable right final,
      Devm.PopBurnBy [flag] (gVerylow + gHigh + gJumpdest)
        cursor.pre arm.pre ∧
      frame.NinstOccurrenceFromCursor arm (.reg .sstore)
        stepPre stepPost slot) := by
  cases cursor.selectBranchWithSourcePrefix with
  | zero arm pop compilerPrefix =>
      exact Or.inl ⟨arm, pop,
        compilerPrefix.trim_balanceSstoreOccurrence occurrence⟩
  | succ flag nonzero arm pop compilerPrefix =>
      exact Or.inr ⟨flag, nonzero, arm, pop,
        compilerPrefix.trim_balanceSstoreOccurrence occurrence⟩

/-- Generic reverse source traversal through a compiled branch: the actual
balance-write occurrence belongs to the one source arm selected by the
original execution, never to the compiler's branch glue. -/
theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_branch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {left right : Func} {final : Devm}
    {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.branch left right) final)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    (∃ arm : frame.CompiledCursor dp ca fs sourceTable left final,
      frame.NinstOccurrenceFromCursor arm (.reg .sstore)
        stepPre stepPost slot) ∨
    (∃ arm : frame.CompiledCursor dp ca fs sourceTable right final,
      frame.NinstOccurrenceFromCursor arm (.reg .sstore)
        stepPre stepPost slot) := by
  rcases cursor.balanceSstoreOccurrence_branchWithFlag occurrence with
    ⟨arm, _pop, inside⟩ |
      ⟨flag, nonzero, arm, _pop, inside⟩
  · exact Or.inl ⟨arm, inside⟩
  · exact Or.inr ⟨arm, inside⟩

/-- Enter a generated internal source call while retaining the exact
PUSH/JUMP/JUMPDEST prefix.  These are compiler boundaries rather than source
instructions, and each is explicitly ruled out as the selected `SSTORE`. -/
private theorem Exec.Frame.CompiledCursor.enterCallWithSourcePrefix
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        Exec.Deriv.ParentNonSstorePrefix dp ca
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
          ⟨bodyCursor.pc, frame.sevm, bodyCursor.pre, frame.out,
            bodyCursor.current⟩ := by
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
      rcases frame.advance_cont cursor.current cursor.parentPrefix
          hstepPush with
        ⟨afterPush, hprefixPush⟩
      rcases frame.advance_cont afterPush hprefixPush hstepJump with
        ⟨afterJump, hprefixJump⟩
      rcases frame.advance_cont afterJump hprefixJump hstepJumpdest with
        ⟨bodyExec, hprefixBody⟩
      have currentEq : cursor.current = .cont hstepPush afterPush :=
        Exec.unique _ _
      have afterPushEq : afterPush = .cont hstepJump afterJump :=
        Exec.unique _ _
      have afterJumpEq : afterJump = .cont hstepJumpdest bodyExec :=
        Exec.unique _ _
      let bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) _ final :=
        ⟨loc + 1, _, bodyExec, cursor.actions, hprefixBody,
          hbody, hsub, hjumpable.2⟩
      have pushEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨cursor.pc + 3, frame.sevm, _, frame.out, afterPush⟩
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ [] :=
        by
          rw [currentEq]
          exact .cont hstepPush afterPush
      have jumpEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨loc, frame.sevm, _, frame.out, afterJump⟩
          ⟨cursor.pc + 3, frame.sevm, _, frame.out, afterPush⟩ [] :=
        by
          rw [afterPushEq]
          exact .cont hstepJump afterJump
      have jumpdestEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨loc + 1, frame.sevm, bodyCursor.pre, frame.out,
            bodyCursor.current⟩
          ⟨loc, frame.sevm, _, frame.out, afterJump⟩ [] :=
        by
          rw [afterJumpEq]
          exact .cont hstepJumpdest bodyCursor.current
      have pushNotStore : ¬ Ninst.At frame.sevm.code cursor.pc
          (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.At.eq_of_at storeAt hpush
        cases impossible
      have jumpNotStore : ¬ Ninst.At frame.sevm.code (cursor.pc + 3)
          (.reg .sstore) := fun storeAt =>
        Ninst.At.false_of_jinstAt storeAt hjump
      have jumpdestNotStore : ¬ Ninst.At frame.sevm.code loc
          (.reg .sstore) := fun storeAt =>
        Ninst.At.false_of_jinstAt storeAt hjumpdest
      exact ⟨_, hget, bodyCursor,
        .step pushEdge pushNotStore
          (.step jumpEdge jumpNotStore
            (.step jumpdestEdge jumpdestNotStore (.refl _)))⟩

/-- Generic reverse source traversal through a compiled internal call.  An
actual balance write in the call suffix belongs to the selected table body,
not to the call's compiler-generated transfer of control. -/
theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_call
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        frame.NinstOccurrenceFromCursor bodyCursor (.reg .sstore)
          stepPre stepPost slot := by
  rcases cursor.enterCallWithSourcePrefix hcode with
    ⟨body, hget, bodyCursor, compilerPrefix⟩
  exact ⟨body, hget, bodyCursor,
    compilerPrefix.trim_balanceSstoreOccurrence occurrence⟩

theorem Exec.Frame.NinstOccurrence.run
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {n : Ninst} {stepPre stepPost : Devm} {slot : Xlot}
    (occurrence : frame.NinstOccurrence dp ca n stepPre stepPost slot) :
    Ninst.Run frame.sevm stepPre n stepPost := by
  rcases occurrence with
    ⟨pc, current, continuation, before, selected, hprefix, hat,
      filled, step, prec, edge⟩
  exact ⟨slot, filled, pc, step⟩

/-- A non-SSTORE source head cannot be the selected SSTORE occurrence, so the
same proof-indexed occurrence is retained by the exact tail cursor.  The
executed head occurrence is returned as well, allowing callers to transport
stack/state invariants into that tail. -/
theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_next_ne
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {source : Ninst} {tail : Func} {final : Devm}
    {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.next source tail) final)
    (notStore : source ≠ .reg .sstore)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    ∃ (tailCursor : frame.CompiledCursor dp ca fs sourceTable tail final)
        (sourceSlot : Xlot),
      frame.NinstOccurrence dp ca source cursor.pre tailCursor.pre
        sourceSlot ∧
      frame.NinstOccurrenceFromCursor tailCursor (.reg .sstore)
        stepPre stepPost slot := by
  rcases cursor.ninstOccurrenceFromCursor_head_or_tail occurrence with
    ⟨sourceEq, _preEq⟩ |
      ⟨tailCursor, sourceSlot, sourceOccurrence, remaining⟩
  · exact (notStore sourceEq.symm).elim
  · exact ⟨tailCursor, sourceSlot, sourceOccurrence, remaining⟩

/-- Dynamically skip a source line containing no `SSTORE`, returning both its
actual `Line.Run` and the retained occurrence in the exact suffix cursor. -/
theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_after_line
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {line : Line} {tail : Func} {final : Devm}
    {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (line +++ tail) final)
    (noStore : ∀ n ∈ line, n ≠ .reg .sstore)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    ∃ tailCursor : frame.CompiledCursor dp ca fs sourceTable tail final,
      Line.Run frame.sevm cursor.pre line tailCursor.pre ∧
      frame.NinstOccurrenceFromCursor tailCursor (.reg .sstore)
        stepPre stepPost slot := by
  induction line with
  | nil => exact ⟨cursor, .nil, occurrence⟩
  | cons source line ih =>
      change frame.CompiledCursor dp ca fs sourceTable
        (.next source (line +++ tail)) final at cursor
      have sourceNotStore : source ≠ .reg .sstore :=
        noStore source (by simp)
      rcases cursor.balanceSstoreOccurrence_next_ne sourceNotStore
          occurrence with
        ⟨nextCursor, sourceSlot, sourceOccurrence, remaining⟩
      rcases ih nextCursor (fun n hn => noStore n (by simp [hn]))
          remaining with
        ⟨tailCursor, tailRun, retained⟩
      exact ⟨tailCursor, .cons sourceOccurrence.run tailRun, retained⟩

/-- Transport a proof-indexed cursor and retained occurrence across an exact
source equality.  Keeping this dependent cast explicit avoids erasing the
cursor proof or its immediate pre-state when a source fragment is reassociated
around a selected SSTORE. -/
theorem Exec.Frame.CompiledCursor.castSourceWithOccurrence
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {source target : Func} {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable source final)
    (sourceEq : source = target)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    ∃ targetCursor : frame.CompiledCursor dp ca fs sourceTable target final,
      targetCursor.pre = cursor.pre ∧
      frame.NinstOccurrenceFromCursor targetCursor (.reg .sstore)
        stepPre stepPost slot := by
  subst target
  exact ⟨cursor, rfl, occurrence⟩

/-- Constructive source-level provenance for an executed balance `SSTORE`.
Unlike a byte/PC membership predicate, the call constructor records the exact
table lookup and branch constructors record the source arm actually entered. -/
inductive Func.BalanceSstoreSourcePath (fs : List Func) : Func → Prop
  | head (tail : Func) :
      BalanceSstoreSourcePath fs (.next (.reg .sstore) tail)
  | next {source : Ninst} {tail : Func}
      (rest : BalanceSstoreSourcePath fs tail) :
      BalanceSstoreSourcePath fs (.next source tail)
  | branchLeft {left right : Func}
      (selected : BalanceSstoreSourcePath fs left) :
      BalanceSstoreSourcePath fs (.branch left right)
  | branchRight {left right : Func}
      (selected : BalanceSstoreSourcePath fs right) :
      BalanceSstoreSourcePath fs (.branch left right)
  | call {k : Nat} {body : Func}
      (selected : fs[k]? = some body)
      (inside : BalanceSstoreSourcePath fs body) :
      BalanceSstoreSourcePath fs (.call k)

private theorem Ninst.At.false_of_linstAt
    {code : ByteArray} {pc : Nat} {n : Ninst} {i : Linst}
    (nextAt : Ninst.At code pc n) (lastAt : Linst.At code pc i) : False := by
  unfold Ninst.At at nextAt
  unfold Linst.At at lastAt
  rw [nextAt] at lastAt
  cases lastAt

private theorem Exec.Deriv.ParentStepActions.false_of_halt
    {dp : DeployParams} {ca : Adr}
    {root next : Exec.Deriv} {actions : List FlowAction}
    {haltOut : Execution}
    (edge : Exec.Deriv.ParentStepActions dp ca next root actions)
    (halt : Evm.step ⟨root.pc, root.sevm, root.devm⟩ = .halt haltOut) :
    False := by
  cases edge with
  | cont sourceStep next => cases halt.symm.trans sourceStep
  | doneOk sourceStep henter hresume next =>
      cases halt.symm.trans sourceStep
  | runOk sourceStep henter child hresume next =>
      cases halt.symm.trans sourceStep

private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_last
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {i : Linst} {final : Devm}
    {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable (.last i) final)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) : False := by
  cases hrun : cursor.run with
  | last terminalRun =>
      rcases occurrence with
        ⟨pc, current, continuation, crossed, selected, hpath, storeAt,
          filled, stepRun, prec, edge⟩
      have lastAt : Linst.At frame.sevm.code cursor.pc i :=
        Linst.at_of_slice cursor.codeSlice
      have outEq : frame.out = .ok final :=
        (cursor.current.last_inv lastAt).trans terminalRun
      have terminalStep : Evm.step
          ⟨cursor.pc, frame.sevm, cursor.pre⟩ = .halt frame.out := by
        rw [Evm.step_last lastAt, terminalRun, ← outEq]
      cases hpath with
      | refl => exact Ninst.At.false_of_linstAt storeAt lastAt
      | step head rest =>
          exact head.false_of_halt terminalStep

private def ninstSstoreFree : Ninst → Bool
  | .reg .sstore => false
  | _ => true

private theorem ninst_ne_sstore_of_free {source : Ninst}
    (free : ninstSstoreFree source = true) :
    source ≠ .reg .sstore := by
  cases source with
  | reg operation =>
      cases operation <;> simp [ninstSstoreFree] at free ⊢
  | exec operation => simp
  | push bytes size => simp

/-- Executable finite certificate that a source body and every table body it
can call within `fuel` contain no `SSTORE`.  A zero fuel is deliberately
false, so a successful certificate can never hide a recursive call cycle. -/
def Func.sstoreFreeWithin : Nat → List Func → Func → Bool
  | 0, _, _ => false
  | fuel + 1, fs, .branch left right =>
      sstoreFreeWithin fuel fs left && sstoreFreeWithin fuel fs right
  | _fuel + 1, _, .last _ => true
  | fuel + 1, fs, .next source tail =>
      ninstSstoreFree source && sstoreFreeWithin fuel fs tail
  | fuel + 1, fs, .call k =>
      match fs[k]? with
      | none => false
      | some body => sstoreFreeWithin fuel fs body

/-- A call-free source certificate is independent of the installed function
table.  This lets fixed local error bodies be computed against `[]` without
reducing the parameterized WETH program. -/
private theorem Func.sstoreFreeWithin_eq_of_noCalls
    {fuel : Nat} {body : Func} (noCalls : body.NoCalls)
    (left right : List Func) :
    Func.sstoreFreeWithin fuel left body =
      Func.sstoreFreeWithin fuel right body := by
  induction fuel generalizing body with
  | zero => rfl
  | succ fuel ih =>
      cases body with
      | branch first second =>
          simp only [Func.NoCalls] at noCalls
          simp only [Func.sstoreFreeWithin]
          rw [ih noCalls.1, ih noCalls.2]
      | last terminal => rfl
      | next source tail =>
          simp only [Func.NoCalls] at noCalls
          simp only [Func.sstoreFreeWithin]
          rw [ih noCalls]
      | call k => simp [Func.NoCalls] at noCalls

/-- Soundness of the executable no-SSTORE certificate against an arbitrary
actual occurrence.  The proof still follows the executed cursor branch/call;
the Boolean is only the finite source certificate used to close that path. -/
theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_of_free
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {body : Func} {final : Devm}
    {stepPre stepPost : Devm} {slot : Xlot} {fuel : Nat}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) body final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (free : Func.sstoreFreeWithin fuel (f₀ :: aux) body = true)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) : False := by
  induction fuel generalizing body with
  | zero => simp [Func.sstoreFreeWithin] at free
  | succ fuel ih =>
      cases body with
      | branch left right =>
          simp [Func.sstoreFreeWithin] at free
          rcases cursor.balanceSstoreOccurrence_branch occurrence with
            ⟨leftCursor, inside⟩ | ⟨rightCursor, inside⟩
          · exact ih leftCursor free.1 inside
          · exact ih rightCursor free.2 inside
      | last i =>
          exact cursor.no_balanceSstoreOccurrence_last occurrence
      | next source tail =>
          simp [Func.sstoreFreeWithin] at free
          have notStore := ninst_ne_sstore_of_free free.1
          rcases cursor.balanceSstoreOccurrence_next_ne notStore occurrence with
            ⟨tailCursor, sourceSlot, sourceOccurrence, inside⟩
          exact ih tailCursor free.2 inside
      | call k =>
          cases hlookup : (f₀ :: aux)[k]? with
          | none => simp [Func.sstoreFreeWithin, hlookup] at free
          | some called =>
            simp [Func.sstoreFreeWithin, hlookup] at free
            rcases cursor.balanceSstoreOccurrence_call hcode occurrence with
              ⟨actualBody, actualLookup, bodyCursor, inside⟩
            have bodyEq : actualBody = called := by
              exact Option.some.inj (actualLookup.symm.trans hlookup)
            subst actualBody
            exact ih bodyCursor free inside

/-- Executable local certificate saying that every possible balance write in a
source suffix is routed through one distinguished internal call.  Other calls
must lead to locally SSTORE-free bodies. -/
def Func.balanceSstoreRoutedToCallWithin :
    Nat → List Func → Nat → Func → Bool
  | 0, _, _, _ => false
  | fuel + 1, fs, target, .branch left right =>
      balanceSstoreRoutedToCallWithin fuel fs target left &&
        balanceSstoreRoutedToCallWithin fuel fs target right
  | _fuel + 1, _, _, .last _ => true
  | fuel + 1, fs, target, .next source tail =>
      ninstSstoreFree source &&
        balanceSstoreRoutedToCallWithin fuel fs target tail
  | fuel + 1, fs, target, .call k =>
      if k = target then true
      else
        match fs[k]? with
        | none => false
        | some body => Func.sstoreFreeWithin fuel fs body

/-- Soundness of the distinguished-call routing certificate against the
original proof-indexed execution cursor. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_routedToCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {body : Func} {target fuel : Nat}
    {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) body final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (routed : Func.balanceSstoreRoutedToCallWithin fuel
      (f₀ :: aux) target body = true)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    ∃ targetBody, (f₀ :: aux)[target]? = some targetBody ∧
      ∃ targetCursor : frame.CompiledCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) targetBody final,
        frame.NinstOccurrenceFromCursor targetCursor (.reg .sstore)
          stepPre stepPost slot := by
  induction fuel generalizing body with
  | zero => simp [Func.balanceSstoreRoutedToCallWithin] at routed
  | succ fuel ih =>
      cases body with
      | branch left right =>
          simp [Func.balanceSstoreRoutedToCallWithin] at routed
          rcases cursor.balanceSstoreOccurrence_branch occurrence with
            ⟨leftCursor, inside⟩ | ⟨rightCursor, inside⟩
          · exact ih leftCursor routed.1 inside
          · exact ih rightCursor routed.2 inside
      | last terminal =>
          exact (cursor.no_balanceSstoreOccurrence_last occurrence).elim
      | next source tail =>
          simp [Func.balanceSstoreRoutedToCallWithin] at routed
          rcases cursor.balanceSstoreOccurrence_next_ne
              (ninst_ne_sstore_of_free routed.1) occurrence with
            ⟨tailCursor, _sourceSlot, _sourceOccurrence, insideTail⟩
          exact ih tailCursor routed.2 insideTail
      | call k =>
          by_cases selected : k = target
          · subst k
            exact cursor.balanceSstoreOccurrence_call hcode occurrence
          · simp [Func.balanceSstoreRoutedToCallWithin, selected] at routed
            cases lookup : (f₀ :: aux)[k]? with
            | none => simp [lookup] at routed
            | some called =>
                simp [lookup] at routed
                rcases cursor.balanceSstoreOccurrence_call hcode occurrence with
                  ⟨actualBody, actualLookup, bodyCursor, insideBody⟩
                have bodyEq : actualBody = called :=
                  Option.some.inj (actualLookup.symm.trans lookup)
                subst actualBody
                exact (bodyCursor.no_balanceSstoreOccurrence_of_free
                  hcode routed insideBody).elim

/-- Main-entry cursor with the hidden leading `JUMPDEST` retained as an
explicit non-SSTORE prefix. -/
private theorem Exec.Frame.compiledMainCursorWithSourcePrefix
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca) :
    ∃ cursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (weth10 dp).main frame.post,
      Exec.Deriv.ParentNonSstorePrefix dp ca
        ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
        ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩ := by
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
      rcases subcode_of_get?_eq_some hcode hget with
        ⟨jumpdestAt, sourceSlice⟩
      have sourceBoundary : noPushBefore e.code 1 32 = true :=
        (Prog.jumpable_of_get?_table hcode hget).2
      rcases jumpdest_at_exact run jumpdestAt with
        ⟨actualMid, continuation, hburn, hgas, _prec⟩
      have midEq : actualMid = compiledMid :=
        Devm.eq_of_burnBy
          (Devm.BurnBy.of_burn hburn hgas)
          hcompiledBurn
      subst compiledMid
      have entryStep : Evm.step ⟨0, e, pre⟩ = .cont 1 actualMid :=
        Evm.jumpdest_cont jumpdestAt
          (Devm.BurnBy.of_burn hburn hgas)
      have runEq : run = .cont entryStep continuation := Exec.unique _ _
      have entryEdge : Exec.Deriv.ParentStepActions dp ca
          ⟨1, e, actualMid, .ok post, continuation⟩
          ⟨0, e, pre, .ok post, run⟩ [] := by
        rw [runEq]
        exact .cont entryStep continuation
      have entryPrefix : Exec.Deriv.ParentPrefixActions dp ca
          ⟨0, e, pre, .ok post, run⟩
          ⟨1, e, actualMid, .ok post, continuation⟩ [] :=
        .step entryEdge (.refl _)
      let cursor : Exec.Frame.CompiledCursor dp ca
          ⟨0, e, pre, .ok post, run, committed⟩
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (weth10 dp).main post :=
        ⟨1, actualMid, continuation, [], entryPrefix, hmain,
          sourceSlice, sourceBoundary⟩
      have notStore : ¬ Ninst.At e.code 0 (.reg .sstore) :=
        fun storeAt => Ninst.At.false_of_jinstAt storeAt jumpdestAt
      exact ⟨cursor,
        .step entryEdge notStore (.refl _)⟩

theorem Exec.Frame.BalanceSstoreOccurrence.fromMainCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    ∃ mainCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (weth10 dp).main frame.post,
      frame.NinstOccurrenceFromCursor mainCursor (.reg .sstore)
        stepPre stepPost slot := by
  rcases frame.compiledMainCursorWithSourcePrefix context with
    ⟨mainCursor, entryPrefix⟩
  have fromRoot : frame.NinstOccurrenceFromDeriv dp ca
      ⟨frame.pc, frame.sevm, frame.pre, frame.out, frame.run⟩
      (.reg .sstore) stepPre stepPost slot := occurrence.1
  exact ⟨mainCursor,
    entryPrefix.trim_balanceSstoreOccurrence fromRoot⟩

/-- The first source branch is selected from the actual calldata-size flag,
and the arbitrary occurrence is retained in exactly the dispatch or receive
arm chosen by that flag. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_main
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (weth10 dp).main frame.post)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    (∃ dispatchCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)) frame.post,
      frame.sevm.data.length.toB256 ≠ 0 ∧
      frame.NinstOccurrenceFromCursor dispatchCursor (.reg .sstore)
        stepPre stepPost slot) ∨
    (∃ receiveCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        receiveEther frame.post,
      frame.sevm.data.length.toB256 = 0 ∧
      frame.NinstOccurrenceFromCursor receiveCursor (.reg .sstore)
        stepPre stepPost slot) := by
  unfold weth10 weth10Main at cursor
  change frame.CompiledCursor dp ca
    (weth10Main dp :: weth10Aux)
    (table 0 (weth10Main dp :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (.branch (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))
        receiveEther)) frame.post at cursor
  rcases cursor.balanceSstoreOccurrence_after_line
      (by simp) occurrence with
    ⟨branchCursor, entryRun, atBranch⟩
  have flagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        branchCursor.pre.stack := by
    rcases Line.of_run_cons entryRun with
      ⟨afterSize, sizeStep, restSize⟩
    rcases Line.of_run_cons restSize with
      ⟨afterZero, zeroStep, emptyLine⟩
    cases emptyLine
    have sizePrefix : [frame.sevm.data.length.toB256] <<+
        afterSize.stack :=
      prefix_of_push (of_run_calldatasize sizeStep) nil_pref
    exact prefix_of_iszero zeroStep sizePrefix
  rcases branchCursor.balanceSstoreOccurrence_branchWithFlag atBranch with
    ⟨dispatchCursor, pop, inside⟩ |
      ⟨flag, nonzero, receiveCursor, pop, inside⟩
  · have zeroPrefix : [(0 : B256)] <<+ branchCursor.pre.stack :=
      pref_of_split pop.stack
    have flagEq : (frame.sevm.data.length.toB256 =? 0) = 0 :=
      pref_head_unique flagPrefix zeroPrefix
    have nonempty : frame.sevm.data.length.toB256 ≠ 0 := by
      intro empty
      rw [empty] at flagEq
      simp [B256.eqCheck] at flagEq
      exact (by decide : (1 : B256) ≠ 0) flagEq
    exact Or.inl ⟨dispatchCursor, nonempty, inside⟩
  · have selectedPrefix : [flag] <<+ branchCursor.pre.stack :=
      pref_of_split pop.stack
    have flagEq : (frame.sevm.data.length.toB256 =? 0) = flag :=
      pref_head_unique flagPrefix selectedPrefix
    have empty : frame.sevm.data.length.toB256 = 0 := by
      by_contra nonempty
      have checkZero : (frame.sevm.data.length.toB256 =? 0) = 0 := by
        simp [B256.eqCheck, nonempty]
      apply nonzero
      rw [← flagEq]
      exact checkZero
    exact Or.inr ⟨receiveCursor, empty, inside⟩

/-- Reverse traversal of generated dispatch syntax.  The exact selector word
is threaded on the live stack; compiler branch flags decide the recursive
tree arm, and a matched leaf proves both selector equality and retention of
the arbitrary occurrence in that leaf's body. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_dispatchWith :
    ∀ {tree : DispatchTree} {sig : B256} {stack : Stack}
      {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
      {f₀ : Func} {aux : List Func} {k fuel : Nat}
      {fallback : Func} {final stepPre stepPost : Devm} {slot : Xlot},
      (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
        (table 0 (f₀ :: aux)) (dispatchWith k tree) final) →
      some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩ →
      (f₀ :: aux)[k]? = some fallback →
      Func.sstoreFreeWithin fuel (f₀ :: aux) fallback = true →
      sig :: stack <<+ cursor.pre.stack →
      frame.NinstOccurrenceFromCursor cursor (.reg .sstore)
        stepPre stepPost slot →
      ∃ body : Func, (sig, body) ∈ tree ∧
        ∃ bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
            (table 0 (f₀ :: aux)) body final,
          stack <<+ bodyCursor.pre.stack ∧
          frame.NinstOccurrenceFromCursor bodyCursor (.reg .sstore)
            stepPre stepPost slot := by
  intro tree
  induction tree with
  | leaf word body =>
      intro sig stack dp ca frame f₀ aux k fuel fallback final
        stepPre stepPost slot cursor hcode fallbackLookup fallbackFree
        selectorPrefix occurrence
      rcases cursor.balanceSstoreOccurrence_after_line
          (line := [Ninst.pushB256 word, Ninst.eq])
          (tail := .branch (.call k) body)
          (by simp [Ninst.pushB256]) occurrence with
        ⟨branchCursor, compareRun, atBranch⟩
      have flagPrefix : (word =? sig) :: stack <<+
          branchCursor.pre.stack := by
        rcases Line.of_run_cons compareRun with
          ⟨afterPush, pushStep, restPush⟩
        rcases Line.of_run_cons restPush with
          ⟨afterEq, eqStep, emptyLine⟩
        cases emptyLine
        have pushed : word :: sig :: stack <<+ afterPush.stack := by
          simpa using prefix_of_push
            (of_run_pushB256 pushStep) selectorPrefix
        exact prefix_of_eq eqStep pushed
      rcases branchCursor.balanceSstoreOccurrence_branchWithFlag atBranch with
        ⟨fallbackCursor, pop, insideFallback⟩ |
          ⟨flag, nonzero, bodyCursor, pop, insideBody⟩
      · rcases fallbackCursor.balanceSstoreOccurrence_call hcode
            insideFallback with
          ⟨actualFallback, actualLookup, fallbackBodyCursor,
            insideFallbackBody⟩
        have fallbackEq : actualFallback = fallback := by
          exact Option.some.inj (actualLookup.symm.trans fallbackLookup)
        subst actualFallback
        exact (fallbackBodyCursor.no_balanceSstoreOccurrence_of_free
          hcode fallbackFree insideFallbackBody).elim
      · have bodyStack : stack <<+ bodyCursor.pre.stack :=
          prefix_of_pop
            ⟨flag, Devm.PopBurn.of_popBurnBy pop⟩ flagPrefix
        have selectedPrefix : [flag] <<+ branchCursor.pre.stack :=
          pref_of_split pop.stack
        have flagEq : (word =? sig) = flag :=
          pref_head_unique flagPrefix selectedPrefix
        have wordEq : word = sig := by
          by_contra different
          have checkZero : (word =? sig) = 0 := by
            simp [B256.eqCheck, different]
          apply nonzero
          rw [← flagEq]
          exact checkZero
        subst sig
        exact ⟨body, rfl, bodyCursor, bodyStack, insideBody⟩
  | fork left right ihLeft ihRight =>
      intro sig stack dp ca frame f₀ aux k fuel fallback final
        stepPre stepPost slot cursor hcode fallbackLookup fallbackFree
        selectorPrefix occurrence
      rcases cursor.balanceSstoreOccurrence_after_line
          (line := [Ninst.dup 0, Ninst.pushB256 (leftmostFsig right),
            Ninst.gt])
          (tail := .branch (dispatchWith k right) (dispatchWith k left))
          (by simp [Ninst.pushB256]) occurrence with
        ⟨branchCursor, compareRun, atBranch⟩
      have flagPrefix :
          (leftmostFsig right >? sig) :: sig :: stack <<+
            branchCursor.pre.stack := by
        rcases Line.of_run_cons compareRun with
          ⟨afterDup, dupStep, restDup⟩
        rcases Line.of_run_cons restDup with
          ⟨afterPush, pushStep, restPush⟩
        rcases Line.of_run_cons restPush with
          ⟨afterGt, gtStep, emptyLine⟩
        cases emptyLine
        have duplicated : sig :: sig :: stack <<+ afterDup.stack :=
          prefix_of_dup_val dupStep (by show_nth) selectorPrefix
        have pushed : leftmostFsig right :: sig :: sig :: stack <<+
            afterPush.stack := by
          simpa using prefix_of_push
            (of_run_pushB256 pushStep) duplicated
        exact prefix_of_gt gtStep pushed
      rcases branchCursor.balanceSstoreOccurrence_branchWithFlag atBranch with
        ⟨rightCursor, pop, insideRight⟩ |
          ⟨flag, nonzero, leftCursor, pop, insideLeft⟩
      · have rightStack : sig :: stack <<+ rightCursor.pre.stack :=
          prefix_of_pop
            ⟨0, Devm.PopBurn.of_popBurnBy pop⟩ flagPrefix
        rcases ihRight rightCursor hcode fallbackLookup fallbackFree
            rightStack insideRight with
          ⟨body, member, bodyCursor, bodyStack, insideBody⟩
        exact ⟨body, Or.inr member, bodyCursor, bodyStack, insideBody⟩
      · have leftStack : sig :: stack <<+ leftCursor.pre.stack :=
          prefix_of_pop
            ⟨flag, Devm.PopBurn.of_popBurnBy pop⟩ flagPrefix
        rcases ihLeft leftCursor hcode fallbackLookup fallbackFree
            leftStack insideLeft with
          ⟨body, member, bodyCursor, bodyStack, insideBody⟩
        exact ⟨body, Or.inl member, bodyCursor, bodyStack, insideBody⟩

/-- A retained non-receive occurrence reaches the exact source body selected
by the live calldata selector.  Unlike the ordinary forward dispatch theorem,
the returned cursor retains the arbitrary occurrence selected by the caller. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_selectorBody
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (weth10 dp).main frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (context : frame.AuthenticContext dp ca)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ body : Func,
      (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp ∧
      ∃ bodyCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) body frame.post,
        [] <<+ bodyCursor.pre.stack ∧
        frame.NinstOccurrenceFromCursor bodyCursor (.reg .sstore)
          stepPre stepPost slot := by
  rcases cursor.balanceSstoreOccurrence_main fromCursor with
    ⟨dispatchPrefixCursor, _selectedNonempty, insideDispatch⟩ |
      ⟨_receiveCursor, selectedEmpty, _insideReceive⟩
  · rcases dispatchPrefixCursor.balanceSstoreOccurrence_after_line
        (line := fsig)
        (tail := dispatchWith fallbackSlot (weth10Tree dp))
        (by simp [fsig, cdl, shiftRight, Ninst.pushB256])
        insideDispatch with
      ⟨dispatchCursor, fsigRun, insideTree⟩
    have selectorPrefix : Sevm.selector frame.sevm :: [] <<+
        dispatchCursor.pre.stack :=
      prefix_of_fsig nil_pref fsigRun
    have fallbackLookup :
        (((weth10 dp).main :: weth10Aux)[fallbackSlot]?) =
          some Func.rev := by
      simp [fallbackSlot, weth10, weth10Aux]
    have fallbackFree : Func.sstoreFreeWithin 4
        ((weth10 dp).main :: weth10Aux) Func.rev = true := by
      rfl
    rcases dispatchCursor.balanceSstoreOccurrence_dispatchWith
        context.invocation.2.2.2 fallbackLookup fallbackFree
        selectorPrefix insideTree with
      ⟨body, treeMember, bodyCursor, bodyStack, insideBody⟩
    have listMember :
        (Sevm.selector frame.sevm, body) ∈ weth10Funcs dp :=
      DispatchTree.mem_of_mem_ofSorted
        (by simp [weth10Funcs]) (by simpa [weth10Tree] using treeMember)
    exact ⟨body, listMember, bodyCursor, bodyStack, insideBody⟩
  · exact (nonempty selectedEmpty).elim

/-- Strip the generated nonpayable guard while retaining an arbitrary
balance-region occurrence.  The rejecting arm is source-certified SSTORE-free
locally, so every retained write lies in the guarded body cursor. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_nonpayable
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func}
    {body : Func} {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (nonpayable body) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    ∃ bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
        (table 0 (f₀ :: aux)) body final,
      frame.NinstOccurrenceFromCursor bodyCursor (.reg .sstore)
        stepPre stepPost slot := by
  rcases cursor.balanceSstoreOccurrence_after_line
      (line := [Ninst.callvalue, Ninst.iszero])
      (tail := .branch Func.rev body)
      (by simp) fromCursor with
    ⟨branchCursor, _guardRun, atBranch⟩
  rcases branchCursor.balanceSstoreOccurrence_branch atBranch with
    ⟨revertCursor, insideRevert⟩ | ⟨bodyCursor, insideBody⟩
  · have revertFree : Func.sstoreFreeWithin 4
        (f₀ :: aux) Func.rev = true := by
      rfl
    exact (revertCursor.no_balanceSstoreOccurrence_of_free
      hcode revertFree insideRevert).elim
  · exact ⟨bodyCursor, insideBody⟩

private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_nonpayable_of_free
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {body : Func}
    {final stepPre stepPost : Devm} {slot : Xlot} {fuel : Nat}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (nonpayable body) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (free : Func.sstoreFreeWithin fuel (f₀ :: aux) body = true)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) : False := by
  rcases cursor.balanceSstoreOccurrence_nonpayable hcode occurrence with
    ⟨bodyCursor, insideBody⟩
  exact bodyCursor.no_balanceSstoreOccurrence_of_free
    hcode free insideBody

private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_nonpayable_of_noCalls
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {body : Func}
    {final stepPre stepPost : Devm} {slot : Xlot} {fuel : Nat}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (nonpayable body) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (noCalls : body.NoCalls)
    (nilFree : Func.sstoreFreeWithin fuel [] body = true)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) : False := by
  have free : Func.sstoreFreeWithin fuel (f₀ :: aux) body = true := by
    calc
      Func.sstoreFreeWithin fuel (f₀ :: aux) body =
          Func.sstoreFreeWithin fuel [] body :=
        Func.sstoreFreeWithin_eq_of_noCalls noCalls _ _
      _ = true := nilFree
  exact cursor.no_balanceSstoreOccurrence_nonpayable_of_free
    hcode free occurrence

private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_of_noCalls
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {body : Func}
    {final stepPre stepPost : Devm} {slot : Xlot} {fuel : Nat}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) body final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (noCalls : body.NoCalls)
    (nilFree : Func.sstoreFreeWithin fuel [] body = true)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) : False := by
  have free : Func.sstoreFreeWithin fuel (f₀ :: aux) body = true := by
    calc
      Func.sstoreFreeWithin fuel (f₀ :: aux) body =
          Func.sstoreFreeWithin fuel [] body :=
        Func.sstoreFreeWithin_eq_of_noCalls noCalls _ _
      _ = true := nilFree
  exact cursor.no_balanceSstoreOccurrence_of_free hcode free occurrence

/-- Exhaustive structural view of the exact 27-entry WETH10 dispatcher.
Keeping the selected selector and body as indices lets later occurrence proofs
case-split without losing their dependent body cursor. -/
inductive Weth10BodyCase (dp : DeployParams) : B256 → Func → Prop
  | nameCase : Weth10BodyCase dp
      (selector "name" []) (nonpayable name)
  | approveCase : Weth10BodyCase dp
      (selector "approve" [.address, .uint256]) (nonpayable approve)
  | totalSupplyCase : Weth10BodyCase dp
      (selector "totalSupply" []) (nonpayable totalSupply)
  | withdrawToCase : Weth10BodyCase dp
      (selector "withdrawTo" [.address, .uint256]) (nonpayable withdrawTo)
  | transferFromCase : Weth10BodyCase dp
      (selector "transferFrom" [.address, .address, .uint256])
      (nonpayable transferFrom)
  | withdrawCase : Weth10BodyCase dp
      (selector "withdraw" [.uint256]) (nonpayable withdraw)
  | permitTypehashCase : Weth10BodyCase dp
      (selector "PERMIT_TYPEHASH" []) (nonpayable permitTypehash)
  | decimalsCase : Weth10BodyCase dp
      (selector "decimals" []) (nonpayable decimals)
  | domainSeparatorCase : Weth10BodyCase dp
      (selector "DOMAIN_SEPARATOR" []) (nonpayable (domainSeparator dp))
  | transferAndCallCase : Weth10BodyCase dp
      (selector "transferAndCall" [.address, .uint256, .dynBytes])
      (nonpayable transferAndCall)
  | flashLoanCase : Weth10BodyCase dp
      (selector "flashLoan" [.address, .address, .uint256, .dynBytes])
      (nonpayable flashLoan)
  | depositToAndCallCase : Weth10BodyCase dp
      (selector "depositToAndCall" [.address, .dynBytes]) depositToAndCall
  | maxFlashLoanCase : Weth10BodyCase dp
      (selector "maxFlashLoan" [.address]) (nonpayable maxFlashLoan)
  | balanceOfCase : Weth10BodyCase dp
      (selector "balanceOf" [.address]) (nonpayable balanceOfEndpoint)
  | noncesCase : Weth10BodyCase dp
      (selector "nonces" [.address]) (nonpayable nonces)
  | callbackSuccessCase : Weth10BodyCase dp
      (selector "CALLBACK_SUCCESS" []) (nonpayable callbackSuccess)
  | flashMintedCase : Weth10BodyCase dp
      (selector "flashMinted" []) (nonpayable flashMinted)
  | withdrawFromCase : Weth10BodyCase dp
      (selector "withdrawFrom" [.address, .address, .uint256])
      (nonpayable withdrawFrom)
  | symbolCase : Weth10BodyCase dp
      (selector "symbol" []) (nonpayable symbol)
  | transferCase : Weth10BodyCase dp
      (selector "transfer" [.address, .uint256]) (nonpayable transfer)
  | depositToCase : Weth10BodyCase dp
      (selector "depositTo" [.address]) depositTo
  | approveAndCallCase : Weth10BodyCase dp
      (selector "approveAndCall" [.address, .uint256, .dynBytes])
      (nonpayable approveAndCall)
  | deploymentChainIdCase : Weth10BodyCase dp
      (selector "deploymentChainId" [])
      (nonpayable (deploymentChainId dp))
  | depositCase : Weth10BodyCase dp
      (selector "deposit" []) deposit
  | permitCase : Weth10BodyCase dp
      (selector "permit"
        [.address, .address, .uint256, .uint256, .uint 8, .bytes 32,
          .bytes 32])
      (nonpayable (permit dp))
  | flashFeeCase : Weth10BodyCase dp
      (selector "flashFee" [.address, .uint256]) (nonpayable flashFee)
  | allowanceCase : Weth10BodyCase dp
      (selector "allowance" [.address, .address]) (nonpayable allowance)

private theorem Weth10BodyCase.of_mem
    {dp : DeployParams} {sig : B256} {body : Func}
    (member : (sig, body) ∈ weth10Funcs dp) :
    Weth10BodyCase dp sig body := by
  simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · cases h; exact .nameCase
  · cases h; exact .approveCase
  · cases h; exact .totalSupplyCase
  · cases h; exact .withdrawToCase
  · cases h; exact .transferFromCase
  · cases h; exact .withdrawCase
  · cases h; exact .permitTypehashCase
  · cases h; exact .decimalsCase
  · cases h; exact .domainSeparatorCase
  · cases h; exact .transferAndCallCase
  · cases h; exact .flashLoanCase
  · cases h; exact .depositToAndCallCase
  · cases h; exact .maxFlashLoanCase
  · cases h; exact .balanceOfCase
  · cases h; exact .noncesCase
  · cases h; exact .callbackSuccessCase
  · cases h; exact .flashMintedCase
  · cases h; exact .withdrawFromCase
  · cases h; exact .symbolCase
  · cases h; exact .transferCase
  · cases h; exact .depositToCase
  · cases h; exact .approveAndCallCase
  · cases h; exact .deploymentChainIdCase
  · cases h; exact .depositCase
  · cases h; exact .permitCase
  · cases h; exact .flashFeeCase
  · cases h; exact .allowanceCase

/-- The exact local role of one balance-region stored word.  Transfer and
flash actions have separate debit and credit constructors; for a self
transfer the credit constructor reads the balance from its own immediate
pre-state, after the debit occurrence. -/
inductive BalanceSstoreRole (ca : Adr) (stepPre : Devm) :
    FlowAtom → Adr → B256 → Prop
  | ordinaryMintCredit (rawRecipient : B256) (recipient : Adr)
      (amount : Nat) :
      BalanceSstoreRole ca stepPre
        (.ordinaryMint rawRecipient recipient amount) recipient
        (Stor.rest (Devm.getStor stepPre ca) recipient +
          Nat.toB256 amount)
  | transferDebit (rawSource rawRecipient : B256)
      (source recipient : Adr) (amount : Nat) :
      BalanceSstoreRole ca stepPre
        (.transfer rawSource rawRecipient source recipient amount) source
        (Stor.rest (Devm.getStor stepPre ca) source - Nat.toB256 amount)
  | transferCredit (rawSource rawRecipient : B256)
      (source recipient : Adr) (amount : Nat) :
      BalanceSstoreRole ca stepPre
        (.transfer rawSource rawRecipient source recipient amount) recipient
        (Stor.rest (Devm.getStor stepPre ca) recipient + Nat.toB256 amount)
  | redemptionDebit (rawSource : B256) (source ethRecipient : Adr)
      (amount : Nat) :
      BalanceSstoreRole ca stepPre
        (.redemption rawSource source ethRecipient amount) source
        (Stor.rest (Devm.getStor stepPre ca) source - Nat.toB256 amount)
  | flashCredit (rawReceiver : B256) (receiver : Adr) (amount : Nat) :
      BalanceSstoreRole ca stepPre
        (.flashPair rawReceiver receiver amount) receiver
        (Stor.rest (Devm.getStor stepPre ca) receiver + Nat.toB256 amount)
  | flashRepayment (rawReceiver : B256) (receiver : Adr) (amount : Nat) :
      BalanceSstoreRole ca stepPre
        (.flashPair rawReceiver receiver amount) receiver
        (Stor.rest (Devm.getStor stepPre ca) receiver - Nat.toB256 amount)

/-- Full C1 evidence attached to one executed balance-region write.  The
classification equation selects the same action used by the rich storage,
emitter, and accepted-debit witnesses; `role` ties the concrete stored word
to that action at the occurrence's immediate pre-state. -/
structure Exec.Frame.BalanceSstoreClassification
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame)
    (stepPre stepPost : Devm) (slot : Xlot)
    (key value : B256) (holder : Adr) (action : FlowAction) : Prop where
  occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
    key value holder
  authentic : frame.AuthenticContext dp ca
  classified : frame.flowAction? dp ca = some action
  role : BalanceSstoreRole ca stepPre action.atom holder value
  rich : frame.HasRichLocalStorageEffect dp ca action
  emitter : frame.HasGenuineWethEmitterEffect dp ca action
  acceptedDebit : frame.HasAcceptedDebit dp ca action

/-- Once a source-path proof has identified the role of an occurrence, the
existing compiled-functional theorems attach the exact rich storage, genuine
WETH-emitter, and mechanically accepted debit evidence. -/
theorem Exec.Frame.BalanceSstoreOccurrence.classify_of_role
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr} {action : FlowAction}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = some action)
    (role : BalanceSstoreRole ca stepPre action.atom holder value) :
    frame.BalanceSstoreClassification dp ca stepPre stepPost slot
      key value holder action := by
  exact
    { occurrence
      authentic := context
      classified
      role
      rich := frame.hasRichLocalStorageEffect_of_flowAction?_eq_some
        context classified
      emitter := frame.hasGenuineWethEmitterEffect_of_flowAction?_eq_some
        context classified
      acceptedDebit := frame.hasAcceptedDebit_of_flowAction?_eq_some
        context classified }

/-- Project the atom selected by the executable frame classifier without
discarding the installed invocation guard. -/
theorem Exec.Frame.primaryFlowAtom_eq_some_of_flowAction_eq_some
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = some action) :
    primaryFlowAtom frame.sevm = some action.atom := by
  unfold Exec.Frame.flowAction? at classified
  rw [if_pos context.invocation] at classified
  have mapped := congrArg (Option.map FlowAction.atom) classified
  simpa [Function.comp_def] using mapped

/-- Package an immediate source-site role once the same atom is selected by
the executable primary classifier.  This is the non-circular bridge from the
local occurrence proof to the existing rich/emitter/debit action evidence. -/
theorem Exec.Frame.BalanceSstoreOccurrence.classify_of_primary_role
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr} {atom : FlowAtom}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (primary : primaryFlowAtom frame.sevm = some atom)
    (role : BalanceSstoreRole ca stepPre atom holder value) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  cases classified : frame.flowAction? dp ca with
  | none =>
      unfold Exec.Frame.flowAction? at classified
      rw [if_pos context.invocation, primary] at classified
      simp at classified
  | some action =>
      have selected :=
        frame.primaryFlowAtom_eq_some_of_flowAction_eq_some
          context classified
      have atomEq : action.atom = atom := by
        rw [primary] at selected
        exact Option.some.inj selected.symm
      refine ⟨action,
        occurrence.classify_of_role context classified ?_⟩
      rw [atomEq]
      exact role

/-- A compiled cursor whose next source instruction is `SSTORE` produces an
occurrence in the original retained `Exec`, including when `value` is already
stored at `key`. -/
theorem Exec.Frame.CompiledCursor.exists_balanceSstoreOccurrence
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {table : List (Nat × Func)}
    {tail : Func} {final : Devm}
    {key value : B256} {stack : Stack}
    (cursor : frame.CompiledCursor dp ca fs table
      (.next (.reg .sstore) tail) final)
    (valid : ValidAdr key)
    (stackPrefix : key :: value :: stack <<+ cursor.pre.stack) :
    ∃ (tailCursor : frame.CompiledCursor dp ca fs table tail final)
        (slot : Xlot) (holder : Adr),
      frame.BalanceSstoreOccurrence dp ca cursor.pre tailCursor.pre slot
        key value holder := by
  rcases valid with ⟨holder, holderKey⟩
  rcases cursor.selectNextChildless (by simp [NinstIsChildless]) with
    ⟨tailCursor, slot, _run, occurrence, _actions⟩
  exact ⟨tailCursor, slot, holder, occurrence, ⟨holder, holderKey⟩,
    holderKey.symm, stack, stackPrefix⟩

/-- Skip an actually executed `SSTORE` whose immediate stack key is proved
outside the address-shaped balance region.  This is the reusable boundary for
allowance, nonce, and flash-counter writes; no stored-value inequality is
assumed, so no-op stores are covered as well. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_after_invalidKeyStore
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {tail : Func} {final stepPre stepPost : Devm} {slot : Xlot}
    {key value storeKey storeValue : B256} {holder : Adr} {stack : Stack}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.next (.reg .sstore) tail) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (invalid : ¬ ValidAdr storeKey)
    (storePrefix : storeKey :: storeValue :: stack <<+ cursor.pre.stack) :
    ∃ tailCursor : frame.CompiledCursor dp ca fs sourceTable tail final,
      frame.NinstOccurrenceFromCursor tailCursor (.reg .sstore)
        stepPre stepPost slot := by
  rcases cursor.ninstOccurrenceFromCursor_head_or_tail fromCursor with
    ⟨_sourceEq, preEq⟩ |
      ⟨tailCursor, _sourceSlot, _sourceOccurrence, insideTail⟩
  · subst stepPre
    rcases occurrence.2.2.2 with ⟨occurrenceTail, occurrencePrefix⟩
    have occurrenceKeyPrefix : [key] <<+ cursor.pre.stack :=
      pref_trans (pref_append [key] (value :: occurrenceTail))
        occurrencePrefix
    have expectedKeyPrefix : [storeKey] <<+ cursor.pre.stack :=
      pref_trans (pref_append [storeKey] (storeValue :: stack)) storePrefix
    have keyEq : key = storeKey :=
      pref_head_unique occurrenceKeyPrefix expectedKeyPrefix
    exact (invalid (keyEq ▸ occurrence.2.1)).elim
  · exact ⟨tailCursor, insideTail⟩

private def mintCallerBeforeSstore : Line :=
  [Ninst.caller, Ninst.sload, Ninst.callvalue, Ninst.add, Ninst.caller]

private def mintCallerAfterSstore : Func :=
  Ninst.callvalue ::: mstoreAt 0 +++
  Ninst.caller ::: Ninst.pushB256 0 :::
  Ninst.pushB256 Blanc.transferEvent :::
  logWith 2 0 1 +++ Func.stop

private theorem receiveEther_eq_sstoreSplit :
    receiveEther =
      mintCallerBeforeSstore +++
        (.next (.reg .sstore) mintCallerAfterSstore) := by
  rfl

private def mintToBeforeSstore : Line :=
  addressArg 0 ++ [Ninst.sload, Ninst.callvalue, Ninst.add] ++ addressArg 0

private def mintToAfterSstoreLine : Line :=
  [Ninst.callvalue] ++ mstoreAt 0 ++ addressArg 0 ++
    [Ninst.pushB256 0, Ninst.pushB256 Blanc.transferEvent] ++
    logWith 2 0 1

private def mintToAfterSstore (continuation : Func) : Func :=
  mintToAfterSstoreLine +++ continuation

private theorem prepend_append_writeCompleteness
    (left right : Line) (tail : Func) :
    (left ++ right) +++ tail = left +++ (right +++ tail) := by
  induction left with
  | nil => rfl
  | cons head left ih => simp [prepend, ih]

private theorem mintToPrefix_eq_lineSplit :
    mintToPrefix =
      mintToBeforeSstore ++ [Ninst.sstore] ++ mintToAfterSstoreLine := by
  simp [mintToPrefix, mintToBeforeSstore, mintToAfterSstoreLine,
    List.append_assoc]

private theorem mintToPrefix_append_eq_sstoreSplit (continuation : Func) :
    mintToPrefix +++ continuation =
      mintToBeforeSstore +++
        (.next (.reg .sstore) (mintToAfterSstore continuation)) := by
  rw [mintToPrefix_eq_lineSplit,
    prepend_append_writeCompleteness,
    prepend_append_writeCompleteness]
  rfl

private theorem normalizedAddressArg_eq_toAdr_toB256_writeCompleteness
    (e : Sevm) (k : B256) :
    normalizedAddressArg e k = (Sevm.argWord e k).toAdr.toB256 := by
  have lowMask (x : UInt64) :
      (0x00000000ffffffff : UInt64) &&& x =
        x.toUInt32.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt64.toNat_toUInt32,
      UInt32.toNat_toUInt64]
    rw [Nat.and_comm]
    change x.toNat &&& 2 ^ 32 - 1 = x.toNat % 2 ^ 32
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have andMax (x : UInt64) : UInt64.max &&& x = x := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_and]
    have hmax : UInt64.max.toBitVec = BitVec.allOnes 64 := by
      rfl
    rw [hmax]
    exact BitVec.allOnes_and
  have b128AndMax (x : B128) : B128.max &&& x = x := by
    apply Prod.ext <;> apply andMax
  have hmask : (~~~ addressMask) =
      (⟨⟨0, 0x00000000ffffffff⟩, B128.max⟩ : B256) := by
    decide +kernel +revert
  unfold normalizedAddressArg
  rw [hmask]
  rcases Sevm.argWord e k with ⟨⟨high, middle⟩, low⟩
  simp only [B256.toAdr, Adr.toB256, B256.and_eq_and_prod_and,
    B128.and_eq_and_prod_and, UInt64.zero_and]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact lowMask middle
  · exact b128AndMax low

/-- Reverse classification of the arbitrary retained occurrence in the shared
`receive`/`deposit` mint body.  The immediate pre-stack, rather than an
endpoint storage equation, identifies the stored caller credit. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_mintCaller
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      receiveEther frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    BalanceSstoreRole ca stepPre
      (.ordinaryMint frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.value.toNat) holder value := by
  rcases cursor.castSourceWithOccurrence receiveEther_eq_sstoreSplit
      fromCursor with
    ⟨splitCursor, _splitPre, fromSplit⟩
  rcases splitCursor.balanceSstoreOccurrence_after_line
      (by simp [mintCallerBeforeSstore]) fromSplit with
    ⟨storeCursor, prefixRun, atStore⟩
  rcases storeCursor.ninstOccurrenceFromCursor_head_or_tail atStore with
    ⟨_sourceEq, preEq⟩ |
      ⟨tailCursor, sourceSlot, sourceOccurrence, insideTail⟩
  · subst stepPre
    rcases Line.of_run_cons prefixRun with
      ⟨afterCaller, callerStep, restCaller⟩
    rcases Line.of_run_cons restCaller with
      ⟨afterLoad, loadStep, restLoad⟩
    rcases Line.of_run_cons restLoad with
      ⟨afterValue, valueStep, restValue⟩
    rcases Line.of_run_cons restValue with
      ⟨afterAdd, addStep, restAdd⟩
    rcases Line.of_run_cons restAdd with
      ⟨afterCallerAgain, callerAgainStep, emptyLine⟩
    cases emptyLine
    have callerPrefix : [frame.sevm.caller.toB256] <<+
        afterCaller.stack :=
      prefix_of_push (of_run_caller callerStep) nil_pref
    rcases prefix_of_sload loadStep callerPrefix with
      ⟨callerBalance, balancePrefix, callerBalanceEq⟩
    have valuePrefix : [frame.sevm.value, callerBalance] <<+
        afterValue.stack :=
      prefix_of_push (of_run_callvalue valueStep) balancePrefix
    have sumPrefix : [frame.sevm.value + callerBalance] <<+
        afterAdd.stack :=
      prefix_of_add addStep valuePrefix
    have storePrefix :
        [frame.sevm.caller.toB256, frame.sevm.value + callerBalance] <<+
          storeCursor.pre.stack :=
      prefix_of_push (of_run_caller callerAgainStep) sumPrefix
    have storLoad : Devm.getStor afterCaller = Devm.getStor afterLoad :=
      Ninst.Hinv.inv (f := Devm.getStor) loadStep
    have storValue : Devm.getStor afterLoad = Devm.getStor afterValue :=
      Ninst.Hinv.inv (f := Devm.getStor) valueStep
    have storAdd : Devm.getStor afterValue = Devm.getStor afterAdd :=
      Ninst.Hinv.inv (f := Devm.getStor) addStep
    have storCaller : Devm.getStor afterAdd = Devm.getStor storeCursor.pre :=
      Ninst.Hinv.inv (f := Devm.getStor) callerAgainStep
    have callerBalanceAtStore :
        callerBalance =
          (Devm.getStor storeCursor.pre frame.sevm.currentTarget).get
            frame.sevm.caller.toB256 := by
      rw [callerBalanceEq]
      change
        (Devm.getStor afterCaller frame.sevm.currentTarget).get
            frame.sevm.caller.toB256 = _
      rw [storLoad, storValue, storAdd, storCaller]
    have target : frame.sevm.currentTarget = ca := context.invocation.2.1
    have storedWord :
        frame.sevm.value + callerBalance =
          Stor.rest (Devm.getStor storeCursor.pre ca) frame.sevm.caller +
            Nat.toB256 frame.sevm.value.toNat := by
      rw [Jaune.toB256_toNat, callerBalanceAtStore, target]
      simp only [Stor.rest, Function.comp_apply]
      exact B256.add_comm
    rcases occurrence.2.2.2 with ⟨occurrenceTail, occurrencePrefix⟩
    have occurrencePairPrefix : [key, value] <<+
        storeCursor.pre.stack :=
      pref_trans (pref_append [key, value] occurrenceTail) occurrencePrefix
    have expectedPrefix :
        [frame.sevm.caller.toB256,
          Stor.rest (Devm.getStor storeCursor.pre ca) frame.sevm.caller +
            Nat.toB256 frame.sevm.value.toNat] <<+
          storeCursor.pre.stack := by
      rw [← storedWord]
      exact storePrefix
    have pairEq : [key, value] =
        [frame.sevm.caller.toB256,
          Stor.rest (Devm.getStor storeCursor.pre ca) frame.sevm.caller +
            Nat.toB256 frame.sevm.value.toNat] :=
      List.pref_unique (by simp) occurrencePairPrefix expectedPrefix
    injection pairEq with keyEq valueTailEq
    injection valueTailEq with valueEq
    have holderEq : holder = frame.sevm.caller := by
      apply Adr.toB256_inj
      exact occurrence.2.2.1.symm.trans keyEq
    subst holder
    rw [valueEq]
    exact .ordinaryMintCredit _ _ _
  · have freeTail : Func.sstoreFreeWithin 64
        ((weth10 dp).main :: weth10Aux) mintCallerAfterSstore = true := by
      rfl
    exact (tailCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 freeTail insideTail).elim

/-- Reverse classification of the unique balance write in `mintToPrefix`,
with an arbitrary SSTORE-free continuation.  The proof reconstructs the exact
key/value pair from the immediate source-site stack. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_mintTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {continuation : Func} {fuel : Nat}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (mintToPrefix +++ continuation) frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (freeTail : Func.sstoreFreeWithin fuel
      ((weth10 dp).main :: weth10Aux)
      (mintToAfterSstore continuation) = true) :
    BalanceSstoreRole ca stepPre
      (.ordinaryMint (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat)
      holder value := by
  rcases cursor.castSourceWithOccurrence
      (mintToPrefix_append_eq_sstoreSplit continuation) fromCursor with
    ⟨splitCursor, _splitPre, fromSplit⟩
  rcases splitCursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [mintToBeforeSstore, addressArg, normalizeAddress,
          pushAddressMask, arg, cdl, Ninst.pushB256] at hn) fromSplit with
    ⟨storeCursor, prefixRun, atStore⟩
  rcases storeCursor.ninstOccurrenceFromCursor_head_or_tail atStore with
    ⟨_sourceEq, preEq⟩ |
      ⟨tailCursor, _sourceSlot, _sourceOccurrence, insideTail⟩
  · subst stepPre
    rcases of_run_append (addressArg 0) prefixRun with
      ⟨afterRecipient, recipientRun, afterRecipientRun⟩
    rcases Line.of_run_cons afterRecipientRun with
      ⟨afterLoad, loadStep, afterLoadRun⟩
    rcases Line.of_run_cons afterLoadRun with
      ⟨afterValue, valueStep, afterValueRun⟩
    rcases Line.of_run_cons afterValueRun with
      ⟨afterAdd, addStep, afterAddRun⟩
    rcases of_run_append (addressArg 0) afterAddRun with
      ⟨afterRecipientAgain, recipientAgainRun, emptyLine⟩
    cases emptyLine
    have recipientPrefix : normalizedAddressArg frame.sevm 0 :: [] <<+
        afterRecipient.stack := by
      simpa [normalizedAddressArg] using
        prefix_of_addressArg nil_pref recipientRun
    rcases prefix_of_sload loadStep recipientPrefix with
      ⟨recipientBalance, balancePrefix, recipientBalanceEq⟩
    have valuePrefix : frame.sevm.value :: recipientBalance :: [] <<+
        afterValue.stack :=
      prefix_of_push (of_run_callvalue valueStep) balancePrefix
    have sumPrefix : (frame.sevm.value + recipientBalance) :: [] <<+
        afterAdd.stack :=
      prefix_of_add addStep valuePrefix
    have storePrefix :
        normalizedAddressArg frame.sevm 0 ::
          (frame.sevm.value + recipientBalance) :: [] <<+
            storeCursor.pre.stack := by
      simpa [normalizedAddressArg] using
        prefix_of_addressArg sumPrefix recipientAgainRun
    have storLoad : Devm.getStor afterRecipient =
        Devm.getStor afterLoad :=
      Ninst.Hinv.inv (f := Devm.getStor) loadStep
    have storValue : Devm.getStor afterLoad = Devm.getStor afterValue :=
      Ninst.Hinv.inv (f := Devm.getStor) valueStep
    have storAdd : Devm.getStor afterValue = Devm.getStor afterAdd :=
      Ninst.Hinv.inv (f := Devm.getStor) addStep
    have storRecipientAgain : Devm.getStor afterAdd =
        Devm.getStor storeCursor.pre :=
      Line.of_inv Devm.getStor (by
        unfold addressArg normalizeAddress pushAddressMask
        line_inv) recipientAgainRun
    have recipientBalanceAtStore :
        recipientBalance =
          (Devm.getStor storeCursor.pre ca).get
            (normalizedAddressArg frame.sevm 0) := by
      rw [recipientBalanceEq]
      change
        (Devm.getStor afterRecipient frame.sevm.currentTarget).get
            (normalizedAddressArg frame.sevm 0) = _
      rw [storLoad, storValue, storAdd, storRecipientAgain,
        context.invocation.2.1]
    have keyEq : normalizedAddressArg frame.sevm 0 =
        (Sevm.argWord frame.sevm 0).toAdr.toB256 :=
      normalizedAddressArg_eq_toAdr_toB256_writeCompleteness _ _
    have storedWord :
        frame.sevm.value + recipientBalance =
          Stor.rest (Devm.getStor storeCursor.pre ca)
              (Sevm.argWord frame.sevm 0).toAdr +
            Nat.toB256 frame.sevm.value.toNat := by
      rw [Jaune.toB256_toNat, recipientBalanceAtStore, keyEq]
      simp only [Stor.rest, Function.comp_apply]
      exact B256.add_comm
    rcases occurrence.2.2.2 with ⟨occurrenceTail, occurrencePrefix⟩
    have occurrencePairPrefix : [key, value] <<+
        storeCursor.pre.stack :=
      pref_trans (pref_append [key, value] occurrenceTail) occurrencePrefix
    have expectedPrefix :
        (Sevm.argWord frame.sevm 0).toAdr.toB256 ::
          (Stor.rest (Devm.getStor storeCursor.pre ca)
              (Sevm.argWord frame.sevm 0).toAdr +
            Nat.toB256 frame.sevm.value.toNat) :: [] <<+
            storeCursor.pre.stack := by
      rw [← keyEq, ← storedWord]
      exact storePrefix
    have pairEq : [key, value] =
        [(Sevm.argWord frame.sevm 0).toAdr.toB256,
          Stor.rest (Devm.getStor storeCursor.pre ca)
              (Sevm.argWord frame.sevm 0).toAdr +
            Nat.toB256 frame.sevm.value.toNat] :=
      List.pref_unique (by simp) occurrencePairPrefix expectedPrefix
    injection pairEq with occurrenceKeyEq valueTailEq
    injection valueTailEq with occurrenceValueEq
    have holderEq : holder = (Sevm.argWord frame.sevm 0).toAdr := by
      apply Adr.toB256_inj
      exact occurrence.2.2.1.symm.trans occurrenceKeyEq
    subst holder
    rw [occurrenceValueEq]
    exact .ordinaryMintCredit _ _ _
  · exact (tailCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 freeTail insideTail).elim

private theorem Exec.Frame.CompiledCursor.balanceSstorePrimaryRole_deposit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) deposit frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = depositSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    primaryFlowAtom frame.sevm = some
        (.ordinaryMint frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.value.toNat) ∧
      BalanceSstoreRole ca stepPre
        (.ordinaryMint frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.value.toNat) holder value := by
  refine ⟨?_, cursor.balanceSstoreRole_mintCaller
    fromCursor occurrence context⟩
  simp [primaryFlowAtom, nonempty, selectorEq]

private theorem Exec.Frame.CompiledCursor.balanceSstorePrimaryRole_depositTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) depositTo frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = depositToSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    primaryFlowAtom frame.sevm = some
        (.ordinaryMint (Sevm.argWord frame.sevm 0)
          (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat) ∧
      BalanceSstoreRole ca stepPre
        (.ordinaryMint (Sevm.argWord frame.sevm 0)
          (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat)
        holder value := by
  have freeTail : Func.sstoreFreeWithin 64
      ((weth10 dp).main :: weth10Aux)
      (mintToAfterSstore Func.stop) = true := by
    rfl
  refine ⟨?_, cursor.balanceSstoreRole_mintTo
    fromCursor occurrence context freeTail⟩
  simp [primaryFlowAtom, nonempty, selectorEq,
    depositToSelector_ne_depositSelector]

private theorem Exec.Frame.CompiledCursor.balanceSstorePrimaryRole_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      depositToAndCall frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = depositToAndCallSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    primaryFlowAtom frame.sevm = some
        (.ordinaryMint (Sevm.argWord frame.sevm 0)
          (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat) ∧
      BalanceSstoreRole ca stepPre
        (.ordinaryMint (Sevm.argWord frame.sevm 0)
          (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat)
        holder value := by
  have freeTail : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux)
      (mintToAfterSstore
        (callBoolCallback onTokenTransferSelector 0 1 [Ninst.callvalue])) =
          true := by
    rfl
  refine ⟨?_, cursor.balanceSstoreRole_mintTo
    fromCursor occurrence context freeTail⟩
  simp [primaryFlowAtom, nonempty, selectorEq,
    depositToAndCallSelector_ne_depositSelector]

private theorem debitLoadedBalance_append_eq_sstoreSplit
    (continuation : Func) :
    debitLoadedBalance +++ continuation =
      [Ninst.sub, Ninst.swap 0] +++
        (.next (.reg .sstore) continuation) := by
  rfl

/-- Decompose an arbitrary occurrence at the shared debit fragment.  The head
case reconstructs its holder and stored subtraction from the immediate stack;
the tail case retains the exact continuation cursor for further site analysis. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_debitLoadedBalance
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {continuation : Func} {final stepPre stepPost : Devm} {slot : Xlot}
    {key value balance amount : B256} {holder owner : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (debitLoadedBalance +++ continuation) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (stackPrefix : [balance, amount, owner.toB256] <<+ cursor.pre.stack)
    (balanceEq : balance =
      (Devm.getStor cursor.pre ca).get owner.toB256) :
    (holder = owner ∧
        value = Stor.rest (Devm.getStor stepPre ca) owner - amount) ∨
      ∃ tailCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) continuation final,
        frame.NinstOccurrenceFromCursor tailCursor (.reg .sstore)
          stepPre stepPost slot := by
  rcases cursor.castSourceWithOccurrence
      (debitLoadedBalance_append_eq_sstoreSplit continuation) fromCursor with
    ⟨splitCursor, splitPre, fromSplit⟩
  have splitStack : [balance, amount, owner.toB256] <<+
      splitCursor.pre.stack := by
    rw [splitPre]
    exact stackPrefix
  have splitBalance : balance =
      (Devm.getStor splitCursor.pre ca).get owner.toB256 := by
    rw [splitPre]
    exact balanceEq
  rcases splitCursor.balanceSstoreOccurrence_after_line
      (by simp) fromSplit with
    ⟨storeCursor, prefixRun, atStore⟩
  rcases storeCursor.ninstOccurrenceFromCursor_head_or_tail atStore with
    ⟨_sourceEq, preEq⟩ |
      ⟨tailCursor, _sourceSlot, _sourceOccurrence, insideTail⟩
  · subst stepPre
    rcases Line.of_run_cons prefixRun with
      ⟨afterSub, subStep, afterSubRun⟩
    rcases Line.of_run_cons afterSubRun with
      ⟨afterSwap, swapStep, emptyLine⟩
    cases emptyLine
    have subPrefix : [balance - amount, owner.toB256] <<+
        afterSub.stack :=
      prefix_of_sub subStep splitStack
    have swapCore : Stack.Swap (0 : Fin 16).val
        [balance - amount, owner.toB256]
        [owner.toB256, balance - amount] :=
      Stack.swapCore_zero
    have storePrefix : [owner.toB256, balance - amount] <<+
        storeCursor.pre.stack :=
      Stack.prefix_of_swap swapCore (of_run_swap swapStep) subPrefix
    have storSub : Devm.getStor splitCursor.pre = Devm.getStor afterSub :=
      Ninst.Hinv.inv (f := Devm.getStor) subStep
    have storSwap : Devm.getStor afterSub = Devm.getStor storeCursor.pre :=
      Ninst.Hinv.inv (f := Devm.getStor) swapStep
    have balanceAtStore : balance =
        (Devm.getStor storeCursor.pre ca).get owner.toB256 := by
      rw [splitBalance, storSub, storSwap]
    rcases occurrence.2.2.2 with ⟨occurrenceTail, occurrencePrefix⟩
    have occurrencePairPrefix : [key, value] <<+
        storeCursor.pre.stack :=
      pref_trans (pref_append [key, value] occurrenceTail) occurrencePrefix
    have expectedPrefix :
        [owner.toB256,
          Stor.rest (Devm.getStor storeCursor.pre ca) owner - amount] <<+
            storeCursor.pre.stack := by
      simp only [Stor.rest, Function.comp_apply]
      rw [← balanceAtStore]
      exact storePrefix
    have pairEq : [key, value] =
        [owner.toB256,
          Stor.rest (Devm.getStor storeCursor.pre ca) owner - amount] :=
      List.pref_unique (by simp) occurrencePairPrefix expectedPrefix
    injection pairEq with occurrenceKeyEq occurrenceValueTailEq
    injection occurrenceValueTailEq with occurrenceValueEq
    have holderEq : holder = owner := by
      apply Adr.toB256_inj
      exact occurrence.2.2.1.symm.trans occurrenceKeyEq
    exact Or.inl ⟨holderEq, occurrenceValueEq⟩
  · exact Or.inr ⟨tailCursor, insideTail⟩

private def callerDebitGuardLine (amountArg : B256) : Line :=
  loadCallerBalanceAmount amountArg ++ balanceTooSmall

private def callerDebitSource
    (amountArg : B256) (errorSlot : Nat) (continuation : Func) : Func :=
  callerDebitGuardLine amountArg +++
    (.branch (debitLoadedBalance +++ continuation) (.call errorSlot))

/-- Follow the successful caller-balance guard to its exact debit cursor while
retaining an arbitrary later occurrence.  The reverting error arm is excluded
only by its local source certificate. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_callerDebit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {amountArg : B256} {errorSlot fuel : Nat}
    {errorBody continuation : Func}
    {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (callerDebitSource amountArg errorSlot continuation) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (context : frame.AuthenticContext dp ca)
    (errorLookup : (((weth10 dp).main :: weth10Aux)[errorSlot]?) =
      some errorBody)
    (errorFree : Func.sstoreFreeWithin fuel
      ((weth10 dp).main :: weth10Aux) errorBody = true) :
    ∃ (balance : B256)
        (debitCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (debitLoadedBalance +++ continuation) final),
      [balance, Sevm.argWord frame.sevm amountArg,
          frame.sevm.caller.toB256] <<+ debitCursor.pre.stack ∧
      balance = (Devm.getStor debitCursor.pre ca).get
        frame.sevm.caller.toB256 ∧
      frame.NinstOccurrenceFromCursor debitCursor (.reg .sstore)
        stepPre stepPost slot := by
  rcases cursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [callerDebitGuardLine, loadCallerBalanceAmount,
          balanceTooSmall, arg, cdl, Ninst.pushB256] at hn) fromCursor with
    ⟨branchCursor, guardRun, atBranch⟩
  rcases of_run_append (loadCallerBalanceAmount amountArg) guardRun with
    ⟨afterLoad, loadRun, guardTailRun⟩
  rcases prefix_of_loadCallerBalanceAmount nil_pref loadRun with
    ⟨balance, balanceEq, loadPrefix⟩
  have guardPrefix :
      (balance <? Sevm.argWord frame.sevm amountArg) :: balance ::
        Sevm.argWord frame.sevm amountArg :: frame.sevm.caller.toB256 ::
          [] <<+ branchCursor.pre.stack :=
    prefix_of_balanceTooSmall loadPrefix guardTailRun
  rcases branchCursor.balanceSstoreOccurrence_branchWithFlag atBranch with
    ⟨debitCursor, pop, insideDebit⟩ |
      ⟨_flag, _nonzero, errorCursor, _pop, insideError⟩
  · have debitPrefix :
        [balance, Sevm.argWord frame.sevm amountArg,
          frame.sevm.caller.toB256] <<+ debitCursor.pre.stack :=
      prefix_of_pop
        ⟨0, Devm.PopBurn.of_popBurnBy pop⟩ guardPrefix
    have storLoad : Devm.getStor cursor.pre = Devm.getStor afterLoad :=
      Line.of_inv Devm.getStor (by line_inv) loadRun
    have storGuard : Devm.getStor afterLoad =
        Devm.getStor branchCursor.pre :=
      Line.of_inv Devm.getStor (by line_inv) guardTailRun
    have storPop : Devm.getStor branchCursor.pre =
        Devm.getStor debitCursor.pre :=
      PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy pop)
    have balanceAtDebit : balance =
        (Devm.getStor debitCursor.pre ca).get
          frame.sevm.caller.toB256 := by
      rw [balanceEq, storLoad, storGuard, storPop,
        context.invocation.2.1]
    exact ⟨balance, debitCursor, debitPrefix, balanceAtDebit, insideDebit⟩
  · rcases errorCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideError with
      ⟨actualError, actualLookup, errorBodyCursor, insideErrorBody⟩
    have errorEq : actualError = errorBody :=
      Option.some.inj (actualLookup.symm.trans errorLookup)
    subst actualError
    exact (errorBodyCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 errorFree insideErrorBody).elim

private def withdrawAfterDebit : Func :=
  Ninst.caller ::: arg 0 +++ Ninst.pushB256 0 ::: emitTransfer +++
  Ninst.swap 0 ::: Ninst.pop :::
  sendValueToCaller +++ Ninst.iszero :::
  ((.call ethTransferErrorSlot) <?> Func.stop)

private theorem prependStoresRev_noCalls
    (stores : List (B256 × Nat)) {tail : Func} (tailNoCalls : tail.NoCalls) :
    (prependStoresRev stores tail).NoCalls := by
  induction stores generalizing tail with
  | nil => exact tailNoCalls
  | cons store stores ih =>
      apply ih
      simp [prependStore, Func.NoCalls, tailNoCalls]

private theorem revWith_noCalls (reason : String) :
    (Func.revWith reason).NoCalls := by
  unfold Func.revWith Func.revData
  apply prependStoresRev_noCalls
  simp [Func.NoCalls]

private theorem burnBalanceError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs burnBalanceError = true := by
  calc
      Func.sstoreFreeWithin 256 fs burnBalanceError =
        Func.sstoreFreeWithin 256 [] burnBalanceError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem ethTransferError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs ethTransferError = true := by
  calc
      Func.sstoreFreeWithin 256 fs ethTransferError =
        Func.sstoreFreeWithin 256 [] ethTransferError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem transferBalanceError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs transferBalanceError = true := by
  calc
    Func.sstoreFreeWithin 256 fs transferBalanceError =
        Func.sstoreFreeWithin 256 [] transferBalanceError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem allowanceError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs allowanceError = true := by
  calc
    Func.sstoreFreeWithin 256 fs allowanceError =
        Func.sstoreFreeWithin 256 [] allowanceError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem etherTransferError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs etherTransferError = true := by
  calc
    Func.sstoreFreeWithin 256 fs etherTransferError =
        Func.sstoreFreeWithin 256 [] etherTransferError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem flashTokenError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs flashTokenError = true := by
  calc
    Func.sstoreFreeWithin 256 fs flashTokenError =
        Func.sstoreFreeWithin 256 [] flashTokenError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem individualLimitError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs individualLimitError = true := by
  calc
    Func.sstoreFreeWithin 256 fs individualLimitError =
        Func.sstoreFreeWithin 256 [] individualLimitError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem totalLimitError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs totalLimitError = true := by
  calc
    Func.sstoreFreeWithin 256 fs totalLimitError =
        Func.sstoreFreeWithin 256 [] totalLimitError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem expiredPermitError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs expiredPermitError = true := by
  calc
    Func.sstoreFreeWithin 256 fs expiredPermitError =
        Func.sstoreFreeWithin 256 [] expiredPermitError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem invalidPermitError_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 256 fs invalidPermitError = true := by
  calc
    Func.sstoreFreeWithin 256 fs invalidPermitError =
        Func.sstoreFreeWithin 256 [] invalidPermitError :=
      Func.sstoreFreeWithin_eq_of_noCalls
        (by exact revWith_noCalls _) fs []
    _ = true := by decide +kernel

private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_stopOrError
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {linePrefix : Line} {errorSlot fuel : Nat} {errorBody : Func}
    {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (linePrefix +++ (.branch Func.stop (.call errorSlot))) final)
    (noStore : ∀ n ∈ linePrefix, n ≠ .reg .sstore)
    (context : frame.AuthenticContext dp ca)
    (errorLookup : (((weth10 dp).main :: weth10Aux)[errorSlot]?) =
      some errorBody)
    (errorFree : Func.sstoreFreeWithin fuel
      ((weth10 dp).main :: weth10Aux) errorBody = true)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) : False := by
  rcases cursor.balanceSstoreOccurrence_after_line noStore occurrence with
    ⟨branchCursor, _prefixRun, atBranch⟩
  rcases branchCursor.balanceSstoreOccurrence_branch atBranch with
    ⟨stopCursor, insideStop⟩ | ⟨errorCursor, insideError⟩
  · have stopFree : Func.sstoreFreeWithin 4
        ((weth10 dp).main :: weth10Aux) Func.stop = true := by
      rfl
    exact stopCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 stopFree insideStop
  · rcases errorCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideError with
      ⟨actualError, actualLookup, errorBodyCursor, insideErrorBody⟩
    have errorEq : actualError = errorBody :=
      Option.some.inj (actualLookup.symm.trans errorLookup)
    subst actualError
    exact errorBodyCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 errorFree insideErrorBody

private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_successOrError
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {linePrefix : Line} {success errorBody : Func}
    {errorSlot successFuel errorFuel : Nat}
    {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (linePrefix +++ (.branch success (.call errorSlot))) final)
    (noStore : ∀ n ∈ linePrefix, n ≠ .reg .sstore)
    (context : frame.AuthenticContext dp ca)
    (successFree : Func.sstoreFreeWithin successFuel
      ((weth10 dp).main :: weth10Aux) success = true)
    (errorLookup : (((weth10 dp).main :: weth10Aux)[errorSlot]?) =
      some errorBody)
    (errorFree : Func.sstoreFreeWithin errorFuel
      ((weth10 dp).main :: weth10Aux) errorBody = true)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) : False := by
  rcases cursor.balanceSstoreOccurrence_after_line noStore occurrence with
    ⟨branchCursor, _prefixRun, atBranch⟩
  rcases branchCursor.balanceSstoreOccurrence_branch atBranch with
    ⟨successCursor, insideSuccess⟩ | ⟨errorCursor, insideError⟩
  · exact successCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 successFree insideSuccess
  · rcases errorCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideError with
      ⟨actualError, actualLookup, errorBodyCursor, insideErrorBody⟩
    have errorEq : actualError = errorBody :=
      Option.some.inj (actualLookup.symm.trans errorLookup)
    subst actualError
    exact errorBodyCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 errorFree insideErrorBody

private def redemptionAfterDebitPrefix
    (amountArg : B256) (sendLine : Line) : Line :=
  [Ninst.caller] ++ arg amountArg ++ [Ninst.pushB256 0] ++
    emitTransfer ++ [Ninst.swap 0, Ninst.pop] ++ sendLine ++ [Ninst.iszero]

private theorem withdrawAfterDebit_eq_stopOrError :
    withdrawAfterDebit =
      redemptionAfterDebitPrefix 0 sendValueToCaller +++
        (.branch Func.stop (.call ethTransferErrorSlot)) := by
  rfl

private theorem withdraw_eq_callerDebitSource :
    withdraw = callerDebitSource 0 burnBalanceErrorSlot withdrawAfterDebit := by
  simp [withdraw, callerDebitSource, callerDebitGuardLine,
    withdrawAfterDebit, prepend_append_writeCompleteness]

private theorem Exec.Frame.CompiledCursor.balanceSstorePrimaryRole_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) withdraw frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = withdrawSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    primaryFlowAtom frame.sevm = some
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.caller (Sevm.argWord frame.sevm 0).toNat) ∧
      BalanceSstoreRole ca stepPre
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.caller (Sevm.argWord frame.sevm 0).toNat)
        holder value := by
  have primary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.caller (Sevm.argWord frame.sevm 0).toNat) := by
    simp [primaryFlowAtom, nonempty, selectorEq,
      withdrawSelector_ne_depositSelector,
      withdrawSelector_ne_depositToSelector,
      withdrawSelector_ne_depositToAndCallSelector,
      withdrawSelector_ne_transferSelector,
      withdrawSelector_ne_transferAndCallSelector,
      withdrawSelector_ne_transferFromSelector]
  rcases cursor.castSourceWithOccurrence withdraw_eq_callerDebitSource
      fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  have errorLookup :
      (((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]?) =
        some burnBalanceError := by
    simp [burnBalanceErrorSlot, weth10, weth10Aux]
  have errorFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux) burnBalanceError = true := by
    exact burnBalanceError_sstoreFree _
  rcases sourceCursor.balanceSstoreOccurrence_callerDebit fromSource
      context errorLookup errorFree with
    ⟨balance, debitCursor, debitPrefix, balanceEq, insideDebit⟩
  rcases debitCursor.balanceSstoreOccurrence_debitLoadedBalance
      insideDebit occurrence debitPrefix balanceEq with
    ⟨holderEq, valueEq⟩ | ⟨tailCursor, insideTail⟩
  · subst holder
    refine ⟨primary, ?_⟩
    rw [valueEq]
    simpa only [Jaune.toB256_toNat] using
      (BalanceSstoreRole.redemptionDebit
        (ca := ca) (stepPre := stepPre)
        frame.sevm.caller.toB256 frame.sevm.caller frame.sevm.caller
        (Sevm.argWord frame.sevm 0).toNat)
  · rcases tailCursor.castSourceWithOccurrence
        withdrawAfterDebit_eq_stopOrError insideTail with
      ⟨tailSplitCursor, _tailPre, insideTailSplit⟩
    have errorLookup :
        (((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]?) =
          some ethTransferError := by
      simp [ethTransferErrorSlot, weth10, weth10Aux]
    have errorFree : Func.sstoreFreeWithin 256
        ((weth10 dp).main :: weth10Aux) ethTransferError = true :=
      ethTransferError_sstoreFree _
    exact (tailSplitCursor.no_balanceSstoreOccurrence_stopOrError
      (by
        rintro n hn rfl
        simp [redemptionAfterDebitPrefix, sendValueToCaller, pushList,
          emitTransfer, Blanc.transferFromLog, arg, cdl, mstoreAt,
          logWith, Ninst.pushB256] at hn)
      context errorLookup errorFree insideTailSplit).elim

private def withdrawToAfterDebit : Func :=
  Ninst.caller ::: arg 1 +++ Ninst.pushB256 0 ::: emitTransfer +++
  Ninst.swap 0 ::: Ninst.pop :::
  sendValueToArg 0 +++ Ninst.iszero :::
  ((.call ethTransferErrorSlot) <?> Func.stop)

private theorem withdrawToAfterDebit_eq_stopOrError :
    withdrawToAfterDebit =
      redemptionAfterDebitPrefix 1 (sendValueToArg 0) +++
        (.branch Func.stop (.call ethTransferErrorSlot)) := by
  rfl

private theorem withdrawTo_eq_callerDebitSource :
    withdrawTo =
      callerDebitSource 1 burnBalanceErrorSlot withdrawToAfterDebit := by
  simp [withdrawTo, callerDebitSource, callerDebitGuardLine,
    withdrawToAfterDebit, prepend_append_writeCompleteness]

private theorem Exec.Frame.CompiledCursor.balanceSstorePrimaryRole_withdrawTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) withdrawTo frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = withdrawToSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    primaryFlowAtom frame.sevm = some
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toNat) ∧
      BalanceSstoreRole ca stepPre
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toNat) holder value := by
  have primary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toNat) := by
    simp [primaryFlowAtom, nonempty, selectorEq,
      withdrawToSelector_ne_depositSelector,
      withdrawToSelector_ne_depositToSelector,
      withdrawToSelector_ne_depositToAndCallSelector,
      withdrawToSelector_ne_transferSelector,
      withdrawToSelector_ne_transferAndCallSelector,
      withdrawToSelector_ne_transferFromSelector,
      withdrawToSelector_ne_withdrawSelector]
  rcases cursor.castSourceWithOccurrence withdrawTo_eq_callerDebitSource
      fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  have errorLookup :
      (((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]?) =
        some burnBalanceError := by
    simp [burnBalanceErrorSlot, weth10, weth10Aux]
  have errorFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux) burnBalanceError = true := by
    exact burnBalanceError_sstoreFree _
  rcases sourceCursor.balanceSstoreOccurrence_callerDebit fromSource
      context errorLookup errorFree with
    ⟨balance, debitCursor, debitPrefix, balanceEq, insideDebit⟩
  rcases debitCursor.balanceSstoreOccurrence_debitLoadedBalance
      insideDebit occurrence debitPrefix balanceEq with
    ⟨holderEq, valueEq⟩ | ⟨tailCursor, insideTail⟩
  · subst holder
    refine ⟨primary, ?_⟩
    rw [valueEq]
    simpa only [Jaune.toB256_toNat] using
      (BalanceSstoreRole.redemptionDebit
        (ca := ca) (stepPre := stepPre)
        frame.sevm.caller.toB256 frame.sevm.caller
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toNat)
  · rcases tailCursor.castSourceWithOccurrence
        withdrawToAfterDebit_eq_stopOrError insideTail with
      ⟨tailSplitCursor, _tailPre, insideTailSplit⟩
    have errorLookup :
        (((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]?) =
          some ethTransferError := by
      simp [ethTransferErrorSlot, weth10, weth10Aux]
    have errorFree : Func.sstoreFreeWithin 256
        ((weth10 dp).main :: weth10Aux) ethTransferError = true :=
      ethTransferError_sstoreFree _
    exact (tailSplitCursor.no_balanceSstoreOccurrence_stopOrError
      (by
        rintro n hn rfl
        simp [redemptionAfterDebitPrefix, sendValueToArg, pushList,
          emitTransfer, Blanc.transferFromLog, arg, cdl, mstoreAt,
          logWith, Ninst.pushB256] at hn)
      context errorLookup errorFree insideTailSplit).elim

private def creditAddressArgBeforeSstore
    (ownerArg amountArg : B256) : Line :=
  addressArg ownerArg ++ [Ninst.dup 0, Ninst.sload] ++ arg amountArg ++
    [Ninst.add, Ninst.swap 0]

private def creditAddressArgSource
    (ownerArg amountArg : B256) (continuation : Func) : Func :=
  creditAddressArgBeforeSstore ownerArg amountArg +++
    (.next (.reg .sstore) continuation)

/-- Immediate-site decomposition for the shared normalized recipient-credit
fragment. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_creditAddressArg
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {ownerArg amountArg : B256} {continuation : Func}
    {final stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (creditAddressArgSource ownerArg amountArg continuation) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    (holder = (Sevm.argWord frame.sevm ownerArg).toAdr ∧
        value = Stor.rest (Devm.getStor stepPre ca)
          (Sevm.argWord frame.sevm ownerArg).toAdr +
            Sevm.argWord frame.sevm amountArg) ∨
      ∃ tailCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) continuation final,
        frame.NinstOccurrenceFromCursor tailCursor (.reg .sstore)
          stepPre stepPost slot := by
  rcases cursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [creditAddressArgBeforeSstore, addressArg, normalizeAddress,
          pushAddressMask, arg, cdl, Ninst.pushB256] at hn) fromCursor with
    ⟨storeCursor, prefixRun, atStore⟩
  rcases storeCursor.ninstOccurrenceFromCursor_head_or_tail atStore with
    ⟨_sourceEq, preEq⟩ |
      ⟨tailCursor, _sourceSlot, _sourceOccurrence, insideTail⟩
  · subst stepPre
    rcases of_run_append (addressArg ownerArg) prefixRun with
      ⟨afterOwner, ownerRun, afterOwnerRun⟩
    rcases Line.of_run_cons afterOwnerRun with
      ⟨afterDup, dupStep, afterDupRun⟩
    rcases Line.of_run_cons afterDupRun with
      ⟨afterLoad, loadStep, afterLoadRun⟩
    rcases of_run_append (arg amountArg) afterLoadRun with
      ⟨afterAmount, amountRun, afterAmountRun⟩
    rcases Line.of_run_cons afterAmountRun with
      ⟨afterAdd, addStep, afterAddRun⟩
    rcases Line.of_run_cons afterAddRun with
      ⟨afterSwap, swapStep, emptyLine⟩
    cases emptyLine
    have ownerPrefix : normalizedAddressArg frame.sevm ownerArg :: [] <<+
        afterOwner.stack := by
      simpa [normalizedAddressArg] using
        prefix_of_addressArg nil_pref ownerRun
    have dupPrefix : normalizedAddressArg frame.sevm ownerArg ::
        normalizedAddressArg frame.sevm ownerArg :: [] <<+
          afterDup.stack :=
      prefix_of_dup_val dupStep (by show_nth) ownerPrefix
    rcases prefix_of_sload loadStep dupPrefix with
      ⟨ownerBalance, balancePrefix, ownerBalanceEq⟩
    have amountPrefix : Sevm.argWord frame.sevm amountArg ::
        ownerBalance :: normalizedAddressArg frame.sevm ownerArg :: [] <<+
          afterAmount.stack :=
      prefix_of_arg balancePrefix amountRun
    have addPrefix :
        (Sevm.argWord frame.sevm amountArg + ownerBalance) ::
          normalizedAddressArg frame.sevm ownerArg :: [] <<+
            afterAdd.stack :=
      prefix_of_add addStep amountPrefix
    have swapCore : Stack.Swap (0 : Fin 16).val
        [Sevm.argWord frame.sevm amountArg + ownerBalance,
          normalizedAddressArg frame.sevm ownerArg]
        [normalizedAddressArg frame.sevm ownerArg,
          Sevm.argWord frame.sevm amountArg + ownerBalance] :=
      Stack.swapCore_zero
    have storePrefix :
        [normalizedAddressArg frame.sevm ownerArg,
          Sevm.argWord frame.sevm amountArg + ownerBalance] <<+
            storeCursor.pre.stack :=
      Stack.prefix_of_swap swapCore (of_run_swap swapStep) addPrefix
    have storDup : Devm.getStor afterOwner = Devm.getStor afterDup :=
      Ninst.Hinv.inv (f := Devm.getStor) dupStep
    have storLoad : Devm.getStor afterDup = Devm.getStor afterLoad :=
      Ninst.Hinv.inv (f := Devm.getStor) loadStep
    have storAmount : Devm.getStor afterLoad = Devm.getStor afterAmount :=
      Line.of_inv Devm.getStor (by line_inv) amountRun
    have storAdd : Devm.getStor afterAmount = Devm.getStor afterAdd :=
      Ninst.Hinv.inv (f := Devm.getStor) addStep
    have storSwap : Devm.getStor afterAdd = Devm.getStor storeCursor.pre :=
      Ninst.Hinv.inv (f := Devm.getStor) swapStep
    have ownerBalanceAtStore : ownerBalance =
        (Devm.getStor storeCursor.pre frame.sevm.currentTarget).get
          (normalizedAddressArg frame.sevm ownerArg) := by
      rw [ownerBalanceEq]
      change
        (Devm.getStor afterDup frame.sevm.currentTarget).get
            (normalizedAddressArg frame.sevm ownerArg) = _
      rw [storLoad, storAmount, storAdd, storSwap]
    have normalizedEq : normalizedAddressArg frame.sevm ownerArg =
        (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 :=
      normalizedAddressArg_eq_toAdr_toB256_writeCompleteness _ _
    have targetGetEq :
        (Devm.getStor storeCursor.pre frame.sevm.currentTarget).get
            (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 =
          (Devm.getStor storeCursor.pre ca).get
            (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 :=
      congrArg
        (fun target => (Devm.getStor storeCursor.pre target).get
          (Sevm.argWord frame.sevm ownerArg).toAdr.toB256)
        context.invocation.2.1
    have storedWord :
        Sevm.argWord frame.sevm amountArg + ownerBalance =
          Stor.rest (Devm.getStor storeCursor.pre ca)
              (Sevm.argWord frame.sevm ownerArg).toAdr +
            Sevm.argWord frame.sevm amountArg := by
      simp only [Stor.rest, Function.comp_apply]
      calc
        Sevm.argWord frame.sevm amountArg + ownerBalance =
            Sevm.argWord frame.sevm amountArg +
              (Devm.getStor storeCursor.pre frame.sevm.currentTarget).get
                (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 := by
          rw [ownerBalanceAtStore, normalizedEq]
        _ = Sevm.argWord frame.sevm amountArg +
              (Devm.getStor storeCursor.pre ca).get
                (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 :=
          congrArg (fun word => Sevm.argWord frame.sevm amountArg + word)
            targetGetEq
        _ = (Devm.getStor storeCursor.pre ca).get
                (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 +
              Sevm.argWord frame.sevm amountArg := B256.add_comm
    rcases occurrence.2.2.2 with ⟨occurrenceTail, occurrencePrefix⟩
    have occurrencePairPrefix : [key, value] <<+
        storeCursor.pre.stack :=
      pref_trans (pref_append [key, value] occurrenceTail) occurrencePrefix
    have expectedPrefix :
        [(Sevm.argWord frame.sevm ownerArg).toAdr.toB256,
          Stor.rest (Devm.getStor storeCursor.pre ca)
              (Sevm.argWord frame.sevm ownerArg).toAdr +
            Sevm.argWord frame.sevm amountArg] <<+
              storeCursor.pre.stack := by
      rw [← normalizedEq, ← storedWord]
      exact storePrefix
    have pairEq : [key, value] =
        [(Sevm.argWord frame.sevm ownerArg).toAdr.toB256,
          Stor.rest (Devm.getStor storeCursor.pre ca)
              (Sevm.argWord frame.sevm ownerArg).toAdr +
            Sevm.argWord frame.sevm amountArg] :=
      List.pref_unique (by simp) occurrencePairPrefix expectedPrefix
    injection pairEq with occurrenceKeyEq occurrenceValueTailEq
    injection occurrenceValueTailEq with occurrenceValueEq
    have holderEq : holder =
        (Sevm.argWord frame.sevm ownerArg).toAdr := by
      apply Adr.toB256_inj
      exact occurrence.2.2.1.symm.trans occurrenceKeyEq
    exact Or.inl ⟨holderEq, occurrenceValueEq⟩
  · exact Or.inr ⟨tailCursor, insideTail⟩

private def transferSelectLine : Line := arg 0 ++ [Ninst.iszero]

private theorem transferThen_eq_select (continuation : Func) :
    transferThen continuation =
      transferSelectLine +++
        (.branch (transferNonzeroThen continuation)
          (transferZeroThen continuation)) := by
  rfl

/-- Follow the actual raw-recipient zero test, retaining both the selected
transfer arm cursor and the exact raw-word fact that chose it. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_transferThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {continuation : Func} {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (transferThen continuation) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    (Sevm.argWord frame.sevm 0 ≠ 0 ∧
      ∃ armCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (transferNonzeroThen continuation) final,
        frame.NinstOccurrenceFromCursor armCursor (.reg .sstore)
          stepPre stepPost slot) ∨
      (Sevm.argWord frame.sevm 0 = 0 ∧
      ∃ armCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (transferZeroThen continuation) final,
        frame.NinstOccurrenceFromCursor armCursor (.reg .sstore)
          stepPre stepPost slot) := by
  rcases cursor.castSourceWithOccurrence
      (transferThen_eq_select continuation) fromCursor with
    ⟨selectCursor, _selectPre, fromSelect⟩
  rcases selectCursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [transferSelectLine, arg, cdl, Ninst.pushB256] at hn)
      fromSelect with
    ⟨branchCursor, selectRun, atBranch⟩
  rcases of_run_append (arg 0) selectRun with
    ⟨afterArg, argRun, afterArgRun⟩
  rcases Line.of_run_cons afterArgRun with
    ⟨afterZero, zeroStep, emptyLine⟩
  cases emptyLine
  have argPrefix : [Sevm.argWord frame.sevm 0] <<+ afterArg.stack :=
    prefix_of_arg nil_pref argRun
  have flagPrefix : [Sevm.argWord frame.sevm 0 =? 0] <<+
      branchCursor.pre.stack :=
    prefix_of_iszero zeroStep argPrefix
  rcases branchCursor.balanceSstoreOccurrence_branchWithFlag atBranch with
    ⟨nonzeroCursor, pop, insideNonzero⟩ |
      ⟨flag, flagNonzero, zeroCursor, pop, insideZero⟩
  · have selectedPrefix : [(0 : B256)] <<+ branchCursor.pre.stack :=
      pref_of_split pop.stack
    have flagEq : (Sevm.argWord frame.sevm 0 =? 0) = 0 :=
      pref_head_unique flagPrefix selectedPrefix
    have rawNonzero : Sevm.argWord frame.sevm 0 ≠ 0 := by
      intro rawZero
      rw [rawZero] at flagEq
      simp [B256.eqCheck] at flagEq
      exact (by decide : (1 : B256) ≠ 0) flagEq
    exact Or.inl ⟨rawNonzero, nonzeroCursor, insideNonzero⟩
  · have selectedPrefix : [flag] <<+ branchCursor.pre.stack :=
      pref_of_split pop.stack
    have flagEq : (Sevm.argWord frame.sevm 0 =? 0) = flag :=
      pref_head_unique flagPrefix selectedPrefix
    have rawZero : Sevm.argWord frame.sevm 0 = 0 := by
      by_contra rawNonzero
      have checkZero : (Sevm.argWord frame.sevm 0 =? 0) = 0 := by
        simp [B256.eqCheck, rawNonzero]
      apply flagNonzero
      rw [← flagEq]
      exact checkZero
    exact Or.inr ⟨rawZero, zeroCursor, insideZero⟩

private def transferAfterCredit (continuation : Func) : Func :=
  ([Ninst.caller] ++ arg 1 ++ addressArg 0 ++ emitTransfer) +++ continuation

private def transferCreditSource (continuation : Func) : Func :=
  creditAddressArgSource 0 1 (transferAfterCredit continuation)

private theorem transferNonzeroThen_eq_callerDebitSource
    (continuation : Func) :
    transferNonzeroThen continuation =
      callerDebitSource 1 transferBalanceErrorSlot
        (transferCreditSource continuation) := by
  rfl

private def transferZeroContinuation (continuation : Func) : Func :=
  redemptionAfterDebitPrefix 1 sendValueToCaller +++
    (.branch continuation (.call ethTransferErrorSlot))

private theorem transferZeroContinuation_eq_successOrError
    (continuation : Func) :
    transferZeroContinuation continuation =
      redemptionAfterDebitPrefix 1 sendValueToCaller +++
        (.branch continuation (.call ethTransferErrorSlot)) := by
  rfl

private theorem transferZeroThen_eq_callerDebitSource
    (continuation : Func) :
    transferZeroThen continuation =
      callerDebitSource 1 burnBalanceErrorSlot
        (transferZeroContinuation continuation) := by
  rfl

/-- Reverse classification of every balance write in the nonzero-recipient
transfer arm.  The first write is the caller debit and the second is the
normalized recipient credit; the remaining callback/return suffix is ruled
out by its local source certificate. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_transferNonzeroThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {continuation : Func} {fuel : Nat}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (transferNonzeroThen continuation) frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (freeTail : Func.sstoreFreeWithin fuel
      ((weth10 dp).main :: weth10Aux)
      (transferAfterCredit continuation) = true) :
    BalanceSstoreRole ca stepPre
      (.transfer frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 0)
        frame.sevm.caller (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toNat)
      holder value := by
  rcases cursor.castSourceWithOccurrence
      (transferNonzeroThen_eq_callerDebitSource continuation) fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  have errorLookup :
      (((weth10 dp).main :: weth10Aux)[transferBalanceErrorSlot]?) =
        some transferBalanceError := by
    simp [transferBalanceErrorSlot, weth10, weth10Aux]
  have errorFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux) transferBalanceError = true :=
    transferBalanceError_sstoreFree _
  rcases sourceCursor.balanceSstoreOccurrence_callerDebit fromSource
      context errorLookup errorFree with
    ⟨balance, debitCursor, debitPrefix, balanceEq, insideDebit⟩
  rcases debitCursor.balanceSstoreOccurrence_debitLoadedBalance
      insideDebit occurrence debitPrefix balanceEq with
    ⟨holderEq, valueEq⟩ | ⟨creditCursor, insideCredit⟩
  · subst holder
    rw [valueEq]
    simpa only [Jaune.toB256_toNat] using
      (BalanceSstoreRole.transferDebit
        (ca := ca) (stepPre := stepPre)
        frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 0)
        frame.sevm.caller (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toNat)
  · rcases creditCursor.balanceSstoreOccurrence_creditAddressArg
        insideCredit occurrence context with
      ⟨holderEq, valueEq⟩ | ⟨tailCursor, insideTail⟩
    · subst holder
      rw [valueEq]
      simpa only [Jaune.toB256_toNat] using
        (BalanceSstoreRole.transferCredit
          (ca := ca) (stepPre := stepPre)
          frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 0)
          frame.sevm.caller (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toNat)
    · exact (tailCursor.no_balanceSstoreOccurrence_of_free
        context.invocation.2.2.2 freeTail insideTail).elim

/-- Reverse classification of every balance write in the raw-zero transfer
arm.  Its only balance write is the caller debit; the value-send and selected
callback/return suffix is source-certified SSTORE-free. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_transferZeroThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {continuation : Func} {fuel : Nat}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (transferZeroThen continuation) frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (continuationFree : Func.sstoreFreeWithin fuel
      ((weth10 dp).main :: weth10Aux)
      continuation = true) :
    BalanceSstoreRole ca stepPre
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat)
      holder value := by
  rcases cursor.castSourceWithOccurrence
      (transferZeroThen_eq_callerDebitSource continuation) fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  have errorLookup :
      (((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]?) =
        some burnBalanceError := by
    simp [burnBalanceErrorSlot, weth10, weth10Aux]
  have errorFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux) burnBalanceError = true :=
    burnBalanceError_sstoreFree _
  rcases sourceCursor.balanceSstoreOccurrence_callerDebit fromSource
      context errorLookup errorFree with
    ⟨balance, debitCursor, debitPrefix, balanceEq, insideDebit⟩
  rcases debitCursor.balanceSstoreOccurrence_debitLoadedBalance
      insideDebit occurrence debitPrefix balanceEq with
    ⟨holderEq, valueEq⟩ | ⟨tailCursor, insideTail⟩
  · subst holder
    rw [valueEq]
    simpa only [Jaune.toB256_toNat] using
      (BalanceSstoreRole.redemptionDebit
        (ca := ca) (stepPre := stepPre)
        frame.sevm.caller.toB256 frame.sevm.caller frame.sevm.caller
        (Sevm.argWord frame.sevm 1).toNat)
  · rcases tailCursor.castSourceWithOccurrence
        (transferZeroContinuation_eq_successOrError continuation)
        insideTail with
      ⟨tailSplitCursor, _tailPre, insideTailSplit⟩
    have transferErrorLookup :
        (((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]?) =
          some ethTransferError := by
      simp [ethTransferErrorSlot, weth10, weth10Aux]
    have transferErrorFree : Func.sstoreFreeWithin 256
        ((weth10 dp).main :: weth10Aux) ethTransferError = true :=
      ethTransferError_sstoreFree _
    exact (tailSplitCursor.no_balanceSstoreOccurrence_successOrError
      (by
        rintro n hn rfl
        simp [redemptionAfterDebitPrefix, sendValueToCaller, pushList,
          emitTransfer, Blanc.transferFromLog, arg, cdl, mstoreAt,
          logWith, Ninst.pushB256] at hn)
      context continuationFree transferErrorLookup transferErrorFree
      insideTailSplit).elim

/-- Reverse classification across the runtime's raw-recipient test.  The
returned arm fact is the same machine word that selected the executed source
branch, so dirty nonzero words are never conflated with normalized zero. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_transferThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {continuation : Func} {nonzeroFuel zeroFuel : Nat}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (transferThen continuation) frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (nonzeroFree : Func.sstoreFreeWithin nonzeroFuel
      ((weth10 dp).main :: weth10Aux)
      (transferAfterCredit continuation) = true)
    (zeroFree : Func.sstoreFreeWithin zeroFuel
      ((weth10 dp).main :: weth10Aux)
      continuation = true) :
    (Sevm.argWord frame.sevm 0 ≠ 0 ∧
      BalanceSstoreRole ca stepPre
        (.transfer frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 0)
          frame.sevm.caller (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toNat)
        holder value) ∨
    (Sevm.argWord frame.sevm 0 = 0 ∧
      BalanceSstoreRole ca stepPre
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat)
        holder value) := by
  rcases cursor.balanceSstoreOccurrence_transferThen fromCursor with
    ⟨rawNonzero, armCursor, insideArm⟩ |
      ⟨rawZero, armCursor, insideArm⟩
  · exact Or.inl ⟨rawNonzero,
      armCursor.balanceSstoreRole_transferNonzeroThen insideArm occurrence
        context nonzeroFree⟩
  · exact Or.inr ⟨rawZero,
      armCursor.balanceSstoreRole_transferZeroThen insideArm occurrence
        context zeroFree⟩

/-- Package the two exact source roles of `transfer` against the executable
frame classifier. -/
private theorem Exec.Frame.CompiledCursor.classifyBalanceSstore_transfer
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) transfer frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = transferSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferThen returnTrue) frame.post at cursor
  have nonzeroFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux)
      (transferAfterCredit returnTrue) = true := by
    rfl
  have zeroFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux)
      returnTrue = true := by
    rfl
  rcases cursor.balanceSstoreRole_transferThen fromCursor occurrence context
      nonzeroFree zeroFree with
    ⟨rawNonzero, role⟩ | ⟨rawZero, role⟩
  · have primary : primaryFlowAtom frame.sevm = some
        (.transfer frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 0)
          frame.sevm.caller (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toNat) := by
      simp [primaryFlowAtom, nonempty, selectorEq,
        transferSelector_ne_depositSelector,
        transferSelector_ne_depositToSelector,
        transferSelector_ne_depositToAndCallSelector, rawNonzero]
    exact occurrence.classify_of_primary_role context primary role
  · have primary : primaryFlowAtom frame.sevm = some
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat) := by
      simp [primaryFlowAtom, nonempty, selectorEq,
        transferSelector_ne_depositSelector,
        transferSelector_ne_depositToSelector,
        transferSelector_ne_depositToAndCallSelector, rawZero]
    exact occurrence.classify_of_primary_role context primary role

/-- Package the same two exact transfer roles when the committed source suffix
continues into the ERC-677 callback.  The certificate covers only that local
callback source and its fixed error helpers. -/
private theorem Exec.Frame.CompiledCursor.classifyBalanceSstore_transferAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) transferAndCall frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = transferAndCallSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  let callback :=
    callBoolCallback onTokenTransferSelector 0 2 (arg 1)
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (transferThen callback) frame.post at cursor
  have callbackFree : Func.sstoreFreeWithin 1024
      ((weth10 dp).main :: weth10Aux) callback = true := by
    rfl
  have nonzeroFree : Func.sstoreFreeWithin 2048
      ((weth10 dp).main :: weth10Aux)
      (transferAfterCredit callback) = true := by
    rfl
  rcases cursor.balanceSstoreRole_transferThen fromCursor occurrence context
      nonzeroFree callbackFree with
    ⟨rawNonzero, role⟩ | ⟨rawZero, role⟩
  · have primary : primaryFlowAtom frame.sevm = some
        (.transfer frame.sevm.caller.toB256 (Sevm.argWord frame.sevm 0)
          frame.sevm.caller (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toNat) := by
      simp [primaryFlowAtom, nonempty, selectorEq,
        transferAndCallSelector_ne_depositSelector,
        transferAndCallSelector_ne_depositToSelector,
        transferAndCallSelector_ne_depositToAndCallSelector,
        transferAndCallSelector_ne_transferSelector, rawNonzero]
    exact occurrence.classify_of_primary_role context primary role
  · have primary : primaryFlowAtom frame.sevm = some
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat) := by
      simp [primaryFlowAtom, nonempty, selectorEq,
        transferAndCallSelector_ne_depositSelector,
        transferAndCallSelector_ne_depositToSelector,
        transferAndCallSelector_ne_depositToAndCallSelector,
        transferAndCallSelector_ne_transferSelector, rawZero]
    exact occurrence.classify_of_primary_role context primary role

private def argDebitGuardLine (ownerArg amountArg : B256) : Line :=
  loadArgBalanceAmount ownerArg amountArg ++ balanceTooSmall

private def argDebitSource (ownerArg amountArg : B256)
    (errorSlot : Nat) (continuation : Func) : Func :=
  argDebitGuardLine ownerArg amountArg +++
    (.branch (debitLoadedBalance +++ continuation) (.call errorSlot))

/-- Follow a successful normalized-owner balance guard to the exact debit
cursor.  The owner key is reconstructed from the executed `addressArg`, not
from an endpoint storage comparison. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_argDebit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {ownerArg amountArg : B256} {errorSlot fuel : Nat}
    {errorBody continuation : Func}
    {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (argDebitSource ownerArg amountArg errorSlot continuation) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (context : frame.AuthenticContext dp ca)
    (errorLookup : (((weth10 dp).main :: weth10Aux)[errorSlot]?) =
      some errorBody)
    (errorFree : Func.sstoreFreeWithin fuel
      ((weth10 dp).main :: weth10Aux) errorBody = true) :
    ∃ (balance : B256)
        (debitCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          (debitLoadedBalance +++ continuation) final),
      [balance, Sevm.argWord frame.sevm amountArg,
          (Sevm.argWord frame.sevm ownerArg).toAdr.toB256] <<+
        debitCursor.pre.stack ∧
      balance = (Devm.getStor debitCursor.pre ca).get
        (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 ∧
      frame.NinstOccurrenceFromCursor debitCursor (.reg .sstore)
        stepPre stepPost slot := by
  rcases cursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [argDebitGuardLine, loadArgBalanceAmount, balanceTooSmall,
          addressArg, normalizeAddress, pushAddressMask, arg, cdl,
          Ninst.pushB256] at hn) fromCursor with
    ⟨branchCursor, guardRun, atBranch⟩
  rcases of_run_append (loadArgBalanceAmount ownerArg amountArg) guardRun with
    ⟨afterLoad, loadRun, guardTailRun⟩
  rcases prefix_of_loadArgBalanceAmount ownerArg amountArg nil_pref loadRun with
    ⟨balance, runtimeKey, runtimeKeyEq, balanceEq, loadPrefix⟩
  have guardPrefix :
      (balance <? Sevm.argWord frame.sevm amountArg) :: balance ::
        Sevm.argWord frame.sevm amountArg :: runtimeKey :: [] <<+
          branchCursor.pre.stack :=
    prefix_of_balanceTooSmall loadPrefix guardTailRun
  rcases branchCursor.balanceSstoreOccurrence_branchWithFlag atBranch with
    ⟨debitCursor, pop, insideDebit⟩ |
      ⟨_flag, _nonzero, errorCursor, _pop, insideError⟩
  · have rawDebitPrefix :
        [balance, Sevm.argWord frame.sevm amountArg, runtimeKey] <<+
          debitCursor.pre.stack :=
      prefix_of_pop ⟨0, Devm.PopBurn.of_popBurnBy pop⟩ guardPrefix
    have normalizedEq : runtimeKey =
        (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 := by
      rw [runtimeKeyEq]
      exact normalizedAddressArg_eq_toAdr_toB256_writeCompleteness _ _
    have debitPrefix :
        [balance, Sevm.argWord frame.sevm amountArg,
          (Sevm.argWord frame.sevm ownerArg).toAdr.toB256] <<+
            debitCursor.pre.stack := by
      rw [← normalizedEq]
      exact rawDebitPrefix
    have storLoad : Devm.getStor cursor.pre = Devm.getStor afterLoad :=
      Line.of_inv Devm.getStor (by line_inv) loadRun
    have storGuard : Devm.getStor afterLoad =
        Devm.getStor branchCursor.pre :=
      Line.of_inv Devm.getStor (by line_inv) guardTailRun
    have storPop : Devm.getStor branchCursor.pre =
        Devm.getStor debitCursor.pre :=
      PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy pop)
    have balanceAtDebit : balance =
        (Devm.getStor debitCursor.pre ca).get
          (Sevm.argWord frame.sevm ownerArg).toAdr.toB256 := by
      rw [balanceEq, storLoad, storGuard, storPop,
        context.invocation.2.1, normalizedEq]
    exact ⟨balance, debitCursor, debitPrefix, balanceAtDebit, insideDebit⟩
  · rcases errorCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideError with
      ⟨actualError, actualLookup, errorBodyCursor, insideErrorBody⟩
    have errorEq : actualError = errorBody :=
      Option.some.inj (actualLookup.symm.trans errorLookup)
    subst actualError
    exact (errorBodyCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 errorFree insideErrorBody).elim

private def spendAllowanceLoadLine : Line :=
  arg 0 ++ mstoreAt 0 ++ [Ninst.caller] ++ mstoreAt 1 ++
    allowanceKeyFromMemory ++
    [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ isMax

private def spendAllowanceCheckLine (amount : B256) : Line :=
  arg amount ++ [Ninst.swap 0] ++ balanceTooSmall

private def spendAllowanceBeforeStore : Line :=
  [Ninst.sub, Ninst.dup 0, Ninst.swap 1]

private def spendAllowanceAfterStore (nextSlot : Nat) : Func :=
  (arg 0 ++ [Ninst.swap 0, Ninst.caller] ++ emitApproval ++
    [Ninst.pop, Ninst.pop]) +++ .call nextSlot

/-- A balance-region occurrence cannot be the delegated wrapper's finite
allowance update: the executed key is reconstructed as a tagged allowance key
and is therefore not address-shaped.  Every retained balance write is carried
through the exact selected internal call to the requested core body. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_spendCallerAllowanceThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {amount : B256} {nextSlot : Nat}
    {final stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (spendCallerAllowanceThen amount nextSlot) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    ∃ body,
      (((weth10 dp).main :: weth10Aux)[nextSlot]?) = some body ∧
      ∃ bodyCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux)) body final,
        frame.NinstOccurrenceFromCursor bodyCursor (.reg .sstore)
          stepPre stepPost slot := by
  unfold spendCallerAllowanceThen at cursor
  rcases cursor.balanceSstoreOccurrence_after_line
      (line := arg 0 ++ [Ninst.caller, Ninst.eq])
      (by
        rintro n hn rfl
        simp [arg, cdl, Ninst.pushB256] at hn) fromCursor with
    ⟨callerBranchCursor, _callerRun, atCallerBranch⟩
  rcases callerBranchCursor.balanceSstoreOccurrence_branch atCallerBranch with
    ⟨allowanceCursor, insideAllowance⟩ |
      ⟨directCallCursor, insideDirectCall⟩
  · change frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (spendAllowanceLoadLine +++
          (.branch
            (spendAllowanceCheckLine amount +++
              (.branch
                (spendAllowanceBeforeStore +++
                  (.next (.reg .sstore)
                    (spendAllowanceAfterStore nextSlot)))
                (.call allowanceErrorSlot)))
            ([Ninst.pop, Ninst.pop] +++ .call nextSlot)))
        final at allowanceCursor
    rcases allowanceCursor.balanceSstoreOccurrence_after_line
        (by
          rintro n hn rfl
          simp [spendAllowanceLoadLine, arg, cdl, mstoreAt,
            allowanceKeyFromMemory, pushList, isMax,
            Ninst.pushB256] at hn) insideAllowance with
      ⟨maxBranchCursor, allowanceRun, atMaxBranch⟩
    rcases prefix_of_callerAllowanceIsMax 0 nil_pref allowanceRun with
      ⟨hash, allowance, _allowanceEq, allowancePrefix⟩
    rcases maxBranchCursor.balanceSstoreOccurrence_branchWithFlag
        atMaxBranch with
      ⟨finiteCursor, finitePop, insideFinite⟩ |
        ⟨_maxFlag, _maxNonzero, maxCursor, _maxPop, insideMax⟩
    · have finitePrefix : allowance ::
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
            finiteCursor.pre.stack :=
        prefix_of_pop
          ⟨0, Devm.PopBurn.of_popBurnBy finitePop⟩ allowancePrefix
      rcases finiteCursor.balanceSstoreOccurrence_after_line
          (by
            rintro n hn rfl
            simp [spendAllowanceCheckLine, arg, cdl, balanceTooSmall,
              Ninst.pushB256] at hn) insideFinite with
        ⟨spendBranchCursor, checkRun, atSpendBranch⟩
      rcases of_run_append (arg amount) checkRun with
        ⟨afterAmount, amountRun, afterAmountRun⟩
      rcases Line.of_run_cons afterAmountRun with
        ⟨afterSwap, swapStep, guardRun⟩
      have amountPrefix : Sevm.argWord frame.sevm amount :: allowance ::
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
            afterAmount.stack :=
        prefix_of_arg finitePrefix amountRun
      have swapCore : Stack.Swap (0 : Fin 16).val
          (Sevm.argWord frame.sevm amount :: allowance ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [])
          (allowance :: Sevm.argWord frame.sevm amount ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: []) :=
        Stack.swapCore_zero
      have swappedPrefix : allowance :: Sevm.argWord frame.sevm amount ::
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
            afterSwap.stack :=
        Stack.prefix_of_swap swapCore (of_run_swap swapStep) amountPrefix
      have guardPrefix :
          (allowance <? Sevm.argWord frame.sevm amount) :: allowance ::
            Sevm.argWord frame.sevm amount ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
              spendBranchCursor.pre.stack :=
        prefix_of_balanceTooSmall swappedPrefix guardRun
      rcases spendBranchCursor.balanceSstoreOccurrence_branchWithFlag
          atSpendBranch with
        ⟨successCursor, successPop, insideSuccess⟩ |
          ⟨_errorFlag, _errorNonzero, errorCallCursor, _errorPop,
            insideError⟩
      · have successPrefix : allowance ::
            Sevm.argWord frame.sevm amount ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
              successCursor.pre.stack :=
          prefix_of_pop
            ⟨0, Devm.PopBurn.of_popBurnBy successPop⟩ guardPrefix
        rcases successCursor.balanceSstoreOccurrence_after_line
            (by simp [spendAllowanceBeforeStore]) insideSuccess with
          ⟨storeCursor, beforeStoreRun, atStore⟩
        rcases Line.of_run_cons beforeStoreRun with
          ⟨afterSub, subStep, afterSubRun⟩
        rcases Line.of_run_cons afterSubRun with
          ⟨afterDup, dupStep, afterDupRun⟩
        rcases Line.of_run_cons afterDupRun with
          ⟨afterSwap, storeSwapStep, emptyLine⟩
        cases emptyLine
        have reducedPrefix :
            (allowance - Sevm.argWord frame.sevm amount) ::
              (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
                afterSub.stack :=
          prefix_of_sub subStep successPrefix
        have duplicatePrefix :
            (allowance - Sevm.argWord frame.sevm amount) ::
              (allowance - Sevm.argWord frame.sevm amount) ::
              (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
                afterDup.stack :=
          prefix_of_dup_val dupStep (by show_nth) reducedPrefix
        have storeSwapCore : Stack.Swap (1 : Fin 16).val
            ((allowance - Sevm.argWord frame.sevm amount) ::
              (allowance - Sevm.argWord frame.sevm amount) ::
              (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [])
            ((allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
              (allowance - Sevm.argWord frame.sevm amount) ::
              (allowance - Sevm.argWord frame.sevm amount) :: []) :=
          Stack.swapCore_succ Stack.swapCore_zero
        have storePrefix :
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
              (allowance - Sevm.argWord frame.sevm amount) ::
              (allowance - Sevm.argWord frame.sevm amount) :: [] <<+
                storeCursor.pre.stack :=
          Stack.prefix_of_swap storeSwapCore
            (of_run_swap storeSwapStep) duplicatePrefix
        rcases storeCursor.ninstOccurrenceFromCursor_head_or_tail atStore with
          ⟨_sourceEq, preEq⟩ |
            ⟨tailCursor, _sourceSlot, _sourceOccurrence, insideTail⟩
        · subst stepPre
          rcases occurrence.2.2.2 with
            ⟨occurrenceTail, occurrencePrefix⟩
          have occurrencePairPrefix : [key, value] <<+
              storeCursor.pre.stack :=
            pref_trans (pref_append [key, value] occurrenceTail)
              occurrencePrefix
          have expectedPairPrefix :
              [allowanceTagWord ||| (allowancePayloadMask &&& hash),
                allowance - Sevm.argWord frame.sevm amount] <<+
                  storeCursor.pre.stack :=
            pref_trans
              (pref_append
                [allowanceTagWord ||| (allowancePayloadMask &&& hash),
                  allowance - Sevm.argWord frame.sevm amount]
                [allowance - Sevm.argWord frame.sevm amount])
              storePrefix
          have pairEq : [key, value] =
              [allowanceTagWord ||| (allowancePayloadMask &&& hash),
                allowance - Sevm.argWord frame.sevm amount] :=
            List.pref_unique (by simp) occurrencePairPrefix
              expectedPairPrefix
          injection pairEq with keyEq _valueTailEq
          exact (runtimeAllowanceKey_not_valid hash
            (keyEq ▸ occurrence.2.1)).elim
        · rcases tailCursor.balanceSstoreOccurrence_after_line
              (by
                rintro n hn rfl
                simp [arg, cdl, emitApproval,
                  mstoreAt, logWith, Ninst.pushB256] at hn)
              insideTail with
            ⟨coreCallCursor, _afterStoreRun, insideCoreCall⟩
          exact coreCallCursor.balanceSstoreOccurrence_call
            context.invocation.2.2.2 insideCoreCall
      · rcases errorCallCursor.balanceSstoreOccurrence_call
            context.invocation.2.2.2 insideError with
          ⟨errorBody, errorLookup, errorBodyCursor, insideErrorBody⟩
        have bodyEq : errorBody = allowanceError := by
          simpa [allowanceErrorSlot, weth10, weth10Aux] using
            errorLookup.symm
        subst errorBody
        exact (errorBodyCursor.no_balanceSstoreOccurrence_of_free
          context.invocation.2.2.2 (allowanceError_sstoreFree _)
          insideErrorBody).elim
    · rcases maxCursor.balanceSstoreOccurrence_after_line
          (by simp) insideMax with
        ⟨coreCallCursor, _popRun, insideCoreCall⟩
      exact coreCallCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideCoreCall
  · exact directCallCursor.balanceSstoreOccurrence_call
      context.invocation.2.2.2 insideDirectCall

private def transferFromAfterCredit : Func :=
  (addressArg 0 ++ arg 2 ++ addressArg 1 ++ emitTransfer) +++ returnTrue

private def transferFromCreditSource : Func :=
  creditAddressArgSource 1 2 transferFromAfterCredit

private theorem transferFromNonzero_eq_argDebitSource :
    transferFromNonzero =
      argDebitSource 0 2 transferBalanceErrorSlot
        transferFromCreditSource := by
  rfl

private def transferFromZeroAfterDebitPrefix : Line :=
  addressArg 0 ++ arg 2 ++ [Ninst.pushB256 0] ++ emitTransfer ++
    [Ninst.swap 0, Ninst.pop] ++ sendValueToCaller ++ [Ninst.iszero]

private def transferFromZeroAfterDebit : Func :=
  addressArg 0 +++ arg 2 +++ Ninst.pushB256 0 ::: emitTransfer +++
  Ninst.swap 0 ::: Ninst.pop :::
  sendValueToCaller +++ Ninst.iszero :::
  ((.call ethTransferErrorSlot) <?> returnTrue)

private theorem transferFromZeroAfterDebit_eq_successOrError :
    transferFromZeroAfterDebit =
      transferFromZeroAfterDebitPrefix +++
        (.branch returnTrue (.call ethTransferErrorSlot)) := by
  simp only [transferFromZeroAfterDebit, transferFromZeroAfterDebitPrefix,
    prepend_append_writeCompleteness, List.append_assoc, prepend]

private theorem transferFromZero_eq_argDebitSource :
    transferFromZero =
      argDebitSource 0 2 burnBalanceErrorSlot transferFromZeroAfterDebit := by
  rfl

private def transferFromSelectLine_writeCompleteness : Line :=
  arg 1 ++ [Ninst.iszero]

private theorem transferFromCore_eq_select_writeCompleteness :
    transferFromCore =
      transferFromSelectLine_writeCompleteness +++
        (.branch transferFromNonzero transferFromZero) := by
  rfl

/-- Follow the actual raw recipient test in `transferFromCore`, retaining the
selected exact body cursor and the raw-word fact that chose it. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreOccurrence_transferFromCore
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) transferFromCore final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    (Sevm.argWord frame.sevm 1 ≠ 0 ∧
      ∃ armCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          transferFromNonzero final,
        frame.NinstOccurrenceFromCursor armCursor (.reg .sstore)
          stepPre stepPost slot) ∨
    (Sevm.argWord frame.sevm 1 = 0 ∧
      ∃ armCursor : frame.CompiledCursor dp ca
          ((weth10 dp).main :: weth10Aux)
          (table 0 ((weth10 dp).main :: weth10Aux))
          transferFromZero final,
        frame.NinstOccurrenceFromCursor armCursor (.reg .sstore)
          stepPre stepPost slot) := by
  rcases cursor.castSourceWithOccurrence
      transferFromCore_eq_select_writeCompleteness fromCursor with
    ⟨selectCursor, _selectPre, fromSelect⟩
  rcases selectCursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [transferFromSelectLine_writeCompleteness, arg, cdl,
          Ninst.pushB256] at hn) fromSelect with
    ⟨branchCursor, selectRun, atBranch⟩
  rcases of_run_append (arg 1) selectRun with
    ⟨afterArg, argRun, afterArgRun⟩
  rcases Line.of_run_cons afterArgRun with
    ⟨afterZero, zeroStep, emptyLine⟩
  cases emptyLine
  have argPrefix : [Sevm.argWord frame.sevm 1] <<+ afterArg.stack :=
    prefix_of_arg nil_pref argRun
  have flagPrefix : [Sevm.argWord frame.sevm 1 =? 0] <<+
      branchCursor.pre.stack :=
    prefix_of_iszero zeroStep argPrefix
  rcases branchCursor.balanceSstoreOccurrence_branchWithFlag atBranch with
    ⟨nonzeroCursor, pop, insideNonzero⟩ |
      ⟨flag, flagNonzero, zeroCursor, pop, insideZero⟩
  · have selectedPrefix : [(0 : B256)] <<+ branchCursor.pre.stack :=
      pref_of_split pop.stack
    have flagEq : (Sevm.argWord frame.sevm 1 =? 0) = 0 :=
      pref_head_unique flagPrefix selectedPrefix
    have rawNonzero : Sevm.argWord frame.sevm 1 ≠ 0 := by
      intro rawZero
      rw [rawZero] at flagEq
      simp [B256.eqCheck] at flagEq
      exact (by decide : (1 : B256) ≠ 0) flagEq
    exact Or.inl ⟨rawNonzero, nonzeroCursor, insideNonzero⟩
  · have selectedPrefix : [flag] <<+ branchCursor.pre.stack :=
      pref_of_split pop.stack
    have flagEq : (Sevm.argWord frame.sevm 1 =? 0) = flag :=
      pref_head_unique flagPrefix selectedPrefix
    have rawZero : Sevm.argWord frame.sevm 1 = 0 := by
      by_contra rawNonzero
      have checkZero : (Sevm.argWord frame.sevm 1 =? 0) = 0 := by
        simp [B256.eqCheck, rawNonzero]
      apply flagNonzero
      rw [← flagEq]
      exact checkZero
    exact Or.inr ⟨rawZero, zeroCursor, insideZero⟩

private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_transferFromNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      transferFromNonzero frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    BalanceSstoreRole ca stepPre
      (.transfer (Sevm.argWord frame.sevm 0) (Sevm.argWord frame.sevm 1)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toAdr
        (Sevm.argWord frame.sevm 2).toNat)
      holder value := by
  rcases cursor.castSourceWithOccurrence
      transferFromNonzero_eq_argDebitSource fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  have errorLookup :
      (((weth10 dp).main :: weth10Aux)[transferBalanceErrorSlot]?) =
        some transferBalanceError := by
    simp [transferBalanceErrorSlot, weth10, weth10Aux]
  have errorFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux) transferBalanceError = true :=
    transferBalanceError_sstoreFree _
  rcases sourceCursor.balanceSstoreOccurrence_argDebit fromSource context
      errorLookup errorFree with
    ⟨balance, debitCursor, debitPrefix, balanceEq, insideDebit⟩
  rcases debitCursor.balanceSstoreOccurrence_debitLoadedBalance
      insideDebit occurrence debitPrefix balanceEq with
    ⟨holderEq, valueEq⟩ | ⟨creditCursor, insideCredit⟩
  · subst holder
    rw [valueEq]
    simpa only [Jaune.toB256_toNat] using
      (BalanceSstoreRole.transferDebit
        (ca := ca) (stepPre := stepPre)
        (Sevm.argWord frame.sevm 0) (Sevm.argWord frame.sevm 1)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toAdr
        (Sevm.argWord frame.sevm 2).toNat)
  · rcases creditCursor.balanceSstoreOccurrence_creditAddressArg
        insideCredit occurrence context with
      ⟨holderEq, valueEq⟩ | ⟨tailCursor, insideTail⟩
    · subst holder
      rw [valueEq]
      simpa only [Jaune.toB256_toNat] using
        (BalanceSstoreRole.transferCredit
          (ca := ca) (stepPre := stepPre)
          (Sevm.argWord frame.sevm 0) (Sevm.argWord frame.sevm 1)
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toAdr
          (Sevm.argWord frame.sevm 2).toNat)
    · have freeTail : Func.sstoreFreeWithin 512
          ((weth10 dp).main :: weth10Aux) transferFromAfterCredit = true := by
        rfl
      exact (tailCursor.no_balanceSstoreOccurrence_of_free
        context.invocation.2.2.2 freeTail insideTail).elim

private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_transferFromZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      transferFromZero frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    BalanceSstoreRole ca stepPre
      (.redemption (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr frame.sevm.caller
        (Sevm.argWord frame.sevm 2).toNat)
      holder value := by
  rcases cursor.castSourceWithOccurrence
      transferFromZero_eq_argDebitSource fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  have errorLookup :
      (((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]?) =
        some burnBalanceError := by
    simp [burnBalanceErrorSlot, weth10, weth10Aux]
  have errorFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux) burnBalanceError = true :=
    burnBalanceError_sstoreFree _
  rcases sourceCursor.balanceSstoreOccurrence_argDebit fromSource context
      errorLookup errorFree with
    ⟨balance, debitCursor, debitPrefix, balanceEq, insideDebit⟩
  rcases debitCursor.balanceSstoreOccurrence_debitLoadedBalance
      insideDebit occurrence debitPrefix balanceEq with
    ⟨holderEq, valueEq⟩ | ⟨tailCursor, insideTail⟩
  · subst holder
    rw [valueEq]
    simpa only [Jaune.toB256_toNat] using
      (BalanceSstoreRole.redemptionDebit
        (ca := ca) (stepPre := stepPre)
        (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr frame.sevm.caller
        (Sevm.argWord frame.sevm 2).toNat)
  · rcases tailCursor.castSourceWithOccurrence
        transferFromZeroAfterDebit_eq_successOrError insideTail with
      ⟨tailSplitCursor, _tailPre, insideTailSplit⟩
    have successFree : Func.sstoreFreeWithin 256
        ((weth10 dp).main :: weth10Aux) returnTrue = true := by
      rfl
    have transferErrorLookup :
        (((weth10 dp).main :: weth10Aux)[ethTransferErrorSlot]?) =
          some ethTransferError := by
      simp [ethTransferErrorSlot, weth10, weth10Aux]
    have transferErrorFree : Func.sstoreFreeWithin 256
        ((weth10 dp).main :: weth10Aux) ethTransferError = true :=
      ethTransferError_sstoreFree _
    exact (tailSplitCursor.no_balanceSstoreOccurrence_successOrError
      (by
        rintro n hn rfl
        simp [transferFromZeroAfterDebitPrefix, addressArg,
          normalizeAddress, pushAddressMask, sendValueToCaller, pushList,
          emitTransfer, Blanc.transferFromLog, arg, cdl, mstoreAt,
          logWith, Ninst.pushB256] at hn)
      context successFree transferErrorLookup transferErrorFree
      insideTailSplit).elim

/-- Package all balance writes reached through the delegated allowance wrapper
for `transferFrom`; the wrapper's own finite allowance write has already been
excluded by its tagged runtime key. -/
private theorem Exec.Frame.CompiledCursor.classifyBalanceSstore_transferFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) transferFrom frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = transferFromSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 transferFromCoreSlot) frame.post at cursor
  rcases cursor.balanceSstoreOccurrence_spendCallerAllowanceThen
      fromCursor occurrence context with
    ⟨body, bodyLookup, coreCursor, insideCore⟩
  have bodyEq : body = transferFromCore := by
    simpa [transferFromCoreSlot, weth10, weth10Aux] using bodyLookup.symm
  subst body
  rcases coreCursor.balanceSstoreOccurrence_transferFromCore insideCore with
    ⟨rawNonzero, armCursor, insideArm⟩ |
      ⟨rawZero, armCursor, insideArm⟩
  · have role := armCursor.balanceSstoreRole_transferFromNonzero
      insideArm occurrence context
    have primary : primaryFlowAtom frame.sevm = some
        (.transfer (Sevm.argWord frame.sevm 0) (Sevm.argWord frame.sevm 1)
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toAdr
          (Sevm.argWord frame.sevm 2).toNat) := by
      simp [primaryFlowAtom, nonempty, selectorEq,
        transferFromSelector_ne_depositSelector,
        transferFromSelector_ne_depositToSelector,
        transferFromSelector_ne_depositToAndCallSelector,
        transferFromSelector_ne_transferSelector,
        transferFromSelector_ne_transferAndCallSelector,
        rawNonzero]
    exact occurrence.classify_of_primary_role context primary role
  · have role := armCursor.balanceSstoreRole_transferFromZero
      insideArm occurrence context
    have primary : primaryFlowAtom frame.sevm = some
        (.redemption (Sevm.argWord frame.sevm 0)
          (Sevm.argWord frame.sevm 0).toAdr frame.sevm.caller
          (Sevm.argWord frame.sevm 2).toNat) := by
      simp [primaryFlowAtom, nonempty, selectorEq,
        transferFromSelector_ne_depositSelector,
        transferFromSelector_ne_depositToSelector,
        transferFromSelector_ne_depositToAndCallSelector,
        transferFromSelector_ne_transferSelector,
        transferFromSelector_ne_transferAndCallSelector,
        rawZero]
    exact occurrence.classify_of_primary_role context primary role

private def withdrawFromAfterDebitPrefix : Line :=
  addressArg 0 ++ arg 2 ++ [Ninst.pushB256 0] ++ emitTransfer ++
    [Ninst.swap 0, Ninst.pop] ++ sendValueToArg 1 ++ [Ninst.iszero]

private def withdrawFromAfterDebit : Func :=
  addressArg 0 +++ arg 2 +++ Ninst.pushB256 0 ::: emitTransfer +++
  Ninst.swap 0 ::: Ninst.pop :::
  sendValueToArg 1 +++ Ninst.iszero :::
  ((.call etherTransferErrorSlot) <?> Func.stop)

private theorem withdrawFromAfterDebit_eq_stopOrError :
    withdrawFromAfterDebit =
      withdrawFromAfterDebitPrefix +++
        (.branch Func.stop (.call etherTransferErrorSlot)) := by
  simp only [withdrawFromAfterDebit, withdrawFromAfterDebitPrefix,
    prepend_append_writeCompleteness, List.append_assoc, prepend]

private theorem withdrawFromCore_eq_argDebitSource :
    withdrawFromCore =
      argDebitSource 0 2 burnBalanceErrorSlot withdrawFromAfterDebit := by
  rfl

private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_withdrawFromCore
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      withdrawFromCore frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    BalanceSstoreRole ca stepPre
      (.redemption (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toAdr
        (Sevm.argWord frame.sevm 2).toNat)
      holder value := by
  rcases cursor.castSourceWithOccurrence withdrawFromCore_eq_argDebitSource
      fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  have errorLookup :
      (((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]?) =
        some burnBalanceError := by
    simp [burnBalanceErrorSlot, weth10, weth10Aux]
  have errorFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux) burnBalanceError = true :=
    burnBalanceError_sstoreFree _
  rcases sourceCursor.balanceSstoreOccurrence_argDebit fromSource context
      errorLookup errorFree with
    ⟨balance, debitCursor, debitPrefix, balanceEq, insideDebit⟩
  rcases debitCursor.balanceSstoreOccurrence_debitLoadedBalance
      insideDebit occurrence debitPrefix balanceEq with
    ⟨holderEq, valueEq⟩ | ⟨tailCursor, insideTail⟩
  · subst holder
    rw [valueEq]
    simpa only [Jaune.toB256_toNat] using
      (BalanceSstoreRole.redemptionDebit
        (ca := ca) (stepPre := stepPre)
        (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toAdr
        (Sevm.argWord frame.sevm 2).toNat)
  · rcases tailCursor.castSourceWithOccurrence
        withdrawFromAfterDebit_eq_stopOrError insideTail with
      ⟨tailSplitCursor, _tailPre, insideTailSplit⟩
    have errorLookup :
        (((weth10 dp).main :: weth10Aux)[etherTransferErrorSlot]?) =
          some etherTransferError := by
      simp [etherTransferErrorSlot, weth10, weth10Aux]
    exact (tailSplitCursor.no_balanceSstoreOccurrence_stopOrError
      (by
        rintro n hn rfl
        simp [withdrawFromAfterDebitPrefix, addressArg,
          normalizeAddress, pushAddressMask, sendValueToArg, pushList,
          emitTransfer, Blanc.transferFromLog, arg, cdl, mstoreAt,
          logWith, Ninst.pushB256] at hn)
      context errorLookup (etherTransferError_sstoreFree _)
      insideTailSplit).elim

private theorem Exec.Frame.CompiledCursor.classifyBalanceSstore_withdrawFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) withdrawFrom frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = withdrawFromSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (spendCallerAllowanceThen 2 withdrawFromCoreSlot) frame.post at cursor
  rcases cursor.balanceSstoreOccurrence_spendCallerAllowanceThen
      fromCursor occurrence context with
    ⟨body, bodyLookup, coreCursor, insideCore⟩
  have bodyEq : body = withdrawFromCore := by
    simpa [withdrawFromCoreSlot, weth10, weth10Aux] using bodyLookup.symm
  subst body
  have role := coreCursor.balanceSstoreRole_withdrawFromCore
    insideCore occurrence context
  have primary : primaryFlowAtom frame.sevm = some
      (.redemption (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toAdr
        (Sevm.argWord frame.sevm 2).toNat) := by
    simp [primaryFlowAtom, nonempty, selectorEq,
      withdrawFromSelector_ne_depositSelector,
      withdrawFromSelector_ne_depositToSelector,
      withdrawFromSelector_ne_depositToAndCallSelector,
      withdrawFromSelector_ne_transferSelector,
      withdrawFromSelector_ne_transferAndCallSelector,
      withdrawFromSelector_ne_transferFromSelector,
      withdrawFromSelector_ne_withdrawSelector,
      withdrawFromSelector_ne_withdrawToSelector]
  exact occurrence.classify_of_primary_role context primary role

private def flashBurnAfterDebitBeforeSlot : Line :=
  addressArg 0 ++ arg 2 ++ [Ninst.pushB256 0] ++ emitTransfer ++
    [Ninst.pop, Ninst.pop] ++ pushFlashMintedSlot ++ [Ninst.sload] ++
    arg 2 ++ [Ninst.swap 0, Ninst.sub]

private def flashBurnAfterDebitBeforeStore : Line :=
  flashBurnAfterDebitBeforeSlot ++ pushFlashMintedSlot

private def flashBurnAfterDebit : Func :=
  flashBurnAfterDebitBeforeStore +++
    (.next (.reg .sstore) returnTrue)

private theorem flashBurn_eq_argDebitSource :
    flashBurn =
      argDebitSource 0 2 burnBalanceErrorSlot flashBurnAfterDebit := by
  simp only [flashBurn, argDebitSource, argDebitGuardLine,
    flashBurnAfterDebit, flashBurnAfterDebitBeforeStore,
    flashBurnAfterDebitBeforeSlot, prepend_append_writeCompleteness,
    List.append_assoc, prepend]

/-- Every address-shaped write in the flash burn continuation is the receiver
repayment debit.  The later all-ones flash-counter write is excluded at its
actual immediate stack key. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_flashBurn
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashBurn frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    BalanceSstoreRole ca stepPre
      (.flashPair (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2).toNat)
      holder value := by
  rcases cursor.castSourceWithOccurrence flashBurn_eq_argDebitSource
      fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  have errorLookup :
      (((weth10 dp).main :: weth10Aux)[burnBalanceErrorSlot]?) =
        some burnBalanceError := by
    simp [burnBalanceErrorSlot, weth10, weth10Aux]
  rcases sourceCursor.balanceSstoreOccurrence_argDebit fromSource context
      errorLookup (burnBalanceError_sstoreFree _) with
    ⟨balance, debitCursor, debitPrefix, balanceEq, insideDebit⟩
  rcases debitCursor.balanceSstoreOccurrence_debitLoadedBalance
      insideDebit occurrence debitPrefix balanceEq with
    ⟨holderEq, valueEq⟩ | ⟨tailCursor, insideTail⟩
  · subst holder
    rw [valueEq]
    simpa only [Jaune.toB256_toNat] using
      (BalanceSstoreRole.flashRepayment
        (ca := ca) (stepPre := stepPre)
        (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2).toNat)
  · rcases tailCursor.balanceSstoreOccurrence_after_line
        (by
          rintro n hn rfl
          simp [flashBurnAfterDebitBeforeStore,
            flashBurnAfterDebitBeforeSlot, addressArg, normalizeAddress,
            pushAddressMask, pushFlashMintedSlot, emitTransfer,
            Blanc.transferFromLog, arg, cdl, mstoreAt, logWith,
            Ninst.pushB256] at hn) insideTail with
      ⟨storeCursor, beforeStoreRun, atStore⟩
    rcases of_run_append flashBurnAfterDebitBeforeSlot beforeStoreRun with
      ⟨beforeSlot, _beforeSlotRun, slotRun⟩
    change Line.Run frame.sevm beforeSlot
      [Ninst.pushB256 0, Ninst.not] storeCursor.pre at slotRun
    rcases Line.of_run_cons slotRun with
      ⟨afterPush, pushStep, afterPushRun⟩
    rcases Line.of_run_cons afterPushRun with
      ⟨afterNot, notStep, emptyLine⟩
    cases emptyLine
    have zeroPrefix : [(0 : B256)] <<+ afterPush.stack :=
      prefix_of_push (of_run_pushB256 pushStep) nil_pref
    have flashPrefix : [flashMintedSlot] <<+ storeCursor.pre.stack := by
      have zeroNot : (~~~ (0 : B256)) = flashMintedSlot := rfl
      rw [← zeroNot]
      exact prefix_of_not notStep zeroPrefix
    rcases storeCursor.ninstOccurrenceFromCursor_head_or_tail atStore with
      ⟨_sourceEq, preEq⟩ |
        ⟨returnCursor, _sourceSlot, _sourceOccurrence, insideReturn⟩
    · subst stepPre
      rcases occurrence.2.2.2 with ⟨occurrenceTail, occurrencePrefix⟩
      have occurrenceKeyPrefix : [key] <<+ storeCursor.pre.stack :=
        pref_trans (pref_append [key] (value :: occurrenceTail))
          occurrencePrefix
      have keyEq : key = flashMintedSlot :=
        pref_head_unique occurrenceKeyPrefix flashPrefix
      exact (flashMintedSlot_not_valid (keyEq ▸ occurrence.2.1)).elim
    · have returnFree : Func.sstoreFreeWithin 256
          ((weth10 dp).main :: weth10Aux) returnTrue = true := by
        rfl
      exact (returnCursor.no_balanceSstoreOccurrence_of_free
        context.invocation.2.2.2 returnFree insideReturn).elim

private def flashSettleLoadLine : Line :=
  addressArg 0 ++ mstoreAt 0 ++ [Ninst.address] ++ mstoreAt 1 ++
    allowanceKeyFromMemory ++
    [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ isMax

private def flashSettleCheckLine : Line :=
  arg 2 ++ [Ninst.swap 0] ++ balanceTooSmall

private def flashSettleAfterStore : Func :=
  emitFlashApproval +++ .call flashBurnSlot

/-- Reverse the post-callback allowance phase.  Its finite allowance update is
excluded by the executed tagged key; both finite and maximum arms retain the
same exact flash-burn cursor, where the sole balance write is classified as
the paired repayment. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_flashSettle
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashSettle frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    BalanceSstoreRole ca stepPre
      (.flashPair (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2).toNat)
      holder value := by
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    (flashSettleLoadLine +++
      (.branch
        (flashSettleCheckLine +++
          (.branch
            (spendAllowanceBeforeStore +++
              (.next (.reg .sstore) flashSettleAfterStore))
            (.call allowanceErrorSlot)))
        ([Ninst.pop, Ninst.pop] +++ .call flashBurnSlot)))
    frame.post at cursor
  rcases cursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [flashSettleLoadLine, addressArg, normalizeAddress,
          pushAddressMask, arg, cdl, mstoreAt, allowanceKeyFromMemory,
          pushList, isMax, Ninst.pushB256] at hn) fromCursor with
    ⟨maxBranchCursor, allowanceRun, atMaxBranch⟩
  rcases prefix_of_selfAllowanceIsMax 0 nil_pref allowanceRun with
    ⟨hash, allowance, _allowanceEq, allowancePrefix⟩
  rcases maxBranchCursor.balanceSstoreOccurrence_branchWithFlag
      atMaxBranch with
    ⟨finiteCursor, finitePop, insideFinite⟩ |
      ⟨_maxFlag, _maxNonzero, maxCursor, _maxPop, insideMax⟩
  · have finitePrefix : allowance ::
        (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
          finiteCursor.pre.stack :=
      prefix_of_pop
        ⟨0, Devm.PopBurn.of_popBurnBy finitePop⟩ allowancePrefix
    rcases finiteCursor.balanceSstoreOccurrence_after_line
        (by
          rintro n hn rfl
          simp [flashSettleCheckLine, arg, cdl, balanceTooSmall,
            Ninst.pushB256] at hn) insideFinite with
      ⟨spendBranchCursor, checkRun, atSpendBranch⟩
    rcases of_run_append (arg 2) checkRun with
      ⟨afterAmount, amountRun, afterAmountRun⟩
    rcases Line.of_run_cons afterAmountRun with
      ⟨afterSwap, swapStep, guardRun⟩
    have amountPrefix : Sevm.argWord frame.sevm 2 :: allowance ::
        (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
          afterAmount.stack :=
      prefix_of_arg finitePrefix amountRun
    have swapCore : Stack.Swap (0 : Fin 16).val
        (Sevm.argWord frame.sevm 2 :: allowance ::
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [])
        (allowance :: Sevm.argWord frame.sevm 2 ::
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: []) :=
      Stack.swapCore_zero
    have swappedPrefix : allowance :: Sevm.argWord frame.sevm 2 ::
        (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
          afterSwap.stack :=
      Stack.prefix_of_swap swapCore (of_run_swap swapStep) amountPrefix
    have guardPrefix :
        (allowance <? Sevm.argWord frame.sevm 2) :: allowance ::
          Sevm.argWord frame.sevm 2 ::
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
            spendBranchCursor.pre.stack :=
      prefix_of_balanceTooSmall swappedPrefix guardRun
    rcases spendBranchCursor.balanceSstoreOccurrence_branchWithFlag
        atSpendBranch with
      ⟨successCursor, successPop, insideSuccess⟩ |
        ⟨_errorFlag, _errorNonzero, errorCallCursor, _errorPop,
          insideError⟩
    · have successPrefix : allowance :: Sevm.argWord frame.sevm 2 ::
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
            successCursor.pre.stack :=
        prefix_of_pop
          ⟨0, Devm.PopBurn.of_popBurnBy successPop⟩ guardPrefix
      rcases successCursor.balanceSstoreOccurrence_after_line
          (by simp [spendAllowanceBeforeStore]) insideSuccess with
        ⟨storeCursor, beforeStoreRun, atStore⟩
      rcases Line.of_run_cons beforeStoreRun with
        ⟨afterSub, subStep, afterSubRun⟩
      rcases Line.of_run_cons afterSubRun with
        ⟨afterDup, dupStep, afterDupRun⟩
      rcases Line.of_run_cons afterDupRun with
        ⟨afterSwap, storeSwapStep, emptyLine⟩
      cases emptyLine
      have reducedPrefix :
          (allowance - Sevm.argWord frame.sevm 2) ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
              afterSub.stack :=
        prefix_of_sub subStep successPrefix
      have duplicatePrefix :
          (allowance - Sevm.argWord frame.sevm 2) ::
            (allowance - Sevm.argWord frame.sevm 2) ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
              afterDup.stack :=
        prefix_of_dup_val dupStep (by show_nth) reducedPrefix
      have storeSwapCore : Stack.Swap (1 : Fin 16).val
          ((allowance - Sevm.argWord frame.sevm 2) ::
            (allowance - Sevm.argWord frame.sevm 2) ::
            (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [])
          ((allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
            (allowance - Sevm.argWord frame.sevm 2) ::
            (allowance - Sevm.argWord frame.sevm 2) :: []) :=
        Stack.swapCore_succ Stack.swapCore_zero
      have storePrefix :
          (allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
            (allowance - Sevm.argWord frame.sevm 2) ::
            (allowance - Sevm.argWord frame.sevm 2) :: [] <<+
              storeCursor.pre.stack :=
        Stack.prefix_of_swap storeSwapCore
          (of_run_swap storeSwapStep) duplicatePrefix
      rcases storeCursor.balanceSstoreOccurrence_after_invalidKeyStore
          atStore occurrence (runtimeAllowanceKey_not_valid hash)
          storePrefix with
        ⟨afterStoreCursor, insideAfterStore⟩
      rcases afterStoreCursor.balanceSstoreOccurrence_after_line
          (by
            rintro n hn rfl
            simp [emitFlashApproval, arg, cdl,
              mstoreAt, logWith, Ninst.pushB256] at hn)
          insideAfterStore with
        ⟨burnCallCursor, _approvalRun, insideBurnCall⟩
      rcases burnCallCursor.balanceSstoreOccurrence_call
          context.invocation.2.2.2 insideBurnCall with
        ⟨body, bodyLookup, burnCursor, insideBurn⟩
      have bodyEq : body = flashBurn := by
        simpa [flashBurnSlot, weth10, weth10Aux] using bodyLookup.symm
      subst body
      exact burnCursor.balanceSstoreRole_flashBurn
        insideBurn occurrence context
    · rcases errorCallCursor.balanceSstoreOccurrence_call
          context.invocation.2.2.2 insideError with
        ⟨body, bodyLookup, errorCursor, insideErrorBody⟩
      have bodyEq : body = allowanceError := by
        simpa [allowanceErrorSlot, weth10, weth10Aux] using bodyLookup.symm
      subst body
      exact (errorCursor.no_balanceSstoreOccurrence_of_free
        context.invocation.2.2.2 (allowanceError_sstoreFree _)
        insideErrorBody).elim
  · rcases maxCursor.balanceSstoreOccurrence_after_line
        (by simp) insideMax with
      ⟨burnCallCursor, _popRun, insideBurnCall⟩
    rcases burnCallCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideBurnCall with
      ⟨body, bodyLookup, burnCursor, insideBurn⟩
    have bodyEq : body = flashBurn := by
      simpa [flashBurnSlot, weth10, weth10Aux] using bodyLookup.symm
    subst body
    exact burnCursor.balanceSstoreRole_flashBurn insideBurn occurrence context

private def flashLoanTokenGuardLine : Line :=
  arg 1 ++ [Ninst.address, Ninst.eq, Ninst.iszero]

private def flashLoanIndividualLimitLine : Line :=
  arg 2 ++ [Ninst.dup 0, Ninst.pushB256 maxUint112, Ninst.lt]

private def flashLoanCounterBeforeSlot : Line :=
  pushFlashMintedSlot ++ [Ninst.sload, Ninst.dup 1, Ninst.add]

private def flashLoanCounterBeforeStore : Line :=
  flashLoanCounterBeforeSlot ++ pushFlashMintedSlot

private def flashLoanCapLine : Line :=
  pushFlashMintedSlot ++
    [Ninst.sload, Ninst.dup 0, Ninst.pushB256 maxUint112, Ninst.lt]

private def flashLoanCreditBeforeStore : Line :=
  [Ninst.pop] ++ addressArg 0 ++
    [Ninst.dup 0, Ninst.sload, Ninst.dup 2, Ninst.add, Ninst.dup 1]

private def flashLoanAfterCredit : Func :=
  Ninst.swap 0 ::: Ninst.dup 0 ::: mstoreAt 0 +++
  Ninst.dup 1 ::: Ninst.pushB256 0 :::
  Ninst.pushB256 Blanc.transferEvent ::: logWith 2 0 1 +++
  Ninst.dup 1 ::: Ninst.extcodesize ::: Ninst.iszero :::
  Func.rev <?>
  (Ninst.dup 0 ::: storeFlashCallbackHead +++
    pushList [0, 0] +++
    forwardArgTail 3 6 +++ flashCallbackArgsSize +++
    Ninst.pushB256 callbackArgsOffset ::: Ninst.pushB256 0 :::
    Ninst.dup 6 ::: Ninst.gas ::: Ninst.call ::: Ninst.iszero :::
    (.call bubbleRevertSlot) <?>
    (retdataShorterThan 32 +++
      Func.rev <?>
      (checkRetdataHead CALLBACK_SUCCESS 0 +++ Ninst.iszero :::
        (.call flashFailedErrorSlot) <?>
        (Ninst.pop ::: Ninst.pop ::: .call flashSettleSlot))))

private theorem flashLoanAfterCredit_routedToSettle (dp : DeployParams) :
    Func.balanceSstoreRoutedToCallWithin 512
      ((weth10 dp).main :: weth10Aux) flashSettleSlot
      flashLoanAfterCredit = true := by
  simp [flashLoanAfterCredit, Func.balanceSstoreRoutedToCallWithin, prepend,
    mstoreAt, logWith, pushList, forwardArgTail, flashCallbackArgsSize,
    storeFlashCallbackHead, retdataShorterThan, checkRetdataHead,
    flashSettleSlot, bubbleRevertSlot, flashFailedErrorSlot, weth10,
    weth10Aux, ninstSstoreFree, arg, cdl, Ninst.pushB256, Func.rev]
  constructor
  · calc
      Func.sstoreFreeWithin 434 ((weth10 dp).main :: weth10Aux)
          flashFailedError =
        Func.sstoreFreeWithin 434 [] flashFailedError :=
          Func.sstoreFreeWithin_eq_of_noCalls
            (by exact revWith_noCalls _) _ _
      _ = true := by decide +kernel
  · calc
      Func.sstoreFreeWithin 448 ((weth10 dp).main :: weth10Aux)
          bubbleRevert =
        Func.sstoreFreeWithin 448 [] bubbleRevert :=
          Func.sstoreFreeWithin_eq_of_noCalls
            (by
              unfold bubbleRevert Func.revReturnData
              simp [Func.NoCalls]) _ _
      _ = true := by decide +kernel

private def flashLoanAfterCounterStore : Func :=
  flashLoanCapLine +++
    (.branch
      (flashLoanCreditBeforeStore +++
        (.next (.reg .sstore) flashLoanAfterCredit))
      (.call totalLimitErrorSlot))

private def flashLoanAfterIndividualLimit : Func :=
  flashLoanCounterBeforeStore +++
    (.next (.reg .sstore) flashLoanAfterCounterStore)

private def flashLoanAfterTokenGuard : Func :=
  flashLoanIndividualLimitLine +++
    (.branch flashLoanAfterIndividualLimit (.call individualLimitErrorSlot))

private def flashLoanSource : Func :=
  flashLoanTokenGuardLine +++
    (.branch flashLoanAfterTokenGuard (.call flashTokenErrorSlot))

private theorem flashLoan_eq_source : flashLoan = flashLoanSource := by
  simp only [flashLoan, flashLoanSource, flashLoanAfterTokenGuard,
    flashLoanAfterIndividualLimit, flashLoanAfterCounterStore,
    flashLoanTokenGuardLine, flashLoanIndividualLimitLine,
    flashLoanCounterBeforeStore, flashLoanCounterBeforeSlot,
    flashLoanCapLine, flashLoanCreditBeforeStore, flashLoanAfterCredit,
    prepend_append_writeCompleteness, List.append_assoc, prepend]

/-- Reverse every address-shaped write in the complete flash-loan source.  The
two flash-counter stores are excluded by their all-ones key, the receiver
credit is reconstructed at its immediate stack, and every later balance write
is routed through the exact settlement call to the paired repayment proof. -/
private theorem Exec.Frame.CompiledCursor.balanceSstoreRole_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashLoan frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) :
    BalanceSstoreRole ca stepPre
      (.flashPair (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2).toNat)
      holder value := by
  rcases cursor.castSourceWithOccurrence flashLoan_eq_source fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  rcases sourceCursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [flashLoanTokenGuardLine, arg, cdl, Ninst.pushB256] at hn)
      fromSource with
    ⟨tokenBranchCursor, _tokenRun, atTokenBranch⟩
  rcases tokenBranchCursor.balanceSstoreOccurrence_branch atTokenBranch with
    ⟨limitCursor, insideLimit⟩ | ⟨tokenErrorCursor, insideTokenError⟩
  · rcases limitCursor.balanceSstoreOccurrence_after_line
        (by
          rintro n hn rfl
          simp [flashLoanIndividualLimitLine, arg, cdl,
            Ninst.pushB256] at hn) insideLimit with
      ⟨limitBranchCursor, limitRun, atLimitBranch⟩
    rcases of_run_append (arg 2) limitRun with
      ⟨afterAmount, amountRun, afterAmountRun⟩
    rcases Line.of_run_cons afterAmountRun with
      ⟨afterDup, amountDupStep, afterDupRun⟩
    rcases Line.of_run_cons afterDupRun with
      ⟨afterMax, maxPushStep, afterMaxRun⟩
    rcases Line.of_run_cons afterMaxRun with
      ⟨afterLt, limitLtStep, emptyLine⟩
    cases emptyLine
    have amountPrefix : [Sevm.argWord frame.sevm 2] <<+ afterAmount.stack :=
      prefix_of_arg nil_pref amountRun
    have duplicateAmountPrefix :
        [Sevm.argWord frame.sevm 2, Sevm.argWord frame.sevm 2] <<+
          afterDup.stack :=
      prefix_of_dup_val amountDupStep (by show_nth) amountPrefix
    have maxPrefix : maxUint112 :: Sevm.argWord frame.sevm 2 ::
        Sevm.argWord frame.sevm 2 :: [] <<+ afterMax.stack :=
      prefix_of_push (of_run_pushB256 maxPushStep) duplicateAmountPrefix
    have limitFlagPrefix : (maxUint112 <? Sevm.argWord frame.sevm 2) ::
        Sevm.argWord frame.sevm 2 :: [] <<+ limitBranchCursor.pre.stack :=
      prefix_of_lt limitLtStep maxPrefix
    rcases limitBranchCursor.balanceSstoreOccurrence_branchWithFlag
        atLimitBranch with
      ⟨counterCursor, limitPop, insideCounter⟩ |
        ⟨_limitFlag, _limitNonzero, limitErrorCursor, _limitErrorPop,
          insideLimitError⟩
    · have counterAmountPrefix : [Sevm.argWord frame.sevm 2] <<+
          counterCursor.pre.stack :=
        prefix_of_pop
          ⟨0, Devm.PopBurn.of_popBurnBy limitPop⟩ limitFlagPrefix
      rcases counterCursor.balanceSstoreOccurrence_after_line
          (by
            rintro n hn rfl
            simp [flashLoanCounterBeforeStore, flashLoanCounterBeforeSlot,
              pushFlashMintedSlot, Ninst.pushB256] at hn)
          insideCounter with
        ⟨counterStoreCursor, counterRun, atCounterStore⟩
      rcases of_run_append flashLoanCounterBeforeSlot counterRun with
        ⟨beforeCounterSlot, counterBeforeSlotRun, counterSlotRun⟩
      rcases of_run_append pushFlashMintedSlot counterBeforeSlotRun with
        ⟨afterCounterKey, counterKeyRun, counterMathRun⟩
      change Line.Run frame.sevm counterCursor.pre
        [Ninst.pushB256 0, Ninst.not] afterCounterKey at counterKeyRun
      rcases Line.of_run_cons counterKeyRun with
        ⟨afterCounterZero, counterZeroStep, counterNotRun⟩
      rcases Line.of_run_cons counterNotRun with
        ⟨afterCounterNot, counterNotStep, emptyCounterKey⟩
      cases emptyCounterKey
      have counterZeroPrefix : (0 : B256) ::
          Sevm.argWord frame.sevm 2 :: [] <<+ afterCounterZero.stack :=
        prefix_of_push (of_run_pushB256 counterZeroStep)
          counterAmountPrefix
      have counterKeyPrefix : flashMintedSlot ::
          Sevm.argWord frame.sevm 2 :: [] <<+ afterCounterKey.stack := by
        have zeroNot : (~~~ (0 : B256)) = flashMintedSlot := rfl
        rw [← zeroNot]
        exact prefix_of_not counterNotStep counterZeroPrefix
      rcases Line.of_run_cons counterMathRun with
        ⟨afterCounterLoad, counterLoadStep, counterMathRun⟩
      rcases prefix_of_sload counterLoadStep counterKeyPrefix with
        ⟨counterValue, counterValuePrefix, _counterValueEq⟩
      rcases Line.of_run_cons counterMathRun with
        ⟨afterCounterDup, counterDupStep, counterAddRun⟩
      have counterDupPrefix : Sevm.argWord frame.sevm 2 :: counterValue ::
          Sevm.argWord frame.sevm 2 :: [] <<+ afterCounterDup.stack :=
        prefix_of_dup_val counterDupStep (by show_nth) counterValuePrefix
      rcases Line.of_run_cons counterAddRun with
        ⟨afterCounterAdd, counterAddStep, emptyCounterMath⟩
      cases emptyCounterMath
      have counterSumPrefix :
          (Sevm.argWord frame.sevm 2 + counterValue) ::
            Sevm.argWord frame.sevm 2 :: [] <<+ beforeCounterSlot.stack :=
        prefix_of_add counterAddStep counterDupPrefix
      change Line.Run frame.sevm beforeCounterSlot
        [Ninst.pushB256 0, Ninst.not] counterStoreCursor.pre at counterSlotRun
      rcases Line.of_run_cons counterSlotRun with
        ⟨afterStoreZero, storeZeroStep, storeNotRun⟩
      rcases Line.of_run_cons storeNotRun with
        ⟨afterStoreNot, storeNotStep, emptyStoreKey⟩
      cases emptyStoreKey
      have storeZeroPrefix : (0 : B256) ::
          (Sevm.argWord frame.sevm 2 + counterValue) ::
          Sevm.argWord frame.sevm 2 :: [] <<+ afterStoreZero.stack :=
        prefix_of_push (of_run_pushB256 storeZeroStep) counterSumPrefix
      have counterStorePrefix : flashMintedSlot ::
          (Sevm.argWord frame.sevm 2 + counterValue) ::
          Sevm.argWord frame.sevm 2 :: [] <<+ counterStoreCursor.pre.stack := by
        have zeroNot : (~~~ (0 : B256)) = flashMintedSlot := rfl
        rw [← zeroNot]
        exact prefix_of_not storeNotStep storeZeroPrefix
      rcases counterStoreCursor.ninstOccurrenceFromCursor_head_or_tail
          atCounterStore with
        ⟨_sourceEq, preEq⟩ |
          ⟨capCursor, _counterSlot, counterOccurrence, insideCap⟩
      · subst stepPre
        rcases occurrence.2.2.2 with
          ⟨occurrenceTail, occurrencePrefix⟩
        have occurrenceKeyPrefix : [key] <<+ counterStoreCursor.pre.stack :=
          pref_trans (pref_append [key] (value :: occurrenceTail))
            occurrencePrefix
        have expectedKeyPrefix : [flashMintedSlot] <<+
            counterStoreCursor.pre.stack :=
          pref_trans
            (pref_append [flashMintedSlot]
              ((Sevm.argWord frame.sevm 2 + counterValue) ::
                Sevm.argWord frame.sevm 2 :: []))
            counterStorePrefix
        have keyEq : key = flashMintedSlot :=
          pref_head_unique occurrenceKeyPrefix expectedKeyPrefix
        exact (flashMintedSlot_not_valid
          (keyEq ▸ occurrence.2.1)).elim
      · have capAmountPrefix : [Sevm.argWord frame.sevm 2] <<+
            capCursor.pre.stack :=
          prefix_of_sstore counterOccurrence.run counterStorePrefix
        rcases capCursor.balanceSstoreOccurrence_after_line
            (by
              rintro n hn rfl
              simp [flashLoanCapLine, pushFlashMintedSlot,
                Ninst.pushB256] at hn) insideCap with
          ⟨capBranchCursor, capRun, atCapBranch⟩
        rcases of_run_append pushFlashMintedSlot capRun with
          ⟨afterCapKey, capKeyRun, capTailRun⟩
        change Line.Run frame.sevm capCursor.pre
          [Ninst.pushB256 0, Ninst.not] afterCapKey at capKeyRun
        rcases Line.of_run_cons capKeyRun with
          ⟨afterCapZero, capZeroStep, capNotRun⟩
        rcases Line.of_run_cons capNotRun with
          ⟨afterCapNot, capNotStep, emptyCapKey⟩
        cases emptyCapKey
        have capZeroPrefix : (0 : B256) ::
            Sevm.argWord frame.sevm 2 :: [] <<+ afterCapZero.stack :=
          prefix_of_push (of_run_pushB256 capZeroStep) capAmountPrefix
        have capKeyPrefix : flashMintedSlot ::
            Sevm.argWord frame.sevm 2 :: [] <<+ afterCapKey.stack := by
          have zeroNot : (~~~ (0 : B256)) = flashMintedSlot := rfl
          rw [← zeroNot]
          exact prefix_of_not capNotStep capZeroPrefix
        rcases Line.of_run_cons capTailRun with
          ⟨afterCapLoad, capLoadStep, capTailRun⟩
        rcases prefix_of_sload capLoadStep capKeyPrefix with
          ⟨capValue, capValuePrefix, _capValueEq⟩
        rcases Line.of_run_cons capTailRun with
          ⟨afterCapDup, capDupStep, capTailRun⟩
        have capDuplicatePrefix : capValue :: capValue ::
            Sevm.argWord frame.sevm 2 :: [] <<+ afterCapDup.stack :=
          prefix_of_dup_val capDupStep (by show_nth) capValuePrefix
        rcases Line.of_run_cons capTailRun with
          ⟨afterCapMax, capMaxStep, capLtRun⟩
        have capMaxPrefix : maxUint112 :: capValue :: capValue ::
            Sevm.argWord frame.sevm 2 :: [] <<+ afterCapMax.stack :=
          prefix_of_push (of_run_pushB256 capMaxStep) capDuplicatePrefix
        rcases Line.of_run_cons capLtRun with
          ⟨afterCapLt, capLtStep, emptyCapLine⟩
        cases emptyCapLine
        have capFlagPrefix : (maxUint112 <? capValue) :: capValue ::
            Sevm.argWord frame.sevm 2 :: [] <<+
              capBranchCursor.pre.stack :=
          prefix_of_lt capLtStep capMaxPrefix
        rcases capBranchCursor.balanceSstoreOccurrence_branchWithFlag
            atCapBranch with
          ⟨creditCursor, capPop, insideCredit⟩ |
            ⟨_capFlag, _capNonzero, capErrorCursor, _capErrorPop,
              insideCapError⟩
        · have creditEntryPrefix : capValue ::
              Sevm.argWord frame.sevm 2 :: [] <<+ creditCursor.pre.stack :=
            prefix_of_pop
              ⟨0, Devm.PopBurn.of_popBurnBy capPop⟩ capFlagPrefix
          rcases creditCursor.balanceSstoreOccurrence_after_line
              (by
                rintro n hn rfl
                simp [flashLoanCreditBeforeStore, addressArg,
                  normalizeAddress, pushAddressMask, arg, cdl,
                  Ninst.pushB256] at hn) insideCredit with
            ⟨creditStoreCursor, creditRun, atCreditStore⟩
          rcases Line.of_run_cons creditRun with
            ⟨afterDiscard, discardStep, creditRun⟩
          have creditAmountPrefix : [Sevm.argWord frame.sevm 2] <<+
              afterDiscard.stack :=
            prefix_of_pop (of_run_pop discardStep) creditEntryPrefix
          rcases of_run_append (addressArg 0) creditRun with
            ⟨afterRecipient, recipientRun, creditRun⟩
          have recipientPrefix : normalizedAddressArg frame.sevm 0 ::
              Sevm.argWord frame.sevm 2 :: [] <<+ afterRecipient.stack := by
            simpa [normalizedAddressArg] using
              prefix_of_addressArg creditAmountPrefix recipientRun
          rcases Line.of_run_cons creditRun with
            ⟨afterRecipientDup, recipientDupStep, creditRun⟩
          have recipientDuplicatePrefix : normalizedAddressArg frame.sevm 0 ::
              normalizedAddressArg frame.sevm 0 ::
              Sevm.argWord frame.sevm 2 :: [] <<+
                afterRecipientDup.stack :=
            prefix_of_dup_val recipientDupStep (by show_nth) recipientPrefix
          rcases Line.of_run_cons creditRun with
            ⟨afterRecipientLoad, recipientLoadStep, creditRun⟩
          rcases prefix_of_sload recipientLoadStep recipientDuplicatePrefix with
            ⟨recipientBalance, recipientBalancePrefix, recipientBalanceEq⟩
          rcases Line.of_run_cons creditRun with
            ⟨afterAmountDup, creditAmountDupStep, creditRun⟩
          have amountDuplicatePrefix : Sevm.argWord frame.sevm 2 ::
              recipientBalance :: normalizedAddressArg frame.sevm 0 ::
              Sevm.argWord frame.sevm 2 :: [] <<+ afterAmountDup.stack :=
            prefix_of_dup_val creditAmountDupStep (by show_nth)
              recipientBalancePrefix
          rcases Line.of_run_cons creditRun with
            ⟨afterCreditAdd, creditAddStep, creditRun⟩
          have creditSumPrefix :
              (Sevm.argWord frame.sevm 2 + recipientBalance) ::
                normalizedAddressArg frame.sevm 0 ::
                Sevm.argWord frame.sevm 2 :: [] <<+ afterCreditAdd.stack :=
            prefix_of_add creditAddStep amountDuplicatePrefix
          rcases Line.of_run_cons creditRun with
            ⟨afterCreditKey, creditKeyDupStep, emptyCreditLine⟩
          cases emptyCreditLine
          have creditStorePrefix : normalizedAddressArg frame.sevm 0 ::
              (Sevm.argWord frame.sevm 2 + recipientBalance) ::
              normalizedAddressArg frame.sevm 0 ::
              Sevm.argWord frame.sevm 2 :: [] <<+
                creditStoreCursor.pre.stack :=
            prefix_of_dup_val creditKeyDupStep (by show_nth)
              creditSumPrefix
          have storLoad : Devm.getStor afterRecipientDup =
              Devm.getStor afterRecipientLoad :=
            Ninst.Hinv.inv (f := Devm.getStor) recipientLoadStep
          have storAmountDup : Devm.getStor afterRecipientLoad =
              Devm.getStor afterAmountDup :=
            Ninst.Hinv.inv (f := Devm.getStor) creditAmountDupStep
          have storAdd : Devm.getStor afterAmountDup =
              Devm.getStor afterCreditAdd :=
            Ninst.Hinv.inv (f := Devm.getStor) creditAddStep
          have storKeyDup : Devm.getStor afterCreditAdd =
              Devm.getStor creditStoreCursor.pre :=
            Ninst.Hinv.inv (f := Devm.getStor) creditKeyDupStep
          have normalizedEq : normalizedAddressArg frame.sevm 0 =
              (Sevm.argWord frame.sevm 0).toAdr.toB256 :=
            normalizedAddressArg_eq_toAdr_toB256_writeCompleteness _ _
          have recipientBalanceAtStore : recipientBalance =
              (Devm.getStor creditStoreCursor.pre ca).get
                (Sevm.argWord frame.sevm 0).toAdr.toB256 := by
            rw [recipientBalanceEq]
            change (Devm.getStor afterRecipientDup frame.sevm.currentTarget).get
                (normalizedAddressArg frame.sevm 0) =
              (Devm.getStor creditStoreCursor.pre ca).get
                (Sevm.argWord frame.sevm 0).toAdr.toB256
            rw [storLoad, storAmountDup, storAdd,
              storKeyDup, context.invocation.2.1, normalizedEq]
          have storedWord : Sevm.argWord frame.sevm 2 + recipientBalance =
              Stor.rest (Devm.getStor creditStoreCursor.pre ca)
                  (Sevm.argWord frame.sevm 0).toAdr +
                Sevm.argWord frame.sevm 2 := by
            simp only [Stor.rest, Function.comp_apply]
            rw [← recipientBalanceAtStore]
            exact B256.add_comm
          rcases creditStoreCursor.ninstOccurrenceFromCursor_head_or_tail
              atCreditStore with
            ⟨_sourceEq, preEq⟩ |
              ⟨afterCreditCursor, _creditSlot, _creditOccurrence,
                insideAfterCredit⟩
          · subst stepPre
            rcases occurrence.2.2.2 with
              ⟨occurrenceTail, occurrencePrefix⟩
            have occurrencePairPrefix : [key, value] <<+
                creditStoreCursor.pre.stack :=
              pref_trans (pref_append [key, value] occurrenceTail)
                occurrencePrefix
            have expectedPairPrefix :
                [(Sevm.argWord frame.sevm 0).toAdr.toB256,
                  Stor.rest (Devm.getStor creditStoreCursor.pre ca)
                      (Sevm.argWord frame.sevm 0).toAdr +
                    Sevm.argWord frame.sevm 2] <<+
                  creditStoreCursor.pre.stack := by
              rw [← normalizedEq, ← storedWord]
              exact pref_trans
                (pref_append
                  [normalizedAddressArg frame.sevm 0,
                    Sevm.argWord frame.sevm 2 + recipientBalance]
                  [normalizedAddressArg frame.sevm 0,
                    Sevm.argWord frame.sevm 2])
                creditStorePrefix
            have pairEq : [key, value] =
                [(Sevm.argWord frame.sevm 0).toAdr.toB256,
                  Stor.rest (Devm.getStor creditStoreCursor.pre ca)
                      (Sevm.argWord frame.sevm 0).toAdr +
                    Sevm.argWord frame.sevm 2] :=
              List.pref_unique (by simp) occurrencePairPrefix
                expectedPairPrefix
            injection pairEq with keyEq valueTailEq
            injection valueTailEq with valueEq
            have holderEq : holder =
                (Sevm.argWord frame.sevm 0).toAdr := by
              apply Adr.toB256_inj
              exact occurrence.2.2.1.symm.trans keyEq
            subst holder
            rw [valueEq]
            simpa only [Jaune.toB256_toNat] using
              (BalanceSstoreRole.flashCredit
                (ca := ca) (stepPre := creditStoreCursor.pre)
                (Sevm.argWord frame.sevm 0)
                (Sevm.argWord frame.sevm 0).toAdr
                (Sevm.argWord frame.sevm 2).toNat)
          · rcases afterCreditCursor.balanceSstoreOccurrence_routedToCall
                context.invocation.2.2.2
                (flashLoanAfterCredit_routedToSettle dp)
                insideAfterCredit with
              ⟨body, bodyLookup, settleCursor, insideSettle⟩
            have bodyEq : body = flashSettle := by
              simpa [flashSettleSlot, weth10, weth10Aux] using
                bodyLookup.symm
            subst body
            exact settleCursor.balanceSstoreRole_flashSettle
              insideSettle occurrence context
        · rcases capErrorCursor.balanceSstoreOccurrence_call
              context.invocation.2.2.2 insideCapError with
            ⟨body, bodyLookup, errorCursor, insideErrorBody⟩
          have bodyEq : body = totalLimitError := by
            simpa [totalLimitErrorSlot, weth10, weth10Aux] using
              bodyLookup.symm
          subst body
          exact (errorCursor.no_balanceSstoreOccurrence_of_free
            context.invocation.2.2.2 (totalLimitError_sstoreFree _)
            insideErrorBody).elim
    · rcases limitErrorCursor.balanceSstoreOccurrence_call
          context.invocation.2.2.2 insideLimitError with
        ⟨body, bodyLookup, errorCursor, insideErrorBody⟩
      have bodyEq : body = individualLimitError := by
        simpa [individualLimitErrorSlot, weth10, weth10Aux] using
          bodyLookup.symm
      subst body
      exact (errorCursor.no_balanceSstoreOccurrence_of_free
        context.invocation.2.2.2 (individualLimitError_sstoreFree _)
        insideErrorBody).elim
  · rcases tokenErrorCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideTokenError with
      ⟨body, bodyLookup, errorCursor, insideErrorBody⟩
    have bodyEq : body = flashTokenError := by
      simpa [flashTokenErrorSlot, weth10, weth10Aux] using bodyLookup.symm
    subst body
    exact (errorCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 (flashTokenError_sstoreFree _)
      insideErrorBody).elim

/-- Package the paired flash credit/repayment roles against the executable
primary classifier. -/
private theorem Exec.Frame.CompiledCursor.classifyBalanceSstore_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux)) flashLoan frame.post)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (selectorEq : Sevm.selector frame.sevm = flashLoanSelector)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  have role := cursor.balanceSstoreRole_flashLoan
    fromCursor occurrence context
  have primary : primaryFlowAtom frame.sevm = some
      (.flashPair (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2).toNat) := by
    simp [primaryFlowAtom, nonempty, selectorEq,
      flashLoanSelector_ne_depositSelector,
      flashLoanSelector_ne_depositToSelector,
      flashLoanSelector_ne_depositToAndCallSelector,
      flashLoanSelector_ne_transferSelector,
      flashLoanSelector_ne_transferAndCallSelector,
      flashLoanSelector_ne_transferFromSelector,
      flashLoanSelector_ne_withdrawSelector,
      flashLoanSelector_ne_withdrawToSelector,
      flashLoanSelector_ne_withdrawFromSelector]
  exact occurrence.classify_of_primary_role context primary role

private def approveEntryBeforeKey : Line :=
  [Ninst.caller] ++ mstoreAt 0 ++ argCopy 1 0 1

private def approveEntryBeforeStore : Line :=
  approveEntryBeforeKey ++ allowanceKeyFromMemory ++
    arg 1 ++ [Ninst.swap 0]

private def approveEntryAfterStore (continuation : Func) : Func :=
  Blanc.logApprove +++ continuation

private theorem approvePrefix_append_eq_storeSplit (continuation : Func) :
    approvePrefix +++ continuation =
      approveEntryBeforeStore +++
        (.next (.reg .sstore) (approveEntryAfterStore continuation)) := by
  simp only [approvePrefix, approveEntryBeforeStore, approveEntryBeforeKey,
    approveEntryAfterStore, prepend_append_writeCompleteness,
    List.append_assoc, prepend]

/-- The shared approve prefix writes only the runtime tagged allowance key;
any later balance-shaped write would have to occur in the supplied
continuation, which is discharged by its local source certificate. -/
private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_approvePrefixThen
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {continuation : Func} {fuel : Nat}
    {final stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (approvePrefix +++ continuation) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (tailFree : Func.sstoreFreeWithin fuel
      ((weth10 dp).main :: weth10Aux)
      (approveEntryAfterStore continuation) = true) : False := by
  rcases cursor.castSourceWithOccurrence
      (approvePrefix_append_eq_storeSplit continuation) fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  rcases sourceCursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [approveEntryBeforeStore, approveEntryBeforeKey,
          allowanceKeyFromMemory, argCopy, cdc, arg, cdl, mstoreAt, pushList,
          Ninst.pushB256] at hn)
      fromSource with
    ⟨storeCursor, beforeStoreRun, atStore⟩
  change Line.Run frame.sevm sourceCursor.pre
    approveEntryBeforeStore storeCursor.pre at beforeStoreRun
  unfold approveEntryBeforeStore at beforeStoreRun
  rcases of_run_append approveEntryBeforeKey beforeStoreRun with
    ⟨beforeKey, _entryRun, keyTailRun⟩
  rcases of_run_append allowanceKeyFromMemory keyTailRun with
    ⟨afterKey, keyRun, valueTailRun⟩
  rcases prefix_of_allowanceKeyFromMemory nil_pref keyRun with
    ⟨hash, keyPrefix⟩
  rcases of_run_append (arg 1) valueTailRun with
    ⟨afterValue, valueRun, swapRun⟩
  have valuePrefix : Sevm.argWord frame.sevm 1 ::
      (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
        afterValue.stack :=
    prefix_of_arg keyPrefix valueRun
  rcases Line.of_run_cons swapRun with
    ⟨afterSwap, swapStep, emptyLine⟩
  cases emptyLine
  have swapCore : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord frame.sevm 1 ::
        (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [])
      ((allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
        Sevm.argWord frame.sevm 1 :: []) :=
    Stack.swapCore_zero
  have storePrefix :
      (allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
        Sevm.argWord frame.sevm 1 :: [] <<+ storeCursor.pre.stack :=
    Stack.prefix_of_swap swapCore (of_run_swap swapStep) valuePrefix
  rcases storeCursor.balanceSstoreOccurrence_after_invalidKeyStore
      atStore occurrence (runtimeAllowanceKey_not_valid hash)
      storePrefix with
    ⟨tailCursor, insideTail⟩
  exact tailCursor.no_balanceSstoreOccurrence_of_free
    context.invocation.2.2.2 tailFree insideTail

private def approvePermitBeforeStore : Line :=
  argCopy 0 0 2 ++ allowanceKeyFromMemory ++
    arg 2 ++ [Ninst.swap 0]

private def approvePermitAfterStore : Func :=
  arg 2 +++ mstoreAt 0 +++
  arg 1 +++ arg 0 +++ Ninst.pushB256 Blanc.approvalEvent :::
  logWith 2 0 1 +++ Func.stop

private theorem approvePermit_eq_storeSplit :
    approvePermit =
      approvePermitBeforeStore +++
        (.next (.reg .sstore) approvePermitAfterStore) := by
  simp only [approvePermit, approvePermitBeforeStore,
    approvePermitAfterStore, prepend_append_writeCompleteness,
    List.append_assoc, prepend]

/-- The successful permit tail's sole store is its tagged allowance update. -/
private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_approvePermit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {final stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      approvePermit final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) : False := by
  rcases cursor.castSourceWithOccurrence approvePermit_eq_storeSplit
      fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  rcases sourceCursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [approvePermitBeforeStore, allowanceKeyFromMemory,
          argCopy, cdc, arg, cdl, pushList, Ninst.pushB256] at hn)
      fromSource with
    ⟨storeCursor, beforeStoreRun, atStore⟩
  change Line.Run frame.sevm sourceCursor.pre
    approvePermitBeforeStore storeCursor.pre at beforeStoreRun
  unfold approvePermitBeforeStore at beforeStoreRun
  rcases of_run_append (argCopy 0 0 2) beforeStoreRun with
    ⟨beforeKey, _copyRun, keyTailRun⟩
  rcases of_run_append allowanceKeyFromMemory keyTailRun with
    ⟨afterKey, keyRun, valueTailRun⟩
  rcases prefix_of_allowanceKeyFromMemory nil_pref keyRun with
    ⟨hash, keyPrefix⟩
  rcases of_run_append (arg 2) valueTailRun with
    ⟨afterValue, valueRun, swapRun⟩
  have valuePrefix : Sevm.argWord frame.sevm 2 ::
      (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [] <<+
        afterValue.stack :=
    prefix_of_arg keyPrefix valueRun
  rcases Line.of_run_cons swapRun with
    ⟨afterSwap, swapStep, emptyLine⟩
  cases emptyLine
  have swapCore : Stack.Swap (0 : Fin 16).val
      (Sevm.argWord frame.sevm 2 ::
        (allowanceTagWord ||| (allowancePayloadMask &&& hash)) :: [])
      ((allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
        Sevm.argWord frame.sevm 2 :: []) :=
    Stack.swapCore_zero
  have storePrefix :
      (allowanceTagWord ||| (allowancePayloadMask &&& hash)) ::
        Sevm.argWord frame.sevm 2 :: [] <<+ storeCursor.pre.stack :=
    Stack.prefix_of_swap swapCore (of_run_swap swapStep) valuePrefix
  rcases storeCursor.balanceSstoreOccurrence_after_invalidKeyStore
      atStore occurrence (runtimeAllowanceKey_not_valid hash)
      storePrefix with
    ⟨tailCursor, insideTail⟩
  have tailFree : Func.sstoreFreeWithin 256
      ((weth10 dp).main :: weth10Aux) approvePermitAfterStore = true := by
    rfl
  exact tailCursor.no_balanceSstoreOccurrence_of_free
    context.invocation.2.2.2 tailFree insideTail

private def permitRecoverFirstGuardLine : Line :=
  permitDigest ++ recoverPermitSigner ++ [Ninst.dup 0, Ninst.iszero]

private def permitRecoverSecondGuardLine : Line :=
  arg 0 ++ [Ninst.eq, Ninst.iszero]

private def permitRecoverSource : Func :=
  permitRecoverFirstGuardLine +++
    (.branch
      (permitRecoverSecondGuardLine +++
        (.branch approvePermit (.call invalidPermitErrorSlot)))
      (.call invalidPermitErrorSlot))

private theorem permitRecover_eq_source :
    permitRecover = permitRecoverSource := by
  simp only [permitRecover, permitRecoverSource,
    permitRecoverFirstGuardLine, permitRecoverSecondGuardLine,
    prepend_append_writeCompleteness, List.append_assoc, prepend]

/-- Every persistent write in the permit recovery helper is the tagged
allowance write in `approvePermit`; both rejecting arms are locally
SSTORE-free. -/
private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_permitRecover
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {final stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      permitRecover final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) : False := by
  rcases cursor.castSourceWithOccurrence permitRecover_eq_source
      fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  rcases sourceCursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [permitRecoverFirstGuardLine, permitDigest,
          recoverPermitSigner, arg, cdl, mstoreAt, pushList,
          Ninst.pushB256] at hn)
      fromSource with
    ⟨firstBranchCursor, _firstGuardRun, atFirstBranch⟩
  rcases firstBranchCursor.balanceSstoreOccurrence_branch atFirstBranch with
    ⟨secondGuardCursor, insideSecondGuard⟩ |
      ⟨firstErrorCallCursor, insideFirstError⟩
  · rcases secondGuardCursor.balanceSstoreOccurrence_after_line
        (by
          rintro n hn rfl
          simp [permitRecoverSecondGuardLine, arg, cdl,
            Ninst.pushB256] at hn)
        insideSecondGuard with
      ⟨secondBranchCursor, _secondGuardRun, atSecondBranch⟩
    rcases secondBranchCursor.balanceSstoreOccurrence_branch
        atSecondBranch with
      ⟨approveCursor, insideApprove⟩ |
        ⟨secondErrorCallCursor, insideSecondError⟩
    · exact approveCursor.no_balanceSstoreOccurrence_approvePermit
        insideApprove occurrence context
    · rcases secondErrorCallCursor.balanceSstoreOccurrence_call
          context.invocation.2.2.2 insideSecondError with
        ⟨body, bodyLookup, errorCursor, insideErrorBody⟩
      have bodyEq : body = invalidPermitError := by
        simpa [invalidPermitErrorSlot, weth10, weth10Aux] using
          bodyLookup.symm
      subst body
      exact (errorCursor.no_balanceSstoreOccurrence_of_free
        context.invocation.2.2.2 (invalidPermitError_sstoreFree _)
        insideErrorBody).elim
  · rcases firstErrorCallCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideFirstError with
      ⟨body, bodyLookup, errorCursor, insideErrorBody⟩
    have bodyEq : body = invalidPermitError := by
      simpa [invalidPermitErrorSlot, weth10, weth10Aux] using
        bodyLookup.symm
    subst body
    exact (errorCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 (invalidPermitError_sstoreFree _)
      insideErrorBody).elim

private lemma permitPrefix_of_chainid_writeCompleteness
    {e : Sevm} {s s' : Devm} {xs : Stack}
    (stackPrefix : xs <<+ s.stack)
    (run : Ninst.Run e s Ninst.chainid s') :
    e.benvStat.chainId.toB256 :: xs <<+ s'.stack := by
  rcases of_run_reg run with ⟨_pc, coreRun⟩
  simp only [Rinst.run, Rinst.runCore] at coreRun
  exact prefix_of_push (Devm.pushBurn_of_pushItem coreRun) stackPrefix

private def permitDeadlineGuardLine : Line :=
  arg 3 ++ [Ninst.timestamp, Ninst.gt]

private def permitNonceBeforeStore : Line :=
  [Ninst.chainid] ++ addressArg 0 ++ [Ninst.dup 0] ++ tagNonceKey ++
  [Ninst.dup 0, Ninst.sload, Ninst.dup 0] ++ mstoreAt 4 ++
  [Ninst.pushB256 1, Ninst.add, Ninst.swap 0]

private def permitAfterNonceStore (dp : DeployParams) : Func :=
  Ninst.pop :::
  Ninst.pushB256 PERMIT_TYPEHASH ::: mstoreAt 0 +++
  argCopy 1 0 3 +++ arg 3 +++ mstoreAt 5 +++
  pushList [192, 0] +++ Ninst.kec :::
  Ninst.dup 1 ::: pushDeployWord dp.deploymentChainId ::: Ninst.eq :::
  (.branch
    (Ninst.swap 0 ::: calculateDomainSeparator +++
      .call permitRecoverSlot)
    (Ninst.swap 0 ::: Ninst.pop :::
      pushDeployWord dp.cachedDomainSeparator :::
      .call permitRecoverSlot))

private def permitAfterDeadlineSource (dp : DeployParams) : Func :=
  permitNonceBeforeStore +++
    (.next (.reg .sstore) (permitAfterNonceStore dp))

private def permitSource (dp : DeployParams) : Func :=
  permitDeadlineGuardLine +++
    (.branch (permitAfterDeadlineSource dp) (.call expiredPermitErrorSlot))

private theorem permit_eq_source (dp : DeployParams) :
    permit dp = permitSource dp := by
  simp only [permit, permitSource, permitAfterDeadlineSource,
    permitAfterNonceStore, permitNonceBeforeStore,
    permitDeadlineGuardLine, prepend_append_writeCompleteness,
    List.append_assoc, prepend]

private theorem permitAfterNonceStore_routedToRecover
    (dp : DeployParams) :
    Func.balanceSstoreRoutedToCallWithin 512
      ((weth10 dp).main :: weth10Aux) permitRecoverSlot
      (permitAfterNonceStore dp) = true := by
  rfl

/-- The selected permit entry performs one tagged nonce write and can then
reach only the permit-recovery helper, whose allowance write is tagged too. -/
private theorem Exec.Frame.CompiledCursor.no_balanceSstoreOccurrence_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {final stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (cursor : frame.CompiledCursor dp ca
      ((weth10 dp).main :: weth10Aux)
      (table 0 ((weth10 dp).main :: weth10Aux))
      (permit dp) final)
    (fromCursor : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot)
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca) : False := by
  rcases cursor.castSourceWithOccurrence (permit_eq_source dp)
      fromCursor with
    ⟨sourceCursor, _sourcePre, fromSource⟩
  rcases sourceCursor.balanceSstoreOccurrence_after_line
      (by
        rintro n hn rfl
        simp [permitDeadlineGuardLine, arg, cdl, Ninst.pushB256] at hn)
      fromSource with
    ⟨deadlineBranchCursor, _deadlineRun, atDeadlineBranch⟩
  rcases deadlineBranchCursor.balanceSstoreOccurrence_branch
      atDeadlineBranch with
    ⟨nonceCursor, insideNonce⟩ |
      ⟨deadlineErrorCallCursor, insideDeadlineError⟩
  · rcases nonceCursor.balanceSstoreOccurrence_after_line
        (by
          rintro n hn rfl
          simp [permitNonceBeforeStore, addressArg, normalizeAddress,
            pushAddressMask, tagNonceKey, arg, cdl, mstoreAt,
            Ninst.pushB256] at hn)
        insideNonce with
      ⟨storeCursor, beforeStoreRun, atStore⟩
    change Line.Run frame.sevm nonceCursor.pre
      permitNonceBeforeStore storeCursor.pre at beforeStoreRun
    unfold permitNonceBeforeStore at beforeStoreRun
    rcases Line.of_run_cons beforeStoreRun with
      ⟨afterChain, chainStep, nonceRun⟩
    have chainPrefix : frame.sevm.benvStat.chainId.toB256 :: [] <<+
        afterChain.stack :=
      permitPrefix_of_chainid_writeCompleteness nil_pref chainStep
    rcases of_run_append (addressArg 0) nonceRun with
      ⟨afterOwner, ownerRun, nonceRun⟩
    have ownerPrefix : ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+ afterOwner.stack :=
      prefix_of_addressArg chainPrefix ownerRun
    rcases Line.of_run_cons nonceRun with
      ⟨afterOwnerDup, ownerDupStep, nonceRun⟩
    have ownerDuplicatePrefix :
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+
          afterOwnerDup.stack :=
      prefix_of_dup_val ownerDupStep (by show_nth) ownerPrefix
    rcases of_run_append tagNonceKey nonceRun with
      ⟨afterTag, tagRun, nonceRun⟩
    unfold tagNonceKey at tagRun
    rcases Line.of_run_cons tagRun with
      ⟨afterTagPush, tagPushStep, tagOrRun⟩
    have tagPushPrefix : nonceTagWord ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+
          afterTagPush.stack :=
      prefix_of_push (of_run_pushB256 tagPushStep) ownerDuplicatePrefix
    rcases Line.of_run_cons tagOrRun with
      ⟨afterTagOr, tagOrStep, emptyTag⟩
    cases emptyTag
    have taggedPrefix :
        (nonceTagWord ||| ((~~~ addressMask) &&&
          Sevm.argWord frame.sevm 0)) ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+ afterTag.stack :=
      prefix_of_or tagOrStep tagPushPrefix
    rcases Line.of_run_cons nonceRun with
      ⟨afterKeyDup, keyDupStep, nonceRun⟩
    have keyDuplicatePrefix :
        (nonceTagWord ||| ((~~~ addressMask) &&&
          Sevm.argWord frame.sevm 0)) ::
        (nonceTagWord ||| ((~~~ addressMask) &&&
          Sevm.argWord frame.sevm 0)) ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+ afterKeyDup.stack :=
      prefix_of_dup_val keyDupStep (by show_nth) taggedPrefix
    rcases Line.of_run_cons nonceRun with
      ⟨afterLoad, loadStep, nonceRun⟩
    rcases prefix_of_sload loadStep keyDuplicatePrefix with
      ⟨nonce, loadedPrefix, _nonceEq⟩
    rcases Line.of_run_cons nonceRun with
      ⟨afterNonceDup, nonceDupStep, nonceRun⟩
    have nonceDuplicatePrefix : nonce :: nonce ::
        (nonceTagWord ||| ((~~~ addressMask) &&&
          Sevm.argWord frame.sevm 0)) ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+
          afterNonceDup.stack :=
      prefix_of_dup_val nonceDupStep (by show_nth) loadedPrefix
    rcases of_run_append (mstoreAt 4) nonceRun with
      ⟨afterNonceMemory, nonceMemoryRun, nonceRun⟩
    rcases of_run_mstoreAt_val nonceMemoryRun nonceDuplicatePrefix with
      ⟨afterMemoryPrefix, _memoryEq⟩
    rcases Line.of_run_cons nonceRun with
      ⟨afterOne, oneStep, nonceRun⟩
    have onePrefix : (1 : B256) :: nonce ::
        (nonceTagWord ||| ((~~~ addressMask) &&&
          Sevm.argWord frame.sevm 0)) ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+ afterOne.stack :=
      prefix_of_push (of_run_pushB256 oneStep) afterMemoryPrefix
    rcases Line.of_run_cons nonceRun with
      ⟨afterAdd, addStep, nonceRun⟩
    have addedPrefix : (nonce + 1) ::
        (nonceTagWord ||| ((~~~ addressMask) &&&
          Sevm.argWord frame.sevm 0)) ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+ afterAdd.stack := by
      have added := prefix_of_add addStep onePrefix
      simpa only [B256.add_comm] using added
    rcases Line.of_run_cons nonceRun with
      ⟨afterSwap, swapStep, emptyNonce⟩
    cases emptyNonce
    have swapCore : Stack.Swap (0 : Fin 16).val
        ((nonce + 1) ::
          (nonceTagWord ||| ((~~~ addressMask) &&&
            Sevm.argWord frame.sevm 0)) ::
          ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
          frame.sevm.benvStat.chainId.toB256 :: [])
        ((nonceTagWord ||| ((~~~ addressMask) &&&
            Sevm.argWord frame.sevm 0)) ::
          (nonce + 1) ::
          ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
          frame.sevm.benvStat.chainId.toB256 :: []) :=
      Stack.swapCore_zero
    have storePrefix :
        (nonceTagWord ||| ((~~~ addressMask) &&&
          Sevm.argWord frame.sevm 0)) ::
        (nonce + 1) ::
        ((~~~ addressMask) &&& Sevm.argWord frame.sevm 0) ::
        frame.sevm.benvStat.chainId.toB256 :: [] <<+
          storeCursor.pre.stack :=
      Stack.prefix_of_swap swapCore (of_run_swap swapStep) addedPrefix
    rcases storeCursor.balanceSstoreOccurrence_after_invalidKeyStore
        atStore occurrence
        (runtimeNonceKey_not_valid (Sevm.argWord frame.sevm 0))
        storePrefix with
      ⟨afterNonceCursor, insideAfterNonce⟩
    rcases afterNonceCursor.balanceSstoreOccurrence_routedToCall
        context.invocation.2.2.2
        (permitAfterNonceStore_routedToRecover dp)
        insideAfterNonce with
      ⟨body, bodyLookup, recoverCursor, insideRecover⟩
    have bodyEq : body = permitRecover := by
      simpa [permitRecoverSlot, weth10, weth10Aux] using bodyLookup.symm
    subst body
    exact recoverCursor.no_balanceSstoreOccurrence_permitRecover
      insideRecover occurrence context
  · rcases deadlineErrorCallCursor.balanceSstoreOccurrence_call
        context.invocation.2.2.2 insideDeadlineError with
      ⟨body, bodyLookup, errorCursor, insideErrorBody⟩
    have bodyEq : body = expiredPermitError := by
      simpa [expiredPermitErrorSlot, weth10, weth10Aux] using
        bodyLookup.symm
    subst body
    exact (errorCursor.no_balanceSstoreOccurrence_of_free
      context.invocation.2.2.2 (expiredPermitError_sstoreFree _)
      insideErrorBody).elim

/-- Full reverse classification for an arbitrary actual receive-path balance
write, including the retained rich effect, genuine emitter, and debit record. -/
theorem Exec.Frame.BalanceSstoreOccurrence.classify_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (empty : frame.sevm.data.length.toB256 = 0) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  rcases occurrence.fromMainCursor context with ⟨mainCursor, fromMain⟩
  rcases mainCursor.balanceSstoreOccurrence_main fromMain with
    ⟨dispatchCursor, nonempty, inside⟩ |
      ⟨receiveCursor, _selectedEmpty, inside⟩
  · exact (nonempty empty).elim
  · have role := receiveCursor.balanceSstoreRole_mintCaller
      inside occurrence context
    cases classified : frame.flowAction? dp ca with
    | none =>
        unfold Exec.Frame.flowAction? at classified
        rw [if_pos context.invocation] at classified
        simp [primaryFlowAtom, empty] at classified
    | some action =>
        have atomEq : action.atom =
            .ordinaryMint frame.sevm.caller.toB256 frame.sevm.caller
              frame.sevm.value.toNat := by
          have selected :=
            frame.primaryFlowAtom_eq_some_of_flowAction_eq_some
              context classified
          simpa [primaryFlowAtom, empty] using selected.symm
        refine ⟨action,
          occurrence.classify_of_role context classified ?_⟩
        rw [atomEq]
        exact role

/-- Reach the exact generated receive body while preserving its original
proof-indexed frame execution. -/
private theorem Exec.Frame.compiledReceiveCursor
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (empty : frame.sevm.data.length.toB256 = 0) :
    ∃ receiveCursor : frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        receiveEther frame.post,
      [] <<+ receiveCursor.pre.stack ∧ receiveCursor.actions = [] := by
  rcases frame.compiledMainCursor context with
    ⟨mainCursor, mainActions⟩
  change frame.CompiledCursor dp ca
    ((weth10 dp).main :: weth10Aux)
    (table 0 ((weth10 dp).main :: weth10Aux))
    ([Ninst.calldatasize, Ninst.iszero] +++
      (receiveEther <?>
        (fsig +++ dispatchWith fallbackSlot (weth10Tree dp))))
    frame.post at mainCursor
  rcases mainCursor.peelChildlessLine
      (by simp [NinstIsChildless]) with
    ⟨entryBranchCursor, entryLine, entryActions⟩
  have flagPrefix :
      [frame.sevm.data.length.toB256 =? 0] <<+
        entryBranchCursor.pre.stack := by
    rcases Line.of_run_cons entryLine with
      ⟨afterSize, sizeStep, restSize⟩
    rcases Line.of_run_cons restSize with
      ⟨afterZero, zeroStep, emptyLine⟩
    cases emptyLine
    have sizePrefix : [frame.sevm.data.length.toB256] <<+
        afterSize.stack :=
      prefix_of_push (of_run_calldatasize sizeStep) nil_pref
    exact prefix_of_iszero zeroStep sizePrefix
  rw [empty] at flagPrefix
  have one : ((0 : B256) =? 0) = 1 := by simp [B256.eqCheck]
  rw [one] at flagPrefix
  rcases entryBranchCursor.selectBranchSucc (flag := (1 : B256))
      (by decide) flagPrefix with
    ⟨receiveCursor, receiveStack, receiveActions⟩
  exact ⟨receiveCursor, receiveStack,
    receiveActions.trans (entryActions.trans mainActions)⟩

/-- The receive branch's unique source `SSTORE` is an actual balance-region
occurrence at the caller key, with the exact word computed by its immediate
load/add prefix. -/
theorem Exec.Frame.exists_balanceSstoreOccurrence_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (empty : frame.sevm.data.length.toB256 = 0) :
    ∃ (storePre storePost : Devm) (slot : Xlot),
      frame.BalanceSstoreOccurrence dp ca storePre storePost slot
        frame.sevm.caller.toB256
        (Stor.rest (Devm.getStor storePre ca) frame.sevm.caller +
          Nat.toB256 frame.sevm.value.toNat)
        frame.sevm.caller := by
  rcases frame.compiledReceiveCursor context empty with
    ⟨receiveCursor, _receiveStack, _receiveActions⟩
  rw [receiveEther_eq_sstoreSplit] at receiveCursor
  rcases receiveCursor.peelChildlessLine
      (by simp [mintCallerBeforeSstore, NinstIsChildless]) with
    ⟨storeCursor, prefixRun, _prefixActions⟩
  rcases Line.of_run_cons prefixRun with
    ⟨afterCaller, callerStep, restCaller⟩
  rcases Line.of_run_cons restCaller with
    ⟨afterLoad, loadStep, restLoad⟩
  rcases Line.of_run_cons restLoad with
    ⟨afterValue, valueStep, restValue⟩
  rcases Line.of_run_cons restValue with
    ⟨afterAdd, addStep, restAdd⟩
  rcases Line.of_run_cons restAdd with
    ⟨afterCallerAgain, callerAgainStep, emptyLine⟩
  cases emptyLine
  have callerPrefix : [frame.sevm.caller.toB256] <<+
      afterCaller.stack :=
    prefix_of_push (of_run_caller callerStep) nil_pref
  rcases prefix_of_sload loadStep callerPrefix with
    ⟨callerBalance, balancePrefix, callerBalanceEq⟩
  have valuePrefix : [frame.sevm.value, callerBalance] <<+
      afterValue.stack :=
    prefix_of_push (of_run_callvalue valueStep) balancePrefix
  have sumPrefix : [frame.sevm.value + callerBalance] <<+
      afterAdd.stack :=
    prefix_of_add addStep valuePrefix
  have storePrefix :
      [frame.sevm.caller.toB256, frame.sevm.value + callerBalance] <<+
        storeCursor.pre.stack :=
    prefix_of_push (of_run_caller callerAgainStep) sumPrefix
  have storLoad : Devm.getStor afterCaller = Devm.getStor afterLoad :=
    Ninst.Hinv.inv (f := Devm.getStor) loadStep
  have storValue : Devm.getStor afterLoad = Devm.getStor afterValue :=
    Ninst.Hinv.inv (f := Devm.getStor) valueStep
  have storAdd : Devm.getStor afterValue = Devm.getStor afterAdd :=
    Ninst.Hinv.inv (f := Devm.getStor) addStep
  have storCaller : Devm.getStor afterAdd = Devm.getStor storeCursor.pre :=
    Ninst.Hinv.inv (f := Devm.getStor) callerAgainStep
  have callerBalanceAtStore :
      callerBalance =
        (Devm.getStor storeCursor.pre frame.sevm.currentTarget).get
          frame.sevm.caller.toB256 := by
    rw [callerBalanceEq]
    change
      (Devm.getStor afterCaller frame.sevm.currentTarget).get
          frame.sevm.caller.toB256 = _
    rw [storLoad, storValue, storAdd, storCaller]
  have target : frame.sevm.currentTarget = ca := context.invocation.2.1
  have storedWord :
      frame.sevm.value + callerBalance =
        Stor.rest (Devm.getStor storeCursor.pre ca) frame.sevm.caller +
          Nat.toB256 frame.sevm.value.toNat := by
    rw [Jaune.toB256_toNat, callerBalanceAtStore, target]
    simp only [Stor.rest, Function.comp_apply]
    exact B256.add_comm
  rcases storeCursor.selectNextChildless
      (by simp [NinstIsChildless]) with
    ⟨tailCursor, slot, _storeRun, occurrence, _storeActions⟩
  refine ⟨storeCursor.pre, tailCursor.pre, slot, occurrence,
    balanceKey_valid frame.sevm.caller, rfl, [], ?_⟩
  rw [← storedWord]
  exact storePrefix

/-- The concrete receive write is classified as the ordinary-mint credit of
the same frame action, with rich storage, genuine emitter, and accepted-debit
evidence attached. -/
theorem Exec.Frame.exists_balanceSstoreClassification_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (empty : frame.sevm.data.length.toB256 = 0)
    (classified : frame.flowAction? dp ca = some action) :
    ∃ (storePre storePost : Devm) (slot : Xlot),
      frame.BalanceSstoreClassification dp ca storePre storePost slot
        frame.sevm.caller.toB256
        (Stor.rest (Devm.getStor storePre ca) frame.sevm.caller +
          Nat.toB256 frame.sevm.value.toNat)
        frame.sevm.caller action := by
  rcases frame.exists_balanceSstoreOccurrence_of_receive context empty with
    ⟨storePre, storePost, slot, occurrence⟩
  have atomEq : action.atom =
      .ordinaryMint frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.value.toNat := by
    have selected :=
      frame.primaryFlowAtom_eq_some_of_flowAction_eq_some context classified
    simpa [primaryFlowAtom, empty] using selected.symm
  refine ⟨storePre, storePost, slot,
    occurrence.classify_of_role context classified ?_⟩
  rw [atomEq]
  exact BalanceSstoreRole.ordinaryMintCredit
    frame.sevm.caller.toB256 frame.sevm.caller frame.sevm.value.toNat

private theorem name_sstoreFree (fs : List Func) :
    Func.sstoreFreeWithin 64 fs name = true := by
  rfl

/-- Cast an occurrence cursor through one exact dispatcher-pair equality
without dependent-eliminating the whole concrete function body. -/
private theorem Exec.Frame.CompiledCursor.castSourceWithOccurrence_of_pairEq
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {sig targetSig : B256} {source targetSource : Func}
    {final stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable source final)
    (pairEq : (sig, source) = (targetSig, targetSource))
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sstore) stepPre stepPost slot) :
    sig = targetSig ∧
      ∃ targetCursor : frame.CompiledCursor dp ca fs sourceTable
          targetSource final,
        frame.NinstOccurrenceFromCursor targetCursor (.reg .sstore)
          stepPre stepPost slot := by
  have sigEq : sig = targetSig := congrArg Prod.fst pairEq
  have sourceEq : source = targetSource := congrArg Prod.snd pairEq
  rcases cursor.castSourceWithOccurrence sourceEq occurrence with
    ⟨targetCursor, _preEq, insideTarget⟩
  exact ⟨sigEq, targetCursor, insideTarget⟩

/-- Exhaust the exact 27-entry generated dispatcher after retaining the live
selector body cursor.  Mutating flow bodies are classified at their executed
balance sites; allowance/nonce stores are rejected from the address-shaped
region, and every remaining body has a local no-SSTORE certificate. -/
private theorem Exec.Frame.BalanceSstoreOccurrence.classify_of_nonempty
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder)
    (context : frame.AuthenticContext dp ca)
    (nonempty : frame.sevm.data.length.toB256 ≠ 0) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  rcases occurrence.fromMainCursor context with ⟨mainCursor, fromMain⟩
  rcases mainCursor.balanceSstoreOccurrence_selectorBody fromMain context
      nonempty with
    ⟨body, member, bodyCursor, _bodyStack, insideBody⟩
  simp only [weth10Funcs, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        context.invocation.2.2.2 (name_sstoreFree _)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨approveCursor, insideApprove⟩
    change frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (approvePrefix +++ returnTrue) frame.post at approveCursor
    have tailFree : Func.sstoreFreeWithin 512
          ((weth10 dp).main :: weth10Aux)
          (approveEntryAfterStore returnTrue) = true := by
      rfl
    exact (approveCursor.no_balanceSstoreOccurrence_approvePrefixThen
        insideApprove occurrence context tailFree).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨coreCursor, insideCore⟩
    rcases coreCursor.balanceSstorePrimaryRole_withdrawTo insideCore
          occurrence context selectorEq nonempty with
        ⟨primary, role⟩
    exact occurrence.classify_of_primary_role context primary role
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨coreCursor, insideCore⟩
    exact coreCursor.classifyBalanceSstore_transferFrom insideCore
      occurrence context selectorEq nonempty
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨coreCursor, insideCore⟩
    rcases coreCursor.balanceSstorePrimaryRole_withdraw insideCore
          occurrence context selectorEq nonempty with
        ⟨primary, role⟩
    exact occurrence.classify_of_primary_role context primary role
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨coreCursor, insideCore⟩
    exact coreCursor.classifyBalanceSstore_transferAndCall insideCore
      occurrence context selectorEq nonempty
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨coreCursor, insideCore⟩
    exact coreCursor.classifyBalanceSstore_flashLoan insideCore
      occurrence context selectorEq nonempty
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstorePrimaryRole_depositToAndCall insideCase
          occurrence context selectorEq nonempty with
        ⟨primary, role⟩
    exact occurrence.classify_of_primary_role context primary role
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨coreCursor, insideCore⟩
    exact coreCursor.classifyBalanceSstore_withdrawFrom insideCore
      occurrence context selectorEq nonempty
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨coreCursor, insideCore⟩
    exact coreCursor.classifyBalanceSstore_transfer insideCore
      occurrence context selectorEq nonempty
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstorePrimaryRole_depositTo insideCase
          occurrence context selectorEq nonempty with
        ⟨primary, role⟩
    exact occurrence.classify_of_primary_role context primary role
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨approveCallCursor, insideApproveCall⟩
    let callback :=
      callBoolCallback onTokenApprovalSelector 0 2 (arg 1)
    change frame.CompiledCursor dp ca
        ((weth10 dp).main :: weth10Aux)
        (table 0 ((weth10 dp).main :: weth10Aux))
        (approvePrefix +++ callback) frame.post at approveCallCursor
    have tailFree : Func.sstoreFreeWithin 2048
          ((weth10 dp).main :: weth10Aux)
          (approveEntryAfterStore callback) = true := by
      rfl
    exact (approveCallCursor.no_balanceSstoreOccurrence_approvePrefixThen
      insideApproveCall occurrence context tailFree).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstorePrimaryRole_deposit insideCase
          occurrence context selectorEq nonempty with
        ⟨primary, role⟩
    exact occurrence.classify_of_primary_role context primary role
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    rcases caseCursor.balanceSstoreOccurrence_nonpayable
          context.invocation.2.2.2 insideCase with
        ⟨permitCursor, insidePermit⟩
    exact (permitCursor.no_balanceSstoreOccurrence_permit
      insidePermit occurrence context).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 263) context.invocation.2.2.2 (by
          change Func.sstoreFreeWithin 256
            ((weth10 dp).main :: weth10Aux) flashTokenError = true
          exact flashTokenError_sstoreFree _)
        insideCase).elim
  · rcases bodyCursor.castSourceWithOccurrence_of_pairEq h insideBody with
      ⟨_selectorEq, caseCursor, insideCase⟩
    exact (caseCursor.no_balanceSstoreOccurrence_nonpayable_of_free
        (fuel := 256) context.invocation.2.2.2 (by rfl)
        insideCase).elim

/-! ## Dynamic reverse-completeness boundary -/

/-- The remaining local compiled-program obligation, stated over every actual
balance-region `SSTORE` occurrence in an authentic exact WETH10 frame.  It has
no endpoint balance equation, log list, or preselected action hypothesis. -/
def CompiledBalanceSstoreReverseComplete (dp : DeployParams) (ca : Adr) :
    Prop :=
  ∀ (frame : Exec.Frame), frame.AuthenticContext dp ca →
    ∀ (stepPre stepPost : Devm) (slot : Xlot)
      (key value : B256) (holder : Adr),
      frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
        key value holder →
      ∃ action : FlowAction,
        frame.BalanceSstoreClassification dp ca stepPre stepPost slot
          key value holder action

/-- Concrete dynamic reverse completeness of the generated WETH10 program,
including no-op stores and excluding tagged allowance, nonce, and flash
counter writes by their executed keys. -/
theorem compiledBalanceSstoreReverseComplete
    (dp : DeployParams) (ca : Adr) :
    CompiledBalanceSstoreReverseComplete dp ca := by
  intro frame context stepPre stepPost slot key value holder occurrence
  by_cases empty : frame.sevm.data.length.toB256 = 0
  · exact occurrence.classify_of_receive context empty
  · exact occurrence.classify_of_nonempty context empty

/-- Once local reverse completeness is discharged against the generated
program, the structural committed-frame traversal lifts it to arbitrary
nested depth.  The independently required `exactInvocation` premise excludes
foreign callbacks, lookalike code, and WETH bytes executed against another
account's storage by `DELEGATECALL`/`CALLCODE`. -/
theorem Exec.balanceSstoreClassification_of_mem_committedFrames
    {dp : DeployParams} {ca : Adr}
    (complete : CompiledBalanceSstoreReverseComplete dp ca)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (rootPc : pc = 0) (rootMemory : pre.memory = Mem.empty)
    {frame : Exec.Frame}
    (retained : frame ∈ Exec.committedFrames run)
    (invocation : frame.exactInvocation dp ca)
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  have context :=
    frame.authenticContext_of_mem_committedFrames_exactInvocation
      run installed rootPc rootMemory retained invocation
  exact complete frame context stepPre stepPost slot key value holder occurrence

/-- Premise-free program-level C2 theorem: every address-shaped `SSTORE` in
an exact retained WETH10 frame is classified by the committed holder-flow
action selected for that frame. -/
theorem Exec.weth10BalanceSstoreClassification_of_mem_committedFrames
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (installed : some (pre.getCode ca).toList = Prog.compile (weth10 dp))
    (rootPc : pc = 0) (rootMemory : pre.memory = Mem.empty)
    {frame : Exec.Frame}
    (retained : frame ∈ Exec.committedFrames run)
    (invocation : frame.exactInvocation dp ca)
    {stepPre stepPost : Devm} {slot : Xlot}
    {key value : B256} {holder : Adr}
    (occurrence : frame.BalanceSstoreOccurrence dp ca stepPre stepPost slot
      key value holder) :
    ∃ action : FlowAction,
      frame.BalanceSstoreClassification dp ca stepPre stepPost slot
        key value holder action := by
  exact Exec.balanceSstoreClassification_of_mem_committedFrames
    (compiledBalanceSstoreReverseComplete dp ca) run installed rootPc
    rootMemory retained invocation occurrence

end Weth10

end Blanc
