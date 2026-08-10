import Blanc.Weth10HolderFlowAuthenticity
import Blanc.Weth10HolderFlowCompiled

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

/-- Local copy of the compiler slice fact needed by the reverse traversal;
unlike byte-wise PC enumeration, it recognizes only a genuine source-node
boundary and therefore cannot mistake `0x55` inside PUSH payload data for an
executed `SSTORE` source site. -/
private theorem ninstAt_of_subcode_next_writeCompleteness
    {code : ByteArray} {sourceTable : List (Nat × Func)} {pc : Nat}
    {n : Ninst} {tail : Func}
    (sub : subcode code.toList pc
      (Func.compile sourceTable pc (.next n tail))) :
    Ninst.At code pc n := by
  rcases of_subcode sub with ⟨compiled, compiledEq, slice⟩
  rcases of_bind_eq_some compiledEq with ⟨rest, restEq, headEq⟩
  simp [pure] at headEq
  rw [← headEq] at slice
  exact Ninst.at_of_slice (List.slice_prefix slice)

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
        ninstAt_of_subcode_next_writeCompleteness cursor.codeSlice
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

private theorem Devm.eq_of_burnBy_writeCompleteness
    {cost : Nat} {pre left right : Devm}
    (hleft : Devm.BurnBy cost pre left)
    (hright : Devm.BurnBy cost pre right) : left = right := by
  apply Devm.eq_of_proj
  · exact hleft.stack.symm.trans hright.stack
  · exact hleft.memory.symm.trans hright.memory
  · have hl := hleft.gasLeft
    have hr := hright.gasLeft
    omega
  · exact hleft.logs.symm.trans hright.logs
  · exact hleft.refundCounter.symm.trans hright.refundCounter
  · exact hleft.output.symm.trans hright.output
  · exact hleft.accountsToDelete.symm.trans hright.accountsToDelete
  · exact hleft.returnData.symm.trans hright.returnData
  · exact hleft.error.symm.trans hright.error
  · exact hleft.accessedAddresses.symm.trans hright.accessedAddresses
  · exact hleft.accessedStorageKeys.symm.trans hright.accessedStorageKeys
  · exact hleft.state.symm.trans hright.state
  · exact hleft.createdAccounts.symm.trans hright.createdAccounts
  · exact hleft.transientStorage.symm.trans hright.transientStorage

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
        Devm.eq_of_burnBy_writeCompleteness
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
  have notDeposit : depositToSelector ≠ depositSelector := by
    decide +kernel
  simp [primaryFlowAtom, nonempty, selectorEq, notDeposit]

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
  have notDeposit : depositToAndCallSelector ≠ depositSelector := by
    decide +kernel
  simp [primaryFlowAtom, nonempty, selectorEq, notDeposit]

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
  have notDeposit : withdrawSelector ≠ depositSelector := by
    decide +kernel
  have notDepositTo : withdrawSelector ≠ depositToSelector := by
    decide +kernel
  have notDepositCall : withdrawSelector ≠ depositToAndCallSelector := by
    decide +kernel
  have notTransfer : withdrawSelector ≠ transferSelector := by
    decide +kernel
  have notTransferCall : withdrawSelector ≠ transferAndCallSelector := by
    decide +kernel
  have notTransferFrom : withdrawSelector ≠ transferFromSelector := by
    decide +kernel
  have primary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.caller (Sevm.argWord frame.sevm 0).toNat) := by
    simp [primaryFlowAtom, nonempty, selectorEq, notDeposit,
      notDepositTo, notDepositCall, notTransfer, notTransferCall,
      notTransferFrom]
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
  have notDeposit : withdrawToSelector ≠ depositSelector := by
    decide +kernel +revert
  have notDepositTo : withdrawToSelector ≠ depositToSelector := by
    decide +kernel
  have notDepositCall : withdrawToSelector ≠ depositToAndCallSelector := by
    decide +kernel
  have notTransfer : withdrawToSelector ≠ transferSelector := by
    decide +kernel
  have notTransferCall : withdrawToSelector ≠ transferAndCallSelector := by
    decide +kernel
  have notTransferFrom : withdrawToSelector ≠ transferFromSelector := by
    decide +kernel
  have notWithdraw : withdrawToSelector ≠ withdrawSelector := by
    decide +kernel
  have primary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toNat) := by
    simp [primaryFlowAtom, nonempty, selectorEq, notDeposit,
      notDepositTo, notDepositCall, notTransfer, notTransferCall,
      notTransferFrom, notWithdraw]
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

private theorem transferZeroThen_eq_callerDebitSource
    (continuation : Func) :
    transferZeroThen continuation =
      callerDebitSource 1 burnBalanceErrorSlot
        (transferZeroContinuation continuation) := by
  rfl

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

end Weth10

end Blanc
