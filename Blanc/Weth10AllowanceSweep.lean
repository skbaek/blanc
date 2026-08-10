import Blanc.Weth10HolderFlowWriteCompleteness

/-!
Read-side (`SLOAD`) analog of the no-`SSTORE` sweep machinery, plus the fully
generic no-`SSTORE` sweep with no balance key-shape constraint.

`Func.sloadFreeWithin` mirrors `Func.sstoreFreeWithin`: an executable
fuel-bounded certificate that a source body and every table body it can call
within the fuel contain no `SLOAD`.  Soundness walks the executed compiled
cursor exactly as `no_balanceSstoreOccurrence_of_free` does, ruling out the
compiler's PUSH/JUMPI/JUMP/JUMPDEST glue at each hidden step.  The glue
traversal is proved once for an arbitrary `.reg` instruction, so the same
spine also discharges the generic `SSTORE` sweep needed by the allowance
write side.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- `false` exactly on `SLOAD`; the head test of the read-side certificate. -/
def ninstSloadFree : Ninst → Bool
  | .reg .sload => false
  | _ => true

theorem ninst_ne_sload_of_free {source : Ninst}
    (free : ninstSloadFree source = true) :
    source ≠ .reg .sload := by
  cases source with
  | reg operation =>
      cases operation <;> simp [ninstSloadFree] at free ⊢
  | exec operation => simp
  | push bytes size => simp

/-- Executable finite certificate that a source body and every table body it
can call within `fuel` contain no `SLOAD`.  A zero fuel is deliberately
false, so a successful certificate can never hide a recursive call cycle. -/
def Func.sloadFreeWithin : Nat → List Func → Func → Bool
  | 0, _, _ => false
  | fuel + 1, fs, .branch left right =>
      sloadFreeWithin fuel fs left && sloadFreeWithin fuel fs right
  | _fuel + 1, _, .last _ => true
  | fuel + 1, fs, .next source tail =>
      ninstSloadFree source && sloadFreeWithin fuel fs tail
  | fuel + 1, fs, .call k =>
      match fs[k]? with
      | none => false
      | some body => sloadFreeWithin fuel fs body

/-- A call-free source certificate is independent of the installed function
table.  This lets fixed local error bodies be computed against `[]` without
reducing the parameterized WETH program. -/
theorem Func.sloadFreeWithin_eq_of_noCalls
    {fuel : Nat} {body : Func} (noCalls : body.NoCalls)
    (left right : List Func) :
    Func.sloadFreeWithin fuel left body =
      Func.sloadFreeWithin fuel right body := by
  induction fuel generalizing body with
  | zero => rfl
  | succ fuel ih =>
      cases body with
      | branch first second =>
          simp only [Func.NoCalls] at noCalls
          simp only [Func.sloadFreeWithin]
          rw [ih noCalls.1, ih noCalls.2]
      | last terminal => rfl
      | next source tail =>
          simp only [Func.NoCalls] at noCalls
          simp only [Func.sloadFreeWithin]
          rw [ih noCalls]
      | call k => simp [Func.NoCalls] at noCalls

/-! ## Generic glue traversal

The reverse cursor traversal below is the sstore sweep's, restated for an
arbitrary `.reg` instruction: the compiler's branch and call glue consists of
`PUSH`, `JUMPI`, `JUMP`, and `JUMPDEST` only, so it can host no `.reg`
instruction whatsoever.  Instantiating the swept instruction recovers the
`SSTORE` spine and yields the `SLOAD` one. -/

private theorem Ninst.At.eq_of_at
    {code : ByteArray} {pc : Nat} {left right : Ninst}
    (leftAt : Ninst.At code pc left) (rightAt : Ninst.At code pc right) :
    left = right := by
  unfold Ninst.At at leftAt rightAt
  simpa only [Option.some.injEq, Inst.next.injEq] using
    leftAt.symm.trans rightAt

private theorem Ninst.At.false_of_jinstAt
    {code : ByteArray} {pc : Nat} {n : Ninst} {j : Jinst}
    (nextAt : Ninst.At code pc n) (jumpAt : Jinst.At code pc j) : False := by
  unfold Ninst.At at nextAt
  unfold Jinst.At at jumpAt
  rw [nextAt] at jumpAt
  cases jumpAt

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

/-- A same-frame compiler prefix all of whose current instruction boundaries
are known not to be the swept instruction `n`. -/
private inductive Exec.Deriv.ParentNonNinstPrefix
    (dp : DeployParams) (ca : Adr) (n : Ninst) :
    Exec.Deriv → Exec.Deriv → Prop
  | refl (root : Exec.Deriv) : ParentNonNinstPrefix dp ca n root root
  | step {root next tail : Exec.Deriv}
      (edge : Exec.Deriv.ParentStepActions dp ca next root [])
      (notAt : ¬ Ninst.At root.sevm.code root.pc n)
      (rest : ParentNonNinstPrefix dp ca n next tail) :
      ParentNonNinstPrefix dp ca n root tail

/-- Remove a compiler-only prefix free of the swept instruction from an
arbitrary occurrence of that instruction, retaining its exact machine states,
recursive slot, and same-frame continuation proof. -/
private theorem Exec.Deriv.ParentNonNinstPrefix.trim_ninstOccurrence
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {start tail : Exec.Deriv} {n : Ninst}
    (compilerPrefix : Exec.Deriv.ParentNonNinstPrefix dp ca n start tail)
    {stepPre stepPost : Devm} {slot : Xlot}
    (occurrence : frame.NinstOccurrenceFromDeriv dp ca start
      n stepPre stepPost slot) :
    frame.NinstOccurrenceFromDeriv dp ca tail
      n stepPre stepPost slot := by
  induction compilerPrefix with
  | refl => exact occurrence
  | @step root next tail edge notAt rest ih =>
      rcases occurrence with
        ⟨pc, current, continuation, crossed, selected, hpath, hat,
          filled, stepRun, prec, occurrenceEdge⟩
      cases hpath with
      | refl => exact (notAt hat).elim
      | @step _ occurrenceNext _ headActions tailActions head suffix =>
          have unique := edge.unique head
          cases unique.1
          cases unique.2
          apply ih
          exact ⟨pc, current, continuation, tailActions, selected, suffix,
            hat, filled, stepRun, prec, occurrenceEdge⟩

/-- Generic reverse source traversal through a compiled branch: an actual
`.reg` occurrence in the branch suffix belongs to the one source arm selected
by the original execution, never to the compiler's branch glue. -/
private theorem Exec.Frame.CompiledCursor.regOccurrence_branch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {left right : Func} {final : Devm}
    {r : Rinst} {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable
      (.branch left right) final)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg r) stepPre stepPost slot) :
    (∃ arm : frame.CompiledCursor dp ca fs sourceTable left final,
      frame.NinstOccurrenceFromCursor arm (.reg r)
        stepPre stepPost slot) ∨
    (∃ arm : frame.CompiledCursor dp ca fs sourceTable right final,
      frame.NinstOccurrenceFromCursor arm (.reg r)
        stepPre stepPost slot) := by
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
      have pushNotReg : ¬ Ninst.At frame.sevm.code cursor.pc
          (.reg r) := by
        intro regAt
        have impossible := Ninst.At.eq_of_at regAt pushAt
        cases impossible
      have jumpiNotReg : ¬ Ninst.At frame.sevm.code (cursor.pc + 3)
          (.reg r) := fun regAt =>
        Ninst.At.false_of_jinstAt regAt jumpiAt
      have compilerPrefix : Exec.Deriv.ParentNonNinstPrefix dp ca (.reg r)
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
          ⟨arm.pc, frame.sevm, arm.pre, frame.out, arm.current⟩ :=
        .step pushEdge pushNotReg
          (.step jumpiEdge jumpiNotReg (.refl _))
      exact Or.inl ⟨arm, compilerPrefix.trim_ninstOccurrence occurrence⟩
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
      have pushNotReg : ¬ Ninst.At frame.sevm.code cursor.pc
          (.reg r) := by
        intro regAt
        have impossible := Ninst.At.eq_of_at regAt pushAt
        cases impossible
      have jumpiNotReg : ¬ Ninst.At frame.sevm.code (cursor.pc + 3)
          (.reg r) := fun regAt =>
        Ninst.At.false_of_jinstAt regAt jumpiAt
      have jumpdestNotReg : ¬ Ninst.At frame.sevm.code loc
          (.reg r) := fun regAt =>
        Ninst.At.false_of_jinstAt regAt jumpdestAt
      have compilerPrefix : Exec.Deriv.ParentNonNinstPrefix dp ca (.reg r)
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
          ⟨arm.pc, frame.sevm, arm.pre, frame.out, arm.current⟩ :=
        .step pushEdge pushNotReg
          (.step jumpiEdge jumpiNotReg
            (.step jumpdestEdge jumpdestNotReg (.refl _)))
      exact Or.inr ⟨arm, compilerPrefix.trim_ninstOccurrence occurrence⟩

/-- Generic reverse source traversal through a compiled internal call.  An
actual `.reg` occurrence in the call suffix belongs to the selected table
body, not to the call's compiler-generated transfer of control. -/
private theorem Exec.Frame.CompiledCursor.regOccurrence_call
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {k : Nat} {final : Devm}
    {r : Rinst} {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) (.call k) final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg r) stepPre stepPost slot) :
    ∃ body,
      (f₀ :: aux)[k]? = some body ∧
      ∃ bodyCursor : frame.CompiledCursor dp ca (f₀ :: aux)
          (table 0 (f₀ :: aux)) body final,
        frame.NinstOccurrenceFromCursor bodyCursor (.reg r)
          stepPre stepPost slot := by
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
      have pushNotReg : ¬ Ninst.At frame.sevm.code cursor.pc
          (.reg r) := by
        intro regAt
        have impossible := Ninst.At.eq_of_at regAt hpush
        cases impossible
      have jumpNotReg : ¬ Ninst.At frame.sevm.code (cursor.pc + 3)
          (.reg r) := fun regAt =>
        Ninst.At.false_of_jinstAt regAt hjump
      have jumpdestNotReg : ¬ Ninst.At frame.sevm.code loc
          (.reg r) := fun regAt =>
        Ninst.At.false_of_jinstAt regAt hjumpdest
      have compilerPrefix : Exec.Deriv.ParentNonNinstPrefix dp ca (.reg r)
          ⟨cursor.pc, frame.sevm, cursor.pre, frame.out, cursor.current⟩
          ⟨bodyCursor.pc, frame.sevm, bodyCursor.pre, frame.out,
            bodyCursor.current⟩ :=
        .step pushEdge pushNotReg
          (.step jumpEdge jumpNotReg
            (.step jumpdestEdge jumpdestNotReg (.refl _)))
      exact ⟨_, hget, bodyCursor,
        compilerPrefix.trim_ninstOccurrence occurrence⟩

/-- A terminal source node hosts no `Ninst` occurrence at all: its cursor
position holds a `Linst`, and the frame halts there. -/
private theorem Exec.Frame.CompiledCursor.no_ninstOccurrence_last
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {fs : List Func} {sourceTable : List (Nat × Func)}
    {i : Linst} {final : Devm}
    {n : Ninst} {stepPre stepPost : Devm} {slot : Xlot}
    (cursor : frame.CompiledCursor dp ca fs sourceTable (.last i) final)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      n stepPre stepPost slot) : False := by
  cases hrun : cursor.run with
  | last terminalRun =>
      rcases occurrence with
        ⟨pc, current, continuation, crossed, selected, hpath, instAt,
          filled, stepRun, prec, edge⟩
      have lastAt : Linst.At frame.sevm.code cursor.pc i :=
        Linst.at_of_slice cursor.codeSlice
      have outEq : frame.out = .ok final :=
        (cursor.current.last_inv lastAt).trans terminalRun
      have terminalStep : Evm.step
          ⟨cursor.pc, frame.sevm, cursor.pre⟩ = .halt frame.out := by
        rw [Evm.step_last lastAt, terminalRun, ← outEq]
      cases hpath with
      | refl => exact Ninst.At.false_of_linstAt instAt lastAt
      | step head rest =>
          exact head.false_of_halt terminalStep

/-- Soundness of the executable no-SLOAD certificate against an arbitrary
actual occurrence, with no key-shape constraint.  The proof still follows the
executed cursor branch/call; the Boolean is only the finite source
certificate used to close that path. -/
theorem Exec.Frame.CompiledCursor.no_sloadOccurrence_of_free
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {f₀ : Func} {aux : List Func} {body : Func} {final : Devm}
    {stepPre stepPost : Devm} {slot : Xlot} {fuel : Nat}
    (cursor : frame.CompiledCursor dp ca (f₀ :: aux)
      (table 0 (f₀ :: aux)) body final)
    (hcode : some frame.sevm.code.toList = Prog.compile ⟨f₀, aux⟩)
    (free : Func.sloadFreeWithin fuel (f₀ :: aux) body = true)
    (occurrence : frame.NinstOccurrenceFromCursor cursor
      (.reg .sload) stepPre stepPost slot) : False := by
  induction fuel generalizing body with
  | zero => simp [Func.sloadFreeWithin] at free
  | succ fuel ih =>
      cases body with
      | branch left right =>
          simp [Func.sloadFreeWithin] at free
          rcases cursor.regOccurrence_branch occurrence with
            ⟨leftCursor, inside⟩ | ⟨rightCursor, inside⟩
          · exact ih leftCursor free.1 inside
          · exact ih rightCursor free.2 inside
      | last i =>
          exact cursor.no_ninstOccurrence_last occurrence
      | next source tail =>
          simp [Func.sloadFreeWithin] at free
          have notLoad := ninst_ne_sload_of_free free.1
          rcases cursor.ninstOccurrenceFromCursor_head_or_tail
              occurrence with
            ⟨sourceEq, _preEq⟩ |
              ⟨tailCursor, _sourceSlot, _sourceOccurrence, inside⟩
          · exact (notLoad sourceEq.symm).elim
          · exact ih tailCursor free.2 inside
      | call k =>
          cases hlookup : (f₀ :: aux)[k]? with
          | none => simp [Func.sloadFreeWithin, hlookup] at free
          | some called =>
            simp [Func.sloadFreeWithin, hlookup] at free
            rcases cursor.regOccurrence_call hcode occurrence with
              ⟨actualBody, actualLookup, bodyCursor, inside⟩
            have bodyEq : actualBody = called :=
              Option.some.inj (actualLookup.symm.trans hlookup)
            subst actualBody
            exact ih bodyCursor free inside

/-- Generic soundness of the executable no-SSTORE certificate: a
certified-free region hosts no `SSTORE` occurrence at all, with no balance
key-shape constraint. -/
theorem Exec.Frame.CompiledCursor.no_sstoreOccurrence_of_free
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
          rcases cursor.regOccurrence_branch occurrence with
            ⟨leftCursor, inside⟩ | ⟨rightCursor, inside⟩
          · exact ih leftCursor free.1 inside
          · exact ih rightCursor free.2 inside
      | last i =>
          exact cursor.no_ninstOccurrence_last occurrence
      | next source tail =>
          simp [Func.sstoreFreeWithin] at free
          have notStore : source ≠ .reg .sstore := by
            intro sourceEq
            rw [sourceEq] at free
            exact absurd free.1 (by decide)
          rcases cursor.ninstOccurrenceFromCursor_head_or_tail
              occurrence with
            ⟨sourceEq, _preEq⟩ |
              ⟨tailCursor, _sourceSlot, _sourceOccurrence, inside⟩
          · exact (notStore sourceEq.symm).elim
          · exact ih tailCursor free.2 inside
      | call k =>
          cases hlookup : (f₀ :: aux)[k]? with
          | none => simp [Func.sstoreFreeWithin, hlookup] at free
          | some called =>
            simp [Func.sstoreFreeWithin, hlookup] at free
            rcases cursor.regOccurrence_call hcode occurrence with
              ⟨actualBody, actualLookup, bodyCursor, inside⟩
            have bodyEq : actualBody = called :=
              Option.some.inj (actualLookup.symm.trans hlookup)
            subst actualBody
            exact ih bodyCursor free inside

end Weth10

end Blanc
