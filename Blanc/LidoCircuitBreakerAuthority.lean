import Blanc.LidoCircuitBreakerSites
import Blanc.CycleWriteFree

/-!
Arbitrary-outcome runtime authority for Lido CircuitBreaker.

This module starts at canonical raw frame traversal.  Its structural theorem
does not assume that a store succeeds, commits, changes a cell, or survives
message settlement; guard and invocation-role refinements build on this exact
same-instance source cut.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-- One actually executed nonterminal guard, retained at its exact place before
the nominated write in the selected runtime frame. -/
structure RuntimeGuardOccurrence
    (frameRoot write : Exec.Deriv) (instruction : Ninst) where
  guard : Exec.Deriv
  after : Exec.Deriv
  frameToGuard : Exec.Deriv.ParentPrefix frameRoot guard
  guardToWrite : Exec.Deriv.ParentPrefix guard write
  edge : Exec.Deriv.ParentStep after guard
  decoded : Ninst.At guard.sevm.code guard.pc instruction
  run : Ninst.Run frameRoot.sevm guard.devm instruction after.devm
  strictBefore : Exec.Deriv.lt write guard

/-- Actual selector/continuation evidence for the endpoint whose same-frame
execution reached the nominated write.  The cursor is compiler-structural and
the two prefixes are execution evidence, not a source-only path claim. -/
structure RuntimeEndpointOccurrence
    (dp : DeployParams) (frameRoot write : Exec.Deriv) (source : Func) where
  path : Prog.SourcePath
  cursor : Exec.Deriv.SourceCursor frameRoot (runtime dp) path source
  frameToCursor : Exec.Deriv.ParentPrefix frameRoot cursor.node
  cursorToWrite : Exec.Deriv.ParentPrefix cursor.node write

/-- The six runtime-accepted authority roles, each carrying its actual endpoint
and earlier guard occurrences together with the corresponding invocation-entry
fact.  The indexed role is later checked against the exact source row's
`permittedRoles`; this payload alone does not classify a source site. -/
inductive RuntimeWriteAuthority
    (dp : DeployParams) (frameRoot write : Exec.Deriv) :
    InvocationRole → Prop
  | setPauseDuration
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (setPauseDuration dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin) :
      RuntimeWriteAuthority dp frameRoot write .adminConfiguration
  | setHeartbeatInterval
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (setHeartbeatInterval dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin) :
      RuntimeWriteAuthority dp frameRoot write .adminConfiguration
  | adminRegistry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (registerPauser dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin) :
      RuntimeWriteAuthority dp frameRoot write .adminRegistry
  | adminExpiry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write
        (registerPauser dp))
      (guard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (callerEq : frameRoot.sevm.caller.toB256 = dp.admin) :
      RuntimeWriteAuthority dp frameRoot write .adminExpiry
  | heartbeatExpiry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write heartbeat)
      (registeredGuard : RuntimeGuardOccurrence frameRoot write
        (.reg .iszero))
      (liveGuard : RuntimeGuardOccurrence frameRoot write (.reg .lt))
      (registered : frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (countSlot frameRoot.sevm.caller.toB256) ≠ 0)
      (live : frameRoot.sevm.benvStat.time < frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (expirySlot frameRoot.sevm.caller.toB256)) :
      RuntimeWriteAuthority dp frameRoot write .heartbeatExpiry
  | pauseRegistry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write pause)
      (assignedGuard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (liveGuard : RuntimeGuardOccurrence frameRoot write (.reg .lt))
      (assigned : frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) =
          frameRoot.sevm.caller.toB256)
      (live : frameRoot.sevm.benvStat.time < frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (expirySlot frameRoot.sevm.caller.toB256)) :
      RuntimeWriteAuthority dp frameRoot write .pauseRegistry
  | pauseExpiry
      (endpoint : RuntimeEndpointOccurrence dp frameRoot write pause)
      (assignedGuard : RuntimeGuardOccurrence frameRoot write (.reg .eq))
      (liveGuard : RuntimeGuardOccurrence frameRoot write (.reg .lt))
      (assigned : frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) =
          frameRoot.sevm.caller.toB256)
      (live : frameRoot.sevm.benvStat.time < frameRoot.devm.getStorVal
        frameRoot.sevm.currentTarget
        (expirySlot frameRoot.sevm.caller.toB256)) :
      RuntimeWriteAuthority dp frameRoot write .pauseExpiry

private theorem Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {instruction targetInstruction : Ninst} {tail : Func}
    {initial : Exec.Deriv.SourceCursor root program
      initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target targetInstruction cursor)
    (instructionNe : instruction ≠ targetInstruction) :
    ∃ _chronology : Exec.Deriv.SourceCursor.Chronology
        initial cursor target,
      ∃ tailCursor : Exec.Deriv.SourceCursor root program
          ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail,
        Exec.Deriv.ParentStep tailCursor.node cursor.node ∧
        Exec.Deriv.SourceCursor.Toward
          initial target targetInstruction tailCursor := by
  cases route with
  | atTarget cursor chronology site siteEq sourceMember targetEq instructionEq =>
      exact (instructionNe instructionEq).elim
  | next cursor chronology tailCursor edge rest =>
      exact ⟨chronology, tailCursor, edge, rest⟩

private theorem Exec.Deriv.SourceCursor.Toward.chronology
    {root target : Exec.Deriv} {program : Prog}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {targetInstruction : Ninst}
    {initial : Exec.Deriv.SourceCursor root program
      initialPath initialSource}
    {cursor : Exec.Deriv.SourceCursor root program path source}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target targetInstruction cursor) :
    Exec.Deriv.SourceCursor.Chronology initial cursor target := by
  cases route <;> assumption

private theorem Exec.Deriv.SourceCursor.Toward.dropLine
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {line : Line} {tail : Func}
    {cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (line +++ tail)}
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor)
    (lineNe : ∀ instruction ∈ line,
      instruction ≠ (.reg .sstore)) :
    ∃ tailPath,
      ∃ tailCursor : Exec.Deriv.SourceCursor root (runtime dp)
          tailPath tail,
        Exec.Deriv.SourceCursor.Chronology
            initial tailCursor target ∧
          Exec.Deriv.SourceCursor.Toward
            initial target (.reg .sstore) tailCursor := by
  induction line generalizing path with
  | nil => exact ⟨path, cursor,
      Exec.Deriv.SourceCursor.Toward.chronology route, route⟩
  | cons instruction rest ih =>
      change Exec.Deriv.SourceCursor root (runtime dp) path
        (.next instruction (rest +++ tail)) at cursor
      rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
          (lineNe instruction (by simp)) with
        ⟨chronology, restCursor, edge, restRoute⟩
      exact ih restRoute (fun candidate member =>
        lineNe candidate (by simp [member]))

private theorem Exec.Deriv.SourceCursor.instructionAt
    {root : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {instruction : Ninst} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail)) :
    Ninst.At root.sevm.code cursor.pc instruction := by
  rcases cursor with
    ⟨cursorPc, cursorPre, current, parentPrefix, codeSlice,
      codeBoundary, sourceIncluded⟩
  exact Func.sourceSites_sound codeSlice codeBoundary
    (functionIndex := path.functionIndex) (steps := path.steps)
    (site := { path := path, pc := cursorPc, instruction := instruction })
    (by rcases path with ⟨functionIndex, steps⟩
        simp [Func.sourceSites])

private theorem parentPrefixTrans
    {root middle tail : Exec.Deriv}
    (left : Exec.Deriv.ParentPrefix root middle)
    (right : Exec.Deriv.ParentPrefix middle tail) :
    Exec.Deriv.ParentPrefix root tail := by
  induction left with
  | refl => exact right
  | step head rest ih => exact .step head (ih right)

private def RuntimeGuardOccurrence.ofCursor
    {frameRoot write : Exec.Deriv} {dp : DeployParams}
    {initialPath guardPath : Prog.SourcePath}
    {initialSource tail : Func} {instruction : Ninst}
    {initial : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      initialPath initialSource}
    {guardCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      guardPath (.next instruction tail)}
    {afterCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      ⟨guardPath.functionIndex, guardPath.steps ++ [.rest]⟩ tail}
    (frameToInitial : Exec.Deriv.ParentPrefix frameRoot initial.node)
    (chronology : Exec.Deriv.SourceCursor.Chronology
      initial guardCursor write)
    (edge : Exec.Deriv.ParentStep afterCursor.node guardCursor.node)
    (run : Ninst.Run frameRoot.sevm guardCursor.pre instruction
      afterCursor.pre)
    (targetAt : Ninst.At write.sevm.code write.pc (.reg .sstore))
    (instructionNe : instruction ≠ (.reg .sstore)) :
    RuntimeGuardOccurrence frameRoot write instruction := by
  have decoded := Exec.Deriv.SourceCursor.instructionAt guardCursor
  have distinct : guardCursor.node ≠ write := by
    intro equal
    change Ninst.At guardCursor.node.sevm.code guardCursor.node.pc
      instruction at decoded
    rw [equal] at decoded
    exact instructionNe (Ninst.at_unique decoded targetAt)
  exact
    { guard := guardCursor.node
      after := afterCursor.node
      frameToGuard := parentPrefixTrans frameToInitial chronology.initialToCursor
      guardToWrite := chronology.cursorToTarget
      edge := edge
      decoded := decoded
      run := run
      strictBefore := chronology.strictBefore distinct }

private def RuntimeEndpointOccurrence.ofCursor
    {frameRoot write : Exec.Deriv} {dp : DeployParams}
    {initialPath endpointPath : Prog.SourcePath}
    {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      initialPath initialSource}
    (frameToInitial : Exec.Deriv.ParentPrefix frameRoot initial.node)
    (endpointCursor : Exec.Deriv.SourceCursor frameRoot (runtime dp)
      endpointPath source)
    (route : Exec.Deriv.SourceCursor.Toward
      initial write (.reg .sstore) endpointCursor) :
    RuntimeEndpointOccurrence dp frameRoot write source :=
  let chronology := Exec.Deriv.SourceCursor.Toward.chronology route
  { path := endpointPath
    cursor := endpointCursor
    frameToCursor := parentPrefixTrans frameToInitial chronology.initialToCursor
    cursorToWrite := chronology.cursorToTarget }

private theorem Exec.Deriv.SourceCursor.ninstRun_of_nextEdge
    {root : Exec.Deriv} {program : Prog}
    {path : Prog.SourcePath} {instruction : Ninst} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail))
    {tailCursor : Exec.Deriv.SourceCursor root program
      ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail}
    (edge : Exec.Deriv.ParentStep tailCursor.node cursor.node) :
    Ninst.Run root.sevm cursor.pre instruction tailCursor.pre := by
  rcases cursor with
    ⟨cursorPc, cursorPre, current, parentPrefix, codeSlice,
      codeBoundary, sourceIncluded⟩
  rcases tailCursor with
    ⟨tailPc, tailPre, tailCurrent, tailPrefix, tailSlice,
      tailBoundary, tailIncluded⟩
  change Exec.Deriv.ParentStep
    ⟨tailPc, root.sevm, tailPre, root.exn, tailCurrent⟩
    ⟨cursorPc, root.sevm, cursorPre, root.exn, current⟩ at edge
  have sourceAt : Ninst.At root.sevm.code cursorPc instruction :=
    Func.sourceSites_sound codeSlice codeBoundary
      (functionIndex := path.functionIndex) (steps := path.steps)
      (site := { path := path, pc := cursorPc, instruction := instruction })
      (by rcases path with ⟨functionIndex, steps⟩
          simp [Func.sourceSites])
  cases edge with
  | cont hstep next =>
      have actual := (Evm.step_next sourceAt).symm.trans hstep
      refine ⟨.none, trivial, cursorPc, ?_⟩
      simp only [Ninst.StepRun, actual, Step.Run]
      exact ⟨trivial, trivial⟩
  | doneOk hstep henter hresume next =>
      have actual := (Evm.step_next sourceAt).symm.trans hstep
      refine ⟨.none, trivial, cursorPc, ?_⟩
      simp only [Ninst.StepRun, actual, Step.Run]
      exact ⟨_, RunFrame.of_done henter, hresume.symm⟩
  | runOk hstep henter child hresume next =>
      have actual := (Evm.step_next sourceAt).symm.trans hstep
      refine ⟨.some ⟨_, _⟩, ⟨child⟩, cursorPc, ?_⟩
      simp only [Ninst.StepRun, actual, Step.Run]
      exact ⟨_, RunFrame.of_run henter, hresume.symm⟩

private theorem Exec.Deriv.ParentPrefix.advance_pushTowardSstore
    {start target : Exec.Deriv} {xs : Bytes}
    (reached : Exec.Deriv.ParentPrefix start target)
    (pushAt : PushAt start.sevm.code start.pc xs)
    (hne : xs ≠ [])
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ (inter : Devm)
      (next : Exec (start.pc + xs.length + 1) start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ start ∧
      Exec.Deriv.ParentPrefix
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ target ∧
      Devm.PushBurn [xs.toB256] start.devm inter := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  rcases pushAt with ⟨le, pushAt⟩
  cases reached with
  | refl =>
      have impossible := Ninst.at_unique storeAt pushAt
      cases impossible
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          have sourceStep := hstatic.symm.trans hstep
          rw [Ninst.step_push, if_neg hne] at sourceStep
          obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont sourceStep
          cases hpc
          exact ⟨_, next, .cont hstep next, rest,
            Devm.pushBurn_of_run hrun⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          exact (Step.ofExecution_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          exact (Step.ofExecution_ne_spawn (hstatic.symm.trans hstep)).elim

private theorem Exec.Deriv.ParentPrefix.advance_jumpTowardSstore
    {start target : Exec.Deriv} {instruction : Jinst}
    (reached : Exec.Deriv.ParentPrefix start target)
    (jumpAt : Jinst.At start.sevm.code start.pc instruction)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ (nextPc : Nat) (inter : Devm)
      (next : Exec nextPc start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ start ∧
      Exec.Deriv.ParentPrefix
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ target ∧
      Jinst.Run ⟨start.pc, start.sevm, start.devm⟩ instruction
        (.ok ⟨nextPc, inter⟩) := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  dsimp at reached storeAt jumpAt
  cases reached with
  | refl => exact (storeAt.false_of_jinstAt jumpAt).elim
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact ⟨_, _, next, .cont hstep next, rest,
            Step.ofJump_cont (hstatic.symm.trans hstep)⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim

private theorem Exec.Deriv.SourceCursor.branchFlagTowardSstore
    {root target : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {left right : Func}
    (cursor : Exec.Deriv.SourceCursor root program path (.branch left right))
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    (∃ arm : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.ParentPrefix arm.node target ∧
        [(0 : B256)] <<+ cursor.pre.stack) ∨
    (∃ flag : B256, flag ≠ 0 ∧ [flag] <<+ cursor.pre.stack) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, hlocEq, hloc, pushAt, jumpiAt, leftSlice, leftBoundary,
      jumpdestAt, jumpable, rightSlice, rightBoundary⟩
  rcases Exec.Deriv.ParentPrefix.advance_pushTowardSstore reached
      ⟨_, pushAt⟩ (by simp) storeAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ hloc] at pushBurn
  rcases Exec.Deriv.ParentPrefix.advance_jumpTowardSstore
      afterPushReached jumpiAt storeAt with
    ⟨nextPc, armPre, armExec, jumpEdge, armReached, jumpRun⟩
  rcases of_jumpi_run jumpRun with
    ⟨x, nextPcEq, popBurn⟩ | ⟨x, flag, nextPcEq, popBurn,
      actualJumpable, nonzero⟩
  · cases nextPcEq
    let armCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left :=
      ⟨_, _, armExec, cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge,
        leftSlice, leftBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          exact Or.inl member⟩
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have zeroPop : Devm.PopBurn [(0 : B256)] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    exact Or.inl ⟨armCursor, armReached,
      pref_of_split zeroPop.stack⟩
  · rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have flagPop : Devm.PopBurn [flag] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    exact Or.inr ⟨flag, nonzero, pref_of_split flagPop.stack⟩

private theorem linearDispatchWith_bodyCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (entries : List (B256 × Func)) {path : Prog.SourcePath}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (linearDispatchWith fallbackSlot entries))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ word body,
      (word, body) ∈ entries ∧
        ∃ bodyPath,
          ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
              bodyPath body,
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) bodyCursor := by
  induction entries generalizing path with
  | nil =>
      exact (cursor.noSstore_of_entrySstoreFree compiled
        [fallbackSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology route).cursorToTarget
        targetAt).elim
  | cons head tail ih =>
      rcases head with ⟨word, body⟩
      cases tail with
      | nil =>
          unfold linearDispatchWith at cursor
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
              (by intro h; cases h) with
            ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
              (by intro h; cases h) with
            ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
          cases branchRoute with
          | branchLeft branchCursor chronology arm compilerPrefix rest =>
              exact (arm.noSstore_of_entrySstoreFree compiled
                [fallbackSlot] rfl
                (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
                targetAt).elim
          | branchRight branchCursor chronology arm compilerPrefix rest =>
              exact ⟨word, body, by simp, _, arm, rest⟩
      | cons next rest =>
          unfold linearDispatchWith at cursor
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
              (by intro h; cases h) with
            ⟨dupChronology, pushCursor, dupEdge, pushRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne pushRoute
              (by intro h; cases h) with
            ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
          rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
              (by intro h; cases h) with
            ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
          cases branchRoute with
          | branchLeft branchCursor chronology arm compilerPrefix tailRoute =>
              rcases ih arm tailRoute with
                ⟨selectedWord, selectedBody, member, cut⟩
              exact ⟨selectedWord, selectedBody, by simp [member], cut⟩
          | branchRight branchCursor chronology arm compilerPrefix bodyRoute =>
              rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne
                  bodyRoute (by intro h; cases h) with
                ⟨popChronology, bodyCursor, popEdge, restRoute⟩
              exact ⟨word, body, by simp, _, bodyCursor, restRoute⟩

private theorem splitDispatch_bodyCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    {pivot : B256} {left right : Func}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (splitDispatch pivot left right))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    (∃ leftPath,
      ∃ leftCursor : Exec.Deriv.SourceCursor root (runtime dp)
          leftPath left,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) leftCursor) ∨
    (∃ rightPath,
      ∃ rightCursor : Exec.Deriv.SourceCursor root (runtime dp)
          rightPath right,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) rightCursor) := by
  unfold splitDispatch at cursor
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨dupChronology, pushCursor, dupEdge, pushRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne pushRoute
      (by intro h; cases h) with
    ⟨pushChronology, gtCursor, pushEdge, gtRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne gtRoute
      (by intro h; cases h) with
    ⟨gtChronology, branchCursor, gtEdge, branchRoute⟩
  cases branchRoute with
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact Or.inr ⟨_, arm, rest⟩
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact Or.inl ⟨_, arm, rest⟩

private theorem hybridDispatchWith_bodyCut
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (hybridDispatchWith fallbackSlot (funcs dp)))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ word body,
      (word, body) ∈ funcs dp ∧
        ∃ bodyPath,
          ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
              bodyPath body,
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) bodyCursor := by
  unfold hybridDispatchWith at cursor
  rcases splitDispatch_bodyCut cursor route with
    ⟨leftPath, leftCursor, leftRoute⟩ |
      ⟨rightPath, rightCursor, rightRoute⟩
  · rcases splitDispatch_bodyCut leftCursor leftRoute with
      ⟨firstPath, firstCursor, firstRoute⟩ |
        ⟨secondPath, secondCursor, secondRoute⟩
    · rcases linearDispatchWith_bodyCut compiled targetAt
          ((funcs dp).take 5) firstCursor firstRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      exact ⟨word, body, List.mem_of_mem_take member,
        bodyPath, bodyCursor, bodyRoute⟩
    · rcases linearDispatchWith_bodyCut compiled targetAt
          ((funcs dp).drop 5 |>.take 4) secondCursor secondRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      have memberDrop : (word, body) ∈ (funcs dp).drop 5 :=
        List.mem_of_mem_take member
      exact ⟨word, body, List.mem_of_mem_drop memberDrop,
        bodyPath, bodyCursor, bodyRoute⟩
  · rcases splitDispatch_bodyCut rightCursor rightRoute with
      ⟨thirdPath, thirdCursor, thirdRoute⟩ |
        ⟨fourthPath, fourthCursor, fourthRoute⟩
    · rcases linearDispatchWith_bodyCut compiled targetAt
          ((funcs dp).drop 9 |>.take 4) thirdCursor thirdRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      have memberDrop : (word, body) ∈ (funcs dp).drop 9 :=
        List.mem_of_mem_take member
      exact ⟨word, body, List.mem_of_mem_drop memberDrop,
        bodyPath, bodyCursor, bodyRoute⟩
    · rcases linearDispatchWith_bodyCut compiled targetAt
          ((funcs dp).drop 13) fourthCursor fourthRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      exact ⟨word, body, List.mem_of_mem_drop member,
        bodyPath, bodyCursor, bodyRoute⟩

private def runtimeViewSstoreFreeSlots : List Nat :=
  [emptyRevertSlot, bubbleRevertSlot, enumLoopSlot]

private inductive RuntimeDispatchCut
    {dp : DeployParams} {root target : Exec.Deriv}
    (initial : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp)) : Prop
  | setPauseDuration {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (setPauseDuration dp))
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
  | setHeartbeatInterval {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (setHeartbeatInterval dp))
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
  | registerPauser {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
        (registerPauser dp))
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
  | heartbeat {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path heartbeat)
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)
  | pause {path : Prog.SourcePath}
      (cursor : Exec.Deriv.SourceCursor root (runtime dp) path pause)
      (route : Exec.Deriv.SourceCursor.Toward
        initial target (.reg .sstore) cursor)

private theorem runtimeMain_writeEndpointCut
    {dp : DeployParams} {root target : Exec.Deriv}
    (mainCursor : Exec.Deriv.SourceCursor root (runtime dp) ⟨0, []⟩
      (runtimeMain dp))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      mainCursor target (.reg .sstore) mainCursor) :
    RuntimeDispatchCut (target := target) mainCursor := by
  unfold runtimeMain at mainCursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLine route
      (line := [Ninst.callvalue, Ninst.pushB256 4,
        Ninst.calldatasize, Ninst.lt, Ninst.or])
      (by
        intro instruction member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl <;>
          intro h <;> cases h) with
    ⟨entryPath, entryCursor, entryChronology, entryRoute⟩
  cases entryRoute with
  | branchRight cursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled [] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchLeft cursor chronology arm compilerPrefix rest =>
      rcases Exec.Deriv.SourceCursor.Toward.dropLine rest
          (line := fsig) (by
            intro instruction member
            simp only [fsig, cdl, shiftRight, List.mem_append,
              List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with (rfl | rfl) | (rfl | rfl) <;>
              intro h <;> cases h) with
        ⟨dispatchPath, dispatchCursor, dispatchChronology, dispatchRoute⟩
      rcases hybridDispatchWith_bodyCut compiled targetAt dispatchCursor
          dispatchRoute with
        ⟨word, body, member, bodyPath, bodyCursor, bodyRoute⟩
      simp only [funcs, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim

      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact .registerPauser bodyCursor bodyRoute
      · exact .heartbeat bodyCursor bodyRoute
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact .setHeartbeatInterval bodyCursor bodyRoute
      · exact .pause bodyCursor bodyRoute
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim
      · exact .setPauseDuration bodyCursor bodyRoute
      · exact (bodyCursor.noSstore_of_entrySstoreFree compiled
          runtimeViewSstoreFreeSlots rfl
          (Exec.Deriv.SourceCursor.Toward.chronology
            bodyRoute).cursorToTarget targetAt).elim

private theorem onlyAdminGuard
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource tail : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (onlyAdmin dp tail))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ guardPath guardTail,
      ∃ guardCursor : Exec.Deriv.SourceCursor root (runtime dp)
          guardPath (.next (.reg .eq) guardTail),
        ∃ branchCursor : Exec.Deriv.SourceCursor root (runtime dp)
            ⟨guardPath.functionIndex,
              guardPath.steps ++ [.rest]⟩ guardTail,
          Exec.Deriv.SourceCursor.Chronology
              initial guardCursor target ∧
            Exec.Deriv.ParentStep branchCursor.node guardCursor.node ∧
            Ninst.Run root.sevm guardCursor.pre (.reg .eq)
              branchCursor.pre ∧
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) branchCursor ∧
            root.sevm.caller.toB256 = dp.admin := by
  unfold onlyAdmin at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨callerChronology, pushCursor, callerEdge, callerRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne callerRoute
      (by intro h; cases h) with
    ⟨pushChronology, eqCursor, pushEdge, eqRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne eqRoute
      (by intro h; cases h) with
    ⟨eqChronology, branchCursor, eqEdge, branchRoute⟩
  have callerRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge cursor callerEdge
  have pushRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge pushCursor pushEdge
  have eqRun :=
    Exec.Deriv.SourceCursor.ninstRun_of_nextEdge eqCursor eqEdge
  have callerPrefix :
      [root.sevm.caller.toB256] <<+ pushCursor.pre.stack :=
    prefix_of_push (of_run_caller callerRun) nil_pref
  have adminPrefix :
      [dp.admin, root.sevm.caller.toB256] <<+ eqCursor.pre.stack := by
    simpa [pushDeployWord, B256.toB256_toBytes] using
      prefix_of_push (of_run_push pushRun) callerPrefix
  have eqPrefix :
      [(dp.admin =? root.sevm.caller.toB256)] <<+
        branchCursor.pre.stack :=
    prefix_of_eq eqRun adminPrefix
  rcases Exec.Deriv.SourceCursor.branchFlagTowardSstore branchCursor
      (Exec.Deriv.SourceCursor.Toward.chronology branchRoute).cursorToTarget
      targetAt with errorArm | ⟨flag, nonzero, flagPrefix⟩
  · rcases errorArm with ⟨errorCursor, errorReached, zeroPrefix⟩
    exact (errorCursor.noSstore_of_entrySstoreFree compiled
      [senderNotAdminErrorSlot] rfl errorReached targetAt).elim
  · have flagEq :
        (dp.admin =? root.sevm.caller.toB256) = flag :=
      pref_head_unique eqPrefix flagPrefix
    have callerEq : root.sevm.caller.toB256 = dp.admin := by
      by_contra different
      have checkZero :
          (dp.admin =? root.sevm.caller.toB256) = 0 := by
        simp [B256.eqCheck, Ne.symm different]
      exact nonzero (flagEq ▸ checkZero)
    exact ⟨_, _, eqCursor, branchCursor, eqChronology, eqEdge,
      eqRun, branchRoute, callerEq⟩

private theorem requireStaticOnlyAdminGuard
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource tail : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (argCount : Nat)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (requireStaticArgs argCount (onlyAdmin dp tail)))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ guardPath guardTail,
      ∃ guardCursor : Exec.Deriv.SourceCursor root (runtime dp)
          guardPath (.next (.reg .eq) guardTail),
        ∃ branchCursor : Exec.Deriv.SourceCursor root (runtime dp)
            ⟨guardPath.functionIndex,
              guardPath.steps ++ [.rest]⟩ guardTail,
          Exec.Deriv.SourceCursor.Chronology
              initial guardCursor target ∧
            Exec.Deriv.ParentStep branchCursor.node guardCursor.node ∧
            Ninst.Run root.sevm guardCursor.pre (.reg .eq)
              branchCursor.pre ∧
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) branchCursor ∧
            root.sevm.caller.toB256 = dp.admin := by
  unfold requireStaticArgs at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨sizeChronology, sizeCursor, sizeEdge, sizeRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne sizeRoute
      (by intro h; cases h) with
    ⟨calldataChronology, calldataCursor, calldataEdge, calldataRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne calldataRoute
      (by intro h; cases h) with
    ⟨ltChronology, argsBranchCursor, ltEdge, argsBranchRoute⟩
  cases argsBranchRoute with
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled [] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact onlyAdminGuard arm compiled targetAt rest

private theorem requireStaticArgsToward
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource body : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (words : Nat)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (requireStaticArgs words body))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ bodyPath,
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          bodyPath body,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) bodyCursor := by
  unfold requireStaticArgs at cursor route
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne route
      (by intro h; cases h) with
    ⟨sizeChronology, sizeCursor, sizeEdge, sizeRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne sizeRoute
      (by intro h; cases h) with
    ⟨calldataChronology, calldataCursor, calldataEdge, calldataRoute⟩
  rcases Exec.Deriv.SourceCursor.Toward.next_of_instruction_ne calldataRoute
      (by intro h; cases h) with
    ⟨ltChronology, branchCursor, ltEdge, branchRoute⟩
  cases branchRoute with
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled [] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact ⟨_, arm, rest⟩

private theorem canonicalAddressArgToward
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource body : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (index : B256)
    (cursor : Exec.Deriv.SourceCursor root (runtime dp) path
      (canonicalAddressArg index body))
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) cursor) :
    ∃ bodyPath,
      ∃ bodyCursor : Exec.Deriv.SourceCursor root (runtime dp)
          bodyPath body,
        Exec.Deriv.SourceCursor.Toward
          initial target (.reg .sstore) bodyCursor := by
  unfold canonicalAddressArg at cursor
  rcases Exec.Deriv.SourceCursor.Toward.dropLine route
      (line := arg index ++ checkNonAddress)
      (by simp [arg, checkNonAddress, cdl, pushAddressMask,
        Ninst.pushB256]) with
    ⟨branchPath, branchCursor, branchChronology, branchRoute⟩
  cases branchRoute with
  | branchRight branchCursor chronology arm compilerPrefix rest =>
      exact (arm.noSstore_of_entrySstoreFree compiled
        [emptyRevertSlot] rfl
        (Exec.Deriv.SourceCursor.Toward.chronology rest).cursorToTarget
        targetAt).elim
  | branchLeft branchCursor chronology arm compilerPrefix rest =>
      exact ⟨_, arm, rest⟩

/-- A target-directed route through the heartbeat-interval setter retains the
actual `onlyAdmin` equality, its successful next edge, and the entry caller
fact.  This is deliberately local to the concrete Lido source body. -/
private theorem setHeartbeatIntervalBodyGuard
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (sourceEq : source = setHeartbeatInterval dp)
    (bodyCursor : Exec.Deriv.SourceCursor root (runtime dp) path source)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) bodyCursor) :
    ∃ guardPath guardTail,
      ∃ guardCursor : Exec.Deriv.SourceCursor root (runtime dp)
          guardPath (.next (.reg .eq) guardTail),
        ∃ branchCursor : Exec.Deriv.SourceCursor root (runtime dp)
            ⟨guardPath.functionIndex,
              guardPath.steps ++ [.rest]⟩ guardTail,
          Exec.Deriv.SourceCursor.Chronology
              initial guardCursor target ∧
            Exec.Deriv.ParentStep branchCursor.node guardCursor.node ∧
            Ninst.Run root.sevm guardCursor.pre (.reg .eq)
              branchCursor.pre ∧
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) branchCursor ∧
            root.sevm.caller.toB256 = dp.admin := by
  subst source
  exact requireStaticOnlyAdminGuard 1 bodyCursor compiled targetAt route

private theorem registerPauserBodyGuard
    {dp : DeployParams} {root target : Exec.Deriv}
    {initialPath path : Prog.SourcePath} {initialSource source : Func}
    {initial : Exec.Deriv.SourceCursor root (runtime dp)
      initialPath initialSource}
    (sourceEq : source = registerPauser dp)
    (bodyCursor : Exec.Deriv.SourceCursor root (runtime dp) path source)
    (compiled : some root.sevm.code.toList = (runtime dp).compile)
    (targetAt : Ninst.At target.sevm.code target.pc (.reg .sstore))
    (route : Exec.Deriv.SourceCursor.Toward
      initial target (.reg .sstore) bodyCursor) :
    ∃ guardPath guardTail,
      ∃ guardCursor : Exec.Deriv.SourceCursor root (runtime dp)
          guardPath (.next (.reg .eq) guardTail),
        ∃ branchCursor : Exec.Deriv.SourceCursor root (runtime dp)
            ⟨guardPath.functionIndex,
              guardPath.steps ++ [.rest]⟩ guardTail,
          Exec.Deriv.SourceCursor.Chronology
              initial guardCursor target ∧
            Exec.Deriv.ParentStep branchCursor.node guardCursor.node ∧
            Ninst.Run root.sevm guardCursor.pre (.reg .eq)
              branchCursor.pre ∧
            Exec.Deriv.SourceCursor.Toward
              initial target (.reg .sstore) branchCursor ∧
            root.sevm.caller.toB256 = dp.admin := by
  subst source
  rcases requireStaticArgsToward 2 bodyCursor compiled targetAt route with
    ⟨firstPath, firstCursor, firstRoute⟩
  rcases canonicalAddressArgToward 0 firstCursor compiled targetAt firstRoute with
    ⟨secondPath, secondCursor, secondRoute⟩
  rcases canonicalAddressArgToward 1 secondCursor compiled targetAt secondRoute with
    ⟨adminPath, adminCursor, adminRoute⟩
  exact onlyAdminGuard adminCursor compiled targetAt adminRoute

/-- Every nominated same-frame SSTORE occurrence in an exact selected runtime
frame has one unique typed source row.  The selected frame may be any raw
descendant root and may have any terminal outcome. -/
theorem Exec.NinstOccurrence.runtimePersistentWrite_of_rawFrameRoot
    {dp : DeployParams} {ca : Adr}
    {globalRoot frameRoot : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence globalRoot)
    (instructionEq : occurrence.instruction = .reg .sstore)
    (selected : frameRoot ∈ Exec.rawFrameRoots globalRoot.exc)
    (invocation : frameRoot.exactInvocation (runtime dp) ca ca)
    (sameFrame : Exec.Deriv.ParentPrefix frameRoot occurrence.node) :
    ∃ row : RuntimePersistentWrite, ∃ site : Prog.SourceSite,
      row ∈ RuntimePersistentWrite.all ∧
      row.sourceSite? dp = some site ∧
      classifyRuntimePersistentWrite dp site.path site.pc = some row ∧
      site.pc = occurrence.node.pc ∧
      site.instruction = .reg .sstore ∧
      ∀ candidate : RuntimePersistentWrite,
        candidate.sourceSite? dp = some site → candidate = row := by
  rcases occurrence.sourceSite_of_rawFrameRoot instructionEq selected invocation
      sameFrame with ⟨site, sourceMember, pcEq, siteInstruction⟩
  have persistentMember : site ∈ runtimePersistentSourceSites dp := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨sourceMember, by
      simp [siteInstruction, isPersistentWriteInstruction]⟩
  rcases runtimePersistentSourceSite_iff_row.mp persistentMember with
    ⟨row, rowMember, found⟩
  refine ⟨row, site, rowMember, found,
    classifyRuntimePersistentWrite_complete found, pcEq, siteInstruction, ?_⟩
  intro candidate candidateFound
  exact RuntimePersistentWrite.sourceSite?_injective candidateFound found

/-- Clean direct-message settlement preserves the exact committed raw world at
the CircuitBreaker owner.  This is the settlement-altitude bridge used before
retained-last-writer attribution; it does not claim raw log erasure. -/
theorem ProcessMessage.runtimeOwnerStorage_eq_committedPost
    {dp : DeployParams} {ca : Adr} {msg : Msg} {settled : Devm}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out)
    (_invocation :
      (⟨0, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        (runtime dp) ca ca)
    (process : ProcessMessage msg
      (.some ⟨⟨0, sevm, pre⟩, out⟩) (.ok settled))
    (committed : Execution.commits out = true) :
    Devm.getStor settled ca =
      Devm.getStor (Execution.committedPost out committed) ca := by
  have stateEq :=
    ProcessMessage.ok_state_eq_committedPost process committed
  exact congrArg (fun state : State => state.getStor ca) stateEq

end Blanc.LidoCircuitBreaker
